use super::integer::{IntegerChip, IntegerConfig};
use crate::halo2;
use crate::integer;
use crate::maingate;
use ecc::halo2::plonk::Column;
use ecc::halo2::plonk::Instance;
use ecc::maingate::RegionCtx;
use ecc::{AssignedPoint, EccConfig, GeneralEccChip};
use halo2::arithmetic::{CurveAffine, FieldExt};
use halo2::{circuit::Value, plonk::Error};
use integer::rns::Integer;
use integer::{AssignedInteger, IntegerInstructions};
use maingate::{MainGateConfig, RangeConfig};

#[derive(Clone, Debug)]
pub struct EcdsaConfig {
    main_gate_config: MainGateConfig,
    range_config: RangeConfig,
}

impl EcdsaConfig {
    pub fn new(range_config: RangeConfig, main_gate_config: MainGateConfig) -> Self {
        Self {
            range_config,
            main_gate_config,
        }
    }

    pub fn ecc_chip_config(&self) -> EccConfig {
        EccConfig::new(self.range_config.clone(), self.main_gate_config.clone())
    }

    pub fn integer_chip_config(&self) -> IntegerConfig {
        IntegerConfig::new(self.range_config.clone(), self.main_gate_config.clone())
    }
}

#[derive(Clone, Debug)]
pub struct EcdsaSig<
    W: FieldExt,
    N: FieldExt,
    const NUMBER_OF_LIMBS: usize,
    const BIT_LEN_LIMB: usize,
> {
    pub r: Integer<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    pub s: Integer<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
}

pub struct AssignedEcdsaSig<
    W: FieldExt,
    N: FieldExt,
    const NUMBER_OF_LIMBS: usize,
    const BIT_LEN_LIMB: usize,
> {
    pub r: AssignedInteger<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    pub s: AssignedInteger<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
}

pub struct AssignedPublicKey<
    W: FieldExt,
    N: FieldExt,
    const NUMBER_OF_LIMBS: usize,
    const BIT_LEN_LIMB: usize,
> {
    pub point: AssignedPoint<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
}

pub struct EcdsaChip<
    E: CurveAffine,
    N: FieldExt,
    const NUMBER_OF_LIMBS: usize,
    const BIT_LEN_LIMB: usize,
>(GeneralEccChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>);

impl<E: CurveAffine, N: FieldExt, const NUMBER_OF_LIMBS: usize, const BIT_LEN_LIMB: usize>
    EcdsaChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>
{
    pub fn new(ecc_chip: GeneralEccChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>) -> Self {
        Self(ecc_chip)
    }

    pub fn scalar_field_chip(
        &self,
    ) -> &IntegerChip<E::ScalarExt, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
        self.0.scalar_field_chip()
    }

    fn ecc_chip(&self) -> GeneralEccChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
        self.0.clone()
    }
}

impl<E: CurveAffine, N: FieldExt, const NUMBER_OF_LIMBS: usize, const BIT_LEN_LIMB: usize>
    EcdsaChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>
{
    pub fn verify(
        &self,
        ctx: &mut RegionCtx<'_, N>,
        sig: &AssignedEcdsaSig<E::Scalar, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
        pk: &AssignedPublicKey<E::Base, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
        msg_hash: &AssignedInteger<E::Scalar, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    ) -> Result<(), Error> {
        print!("111111111111");
        let ecc_chip = self.ecc_chip();
        let scalar_chip = ecc_chip.scalar_field_chip();
        let base_chip = ecc_chip.base_field_chip();

        // 1. check 0 < r, s < n

        // since `assert_not_zero` already includes a in-field check, we can just
        // call `assert_not_zero`
        scalar_chip.assert_not_zero(ctx, &sig.r)?;
        scalar_chip.assert_not_zero(ctx, &sig.s)?;

        // 2. w = s^(-1) (mod n)
        let (s_inv, _) = scalar_chip.invert(ctx, &sig.s)?;

        // 3. u1 = m' * w (mod n)
        let u1 = scalar_chip.mul(ctx, msg_hash, &s_inv)?;

        // 4. u2 = r * w (mod n)
        let u2 = scalar_chip.mul(ctx, &sig.r, &s_inv)?;

        // 5. compute Q = u1*G + u2*pk
        let e_gen = ecc_chip.assign_point(ctx, Value::known(E::generator()))?;
        let g1 = ecc_chip.mul(ctx, &e_gen, &u1, 2)?;
        let g2 = ecc_chip.mul(ctx, &pk.point, &u2, 2)?;
        let q = ecc_chip.add(ctx, &g1, &g2)?;

        // 6. reduce q_x in E::ScalarExt
        // assuming E::Base/E::ScalarExt have the same number of limbs
        let q_x = q.x();
        let q_x_reduced_in_q = base_chip.reduce(ctx, q_x)?;
        let q_x_reduced_in_r = scalar_chip.reduce_external(ctx, &q_x_reduced_in_q)?;

        // 7. check if Q.x == r (mod n)
        scalar_chip.assert_strict_equal(ctx, &q_x_reduced_in_r, &sig.r)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    // use halo2_gadgets::sinsemilla::chip
    use super::{AssignedEcdsaSig, AssignedPublicKey, EcdsaChip};
    use crate::halo2;
    use crate::integer;
    use crate::maingate;
    use ecc::halo2::halo2curves::secp256k1::Fq;
    // use ecc::halo2::halo2curves::secp256k1::Fp;
    use ecc::halo2::halo2curves::secp256k1::Secp256k1;
    use ecc::halo2::halo2curves::secp256k1::Secp256k1Affine;
    use ecc::halo2::plonk::Advice;
    use ecc::halo2::plonk::Column;
    use ecc::halo2::plonk::Instance;
    // use ecc::halo2::halo2curves::secp256k1::Secp256k1Compressed;
    // use ecc::halo2::plonk::Column;
    // use ecc::halo2::plonk::Instance;
    use ecc::integer::rns::Common;
    use ecc::integer::Range;
    use ecc::maingate::big_to_fe;
    use ecc::maingate::fe_to_big;
    use ecc::maingate::RegionCtx;
    use ecc::{EccConfig, GeneralEccChip};
    use group::ff::Field;
    use group::{Curve, Group};
    use halo2::arithmetic::CurveAffine;
    use halo2::arithmetic::FieldExt;
    use halo2::circuit::{Layouter, SimpleFloorPlanner, Value};
    use halo2::plonk::{Circuit, ConstraintSystem, Error};
    use halo2_gadgets::sinsemilla::chip::SinsemillaChip;
    use halo2_gadgets::sinsemilla::merkle::chip::MerkleChip;
    use halo2_gadgets::sinsemilla::merkle::chip::MerkleConfig;
    use halo2_gadgets::sinsemilla::merkle::MerklePath;
    use integer::IntegerInstructions;
    use maingate::mock_prover_verify;
    use maingate::{MainGate, MainGateConfig, RangeChip, RangeConfig, RangeInstructions};
    use orchard::constants::OrchardCommitDomains;
    use orchard::constants::OrchardFixedBases;
    use orchard::constants::OrchardHashDomains;
    use rand_core::OsRng;
    use std::marker::PhantomData;

    const BIT_LEN_LIMB: usize = 68;
    const NUMBER_OF_LIMBS: usize = 4;

    #[derive(Clone, Debug)]
    struct TestCircuitEcdsaVerifyConfig {
        main_gate_config: MainGateConfig,
        range_config: RangeConfig,
        pk_column: Column<Advice>,
        instance: Column<Instance>,
        // sinsemilla
        merkle_config_1: MerkleConfig<OrchardHashDomains, OrchardCommitDomains, OrchardFixedBases>,
        merkle_config_2: MerkleConfig<OrchardHashDomains, OrchardCommitDomains, OrchardFixedBases>,
    }

    impl TestCircuitEcdsaVerifyConfig {
        pub fn new<C: CurveAffine, N: FieldExt>(meta: &mut ConstraintSystem<N>) -> Self {
            let (rns_base, rns_scalar) =
                GeneralEccChip::<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::rns();

            let num_inst_cols = meta.num_instance_columns();
            println!("1 number of instance columns: {}\n", num_inst_cols);

            let main_gate_config = MainGate::<N>::configure(meta);

            let num_inst_cols = meta.num_instance_columns();
            println!("2 number of instance columns: {}\n", num_inst_cols);

            let mut overflow_bit_lens: Vec<usize> = vec![];
            overflow_bit_lens.extend(rns_base.overflow_lengths());
            overflow_bit_lens.extend(rns_scalar.overflow_lengths());
            let composition_bit_lens = vec![BIT_LEN_LIMB / NUMBER_OF_LIMBS];

            let range_config = RangeChip::<N>::configure(
                meta,
                &main_gate_config,
                composition_bit_lens,
                overflow_bit_lens,
            );

            let pk_column = meta.advice_column();
            meta.enable_equality(pk_column);
            let instance = meta.instance_column();
            meta.enable_equality(instance);

            let num_inst_cols = meta.num_instance_columns();
            println!("3 number of instance columns: {}\n", num_inst_cols);

            // sinsemilla
            {
                // Configuration for a Sinsemilla hash instantiation and a
                // Merkle hash instantiation using this Sinsemilla instance.
                // Since the Sinsemilla config uses only 5 advice columns,
                // we can fit two instances side-by-side.
                let (sinsemilla_config_1, merkle_config_1) = {
                    let sinsemilla_config_1 = SinsemillaChip::configure(
                        meta,
                        advices[..5].try_into().unwrap(),
                        advices[6],
                        lagrange_coeffs[0],
                        lookup,
                        range_check,
                    );
                    let merkle_config_1 = MerkleChip::configure(meta, sinsemilla_config_1.clone());

                    (sinsemilla_config_1, merkle_config_1)
                };

                // Configuration for a Sinsemilla hash instantiation and a
                // Merkle hash instantiation using this Sinsemilla instance.
                // Since the Sinsemilla config uses only 5 advice columns,
                // we can fit two instances side-by-side.
                let (sinsemilla_config_2, merkle_config_2) = {
                    let sinsemilla_config_2 = SinsemillaChip::configure(
                        meta,
                        advices[5..].try_into().unwrap(),
                        advices[7],
                        lagrange_coeffs[1],
                        lookup,
                        range_check,
                    );
                    let merkle_config_2 = MerkleChip::configure(meta, sinsemilla_config_2.clone());

                    (sinsemilla_config_2, merkle_config_2)
                };
            };

            TestCircuitEcdsaVerifyConfig {
                main_gate_config,
                range_config,
                pk_column,
                instance,
            }
        }

        pub fn ecc_chip_config(&self) -> EccConfig {
            EccConfig::new(self.range_config.clone(), self.main_gate_config.clone())
        }

        pub fn merkle_chip_1(
            &self,
        ) -> MerkleChip<OrchardHashDomains, OrchardCommitDomains, OrchardFixedBases> {
            MerkleChip::construct(self.merkle_config_1.clone())
        }

        pub fn merkle_chip_2(
            &self,
        ) -> MerkleChip<OrchardHashDomains, OrchardCommitDomains, OrchardFixedBases> {
            MerkleChip::construct(self.merkle_config_2.clone())
        }

        pub fn config_range<N: FieldExt>(
            &self,
            layouter: &mut impl Layouter<N>,
        ) -> Result<(), Error> {
            let range_chip = RangeChip::<N>::new(self.range_config.clone());
            range_chip.load_table(layouter)?;

            Ok(())
        }
    }

    #[derive(Default, Clone)]
    struct TestCircuitEcdsaVerify<E: CurveAffine, N: FieldExt> {
        public_key: Value<E>,
        signature: Value<(E::Scalar, E::Scalar)>,
        msg_hash: Value<E::Scalar>,

        v: Value<N>,

        aux_generator: E,
        window_size: usize,
        _marker: PhantomData<N>,
    }

    impl<E: CurveAffine, N: FieldExt> Circuit<N> for TestCircuitEcdsaVerify<E, N> {
        type Config = TestCircuitEcdsaVerifyConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<N>) -> Self::Config {
            TestCircuitEcdsaVerifyConfig::new::<E, N>(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<N>,
        ) -> Result<(), Error> {
            println!("self.public_key: {:?}\n", self.public_key);

            let mut ecc_chip = GeneralEccChip::<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::new(
                config.ecc_chip_config(),
            );

            let pk = layouter.assign_region(
                || "assign public key",
                |mut region| {
                    let pk = self.public_key.map(|p| {
                        // let a = p.coordinates().unwrap();
                        let a = ecc_chip.to_rns_point(p);
                        // let b = a.x();
                        // println!("222 bb: {:?}", b);

                        // let a: N = a.x();
                        // let a = a.get_lower_128();

                        // N::from_u128(a)
                        // .into() as N;
                        // N::from(a.into())
                        // n
                    });
                    println!("1111111 pk: {:?}\n", pk);
                    // let a = N::from(self.public_key);

                    // let cell = region.assign_advice(|| "private input", config.pk_column, 0, || pk);

                    // println!("load_private(): region: {:?}, cell: {:?}\n", region, cell);

                    // cell.map(|x| Number(x))
                    Ok(())
                },
                // |region| {
                //     let offset = 0;
                //     let ctx = &mut RegionCtx::new(region, offset);

                //     ecc_chip.assign_aux_generator(ctx, Value::known(self.aux_generator))?;
                //     ecc_chip.assign_aux(ctx, self.window_size, 1)?;

                //     Ok(())
                // },
            )?;

            layouter.assign_region(
                || "assign aux values",
                |region| {
                    let offset = 0;
                    let ctx = &mut RegionCtx::new(region, offset);

                    ecc_chip.assign_aux_generator(ctx, Value::known(self.aux_generator))?;
                    ecc_chip.assign_aux(ctx, self.window_size, 1)?;
                    Ok(())
                },
            )?;

            let a = layouter.assign_region(
                || "load private",
                |mut region| {
                    let cell =
                        region.assign_advice(|| "private input", config.pk_column, 0, || self.v);

                    println!("load_private(): region: {:?}, cell: {:?}\n", region, cell);

                    cell
                },
            )?;

            let ecdsa_chip = EcdsaChip::new(ecc_chip.clone());
            let scalar_chip = ecc_chip.scalar_field_chip();

            let pk1 = layouter.assign_region(
                || "region 0",
                |region| {
                    let offset = 0;
                    let ctx = &mut RegionCtx::new(region, offset);

                    let r = self.signature.map(|signature| signature.0);
                    let s = self.signature.map(|signature| signature.1);
                    let integer_r = ecc_chip.new_unassigned_scalar(r);
                    let integer_s = ecc_chip.new_unassigned_scalar(s);
                    let msg_hash = ecc_chip.new_unassigned_scalar(self.msg_hash);

                    let r_assigned =
                        scalar_chip.assign_integer(ctx, integer_r, Range::Remainder)?;
                    let s_assigned =
                        scalar_chip.assign_integer(ctx, integer_s, Range::Remainder)?;
                    let sig = AssignedEcdsaSig {
                        r: r_assigned,
                        s: s_assigned,
                    };

                    let pk_in_circuit = ecc_chip.assign_point(ctx, self.public_key)?;

                    println!("pk_in_circuit(): {:?}\n", pk_in_circuit);

                    let pk_assigned = AssignedPublicKey {
                        point: pk_in_circuit,
                    };
                    let msg_hash = scalar_chip.assign_integer(ctx, msg_hash, Range::Remainder)?;
                    ecdsa_chip.verify(ctx, &sig, &pk_assigned, &msg_hash)?;

                    Ok(pk_assigned)
                },
            )?;

            let pk_x = pk1.point.x().native();

            println!("pk1: {:?}\n", pk1.point);

            println!("pk_x: {:?}\n", pk_x);

            println!("33 a: {:?}\n", a);

            // layouter.constrain_instance(a.cell(), config.instance, 0)?;
            layouter.constrain_instance(pk_x.cell(), config.instance, 0)?;

            // println!("instance: {:?}\n", config.instance);

            // let a = pk1.point.x().native().cell();

            config.config_range(&mut layouter)?;

            let root = {
                // let path = self
                //     .path
                //     .map(|typed_path| typed_path.map(|node| node.inner()));
                let path = vec![];
                let merkle_inputs = MerklePath::construct(
                    [config.merkle_chip_1(), config.merkle_chip_2()],
                    OrchardHashDomains::MerkleCrh,
                    self.pos,
                    path,
                );
                let leaf = cm_old.extract_p().inner().clone();
                merkle_inputs.calculate_root(layouter.namespace(|| "Merkle path"), leaf)?
            };

            // layouter.constrain_instance(a, config.instance, 0)?;
            // layouter.constrain_instance(cell, column, row);

            Ok(())
        }
    }

    #[test]
    fn test_ecdsa_verifier() {
        fn mod_n<C: CurveAffine>(x: C::Base) -> C::Scalar {
            let x_big = fe_to_big(x);
            big_to_fe(x_big)
        }

        // use halo2::circuit::s
        use ecc::halo2::halo2curves::secp256k1::Fp;
        use ecc::halo2::halo2curves::secp256k1::Fq;
        use ecc::halo2::halo2curves::{CurveAffine, FieldExt};
        use group::ff::PrimeField;
        fn mod_n2(x: Fp) -> Fq {
            let mut x_repr = [0u8; 32];
            x_repr.copy_from_slice(x.to_repr().as_ref());
            let mut x_bytes = [0u8; 64];
            x_bytes[..32].copy_from_slice(&x_repr[..]);
            Fq::from_bytes_wide(&x_bytes)
        }

        fn run<C: CurveAffine, N: FieldExt>(sk: C) {
            let g = C::generator();

            // Generate a key pair
            let sk = <C as CurveAffine>::ScalarExt::random(OsRng);
            let public_key = (g * sk).to_affine();

            println!("public_key: {:?}\n", public_key);

            let b1 = public_key.coordinates().unwrap();

            let b2 = b1.x();

            // let bb: N = bb.x().into();
            //
            //
            //
            // Fp::from_raw(bb.x());
            //
            // b2.to_repr();

            // println!("b2: {:?}\n", b2.to_bytes());

            // Generate a valid signature
            // Suppose `m_hash` is the message hash
            let msg_hash = <C as CurveAffine>::ScalarExt::random(OsRng);

            // Draw arandomness
            let k = <C as CurveAffine>::ScalarExt::random(OsRng);
            let k_inv = k.invert().unwrap();

            // Calculate `r`
            let r_point = (g * k).to_affine().coordinates().unwrap();
            let x = r_point.x();
            let r = mod_n::<C>(*x);

            // Calculate `s`
            let s = k_inv * (msg_hash + (r * sk));

            println!("r: {:?}, s: {:?}\n", r, s);

            // Sanity check. Ensure we construct a valid signature. So lets verify it
            {
                let s_inv = s.invert().unwrap();
                let u_1 = msg_hash * s_inv;
                let u_2 = r * s_inv;
                let r_point = ((g * u_1) + (public_key * u_2))
                    .to_affine()
                    .coordinates()
                    .unwrap();
                let x_candidate = r_point.x();
                let r_candidate = mod_n::<C>(*x_candidate);
                assert_eq!(r, r_candidate);
            }

            let aux_generator = C::CurveExt::random(OsRng).to_affine();
            let circuit = TestCircuitEcdsaVerify::<C, N> {
                public_key: Value::known(public_key),
                signature: Value::known((r, s)),
                msg_hash: Value::known(msg_hash),
                aux_generator,
                window_size: 2,
                ..Default::default()
            };

            let instance = vec![vec![]];
            assert_eq!(mock_prover_verify(&circuit, instance), Ok(()));
        }

        fn run2() {
            let g = Secp256k1::generator();
            let sk = Fq::random(OsRng);
            let pk = (g * sk).to_affine();

            // Generate a valid signature
            // Suppose `m_hash` is the message hash
            let msg_hash = Fq::random(OsRng);

            let (r, s) = {
                // Draw arandomness
                let k = Fq::random(OsRng);
                let k_inv = k.invert().unwrap();

                // Calculate `r`
                let r_point = (g * k).to_affine().coordinates().unwrap();
                let x = r_point.x();
                let r: Fq = mod_n2(*x);

                // Calculate `s`
                let s: Fq = k_inv * (msg_hash + (r * sk));

                (r, s)
            };

            {
                // Verify
                let s_inv = s.invert().unwrap();
                let u_1 = msg_hash * s_inv;
                let u_2: Fq = r * s_inv;

                let v_1 = g * u_1;
                let v_2 = pk * u_2;

                let r_point = (v_1 + v_2).to_affine().coordinates().unwrap();
                let x_candidate = r_point.x();
                let r_candidate = mod_n2(*x_candidate);

                assert_eq!(r, r_candidate);
            }

            let aux_generator = Secp256k1::random(OsRng).to_affine();

            let v = Fq::from(1);
            let v2 = Fq::from(2);
            // let v = N::from_u128(1);

            let circuit = TestCircuitEcdsaVerify::<Secp256k1Affine, Fq> {
                public_key: Value::known(pk),
                signature: Value::known((r, s)),
                msg_hash: Value::known(msg_hash),
                aux_generator,
                window_size: 2,
                v: Value::known(v),
                ..Default::default()
            };

            let input = pk.coordinates().unwrap().x().clone();
            let input = Fq::from_bytes(&input.to_bytes()).unwrap();

            let instance = vec![vec![v], vec![input]];

            println!("pk: {:?}, msg_hash: {:?}\n", pk, msg_hash);
            println!("r: {:?}, s: {:?}\n", r, s);
            println!("input: {:?}\n", input);
            println!("v: {:?}\n", v);

            assert_eq!(mock_prover_verify(&circuit, instance), Ok(()));
        }

        // use crate::curves::bn256::Fr as BnScalar;
        // use crate::curves::pasta::{Fp as PastaFp, Fq as PastaFq};
        // use crate::curves::secp256k1::Secp256k1Affine as Secp256k1;
        // let c = ecc::halo2::halo2curves::secp256k1::Fp::from(0);
        // c.to_bytes();
        // let g = Secp256k1::generator();
        // let sk = Secp256k1::random(OsRng);
        // let a = g * sk;
        // run::<Secp256k1, ecc::halo2::halo2curves::secp256k1::Fp>(sk);
        println!("111");
        run2();
        // run::<Secp256k1, PastaFp>();
        // run::<Secp256k1, PastaFq>();
    }
}

// #[cfg(test)]
// pub mod tests2 {
//     use halo2_gadgets::sinsemilla::merkle::{
//         chip::{MerkleChip, MerkleConfig},
//         MerklePath,
//     };

//     use crate::{
//         ecc::tests::TestFixedBases,
//         sinsemilla::{
//             chip::SinsemillaChip,
//             tests::{TestCommitDomain, TestHashDomain},
//             HashDomains,
//         },
//         utilities::{i2lebsp, lookup_range_check::LookupRangeCheckConfig, UtilitiesInstructions},
//     };

//     use group::ff::{Field, PrimeField, PrimeFieldBits};
//     use halo2_proofs::{
//         circuit::{Layouter, SimpleFloorPlanner, Value},
//         dev::MockProver,
//         pasta::pallas,
//         plonk::{Circuit, ConstraintSystem, Error},
//     };

//     use rand::{rngs::OsRng, RngCore};
//     use std::{convert::TryInto, iter};

//     const MERKLE_DEPTH: usize = 32;

//     #[derive(Default)]
//     struct MyCircuit {
//         leaf: Value<pallas::Base>,
//         leaf_pos: Value<u32>,
//         merkle_path: Value<[pallas::Base; MERKLE_DEPTH]>,
//     }

//     impl Circuit<pallas::Base> for MyCircuit {
//         type Config = (
//             MerkleConfig<TestHashDomain, TestCommitDomain, TestFixedBases>,
//             MerkleConfig<TestHashDomain, TestCommitDomain, TestFixedBases>,
//         );
//         type FloorPlanner = SimpleFloorPlanner;

//         fn without_witnesses(&self) -> Self {
//             Self::default()
//         }

//         fn configure(meta: &mut ConstraintSystem<pallas::Base>) -> Self::Config {
//             let advices = [
//                 meta.advice_column(),
//                 meta.advice_column(),
//                 meta.advice_column(),
//                 meta.advice_column(),
//                 meta.advice_column(),
//                 meta.advice_column(),
//                 meta.advice_column(),
//                 meta.advice_column(),
//                 meta.advice_column(),
//                 meta.advice_column(),
//             ];

//             //   !                              <                       >      <>
//             // 0xb2bd6a00feb3f528ef1f8556699a26a52d1a1fddbec80f87f36bcfed27eb02b0
//             // 0x32bd6a00feb3f528ef1f8556699a26a4e88cede5ac2e1d50c1116e1327eb02ae
//             // 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001

//             // Shared fixed column for loading constants
//             let constants = meta.fixed_column();
//             meta.enable_constant(constants);

//             // NB: In the actual Action circuit, these fixed columns will be reused
//             // by other chips. For this test, we are creating new fixed columns.
//             let fixed_y_q_1 = meta.fixed_column();
//             let fixed_y_q_2 = meta.fixed_column();

//             // Fixed columns for the Sinsemilla generator lookup table
//             let lookup = (
//                 meta.lookup_table_column(),
//                 meta.lookup_table_column(),
//                 meta.lookup_table_column(),
//             );

//             let range_check = LookupRangeCheckConfig::configure(meta, advices[9], lookup.0);

//             let sinsemilla_config_1 = SinsemillaChip::configure(
//                 meta,
//                 advices[5..].try_into().unwrap(),
//                 advices[7],
//                 fixed_y_q_1,
//                 lookup,
//                 range_check,
//             );
//             let config1 = MerkleChip::configure(meta, sinsemilla_config_1);

//             let sinsemilla_config_2 = SinsemillaChip::configure(
//                 meta,
//                 advices[..5].try_into().unwrap(),
//                 advices[2],
//                 fixed_y_q_2,
//                 lookup,
//                 range_check,
//             );
//             let config2 = MerkleChip::configure(meta, sinsemilla_config_2);

//             (config1, config2)
//         }

//         fn synthesize(
//             &self,
//             config: Self::Config,
//             mut layouter: impl Layouter<pallas::Base>,
//         ) -> Result<(), Error> {
//             // Load generator table (shared across both configs)
//             SinsemillaChip::<TestHashDomain, TestCommitDomain, TestFixedBases>::load(
//                 config.0.sinsemilla_config.clone(),
//                 &mut layouter,
//             )?;

//             // Construct Merkle chips which will be placed side-by-side in the circuit.
//             let chip_1 = MerkleChip::construct(config.0.clone());
//             let chip_2 = MerkleChip::construct(config.1.clone());

//             let leaf = chip_1.load_private(
//                 layouter.namespace(|| ""),
//                 config.0.cond_swap_config.a(),
//                 self.leaf,
//             )?;

//             let path = MerklePath {
//                 chips: [chip_1, chip_2],
//                 domain: TestHashDomain,
//                 leaf_pos: self.leaf_pos,
//                 path: self.merkle_path,
//             };

//             let computed_final_root =
//                 path.calculate_root(layouter.namespace(|| "calculate root"), leaf)?;

//             self.leaf
//                 .zip(self.leaf_pos)
//                 .zip(self.merkle_path)
//                 .zip(computed_final_root.value())
//                 .assert_if_known(|(((leaf, leaf_pos), merkle_path), computed_final_root)| {
//                     // The expected final root
//                     let final_root =
//                         merkle_path
//                             .iter()
//                             .enumerate()
//                             .fold(*leaf, |node, (l, sibling)| {
//                                 let l = l as u8;
//                                 let (left, right) = if leaf_pos & (1 << l) == 0 {
//                                     (&node, sibling)
//                                 } else {
//                                     (sibling, &node)
//                                 };

//                                 use crate::sinsemilla::primitives as sinsemilla;
//                                 let merkle_crh =
//                                     sinsemilla::HashDomain::from_Q(TestHashDomain.Q().into());

//                                 merkle_crh
//                                     .hash(
//                                         iter::empty()
//                                             .chain(i2lebsp::<10>(l as u64).iter().copied())
//                                             .chain(
//                                                 left.to_le_bits()
//                                                     .iter()
//                                                     .by_vals()
//                                                     .take(pallas::Base::NUM_BITS as usize),
//                                             )
//                                             .chain(
//                                                 right
//                                                     .to_le_bits()
//                                                     .iter()
//                                                     .by_vals()
//                                                     .take(pallas::Base::NUM_BITS as usize),
//                                             ),
//                                     )
//                                     .unwrap_or(pallas::Base::zero())
//                             });

//                     // Check the computed final root against the expected final root.
//                     computed_final_root == &&final_root
//                 });

//             Ok(())
//         }
//     }

//     #[test]
//     fn merkle_chip() {
//         let mut rng = OsRng;

//         // Choose a random leaf and position
//         let leaf = pallas::Base::random(rng);
//         let pos = rng.next_u32();

//         // Choose a path of random inner nodes
//         let path: Vec<_> = (0..(MERKLE_DEPTH))
//             .map(|_| pallas::Base::random(rng))
//             .collect();

//         println!("leaf: {:?}\n", leaf);

//         println!("leaf pos: {:?}\n", pos);

//         println!("path: {:?}\n", path);

//         // The root is provided as a public input in the Orchard circuit.

//         let circuit = MyCircuit {
//             leaf: Value::known(leaf),
//             leaf_pos: Value::known(pos),
//             merkle_path: Value::known(path.try_into().unwrap()),
//         };

//         let prover = MockProver::run(11, &circuit, vec![]).unwrap();
//         assert_eq!(prover.verify(), Ok(()))
//     }

//     #[cfg(feature = "test-dev-graph")]
//     #[test]
//     fn print_merkle_chip() {
//         use plotters::prelude::*;

//         let root = BitMapBackend::new("merkle-path-layout.png", (1024, 7680)).into_drawing_area();
//         root.fill(&WHITE).unwrap();
//         let root = root.titled("MerkleCRH Path", ("sans-serif", 60)).unwrap();

//         let circuit = MyCircuit::default();
//         halo2_proofs::dev::CircuitLayout::default()
//             .show_labels(false)
//             .render(11, &circuit, &root)
//             .unwrap();
//     }
// }
