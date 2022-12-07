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
    use integer::IntegerInstructions;
    use maingate::mock_prover_verify;
    use maingate::{MainGate, MainGateConfig, RangeChip, RangeConfig, RangeInstructions};
    use rand_core::OsRng;
    use std::marker::PhantomData;

    const BIT_LEN_LIMB: usize = 68;
    const NUMBER_OF_LIMBS: usize = 4;

    #[derive(Clone, Debug)]
    struct TestCircuitEcdsaVerifyConfig {
        main_gate_config: MainGateConfig,
        range_config: RangeConfig,
        pk_column: Column<Advice>,
        // instance: Column<Instance>,
    }

    impl TestCircuitEcdsaVerifyConfig {
        pub fn new<C: CurveAffine, N: FieldExt>(meta: &mut ConstraintSystem<N>) -> Self {
            let (rns_base, rns_scalar) =
                GeneralEccChip::<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::rns();
            let main_gate_config = MainGate::<N>::configure(meta);
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

            // let instance = meta.instance_column();

            TestCircuitEcdsaVerifyConfig {
                main_gate_config,
                range_config,
                pk_column,
                // instance,
            }
        }

        pub fn ecc_chip_config(&self) -> EccConfig {
            EccConfig::new(self.range_config.clone(), self.main_gate_config.clone())
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
                    // let pk = self.public_key.map(|pk| {
                    //     let p = pk.coordinates().unwrap().x().clone();
                    //     // // let input = Fq::from_bytes(&p.to_bytes()).unwrap();
                    //     self.public_key
                    // });
                    //
                    //

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

            // println!("instance: {:?}\n", config.instance);

            // let a = pk1.point.x().native().cell();

            config.config_range(&mut layouter)?;

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

            let circuit = TestCircuitEcdsaVerify::<Secp256k1Affine, Fq> {
                public_key: Value::known(pk),
                signature: Value::known((r, s)),
                msg_hash: Value::known(msg_hash),
                aux_generator,
                window_size: 2,
                ..Default::default()
            };

            let input = pk.coordinates().unwrap().x().clone();
            let input = Fq::from_bytes(&input.to_bytes()).unwrap();

            let instance = vec![vec![input]];

            println!("pk: {:?}, msg_hash: {:?}\n", pk, msg_hash);
            println!("r: {:?}, s: {:?}\n", r, s);
            println!("input: {:?}\n", input);

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
