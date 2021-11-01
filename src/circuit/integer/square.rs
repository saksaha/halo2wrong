use super::{IntegerChip, IntegerInstructions};
use crate::circuit::main_gate::{CombinationOption, MainGateInstructions, Term};
use crate::circuit::range::RangeInstructions;
use crate::circuit::{AssignedInteger, AssignedValue};
use crate::rns::Quotient;
use crate::NUMBER_OF_LIMBS;

use halo2::arithmetic::FieldExt;
use halo2::circuit::Region;
use halo2::plonk::Error;

impl<W: FieldExt, N: FieldExt> IntegerChip<W, N> {
    pub(crate) fn _square(&self, region: &mut Region<'_, N>, a: &mut AssignedInteger<N>, offset: &mut usize) -> Result<AssignedInteger<N>, Error> {
        let main_gate = self.main_gate();
        let (zero, one) = (N::zero(), N::one());

        let negative_wrong_modulus = self.rns.negative_wrong_modulus.clone();

        let reduction_result = a.integer().map(|integer_a| self.rns.mul(&integer_a, &integer_a));

        let quotient = reduction_result.as_ref().map(|reduction_result| {
            let quotient = match reduction_result.quotient.clone() {
                Quotient::Long(quotient) => quotient,
                _ => panic!("long quotient expected"),
            };
            quotient
        });

        let result = reduction_result.as_ref().map(|u| u.result.clone());
        let intermediate_values: Option<Vec<N>> = reduction_result.as_ref().map(|u| u.t.clone());
        let u_0 = reduction_result.as_ref().map(|u| u.u_0);
        let v_0 = reduction_result.as_ref().map(|u| u.v_0);
        let u_1 = reduction_result.as_ref().map(|u| u.u_1);
        let v_1 = reduction_result.as_ref().map(|u| u.v_1);

        // Apply ranges

        let range_chip = self.range_chip();
        let quotient = &mut self.range_assign_integer(region, quotient.into(), self.mul_quotient_range_tune(), offset)?;
        let result = &mut self.range_assign_integer(region, result.into(), self.mul_result_range_tune(), offset)?;
        let v_0 = &mut range_chip.range_value(region, &v_0.into(), self.mul_v0_range_tune(), offset)?;
        let v_1 = &mut range_chip.range_value(region, &v_1.into(), self.mul_v1_range_tune(), offset)?;

        // Constaints:
        // t_0 =  a_0 * b_0
        //     +  q_0 * p_0
        // t_1 =  2 * a_0 * a_1
        //     +  q_0 * p_1 + q_1 * p_0
        // t_2 =  2 * a_0 * a_2 + a_1 * a_1
        //     +  q_0 * p_2 + q_1 * p_1 + q_2 * p_0
        // t_3 =  2 * a_0 * a_3 + 2 * a_1 * a_2
        //        + q_0 * p_3 + q_1 * p_2 + q_2 * p_1 + q_3 * p_0

        // Follow same witness layout with mul:
        // | A   | B   | C   | D     |
        // | --- | --- | --- | ----- |
        // | a_0 | a_0 | q_0 | t_0   |

        // | a_0 | a_1 | q_1 | t_1   |
        // | a_1 | a_0 | q_0 | tmp   |

        // | a_0 | a_2 | q_2 | t_2   |
        // | a_1 | a_1 | q_1 | tmp_a |
        // | a_2 | a_0 | q_0 | tmp_b |

        // | a_0 | a_3 | q_3 | t_3   |
        // | a_1 | a_2 | q_2 | tmp_b |
        // | a_2 | a_1 | q_1 | tmp_a |
        // | a_3 | a_0 | q_0 | tmp_c |

        // A bit more optimized witness layout that we didn't apply yet is below:

        // | A   | B   | C   | D     |
        // | --- | --- | --- | ----- |
        // | a_0 | a_0 | q_0 | t_0   | t_0 = a_0 * a_0 + q_0 * p_0
        // | a_0 | a_1 | q_0 | q_1   | t_1 = 2 * a_0 * a_1 + q_0 * p_1 + q_1 * p_0
        // | a_0 | a_2 | q_0 | t_1   | tmp_a = 2 * a_0 * a_2 + q_0 * p_2
        // | a_1 | a_1 | q_0 | tmp_a | tmp_b = a_1 * a_1 + q_1 * p_1 + tmp_a
        // | t_2 | -   | q_2 | tmp_b | t_2 = tmp_b + q_2 * p_0
        // | a_0 | a_3 | q_0 | q_1   | tmp_a = 2 * a_0 * a_3 + q_0 * p_3 + q_1 * p_2
        // | a_1 | a_2 | q_2 | tmp_a | tmp_b = 2 * a_0 * a_2 + q_2 * p_1 + q_3 * p_0
        // | t_3 | -   | q_3 | tmp_b | t_3 = tmp_b + q_3 * p_0

        let mut intermediate_values_cycling: Vec<AssignedValue<N>> = vec![];

        for i in 0..NUMBER_OF_LIMBS {
            let mut t = intermediate_values.as_ref().map(|intermediate_values| intermediate_values[i]);

            for j in 0..=i {
                let k = i - j;

                let combination_option = if k == 0 {
                    CombinationOption::SingleLinerMul
                } else {
                    CombinationOption::CombineToNextMul(one)
                };

                let mut a_j = a.limb(j);
                let mut a_k = a.limb(k);

                let (_, _, _, t_i_cell) = main_gate.combine(
                    region,
                    Term::Assigned(&mut a_j, zero),
                    Term::Assigned(&mut a_k, zero),
                    Term::Assigned(quotient.limb_mut(k), negative_wrong_modulus[j]),
                    Term::Unassigned(t, -one),
                    zero,
                    offset,
                    combination_option,
                )?;

                if j == 0 {
                    // first time we see t_j assignment
                    intermediate_values_cycling.push(AssignedValue::<N>::new(t_i_cell, t));
                }

                // update running temp value
                t = t.map(|t| {
                    let a_j = a.limb_value(j).unwrap();
                    let a_k = a.limb_value(k).unwrap();
                    let q = quotient.limb_value(k).unwrap();
                    let p = negative_wrong_modulus[j];
                    t - (a_j * a_k + q * p)
                });
            }
        }

        // u_0 = t_0 + (t_1 * R) - r_0 - (r_1 * R)
        // u_0 = v_0 * R^2

        // | A   | B   | C   | D     |
        // | --- | --- | --- | ----- |
        // | t_0 | t_1 | r_0 | r_1   |
        // | -   | -   | v_0 | u_0   |

        let left_shifter_r = self.rns.left_shifter_r;
        let left_shifter_2r = self.rns.left_shifter_2r;

        let (_, _, _, _) = main_gate.combine(
            region,
            Term::Assigned(&mut intermediate_values_cycling[0].clone(), one),
            Term::Assigned(&mut intermediate_values_cycling[1].clone(), left_shifter_r),
            Term::Assigned(&mut result.limbs[0].clone(), -one),
            Term::Assigned(&mut result.limbs[1].clone(), -left_shifter_r),
            zero,
            offset,
            CombinationOption::CombineToNextAdd(-one),
        )?;

        main_gate.combine(
            region,
            Term::Zero,
            Term::Zero,
            Term::Assigned(v_0, left_shifter_2r),
            Term::Unassigned(u_0, -one),
            zero,
            offset,
            CombinationOption::SingleLinerAdd,
        )?;

        // u_1 = t_2 + (t_3 * R) - r_2 - (r_3 * R)
        // v_1 * 2R = u_1 + v_0

        // | A   | B   | C   | D     |
        // | --- | --- | --- | ----- |
        // | t_2 | t_3 | r_2 | r_3   |
        // | -   | v_1 | v_0 | u_1   |

        main_gate.combine(
            region,
            Term::Assigned(&mut intermediate_values_cycling[2].clone(), one),
            Term::Assigned(&mut intermediate_values_cycling[3].clone(), left_shifter_r),
            Term::Assigned(&mut result.limbs[2].clone(), -one),
            Term::Assigned(&mut result.limbs[3].clone(), -left_shifter_r),
            zero,
            offset,
            CombinationOption::CombineToNextAdd(-one),
        )?;

        main_gate.combine(
            region,
            Term::Zero,
            Term::Assigned(v_1, left_shifter_2r),
            Term::Assigned(v_0, -one),
            Term::Unassigned(u_1, -one),
            zero,
            offset,
            CombinationOption::SingleLinerAdd,
        )?;

        // update native value
        let a_native = a.native();
        main_gate.combine(
            region,
            Term::Assigned(&mut a_native.clone(), zero),
            Term::Assigned(&mut a_native.clone(), zero),
            Term::Assigned(quotient.native_mut(), -self.rns.wrong_modulus_in_native_modulus),
            Term::Assigned(result.native_mut(), -one),
            zero,
            offset,
            CombinationOption::SingleLinerMul,
        )?;

        Ok(result.clone())
    }
}