use super::AssignedPoint;
use super::BaseFieldEccChip;
use crate::halo2;
use crate::integer::IntegerInstructions;
use halo2::arithmetic::CurveAffine;
use halo2::circuit::Region;
use halo2::plonk::Error;

impl<C: CurveAffine> BaseFieldEccChip<C> {
    pub(crate) fn _add_incomplete_unsafe(
        &self,
        region: &mut Region<'_, C::Scalar>,
        a: &AssignedPoint<C::Scalar>,
        b: &AssignedPoint<C::Scalar>,
        offset: &mut usize,
    ) -> Result<AssignedPoint<C::Scalar>, Error> {
        let ch = self.integer_chip();

        // lambda = b_y - a_y / b_x - a_x
        let numerator = &ch.sub(region, &b.y, &a.y, offset)?;
        let denominator = &ch.sub(region, &b.x, &a.x, offset)?;
        let lambda = &ch.div_incomplete(region, numerator, denominator, offset)?;

        // c_x =  lambda * lambda - a_x - b_x
        let lambda_square = &ch.square(region, lambda, offset)?;
        let x = &ch.sub_sub(region, lambda_square, &a.x, &b.x, offset)?;

        // c_y = lambda * (a_x - c_x) - a_y
        let t = &ch.sub(region, &a.x, x, offset)?;
        let t = &ch.mul(region, t, lambda, offset)?;
        let y = ch.sub(region, t, &a.y, offset)?;

        let p_0 = AssignedPoint::new(x.clone(), y);

        Ok(p_0)
    }

    pub(crate) fn _double_incomplete(
        &self,
        region: &mut Region<'_, C::Scalar>,
        point: &AssignedPoint<C::Scalar>,
        offset: &mut usize,
    ) -> Result<AssignedPoint<C::Scalar>, Error> {
        let integer_chip = self.integer_chip();

        // lambda = (3 * a_x^2) / 2 * a_y
        let x_0_square = &integer_chip.square(region, &point.x, offset)?;
        let numerator = &integer_chip.mul3(region, x_0_square, offset)?;
        let denominator = &integer_chip.mul2(region, &point.y, offset)?;
        let lambda = &integer_chip.div_incomplete(region, numerator, denominator, offset)?;

        // c_x = lambda * lambda - 2 * a_x
        let lambda_square = &integer_chip.square(region, lambda, offset)?;
        let x = &integer_chip.sub_sub(region, lambda_square, &point.x, &point.x, offset)?;

        // c_y = lambda * (a_x - c_x) - a_y
        let t = &integer_chip.sub(region, &point.x, x, offset)?;
        let t = &integer_chip.mul(region, lambda, t, offset)?;
        let y = integer_chip.sub(region, t, &point.y, offset)?;

        Ok(AssignedPoint::new(x.clone(), y))
    }

    pub(crate) fn _ladder_incomplete(
        &self,
        region: &mut Region<'_, C::Scalar>,
        to_double: &AssignedPoint<C::Scalar>,
        to_add: &AssignedPoint<C::Scalar>,
        offset: &mut usize,
    ) -> Result<AssignedPoint<C::Scalar>, Error> {
        let ch = self.integer_chip();

        // (P + Q) + P
        // P is to_double (x_1, y_1)
        // Q is to_add (x_2, y_2)

        // lambda_0 = (y_2 - y_1) / (x_2 - x_1)
        let numerator = &ch.sub(region, &to_add.y, &to_double.y, offset)?;
        let denominator = &ch.sub(region, &to_add.x, &to_double.x, offset)?;
        let lambda_0 = &ch.div_incomplete(region, numerator, denominator, offset)?;

        // x_3 = lambda_0 * lambda_0 - x_1 - x_2
        let lambda_0_square = &ch.square(region, lambda_0, offset)?;
        let x_3 = &ch.sub_sub(region, lambda_0_square, &to_add.x, &to_double.x, offset)?;

        // lambda_1 = lambda_0 + 2 * y_1 / (x_3 - x_1)
        let numerator = &ch.mul2(region, &to_double.y, offset)?;
        let denominator = &ch.sub(region, x_3, &to_double.x, offset)?;
        let lambda_1 = &ch.div_incomplete(region, numerator, denominator, offset)?;
        let lambda_1 = &ch.add(region, lambda_0, lambda_1, offset)?;

        // x_4 = lambda_1 * lambda_1 - x_1 - x_3
        let lambda_1_square = &ch.square(region, lambda_1, offset)?;
        let x_4 = &ch.sub_sub(region, lambda_1_square, x_3, &to_double.x, offset)?;

        // y_4 = lambda_1 * (x_4 - x_1) - y_1
        let t = &ch.sub(region, x_4, &to_double.x, offset)?;
        let t = &ch.mul(region, t, lambda_1, offset)?;
        let y_4 = ch.sub(region, t, &to_double.y, offset)?;

        let p_0 = AssignedPoint::new(x_4.clone(), y_4);

        Ok(p_0)
    }
}