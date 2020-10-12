//! Field arithmetic modulo p = 2^256 - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1

use core::cmp::{Eq, PartialEq};

use elliptic_curve::subtle::{ConstantTimeEq, CtOption};

#[cfg(test)]
use num_bigint::{BigUint, ToBigUint};

#[cfg(feature = "u64_backend")]
pub use crate::arithmetic::backend::u64::field::FieldElement5x52;

#[cfg(feature = "u32_backend")]
pub use crate::arithmetic::backend::u32::field::FieldElement10x26;

/// The `FieldElement` type is an alias for 64-bit arithmetic that leverages
/// "lazy arithmetic" with five u64 ints to hold 52 bits each.
///
/// A `FieldElement` represents an element of the field
/// 2^256 - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1
#[cfg(feature = "u64_backend")]
pub type FieldElement = FieldElement5x52;

/// The `FieldElement` type is an alias for 32-bit arithmetic that leverages
/// "lazy arithmetic" with 10 u32 ints to hold 26 bits each.
///
/// A `FieldElement` represents an element of the field
/// 2^256 - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1
#[cfg(feature = "u32_backend")]
pub type FieldElement = FieldElement10x26;

impl Eq for FieldElement {}

impl PartialEq for FieldElement {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(&other).into()
    }
}

impl FieldElement {
    /// Returns 2*self
    /// Doubles the magnitude.
    pub fn double(&self) -> Self {
        self + self
    }

    /// Returns self * self
    /// Brings the magnitude to 1 (but doesn't normalize the result).
    /// The magnitude should be <= 8.
    pub fn square(&self) -> Self {
        self * self
    }

    /// Raises the scalar to the power `2^k`
    fn pow2k(&self, k: usize) -> Self {
        let mut x = *self;
        for _j in 0..k {
            x = x.square();
        }
        x
    }

    /// Returns the multiplicative inverse of self, if self is non-zero.
    /// The result has magnitude 1, but is not normalized.
    pub fn invert(&self) -> CtOption<Self> {
        // The binary representation of (p - 2) has 5 blocks of 1s, with lengths in
        // { 1, 2, 22, 223 }. Use an addition chain to calculate 2^n - 1 for each block:
        // [1], [2], 3, 6, 9, 11, [22], 44, 88, 176, 220, [223]

        let x2 = &self.pow2k(1) * self;
        let x3 = &x2.pow2k(1) * self;
        let x6 = &x3.pow2k(3) * &x3;
        let x9 = &x6.pow2k(3) * &x3;
        let x11 = &x9.pow2k(2) * &x2;
        let x22 = &x11.pow2k(11) * &x11;
        let x44 = &x22.pow2k(22) * &x22;
        let x88 = &x44.pow2k(44) * &x44;
        let x176 = &x88.pow2k(88) * &x88;
        let x220 = &x176.pow2k(44) * &x44;
        let x223 = &x220.pow2k(3) * &x3;

        // The final result is then assembled using a sliding window over the blocks.
        let res = &(&(&(&x223.pow2k(23) * &x22).pow2k(5) * self).pow2k(3) * &x2).pow2k(2) * self;
        //.pow2k(23)
        //.mul(&x22)
        //.pow2k(5)
        //.mul(self)
        //.pow2k(3)
        //.mul(&x2)
        //.pow2k(2)
        //.mul(self);

        CtOption::new(res, !self.normalizes_to_zero())
    }

    /// Returns the square root of self mod p, or `None` if no square root exists.
    /// The result has magnitude 1, but is not normalized.
    pub fn sqrt(&self) -> CtOption<Self> {
        /*
        Given that p is congruent to 3 mod 4, we can compute the square root of
        a mod p as the (p+1)/4'th power of a.

        As (p+1)/4 is an even number, it will have the same result for a and for
        (-a). Only one of these two numbers actually has a square root however,
        so we test at the end by squaring and comparing to the input.
        Also because (p+1)/4 is an even number, the computed square root is
        itself always a square (a ** ((p+1)/4) is the square of a ** ((p+1)/8)).
        */

        // The binary representation of (p + 1)/4 has 3 blocks of 1s, with lengths in
        // { 2, 22, 223 }. Use an addition chain to calculate 2^n - 1 for each block:
        // 1, [2], 3, 6, 9, 11, [22], 44, 88, 176, 220, [223]

        let x2 = &self.pow2k(1) * self;
        let x3 = &x2.pow2k(1) * self;
        let x6 = &x3.pow2k(3) * &x3;
        let x9 = &x6.pow2k(3) * &x3;
        let x11 = &x9.pow2k(2) * &x2;
        let x22 = &x11.pow2k(11) * &x11;
        let x44 = &x22.pow2k(22) * &x22;
        let x88 = &x44.pow2k(44) * &x44;
        let x176 = &x88.pow2k(88) * &x88;
        let x220 = &x176.pow2k(44) * &x44;
        let x223 = &x220.pow2k(3) * &x3;

        // The final result is then assembled using a sliding window over the blocks.
        let res = (&(&x223.pow2k(23) * &x22).pow2k(6) * &x2).pow2k(2);
        let is_root = (&res.square().negate(1) + &self).normalizes_to_zero();

        // Only return Some if it's the square root.
        CtOption::new(res, is_root)
    }

    #[cfg(test)]
    pub fn modulus_as_biguint() -> BigUint {
        Self::one().negate(1).to_biguint().unwrap() + 1.to_biguint().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use num_bigint::{BigUint, ToBigUint};
    use proptest::prelude::*;

    use super::FieldElement;
    use super::FieldElement5x52;
    use crate::arithmetic::util::{biguint_to_bytes, bytes_to_biguint};
    use crate::test_vectors::field::DBL_TEST_VECTORS;

    impl From<&BigUint> for FieldElement {
        fn from(x: &BigUint) -> Self {
            let bytes = biguint_to_bytes(x);
            Self::from_bytes(&bytes).unwrap()
        }
    }

    impl ToBigUint for FieldElement {
        fn to_biguint(&self) -> Option<BigUint> {
            Some(bytes_to_biguint(&(self.to_bytes())))
        }
    }

    #[test]
    fn zero_is_additive_identity() {
        let zero = FieldElement::zero();
        let one = FieldElement::one();
        assert_eq!((&zero + &zero).normalize(), zero);
        assert_eq!((&one + &zero).normalize(), one);
    }

    #[test]
    fn one_is_multiplicative_identity() {
        let one = FieldElement::one();
        assert_eq!((&one * &one).normalize(), one);
    }

    #[test]
    fn from_bytes() {
        assert_eq!(
            FieldElement::from_bytes(&[0; 32]).unwrap(),
            FieldElement::zero()
        );
        assert_eq!(
            FieldElement::from_bytes(&[
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 1
            ])
            .unwrap(),
            FieldElement::one()
        );
        assert!(bool::from(FieldElement::from_bytes(&[0xff; 32]).is_none()));
    }

    #[test]
    fn to_bytes() {
        assert_eq!(FieldElement::zero().to_bytes(), [0; 32]);
        assert_eq!(
            FieldElement::one().to_bytes(),
            [
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 1
            ]
        );
    }

    #[test]
    fn repeated_add() {
        let mut r = FieldElement::one();
        for i in 0..DBL_TEST_VECTORS.len() {
            assert_eq!(hex::encode(r.to_bytes()), DBL_TEST_VECTORS[i]);
            r = (&r + &r).normalize();
        }
    }

    #[test]
    fn repeated_double() {
        let mut r = FieldElement::one();
        for i in 0..DBL_TEST_VECTORS.len() {
            assert_eq!(hex::encode(r.to_bytes()), DBL_TEST_VECTORS[i]);
            r = r.double().normalize();
        }
    }

    #[test]
    fn repeated_mul() {
        let mut r = FieldElement::one();
        let two = &r + &r;
        for i in 0..DBL_TEST_VECTORS.len() {
            assert_eq!(hex::encode(r.normalize().to_bytes()), DBL_TEST_VECTORS[i]);
            r = &r * &two;
        }
    }

    #[test]
    fn negation() {
        let two = FieldElement::one().double();
        let neg_two = two.negate(2);
        assert_eq!((&two + &neg_two).normalize(), FieldElement::zero());
        assert_eq!(neg_two.negate(3).normalize(), two.normalize());
    }

    #[test]
    fn invert() {
        assert!(bool::from(FieldElement::zero().invert().is_none()));

        let one = FieldElement::one();
        assert_eq!(one.invert().unwrap().normalize(), one);

        let two = &one + &one;
        let inv_two = two.invert().unwrap();
        assert_eq!((&two * &inv_two).normalize(), one);
    }

    #[test]
    fn sqrt() {
        let one = FieldElement::one();
        let two = &one + &one;
        let four = &two.square();
        assert_eq!(four.sqrt().unwrap().normalize(), two.normalize());
    }

    prop_compose! {
        fn field_element()(bytes in any::<[u8; 32]>()) -> FieldElement {
            let mut res = bytes_to_biguint(&bytes);
            let m = FieldElement::modulus_as_biguint();
            // Modulus is 256 bit long, same as the maximum `res`,
            // so this is guaranteed to land us in the correct range.
            if res >= m {
                res -= m;
            }
            FieldElement::from(&res)
        }
    }

    proptest! {

        #[test]
        fn fuzzy_add(
            a in field_element(),
            b in field_element()
        ) {
            let a_bi = a.to_biguint().unwrap();
            let b_bi = b.to_biguint().unwrap();
            let res_bi = (&a_bi + &b_bi) % FieldElement::modulus_as_biguint();
            let res_ref = FieldElement::from(&res_bi);
            let res_test = (&a + &b).normalize();
            assert_eq!(res_test, res_ref);
        }

        #[test]
        fn fuzzy_mul(
            a in field_element(),
            b in field_element()
        ) {
            let a_bi = a.to_biguint().unwrap();
            let b_bi = b.to_biguint().unwrap();
            let res_bi = (&a_bi * &b_bi) % FieldElement::modulus_as_biguint();
            let res_ref = FieldElement::from(&res_bi);
            let res_test = (&a * &b).normalize();
            assert_eq!(res_test, res_ref);
        }

        #[test]
        fn fuzzy_square(
            a in field_element()
        ) {
            let a_bi = a.to_biguint().unwrap();
            let res_bi = (&a_bi * &a_bi) % FieldElement::modulus_as_biguint();
            let res_ref = FieldElement::from(&res_bi);
            let res_test = a.square().normalize();
            assert_eq!(res_test, res_ref);
        }

        #[test]
        fn fuzzy_negate(
            a in field_element()
        ) {
            let m = FieldElement::modulus_as_biguint();
            let a_bi = a.to_biguint().unwrap();
            let res_bi = (&m - &a_bi) % &m;
            let res_ref = FieldElement::from(&res_bi);
            let res_test = a.negate(1).normalize();
            assert_eq!(res_test, res_ref);
        }

        #[test]
        fn fuzzy_sqrt(
            a in field_element()
        ) {
            let m = FieldElement::modulus_as_biguint();
            let a_bi = a.to_biguint().unwrap();
            let sqr_bi = (&a_bi * &a_bi) % &m;
            let sqr = FieldElement::from(&sqr_bi);

            let res_ref1 = a;
            let possible_sqrt = (&m - &a_bi) % &m;
            let res_ref2 = FieldElement::from(&possible_sqrt);
            let res_test = sqr.sqrt().unwrap().normalize();
            // FIXME: is there a rule which square root is returned?
            assert!(res_test == res_ref1 || res_test == res_ref2);
        }

        #[test]
        fn fuzzy_invert(
            a in field_element()
        ) {
            let a = if bool::from(a.is_zero()) { FieldElement::one() } else { a };
            let a_bi = a.to_biguint().unwrap();
            let inv = a.invert().unwrap().normalize();
            let inv_bi = inv.to_biguint().unwrap();
            let m = FieldElement::modulus_as_biguint();
            assert_eq!((&inv_bi * &a_bi) % &m, 1.to_biguint().unwrap());
        }
    }

    #[test]
    fn test_blah() {
        let a = FieldElement5x52([0xFFFFFFFFu64, 1, 0, 0, 0]);
        let b = FieldElement5x52([1u64, 0, 0, 0, 0]);

        println!("{:?}", (&a * &b).0);
    }
}
