//! Field element modulo the curve internal modulus using 64-bit limbs.
//! Ported from https://github.com/bitcoin-core/secp256k1

use core::ops::{Add, AddAssign};
use core::ops::{Mul, MulAssign};

use elliptic_curve::subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

/// Scalars modulo SECP256k1 modulus (2^256 - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1).
/// Uses 5 64-bit limbs (little-endian), where in the normalized form
/// first 4 contain 52 bits of the value each, and the last one contains 48 bits.
/// Arithmetic operations can be done without modulo reduction for some time,
/// using the remaining overflow bits.
#[derive(Clone, Copy, Debug)]
pub struct FieldElement5x52(pub(crate) [u64; 5]);

impl<'b> AddAssign<&'b FieldElement5x52> for FieldElement5x52 {
    fn add_assign(&mut self, rhs: &'b FieldElement5x52) {
        let result = (self as &FieldElement5x52) + rhs;
        self.0 = result.0
    }
}

impl<'a, 'b> Add<&'b FieldElement5x52> for &'a FieldElement5x52 {
    type Output = FieldElement5x52;
    fn add(self, rhs: &'b FieldElement5x52) -> FieldElement5x52 {
        FieldElement5x52([
            self.0[0] + rhs.0[0],
            self.0[1] + rhs.0[1],
            self.0[2] + rhs.0[2],
            self.0[3] + rhs.0[3],
            self.0[4] + rhs.0[4],
        ])
    }
}

/// Returns self *= rhs mod p
/// Brings the magnitude to 1 (but doesn't normalize the result).
/// The magnitudes of arguments should be <= 8.
impl<'b> MulAssign<&'b FieldElement5x52> for FieldElement5x52 {
    fn mul_assign(&mut self, rhs: &'b FieldElement5x52) {
        let result = (self as &FieldElement5x52) * rhs;
        self.0 = result.0
    }
}

/// Returns self * rhs mod p
/// Brings the magnitude to 1 (but doesn't normalize the result).
/// The magnitudes of arguments should be <= 8.
impl<'a, 'b> Mul<&'b FieldElement5x52> for &'a FieldElement5x52 {
    type Output = FieldElement5x52;
    fn mul(self, rhs: &'b FieldElement5x52) -> FieldElement5x52 {
        const LOW_52_BIT_MASK: u128 = (1 << 52) - 1;
        const LOW_48_BIT_MASK: u128  = (1 << 48) - 1;
        const R: u128 = 0x1000003D10; // R = 2^256 mod p

        #[inline(always)]
        fn m(x: u64, y: u64) -> u128 { (x as u128) * (y as u128) }

        let a: &[u64; 5] = &self.0;
        let b: &[u64; 5] = &rhs.0;

        // Schoolbook multiplication
        let mut l0: u128 = m(a[0], b[0]);
        let mut l1: u128 = m(a[0], b[1]) + m(a[1], b[0]);
        let mut l2: u128 = m(a[0], b[2]) + m(a[1], b[1]) + m(a[2], b[0]);
        let mut l3: u128 = m(a[0], b[3]) + m(a[1], b[2]) + m(a[2], b[1]) + m(a[3], b[0]);
        let mut mid: u128 = m(a[0], b[4]) + m(a[1], b[3]) + m(a[2], b[2]) + m(a[3], b[1]) + m(a[4], b[0]);
        let mut h0: u128 = m(a[1], b[4]) + m(a[2], b[3]) + m(a[3], b[2]) + m(a[4], b[1]);
        let mut h1: u128 = m(a[2], b[4]) + m(a[3], b[3]) + m(a[4], b[2]);
        let mut h2: u128 = m(a[3], b[4]) + m(a[4], b[3]);
        let mut h3: u128 = m(a[4], b[4]);

        let test: u128 = l3 + ((h3 & LOW_52_BIT_MASK) * R);
        // Begin the reduction
        //
        // The idea is we multiply the high bits with R and add it to the low bits.
        // Then we set the carries for each to use in the preceeding calculation.

        let mut out = [0u64; 5];

        // c*2^156
        l3 += (h3 & LOW_52_BIT_MASK) * R;
        out[3] = (l3 & LOW_52_BIT_MASK) as u64;
        h3 >>= 52;
        l3 >>= 52;

        println!("t, l, h, R = {},{},{},{}", test, l3, h3, R); 

        // c*2^208
        mid += ((l3 as u64) as u128) + (((h3 as u64) as u128) * R);
        out[4] = ((mid & LOW_52_BIT_MASK) & LOW_48_BIT_MASK) as u64;
        let carry: u128 = (mid & LOW_52_BIT_MASK) >> 48;
        mid >>= 52;

        // c*2^0
        h0 += ((mid as u64) as u128);
        l0 += (((((h0 & LOW_52_BIT_MASK) << 4) | carry) as u64) as u128) * (((R as u64) >> 4) as u128);
        out[0] = (l0 & LOW_52_BIT_MASK) as u64;
        h0 >>= 52;
        l0 >>= 52;

        // c*2^52
        h1 += ((h0 as u64) as u128);
        l1 += (((l0 as u64) as u128)) + ((h1 & LOW_52_BIT_MASK) * R);
        out[1] = (l1 & LOW_52_BIT_MASK) as u64;
        h1 >>= 52;
        l1 >>= 52;

        // c*2^104
        h2 += ((h1 as u64) as u128);
        l2 += ((l1 as u64) as u128) + ((h2 & LOW_52_BIT_MASK) * R);
        out[2] = (l2 & LOW_52_BIT_MASK) as u64;
        h2 >>= 52;
        l2 >>= 52;

        // c*2^156
        l3 = ((l2 as u64) as u128) + (((h2 as u64) as u128) * R) + out[3] as u128;
        out[3] = (l3 & LOW_52_BIT_MASK) as u64;
        l3 >>= 52;

        // c*2^208
        out[4] = (((l3 as u64) as u128) + out[4] as u128) as u64;

        FieldElement5x52(out)
    }
}

impl FieldElement5x52 {
    /// Returns the zero element.
    pub const fn zero() -> Self {
        Self([0, 0, 0, 0, 0])
    }

    /// Returns the multiplicative identity.
    pub const fn one() -> Self {
        Self([1, 0, 0, 0, 0])
    }

    /// Attempts to parse the given byte array as an SEC-1-encoded field element.
    /// Does not check the result for being in the correct range.
    pub const fn from_bytes_unchecked(bytes: &[u8; 32]) -> Self {
        let w0 = (bytes[31] as u64)
            | ((bytes[30] as u64) << 8)
            | ((bytes[29] as u64) << 16)
            | ((bytes[28] as u64) << 24)
            | ((bytes[27] as u64) << 32)
            | ((bytes[26] as u64) << 40)
            | (((bytes[25] & 0xFu8) as u64) << 48);

        let w1 = ((bytes[25] >> 4) as u64)
            | ((bytes[24] as u64) << 4)
            | ((bytes[23] as u64) << 12)
            | ((bytes[22] as u64) << 20)
            | ((bytes[21] as u64) << 28)
            | ((bytes[20] as u64) << 36)
            | ((bytes[19] as u64) << 44);

        let w2 = (bytes[18] as u64)
            | ((bytes[17] as u64) << 8)
            | ((bytes[16] as u64) << 16)
            | ((bytes[15] as u64) << 24)
            | ((bytes[14] as u64) << 32)
            | ((bytes[13] as u64) << 40)
            | (((bytes[12] & 0xFu8) as u64) << 48);

        let w3 = ((bytes[12] >> 4) as u64)
            | ((bytes[11] as u64) << 4)
            | ((bytes[10] as u64) << 12)
            | ((bytes[9] as u64) << 20)
            | ((bytes[8] as u64) << 28)
            | ((bytes[7] as u64) << 36)
            | ((bytes[6] as u64) << 44);

        let w4 = (bytes[5] as u64)
            | ((bytes[4] as u64) << 8)
            | ((bytes[3] as u64) << 16)
            | ((bytes[2] as u64) << 24)
            | ((bytes[1] as u64) << 32)
            | ((bytes[0] as u64) << 40);

        Self([w0, w1, w2, w3, w4])
    }

    /// Attempts to parse the given byte array as an SEC-1-encoded field element.
    ///
    /// Returns None if the byte array does not contain a big-endian integer in the range
    /// [0, p).
    pub fn from_bytes(bytes: &[u8; 32]) -> CtOption<Self> {
        let res = Self::from_bytes_unchecked(bytes);
        let overflow = res.get_overflow();
        CtOption::new(res, !overflow)
    }

    /// Returns the SEC-1 encoding of this field element.
    pub fn to_bytes(&self) -> [u8; 32] {
        // Normalize before encoding
        let norm_self = self.normalize();

        let mut ret = [0u8; 32];
        ret[0] = (norm_self.0[4] >> 40) as u8;
        ret[1] = (norm_self.0[4] >> 32) as u8;
        ret[2] = (norm_self.0[4] >> 24) as u8;
        ret[3] = (norm_self.0[4] >> 16) as u8;
        ret[4] = (norm_self.0[4] >> 8) as u8;
        ret[5] = norm_self.0[4] as u8;
        ret[6] = (norm_self.0[3] >> 44) as u8;
        ret[7] = (norm_self.0[3] >> 36) as u8;
        ret[8] = (norm_self.0[3] >> 28) as u8;
        ret[9] = (norm_self.0[3] >> 20) as u8;
        ret[10] = (norm_self.0[3] >> 12) as u8;
        ret[11] = (norm_self.0[3] >> 4) as u8;
        ret[12] = ((norm_self.0[2] >> 48) as u8 & 0xFu8) | ((norm_self.0[3] as u8 & 0xFu8) << 4);
        ret[13] = (norm_self.0[2] >> 40) as u8;
        ret[14] = (norm_self.0[2] >> 32) as u8;
        ret[15] = (norm_self.0[2] >> 24) as u8;
        ret[16] = (norm_self.0[2] >> 16) as u8;
        ret[17] = (norm_self.0[2] >> 8) as u8;
        ret[18] = norm_self.0[2] as u8;
        ret[19] = (norm_self.0[1] >> 44) as u8;
        ret[20] = (norm_self.0[1] >> 36) as u8;
        ret[21] = (norm_self.0[1] >> 28) as u8;
        ret[22] = (norm_self.0[1] >> 20) as u8;
        ret[23] = (norm_self.0[1] >> 12) as u8;
        ret[24] = (norm_self.0[1] >> 4) as u8;
        ret[25] = ((norm_self.0[0] >> 48) as u8 & 0xFu8) | ((norm_self.0[1] as u8 & 0xFu8) << 4);
        ret[26] = (norm_self.0[0] >> 40) as u8;
        ret[27] = (norm_self.0[0] >> 32) as u8;
        ret[28] = (norm_self.0[0] >> 24) as u8;
        ret[29] = (norm_self.0[0] >> 16) as u8;
        ret[30] = (norm_self.0[0] >> 8) as u8;
        ret[31] = norm_self.0[0] as u8;
        ret
    }

    /// Adds `x * (2^256 - modulus)`.
    fn add_modulus_correction(&self, x: u64) -> Self {
        // add (2^256 - modulus) * x to the first limb
        let t0 = self.0[0] + x * 0x1000003D1u64;

        // Propagate excess bits up the limbs
        let t1 = self.0[1] + (t0 >> 52);
        let t0 = t0 & 0xFFFFFFFFFFFFFu64;

        let t2 = self.0[2] + (t1 >> 52);
        let t1 = t1 & 0xFFFFFFFFFFFFFu64;

        let t3 = self.0[3] + (t2 >> 52);
        let t2 = t2 & 0xFFFFFFFFFFFFFu64;

        let t4 = self.0[4] + (t3 >> 52);
        let t3 = t3 & 0xFFFFFFFFFFFFFu64;

        Self([t0, t1, t2, t3, t4])
    }

    /// Subtracts the overflow in the last limb and return it with the new field element.
    /// Equivalent to subtracting a multiple of 2^256.
    fn subtract_modulus_approximation(&self) -> (Self, u64) {
        let x = self.0[4] >> 48;
        let t4 = self.0[4] & 0x0FFFFFFFFFFFFu64; // equivalent to self -= 2^256 * x
        (Self([self.0[0], self.0[1], self.0[2], self.0[3], t4]), x)
    }

    /// Checks if the field element is greater or equal to the modulus.
    fn get_overflow(&self) -> Choice {
        let m = self.0[1] & self.0[2] & self.0[3];
        let x = (self.0[4] >> 48 != 0)
            | ((self.0[4] == 0x0FFFFFFFFFFFFu64)
                & (m == 0xFFFFFFFFFFFFFu64)
                & (self.0[0] >= 0xFFFFEFFFFFC2Fu64));
        Choice::from(x as u8)
    }

    /// Brings the field element's magnitude to 1, but does not necessarily normalize it.
    pub fn normalize_weak(&self) -> Self {
        // Reduce t4 at the start so there will be at most a single carry from the first pass
        let (t, x) = self.subtract_modulus_approximation();

        // The first pass ensures the magnitude is 1, ...
        let res = t.add_modulus_correction(x);

        // ... except for a possible carry at bit 48 of t4 (i.e. bit 256 of the field element)
        debug_assert!(res.0[4] >> 49 == 0);

        res
    }

    /// Fully normalizes the field element.
    /// That is, first four limbs are at most 52 bit large, the last limb is at most 48 bit large,
    /// and the value is less than the modulus.
    pub fn normalize(&self) -> Self {
        let res = self.normalize_weak();

        // At most a single final reduction is needed;
        // check if the value is >= the field characteristic
        let overflow = res.get_overflow();

        // Apply the final reduction (for constant-time behaviour, we do it always)
        let res_corrected = res.add_modulus_correction(1u64);
        // Mask off the possible multiple of 2^256 from the final reduction
        let (res_corrected, x) = res_corrected.subtract_modulus_approximation();

        // If the last limb didn't carry to bit 48 already,
        // then it should have after any final reduction
        debug_assert!(x == (overflow.unwrap_u8() as u64));

        Self::conditional_select(&res, &res_corrected, overflow)
    }

    /// Checks if the field element becomes zero if normalized.
    pub fn normalizes_to_zero(&self) -> Choice {
        let res = self.normalize_weak();

        let t0 = res.0[0];
        let t1 = res.0[1];
        let t2 = res.0[2];
        let t3 = res.0[3];
        let t4 = res.0[4];

        // z0 tracks a possible raw value of 0, z1 tracks a possible raw value of the modulus
        let z0 = t0 | t1 | t2 | t3 | t4;
        let z1 = (t0 ^ 0x1000003D0u64) & t1 & t2 & t3 & (t4 ^ 0xF000000000000u64);

        Choice::from(((z0 == 0) | (z1 == 0xFFFFFFFFFFFFFu64)) as u8)
    }

    /// Determine if this `FieldElement5x52` is zero.
    ///
    /// # Returns
    ///
    /// If zero, return `Choice(1)`.  Otherwise, return `Choice(0)`.
    pub fn is_zero(&self) -> Choice {
        Choice::from(((self.0[0] | self.0[1] | self.0[2] | self.0[3] | self.0[4]) == 0) as u8)
    }

    /// Determine if this `FieldElement5x52` is odd in the SEC-1 sense: `self mod 2 == 1`.
    ///
    /// # Returns
    ///
    /// If odd, return `Choice(1)`.  Otherwise, return `Choice(0)`.
    pub fn is_odd(&self) -> Choice {
        (self.0[0] as u8 & 1).into()
    }

    /// The maximum number `m` for which `0xFFFFFFFFFFFFF * 2 * (m + 1) < 2^64`
    #[cfg(debug_assertions)]
    pub const fn max_magnitude() -> u32 {
        2047u32
    }

    /// Returns -self, treating it as a value of given magnitude.
    /// The provided magnitude must be equal or greater than the actual magnitude of `self`.
    /// Raises the magnitude by 1.
    pub const fn negate(&self, magnitude: u32) -> Self {
        let m = (magnitude + 1) as u64;
        let r0 = 0xFFFFEFFFFFC2Fu64 * 2 * m - self.0[0];
        let r1 = 0xFFFFFFFFFFFFFu64 * 2 * m - self.0[1];
        let r2 = 0xFFFFFFFFFFFFFu64 * 2 * m - self.0[2];
        let r3 = 0xFFFFFFFFFFFFFu64 * 2 * m - self.0[3];
        let r4 = 0x0FFFFFFFFFFFFu64 * 2 * m - self.0[4];
        Self([r0, r1, r2, r3, r4])
    }

    /// Multiplies by a single-limb integer.
    /// Multiplies the magnitude by the same value.
    pub const fn mul_single(&self, rhs: u32) -> Self {
        let rhs_u64 = rhs as u64;
        Self([
            self.0[0] * rhs_u64,
            self.0[1] * rhs_u64,
            self.0[2] * rhs_u64,
            self.0[3] * rhs_u64,
            self.0[4] * rhs_u64,
        ])
    }
}

impl Default for FieldElement5x52 {
    fn default() -> Self {
        Self::zero()
    }
}

impl ConditionallySelectable for FieldElement5x52 {
    fn conditional_select(
        a: &FieldElement5x52,
        b: &FieldElement5x52,
        choice: Choice,
    ) -> FieldElement5x52 {
        FieldElement5x52([
            u64::conditional_select(&a.0[0], &b.0[0], choice),
            u64::conditional_select(&a.0[1], &b.0[1], choice),
            u64::conditional_select(&a.0[2], &b.0[2], choice),
            u64::conditional_select(&a.0[3], &b.0[3], choice),
            u64::conditional_select(&a.0[4], &b.0[4], choice),
        ])
    }
}

impl ConstantTimeEq for FieldElement5x52 {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0[0].ct_eq(&other.0[0])
            & self.0[1].ct_eq(&other.0[1])
            & self.0[2].ct_eq(&other.0[2])
            & self.0[3].ct_eq(&other.0[3])
            & self.0[4].ct_eq(&other.0[4])
    }
}
