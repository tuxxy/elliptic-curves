//! Arithmetic helper functions for the u32 backend

/// Computes `a + b + carry`, returning the result along with the new carry. 32-bit version.
#[inline(always)]
pub const fn adc(a: u32, b: u32, carry: u32) -> (u32, u32) {
    let ret = (a as u64) + (b as u64) + (carry as u64);
    (ret as u32, (ret >> 32) as u32)
}

/// Computes `a - (b + borrow)`, returning the result along with the new borrow. 32-bit version.
#[inline(always)]
pub const fn sbb(a: u32, b: u32, borrow: u32) -> (u32, u32) {
    let ret = (a as u64).wrapping_sub((b as u64) + ((borrow >> 31) as u64));
    (ret as u32, (ret >> 32) as u32)
}
