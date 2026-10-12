//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for the `NonZero` model: construction, `get`, equality and copying,
//! for one unsigned and one signed width at each end of the range.

use std::num::{NonZeroI8, NonZeroI128, NonZeroU8, NonZeroU64, NonZeroUsize};

/// Zero is rejected.
#[verify::test]
pub fn test_new_zero_is_none() {
    assert!(NonZeroU64::new(0).is_none());
    assert!(NonZeroI8::new(0).is_none());
}

/// A non-zero value is accepted and `get` gives it back.
#[verify::test]
pub fn test_new_get_roundtrip() {
    let x = NonZeroU64::new(42).unwrap();
    assert!(x.get() == 42);
    let y = NonZeroU8::new(u8::MAX).unwrap();
    assert!(y.get() == u8::MAX);
    let z = NonZeroUsize::new(1).unwrap();
    assert!(z.get() == 1);
}

/// Negative values are non-zero.
#[verify::test]
pub fn test_signed_negative() {
    let x = NonZeroI8::new(i8::MIN).unwrap();
    assert!(x.get() == i8::MIN);
    let y = NonZeroI128::new(-1).unwrap();
    assert!(y.get() == -1);
}

/// Equality compares the underlying values.
#[verify::test]
pub fn test_eq() {
    let a = NonZeroU64::new(7).unwrap();
    let b = NonZeroU64::new(7).unwrap();
    let c = NonZeroU64::new(8).unwrap();
    assert!(a == b);
    assert!(a != c);
}

/// Copies compare equal to the original.
#[verify::test]
pub fn test_copy() {
    let a = NonZeroU64::new(9).unwrap();
    let b = a;
    #[allow(clippy::clone_on_copy)]
    let c = a.clone();
    assert!(a == b);
    assert!(a == c);
}
