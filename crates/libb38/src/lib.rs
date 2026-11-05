//! libb38 — the C-ABI key to the balanced base-38 lane.
//!
//! A drop-in exact-arithmetic layer that lets any program compute with
//! balanced base-38 rational numbers the way humans write them — no
//! rounding, no overflow surprises, no binary-decimal conversion tax.
//!
//! The public surface is three doors:
//! - [`parse`] / [`display`] — the human-readable encoding
//! - [`add`] — the exact sum of two balanced base-38 strings
//! - the C-ABI in [`ffi`] — linkable from any language

#![deny(unsafe_op_in_unsafe_fn)]

pub mod ffi;
pub mod string;

pub use string::{fmt_b38_str as display, parse_b38_str as parse};

/// Add two balanced base-38 strings exactly. Returns `Some(result)` or
/// `None` on parse error / overflow beyond the i128 shore.
pub fn add(a: &str, b: &str) -> Option<String> {
    let a_bal = parse(a)?;
    let b_bal = parse(b)?;
    let sum = a_bal.checked_add(&b_bal);
    Some(display(&sum))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_small_numbers() {
        assert_eq!(add("2", "3").unwrap(), "+5");
        assert_eq!(add("0", "0").unwrap(), "0");
        assert_eq!(add("+1", "-1").unwrap(), "0");
    }

    #[test]
    fn add_negative_numbers() {
        assert_eq!(add("-3", "-4").unwrap(), "-7");
        assert_eq!(add("-5", "+2").unwrap(), "-3");
        assert_eq!(add("+5", "-2").unwrap(), "+3");
    }

    #[test]
    fn add_large_numbers() {
        // these are base-38 strings, not decimal: "1z" = 1·38+35 = 73
        assert_eq!(add("1z", "1").unwrap(), "+1_"); // carries the 35 up, land on gap 36
        assert_eq!(add("f", "g").unwrap(), "+v"); // 15+16 = 31
        assert_eq!(add("-100", "-100").unwrap(), "-200");
    }

    #[test]
    fn add_zero_identity() {
        assert_eq!(add("0", "42").unwrap(), "+42");
        assert_eq!(add("42", "0").unwrap(), "+42");
        assert_eq!(add("0", "0").unwrap(), "0");
    }
}
