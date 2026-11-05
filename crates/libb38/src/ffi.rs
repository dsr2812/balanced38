//! ffi — the C-ABI surface: strings in, exact answers out, no runtime.
//!
//! Every allocation goes through libc; every refusal is loud: the
//! string-returning doors hand back NULL, the integer doors hand back a
//! status no valid answer ever matches. The caller owns result strings
//! and must free them with [`b38_free`] — the one door the ABI opens
//! for memory. Bad input is refused, never guessed; a value beyond the
//! i128 shore is refused, never wrapped.

use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::os::raw::c_int;

use balanced38::{Balanced38, Rational38};

use crate::string::{
    fmt_b38_str, fmt_ratio_str, parse_b38_str, parse_radix_str, parse_ratio_str, to_radix_str,
    MAX_RADIX_STEPS,
};

/// The ABI version — one integer the caller can check without parsing
/// a string. Bump on every breaking change to the C surface.
/// v2: the surface grew from `b38_add` alone to the full arithmetic lane.
/// v3: the rational layer — `b38_ratio_*` doors (fraction + radix view).
#[no_mangle]
pub extern "C" fn b38_version() -> u32 {
    3
}

/// Parse one C-string argument into a balanced value — the shared
/// door every parse walks, so the refusals agree across the surface.
/// Never crosses the boundary itself.
///
/// # Safety
/// `c` must be a valid, null-terminated C string. Passing NULL is
/// undefined behaviour.
unsafe fn parse_arg(c: *const c_char) -> Option<Balanced38> {
    unsafe {
        let s = CStr::from_ptr(c).to_str().ok()?;
        parse_b38_str(s)
    }
}

/// parse one C-string argument into a rational — the fraction door's
/// shared entry, so every `b38_ratio_*` refusal agrees across the
/// surface. Never crosses the boundary itself.
///
/// # Safety
/// `c` must be a valid, null-terminated C string. Passing NULL is
/// undefined behaviour.
unsafe fn parse_ratio_arg(c: *const c_char) -> Option<Rational38> {
    unsafe {
        let s = CStr::from_ptr(c).to_str().ok()?;
        parse_ratio_str(s)
    }
}

/// Allocate a result string under the ceremony's ownership rules. The
/// caller (the C world) frees it with [`b38_free`]; NULL only on
/// allocation failure.
fn into_cstring(s: String) -> *mut c_char {
    match CString::new(s) {
        Ok(c) => c.into_raw(),
        Err(_) => std::ptr::null_mut(),
    }
}

/// The refusal status of the integer doors — a value no valid answer
/// ever returns, so a refusal is never mistaken for a result.
pub const B38_REFUSAL: c_int = -1;

/// Add two balanced base-38 strings exactly. Returns a newly allocated
/// string the caller must free with [`b38_free`], or NULL on any error
/// (bad input, allocation failure).
///
/// # Safety
/// `a` and `b` must be valid, null-terminated C strings. Passing NULL
/// is undefined behaviour — the function is a pure computation and
/// refuses to guess.
#[no_mangle]
pub unsafe extern "C" fn b38_add(a: *const c_char, b: *const c_char) -> *mut c_char {
    unsafe {
        let (a_bal, b_bal) = match (parse_arg(a), parse_arg(b)) {
            (Some(x), Some(y)) => (x, y),
            _ => return std::ptr::null_mut(),
        };
        let sum = a_bal.checked_add(&b_bal);
        into_cstring(fmt_b38_str(&sum))
    }
}

/// Subtract `b` from `a` exactly — the reflection law, as a door:
/// subtraction IS the addition of the negation. Returns a newly
/// allocated string (free with [`b38_free`]) or NULL on bad input or
/// allocation failure.
///
/// # Safety
/// `a` and `b` must be valid, null-terminated C strings. Passing NULL
/// is undefined behaviour.
#[no_mangle]
pub unsafe extern "C" fn b38_sub(a: *const c_char, b: *const c_char) -> *mut c_char {
    unsafe {
        let (a_bal, b_bal) = match (parse_arg(a), parse_arg(b)) {
            (Some(x), Some(y)) => (x, y),
            _ => return std::ptr::null_mut(),
        };
        let diff = a_bal.sub(&b_bal);
        into_cstring(fmt_b38_str(&diff))
    }
}

/// Multiply `a` by `b` exactly — the signed grid. Returns a newly
/// allocated string (free with [`b38_free`]) or NULL on bad input, a
/// product beyond the i128 shore, or allocation failure.
///
/// # Safety
/// `a` and `b` must be valid, null-terminated C strings. Passing NULL
/// is undefined behaviour.
#[no_mangle]
pub unsafe extern "C" fn b38_mul(a: *const c_char, b: *const c_char) -> *mut c_char {
    unsafe {
        let (a_bal, b_bal) = match (parse_arg(a), parse_arg(b)) {
            (Some(x), Some(y)) => (x, y),
            _ => return std::ptr::null_mut(),
        };
        let prod = match a_bal.checked_mul(&b_bal) {
            Some(p) => p,
            None => return std::ptr::null_mut(),
        };
        into_cstring(fmt_b38_str(&prod))
    }
}

/// Negate `a` exactly — the mirror. Returns a newly allocated string
/// (free with [`b38_free`]) or NULL on bad input or allocation failure.
///
/// # Safety
/// `a` must be a valid, null-terminated C string. Passing NULL is
/// undefined behaviour.
#[no_mangle]
pub unsafe extern "C" fn b38_neg(a: *const c_char) -> *mut c_char {
    unsafe {
        let a_bal = match parse_arg(a) {
            Some(v) => v,
            None => return std::ptr::null_mut(),
        };
        into_cstring(fmt_b38_str(&a_bal.negate()))
    }
}

/// The Euclidean quotient-remainder: `a` ÷ `b`, with the remainder
/// always in `0..|b|`. Writes the quotient string to `*out_q` and the
/// remainder string to `*out_r` — the caller owns both and frees them
/// with [`b38_free`]. Returns 0 on success. On refusal (bad input, the
/// Void divisor, a beyond-shore quotient or remainder, allocation
/// failure) returns [`B38_REFUSAL`] and leaves both outputs untouched —
/// never a wrapped value.
///
/// # Safety
/// `a` and `b` must be valid, null-terminated C strings; `out_q` and
/// `out_r` must be writable `char **`. Passing NULL is undefined
/// behaviour.
#[no_mangle]
pub unsafe extern "C" fn b38_div_rem(
    a: *const c_char,
    b: *const c_char,
    out_q: *mut *mut c_char,
    out_r: *mut *mut c_char,
) -> c_int {
    unsafe {
        let (a_bal, b_bal) = match (parse_arg(a), parse_arg(b)) {
            (Some(x), Some(y)) => (x, y),
            _ => return B38_REFUSAL,
        };
        let (q, r) = match a_bal.checked_div_rem(&b_bal) {
            Some(pair) => pair,
            None => return B38_REFUSAL,
        };
        let qs = into_cstring(fmt_b38_str(&q));
        let rs = into_cstring(fmt_b38_str(&r));
        if qs.is_null() || rs.is_null() {
            if !qs.is_null() {
                drop(CString::from_raw(qs));
            }
            if !rs.is_null() {
                drop(CString::from_raw(rs));
            }
            return B38_REFUSAL;
        }
        *out_q = qs;
        *out_r = rs;
        0
    }
}

/// The honest shore door, C-side: parse `a` and write its exact i128
/// value to `*out` — the integer that string names, or the door refuses.
/// Returns 0 on success; [`B38_REFUSAL`] on bad input or a string whose
/// value sits beyond the i128 shore. Never wraps.
///
/// # Safety
/// `a` must be a valid, null-terminated C string; `out` a writable
/// 128-bit integer. Passing NULL is undefined behaviour.
#[no_mangle]
pub unsafe extern "C" fn b38_to_i128(a: *const c_char, out: *mut i128) -> c_int {
    unsafe {
        let a_bal = match parse_arg(a) {
            Some(v) => v,
            None => return B38_REFUSAL,
        };
        match a_bal.checked_to_i128() {
            Some(v) => {
                *out = v;
                0
            }
            None => B38_REFUSAL,
        }
    }
}

/// Format an exact i128 value as its canonical balanced base-38 string,
/// written to `*out` (the caller frees it with [`b38_free`]). The value
/// never refuses — every i128 has exactly one string — so the only
/// refusal is allocation failure ([`B38_REFUSAL`], `*out` untouched).
/// Returns 0 on success.
///
/// # Safety
/// `out` must be a writable `char **`. Passing NULL is undefined
/// behaviour.
#[no_mangle]
pub unsafe extern "C" fn b38_from_i128(v: i128, out: *mut *mut c_char) -> c_int {
    unsafe {
        let s = into_cstring(fmt_b38_str(&Balanced38::from_i128(v)));
        if s.is_null() {
            return B38_REFUSAL;
        }
        *out = s;
        0
    }
}

/// Order two balanced base-38 strings as exact integers, like `strcmp`
/// for values: this returns a negative value if `a < b`, zero if equal,
/// a positive value if `a > b` (the implementation hands back −1, 0,
/// +1). On bad input returns a positive value far beyond any valid
/// comparison — [`B38_CMP_REFUSAL`] — so the refusal is never mistaken
/// for an order.
///
/// # Safety
/// `a` and `b` must be valid, null-terminated C strings. Passing NULL
/// is undefined behaviour.
#[no_mangle]
pub unsafe extern "C" fn b38_cmp(a: *const c_char, b: *const c_char) -> c_int {
    unsafe {
        let (a_bal, b_bal) = match (parse_arg(a), parse_arg(b)) {
            (Some(x), Some(y)) => (x, y),
            _ => return B38_CMP_REFUSAL,
        };
        // Every parsed string landed in-shore (built from i128), so the
        // fast fold is honest here — never a wrapped reading.
        let av = a_bal.to_i128();
        let bv = b_bal.to_i128();
        if av < bv {
            -1
        } else if av > bv {
            1
        } else {
            0
        }
    }
}

/// The refusal sentinel of [`b38_cmp`] — a positive value no comparison
/// ever returns. (The surface's own refusal constant is -1; the compare
/// needs a sentinel on the other side of zero so it can never collide
/// with a genuine "less than".)
pub const B38_CMP_REFUSAL: c_int = 1_000_000;

/// Add two fractions exactly (`"+3/+4" + "+1/+2"` → `"+5/+4"`).
/// Arguments are canonical fraction strings (a bare integer rides as
/// `n/1`); the result is reduced, the sign on the numerator, the Void
/// as `"0"`. Returns a freshly allocated string (free with
/// [`b38_free`]) or NULL on any refusal.
///
/// # Safety
/// `a` and `b` must be valid, null-terminated C strings. Passing NULL
/// is undefined behaviour.
#[no_mangle]
pub unsafe extern "C" fn b38_ratio_add(a: *const c_char, b: *const c_char) -> *mut c_char {
    unsafe {
        let (a_rat, b_rat) = match (parse_ratio_arg(a), parse_ratio_arg(b)) {
            (Some(x), Some(y)) => (x, y),
            _ => return std::ptr::null_mut(),
        };
        match a_rat.checked_add(&b_rat) {
            Some(sum) => into_cstring(fmt_ratio_str(&sum)),
            None => std::ptr::null_mut(),
        }
    }
}

/// Subtract `b` from `a` exactly — the fraction door's reflection law.
/// Same ceremony as [`b38_ratio_add`]; NULL on refusal.
///
/// # Safety
/// `a` and `b` must be valid, null-terminated C strings. Passing NULL
/// is undefined behaviour.
#[no_mangle]
pub unsafe extern "C" fn b38_ratio_sub(a: *const c_char, b: *const c_char) -> *mut c_char {
    unsafe {
        let (a_rat, b_rat) = match (parse_ratio_arg(a), parse_ratio_arg(b)) {
            (Some(x), Some(y)) => (x, y),
            _ => return std::ptr::null_mut(),
        };
        match a_rat.checked_sub(&b_rat) {
            Some(diff) => into_cstring(fmt_ratio_str(&diff)),
            None => std::ptr::null_mut(),
        }
    }
}

/// Multiply two fractions exactly. Same ceremony; NULL on refusal.
///
/// # Safety
/// `a` and `b` must be valid, null-terminated C strings. Passing NULL
/// is undefined behaviour.
#[no_mangle]
pub unsafe extern "C" fn b38_ratio_mul(a: *const c_char, b: *const c_char) -> *mut c_char {
    unsafe {
        let (a_rat, b_rat) = match (parse_ratio_arg(a), parse_ratio_arg(b)) {
            (Some(x), Some(y)) => (x, y),
            _ => return std::ptr::null_mut(),
        };
        match a_rat.checked_mul(&b_rat) {
            Some(prod) => into_cstring(fmt_ratio_str(&prod)),
            None => std::ptr::null_mut(),
        }
    }
}

/// Divide `a` by `b` exactly — multiplication by the reciprocal. The
/// Void divisor (`"0"`, `"0/1"`) refuses: NULL. Same ceremony.
///
/// # Safety
/// `a` and `b` must be valid, null-terminated C strings. Passing NULL
/// is undefined behaviour.
#[no_mangle]
pub unsafe extern "C" fn b38_ratio_div(a: *const c_char, b: *const c_char) -> *mut c_char {
    unsafe {
        let (a_rat, b_rat) = match (parse_ratio_arg(a), parse_ratio_arg(b)) {
            (Some(x), Some(y)) => (x, y),
            _ => return std::ptr::null_mut(),
        };
        match a_rat.checked_div(&b_rat) {
            Some(quot) => into_cstring(fmt_ratio_str(&quot)),
            None => std::ptr::null_mut(),
        }
    }
}

/// Negate a fraction exactly. Same ceremony; NULL on refusal.
///
/// # Safety
/// `a` must be a valid, null-terminated C string. Passing NULL is
/// undefined behaviour.
#[no_mangle]
pub unsafe extern "C" fn b38_ratio_neg(a: *const c_char) -> *mut c_char {
    unsafe {
        let a_rat = match parse_ratio_arg(a) {
            Some(v) => v,
            None => return std::ptr::null_mut(),
        };
        into_cstring(fmt_ratio_str(&a_rat.negate()))
    }
}

/// Order two fractions as exact values, like [`b38_cmp`]: −1, 0, +1.
/// On refusal (bad input, a cross-product beyond the shore) returns
/// [`B38_CMP_REFUSAL`] — never mistaken for an order.
///
/// # Safety
/// `a` and `b` must be valid, null-terminated C strings. Passing NULL
/// is undefined behaviour.
#[no_mangle]
pub unsafe extern "C" fn b38_ratio_cmp(a: *const c_char, b: *const c_char) -> c_int {
    unsafe {
        let (a_rat, b_rat) = match (parse_ratio_arg(a), parse_ratio_arg(b)) {
            (Some(x), Some(y)) => (x, y),
            _ => return B38_CMP_REFUSAL,
        };
        match a_rat.checked_cmp(&b_rat) {
            Some(std::cmp::Ordering::Less) => -1,
            Some(std::cmp::Ordering::Equal) => 0,
            Some(std::cmp::Ordering::Greater) => 1,
            None => B38_CMP_REFUSAL,
        }
    }
}

/// The VIEW door out, C-side: the rational's base-38 radix expansion,
/// recurring block in trailing `(…)` — `"+3/+4"` reads `"0.sj"`,
/// `"+1/+2"` reads `"0.j"`, `"0.(cp)"` is a third. The Euclidean floor
/// split puts the sign on the integer part (`"-1.j"` for `-1/2`). The
/// walk refuses (NULL) on the horizon — a period at or beyond 2^16
/// digits — and on a beyond-shore `38·r` product. Returns a freshly
/// allocated string; caller frees with [`b38_free`].
///
/// # Safety
/// `a` must be a valid, null-terminated C string. Passing NULL is
/// undefined behaviour.
#[no_mangle]
pub unsafe extern "C" fn b38_ratio_to_radix(a: *const c_char) -> *mut c_char {
    unsafe {
        let a_rat = match parse_ratio_arg(a) {
            Some(v) => v,
            None => return std::ptr::null_mut(),
        };
        match to_radix_str(&a_rat, MAX_RADIX_STEPS) {
            Some(view) => into_cstring(view),
            None => std::ptr::null_mut(),
        }
    }
}

/// The VIEW door in, C-side: a radix string back into the fraction
/// store, returned in canonical fraction form. `"0.(cp)"` re-reads as
/// `"+1/+3"`, `"0.1"` as `"+1/+38"`. Multivalued or malformed strings
/// refuse (NULL) — the closed form's `38^k` days are pre-registered to
/// refuse beyond the shore instead of re-reading a long view as a lie.
/// Returns a freshly allocated string; caller frees with [`b38_free`].
///
/// # Safety
/// `a` must be a valid, null-terminated C string. Passing NULL is
/// undefined behaviour.
#[no_mangle]
pub unsafe extern "C" fn b38_ratio_from_radix(a: *const c_char) -> *mut c_char {
    unsafe {
        let s = match CStr::from_ptr(a).to_str() {
            Ok(s) => s,
            Err(_) => return std::ptr::null_mut(),
        };
        let view = match parse_radix_str(s) {
            Some(v) => v,
            None => return std::ptr::null_mut(),
        };
        into_cstring(fmt_ratio_str(&view))
    }
}

/// Free a string previously returned by a libb38 function that returns
/// `*mut c_char` (or writes one through a `char **`). Passing NULL is a
/// no-op.
///
/// # Safety
/// The pointer must have been returned by a libb38 function. Passing
/// a dangling or double-freed pointer is undefined behaviour.
#[no_mangle]
pub unsafe extern "C" fn b38_free(s: *mut c_char) {
    if !s.is_null() {
        unsafe {
            drop(CString::from_raw(s));
        }
    }
}
