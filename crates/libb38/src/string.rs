//! string — the human-readable encoding of balanced base-38 numbers.
//!
//! THE ALPHABET: `0-9` for 0–9, `a-z` for 10–35, `_` for 36, `~` for 37.
//! MSB-first, sign prefix: `"0"` is the Void, `"-7"` is minus seven,
//! `"+f"` is plus 15. No leading zeros (the canonical form, matching
//! the unique representation the lane already carries).
//!
//! The parse walks the digit string by Horner into an unsigned accumulator,
//! applies the sign, and hands the result to `from_i128` — the forced
//! residue walk — so the string always lands in the canonical form.
//! The fold back uses `checked_to_i128` and refuses (None) beyond the
//! i128 shore.

use balanced38::{Balanced38, Rational38};

/// The 38-character alphabet for balanced base-38 digits.
const ALPHABET: &[u8; 38] = b"0123456789abcdefghijklmnopqrstuvwxyz_~";

/// The radix walk's honest bound: a period beyond 2^16 digits refuses
/// loudly rather than hang or grow without limit — the pre-registered
/// horizon of the VIEW door (the fraction is the storage).
pub const MAX_RADIX_STEPS: usize = 1 << 16;

/// Map a byte to its digit value (0..=37), or None for invalid chars.
fn digit_value(ch: u8) -> Option<u32> {
    match ch {
        b'0'..=b'9' => Some((ch - b'0') as u32),
        b'a'..=b'z' => Some((ch - b'a' + 10) as u32),
        b'_' => Some(36),
        b'~' => Some(37),
        _ => None,
    }
}

/// Format one digit value (0..=37) as a character.
fn digit_char(d: u32) -> char {
    ALPHABET[d as usize] as char
}

/// Parse a balanced base-38 string into a Balanced38.
///
/// Accepts: optional `+`/`-` sign, then 1+ digit chars from the alphabet.
/// The Void (`"0"`) is the only representation of zero.
/// No leading zeros in the digit part (the canonical form).
/// Returns `None` on any parse error (bad char, empty, overflow).
pub fn parse_b38_str(s: &str) -> Option<Balanced38> {
    let bytes = s.as_bytes();
    if bytes.is_empty() {
        return None;
    }
    let (sign, digits) = match bytes[0] {
        b'+' => (1i128, &bytes[1..]),
        b'-' => (-1i128, &bytes[1..]),
        _ => (1i128, bytes),
    };
    if digits.is_empty() {
        return None; // "+", "-" alone are not valid
    }
    // No leading zeros in the digit part (except the single zero "0")
    if digits.len() > 1 && digits[0] == b'0' {
        return None;
    }
    // Horner fold with the sign applied per place, checked at every
    // step: a magnitude beyond the i128 shore refuses (None) at the
    // place it crosses the shore — the truncating cast of the old fold
    // would have read it back as a wrapped lie.
    let mut acc: i128 = 0;
    for &ch in digits {
        let d = digit_value(ch)? as i128;
        acc = acc.checked_mul(38)?.checked_add(sign.checked_mul(d)?)?;
    }
    Some(Balanced38::from_i128(acc))
}

/// Format a Balanced38 as a balanced base-38 string.
///
/// The Void → `"0"`, positive → `"+"` or bare digits, negative → `"-"` prefix.
/// Uses the canonical residue walk (to_i128) for the fold-back, which is
/// safe for all strings ≤ 24 places (the proven shore).
pub fn fmt_b38_str(b: &Balanced38) -> String {
    if b.is_zero() {
        return "0".to_string();
    }
    let value = b.to_i128();
    let (sign, unsigned) = if value < 0 {
        // unsigned_abs, not negation: i128::MIN's mirror overflows i128,
        // and this is the one form whose magnitude (2^127) still rides
        // u128 exactly.
        ('-', value.unsigned_abs())
    } else {
        ('+', value as u128)
    };
    // Build digits MSB-first by repeated division
    let mut digits = Vec::new();
    let mut n = unsigned;
    while n > 0 {
        digits.push(digit_char((n % 38) as u32));
        n /= 38;
    }
    digits.reverse(); // now MSB-first
    let mut out = String::with_capacity(1 + digits.len());
    out.push(sign);
    for ch in &digits {
        out.push(*ch);
    }
    out
}

/// Parse a fraction string into a Rational38: `"p/q"` or a bare
/// canonical integer. The denominator must parse and must not be the
/// Void; the pair enters the store reduced (`den > 0`, sign on num).
pub fn parse_ratio_str(s: &str) -> Option<Rational38> {
    let bytes = s.as_bytes();
    let slash = bytes.iter().position(|&b| b == b'/');
    // split at most once — "p/q/r" refuses
    if let Some(at) = slash {
        if bytes[at + 1..].contains(&b'/') {
            return None;
        }
        let num = parse_b38_str(std::str::from_utf8(&bytes[..at]).ok()?)?;
        let den = parse_b38_str(std::str::from_utf8(&bytes[at + 1..]).ok()?)?;
        if den.is_zero() {
            return None; // the Void is not an operand
        }
        Rational38::from_ints(num, den)
    } else {
        let n = parse_b38_str(s)?;
        Rational38::from_ints(n, Balanced38::from_i128(1))
    }
}

/// Format a Rational38 canonically: the Void is `"0"`, an integer rides
/// its integer form, otherwise `"num/den"` with the sign on the
/// numerator and the denominator positive.
pub fn fmt_ratio_str(r: &Rational38) -> String {
    if r.is_zero() {
        return "0".to_string();
    }
    let num = fmt_b38_str(r.num());
    if r.den().to_i128() == 1 {
        num
    } else {
        format!("{}/{}", num, fmt_b38_str(r.den()))
    }
}

/// A digit stream (MSB-first) folded by Horner into an unsigned value —
/// the raw number a radix block stands for.
fn fold_digits(bytes: &[u8]) -> Option<u128> {
    let mut acc: u128 = 0;
    for &ch in bytes {
        acc = acc.checked_mul(38)?.checked_add(digit_value(ch)? as u128)?;
    }
    Some(acc)
}

/// A digit value (0..=37) as its alphabet byte.
fn digit_byte(d: u128) -> u8 {
    ALPHABET[d as usize]
}

/// The VIEW door out: a rational's base-38 radix expansion, the
/// recurring block wrapped in trailing `(…)`.
///
/// Uses the Euclidean (floor) split, so a negative rational reads as
/// `−(⌈|a/b|⌉) + fraction` — e.g. `-1/2` is `-1` plus `.j` (`"-1.j"`).
/// Numbers never lie: this is the standard floor reading, not a rounded
/// half. A fraction whose long division crosses the i128 shore at the
/// `38·r` product, or a period beyond `max_steps`, refuses loudly.
pub fn to_radix_str(r: &Rational38, max_steps: usize) -> Option<String> {
    let num = r.num().to_i128();
    let den = r.den().to_i128(); // den > 0 by the store's law
    if num == 0 {
        return Some("0".to_string());
    }
    // the Euclidean split: the integer part carries the floor (and the
    // sign), the remainder is always non-negative
    let (q, rem) = (num.div_euclid(den), num.rem_euclid(den));
    let int_str = fmt_b38_str(&Balanced38::from_i128(q));
    if rem == 0 {
        return Some(int_str);
    }
    let two38 = Balanced38::from_i128(38);
    let import_den = Balanced38::from_i128(den);
    // the walk keys `seen` by the CURRENT remainder before each digit
    // steps forward, so a repeat starts the period exactly at the
    // producing digit — never one (or minus one) digit astray
    let mut seen = std::collections::HashMap::new();
    let mut cur = rem;
    let mut idx = 0usize;
    let mut digits: Vec<u8> = Vec::new();
    loop {
        if let Some(&start) = seen.get(&cur) {
            // the state repeats: the tail digits[start..] cycles forever
            let mut out = int_str;
            out.push('.');
            for &ch in &digits[..start] {
                out.push(ch as char);
            }
            out.push('(');
            for &ch in &digits[start..] {
                out.push(ch as char);
            }
            out.push(')');
            return Some(out);
        }
        if digits.len() >= max_steps {
            return None; // the horizon refused — period too long
        }
        seen.insert(cur, idx);
        let t = two38.checked_mul(&Balanced38::from_i128(cur))?;
        let d = t.checked_div(&import_den)?;
        let next_rem = t.checked_rem(&import_den)?.to_i128();
        digits.push(digit_byte(d.to_i128() as u128));
        idx += 1;
        if next_rem == 0 {
            break; // the walk ended: finite expansion
        }
        cur = next_rem;
    }
    // finite: no wrap, just the dot and the digits
    let mut out = int_str;
    out.push('.');
    for &ch in &digits {
        out.push(ch as char);
    }
    Some(out)
}

/// The VIEW door in: a radix string back into the fraction store.
///
/// Forms: `int`, `int.frac` (finite), `int.pre(per)` (recurring).
/// The integer part is a canonical balanced integer string (sign
/// optional); the fractional streams are unsigned base-38 digit runs
/// (`"0.01"` is 1/38², `"0.(cp)"` is 1/3). The closed form rides the
/// checked lane — a stream whose 38^k crosses the i128 shore refuses.
pub fn parse_radix_str(s: &str) -> Option<Rational38> {
    let bytes = s.as_bytes();
    if bytes.is_empty() {
        return None;
    }
    // split at the single radix point
    let (int_bytes, rest, has_dot) = match bytes.iter().position(|&b| b == b'.') {
        None => (bytes, &b""[..], false),
        Some(at) => (&bytes[..at], &bytes[at + 1..], true),
    };
    // carve the trailing recurring block, if any
    let (frac_bytes, per_bytes) = if let Some(open) = rest.iter().position(|&b| b == b'(') {
        let content = &rest[open + 1..rest.len().saturating_sub(1)];
        let ok = open + 1 < rest.len() - 1
            && rest.ends_with(b")")
            && !content.contains(&b'(')
            && !content.contains(&b')');
        if !ok {
            return None;
        }
        (&rest[..open], &rest[open + 1..rest.len() - 1])
    } else {
        if rest.contains(&b')') {
            return None; // a stray close without its open
        }
        (rest, &b""[..])
    };
    // a bare dot is not a canon: "5." and "." refuse (integers ride
    // their integer form and the dot demands a stream to sit on)
    if has_dot && rest.is_empty() {
        return None;
    }
    let m = frac_bytes.len();
    let n = per_bytes.len();
    let int = parse_b38_str(std::str::from_utf8(int_bytes).ok()?)?;
    let pre = fold_digits(frac_bytes)?;
    let per = if n > 0 { fold_digits(per_bytes)? } else { 0 };
    // the power ladder, checked against the lane at every rung
    let mut pow_m = Balanced38::from_i128(1);
    for _ in 0..m {
        pow_m = pow_m.checked_mul(&Balanced38::from_i128(38))?;
    }
    // the closed form:
    //   finite:     (int·38^m + pre) / 38^m
    //   recurring:  (int·38^m·(38^n−1) + pre·(38^n−1) + per) / (38^m·(38^n−1))
    let (num, den) = if n == 0 {
        let num = int
            .checked_mul(&pow_m)?
            .checked_add(&Balanced38::from_i128(i128::try_from(pre).ok()?));
        (num, pow_m)
    } else {
        let mut pow_n = Balanced38::from_i128(1);
        for _ in 0..n {
            pow_n = pow_n.checked_mul(&Balanced38::from_i128(38))?;
        }
        // 38^n − 1 is the add of the loan: +(−1)
        let pn = pow_n.checked_add(&Balanced38::from_i128(-1));
        let pre_b = Balanced38::from_i128(i128::try_from(pre).ok()?);
        let per_b = Balanced38::from_i128(i128::try_from(per).ok()?);
        let num = int
            .checked_mul(&pow_m)?
            .checked_mul(&pn)?
            .checked_add(&pre_b.checked_mul(&pn)?)
            .checked_add(&per_b);
        let den = pow_m.checked_mul(&pn)?;
        (num, den)
    };
    Rational38::from_ints(num, den)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trip_small_values() {
        for v in -500i128..=500 {
            let b = Balanced38::from_i128(v);
            let s = fmt_b38_str(&b);
            let back = parse_b38_str(&s).expect("parse should succeed");
            assert_eq!(back.to_i128(), v, "round trip broke at {v}: got {s}");
        }
    }

    #[test]
    fn the_void_is_zero() {
        assert_eq!(fmt_b38_str(&Balanced38::zero()), "0");
        assert!(parse_b38_str("0").unwrap().is_zero());
    }

    #[test]
    fn rejects_bad_input() {
        assert!(parse_b38_str("").is_none());
        assert!(parse_b38_str("+").is_none());
        assert!(parse_b38_str("-").is_none());
        assert!(parse_b38_str("07").is_none()); // leading zero
        assert!(parse_b38_str("ZZZ").is_none()); // out of alphabet
    }

    #[test]
    fn sign_prefix_is_optional() {
        assert_eq!(parse_b38_str("7").unwrap().to_i128(), 7);
        assert_eq!(parse_b38_str("+7").unwrap().to_i128(), 7);
        assert_eq!(parse_b38_str("-7").unwrap().to_i128(), -7);
    }

    /// THE EXTREMES ROUND-TRIP: the full i128 shore through the string
    /// door, both edges — the fold-back of MIN must not overflow (its
    /// mirror is one past i128) and the parse must read it back exactly.
    #[test]
    fn the_extremes_round_trip_through_the_string_door() {
        for v in [i128::MAX, i128::MIN, 0, 1, -1, 1i128 << 64, -(1i128 << 64)] {
            let s = fmt_b38_str(&Balanced38::from_i128(v));
            let back = parse_b38_str(&s).expect("the extreme must parse back");
            assert_eq!(back.to_i128(), v, "the shore broke at {v}: got {s}");
        }
    }

    /// THE PARSE GATE IS HONEST: a positive string whose magnitude sits
    /// beyond the i128 shore must refuse (None) — the truncated cast of
    /// the old fold read it back as a false negative, a wrapped lie.
    #[test]
    fn beyond_shore_positive_strings_refuse() {
        // 25 places, every digit the maximum: 19·(38^25−1)/37 > 2^127−1
        let over = "z".repeat(25);
        assert!(parse_b38_str(&over).is_none(), "beyond-shore must refuse");
        // the exact shore edge, 2^127−1 (also 25 places), still fits
        let max = fmt_b38_str(&Balanced38::from_i128(i128::MAX));
        assert_eq!(parse_b38_str(&max).unwrap().to_i128(), i128::MAX);
    }

    // ── the fraction door ──────────────────────────────────────────

    #[test]
    fn fractions_enter_reduced_and_canonical() {
        assert_eq!(fmt_ratio_str(&r(6, 8)), "+3/+4");
        assert_eq!(fmt_ratio_str(&r(-3, -4)), "+3/+4");
        assert_eq!(fmt_ratio_str(&r(3, -4)), "-3/+4");
        assert_eq!(fmt_ratio_str(&r(5, 1)), "+5"); // an integer rides bare
        assert_eq!(fmt_ratio_str(&r(0, 7)), "0"); // the Void canonicalizes
        assert_eq!(fmt_ratio_str(&r(-5, -2)), "+5/+2");
        assert_eq!(fmt_ratio_str(&r(0, -9)), "0");
    }

    #[test]
    fn the_fraction_string_door_is_an_identity() {
        for n in -40i128..=40 {
            for d in 1i128..=40 {
                let s = fmt_ratio_str(&r(n, d));
                let back = parse_ratio_str(&s).expect("must parse back");
                assert_eq!(back, r(n, d), "ratio round-trip broke at {n}/{d}: {s}");
            }
        }
    }

    #[test]
    fn fraction_refusals_are_loud() {
        assert_eq!(parse_ratio_str("7/0"), None, "the Void divisor refuses");
        assert_eq!(parse_ratio_str("0/0"), None);
        assert_eq!(parse_ratio_str("1/2/3"), None, "one slash only");
        assert_eq!(parse_ratio_str("/3"), None, "no empty numerator");
        assert_eq!(parse_ratio_str("p/"), None, "no empty denominator");
        assert_eq!(parse_ratio_str("3/0"), None);
        assert_eq!(
            parse_ratio_str(&format!("{0}{1}", "z".repeat(25), "/3")),
            None,
            "beyond-shore num"
        );
    }

    /// THE RECEIPT: the husk keeps counting — "+3/+4" + "+1/+2" is
    /// "+5/+4", exactly, through the fraction door.
    #[test]
    fn the_certified_ratio_receipt() {
        let a = parse_ratio_str("+3/+4").unwrap();
        let b = parse_ratio_str("+1/+2").unwrap();
        let sum = a.checked_add(&b).expect("in-shore");
        assert_eq!(fmt_ratio_str(&sum), "+5/+4");
    }

    // ── the radix VIEW door ────────────────────────────────────────

    #[test]
    fn the_radix_receipts() {
        assert_eq!(to_radix_str(&r(1, 3), 100).unwrap(), "0.(cp)");
        assert_eq!(to_radix_str(&r(1, 38), 100).unwrap(), "0.1");
        assert_eq!(to_radix_str(&r(1, 1444), 100).unwrap(), "0.01");
        assert_eq!(to_radix_str(&r(3, 4), 100).unwrap(), "0.sj");
        assert_eq!(to_radix_str(&r(1, 7), 100).unwrap(), "0.(5gawlr)");
        assert_eq!(to_radix_str(&r(4, 3), 100).unwrap(), "+1.(cp)");
        assert_eq!(to_radix_str(&r(2, 3), 100).unwrap(), "0.(pc)");
        assert_eq!(to_radix_str(&r(37, 38), 100).unwrap(), "0.~");
        assert_eq!(to_radix_str(&r(1, 1), 100).unwrap(), "+1");
        assert_eq!(to_radix_str(&r(5, 1), 100).unwrap(), "+5");
        assert_eq!(to_radix_str(&Rational38::zero(), 100).unwrap(), "0");
        // the Euclidean (floor) split: −1/2 reads as −1 + 1/2
        assert_eq!(to_radix_str(&r(-1, 2), 100).unwrap(), "-1.j");
        assert_eq!(to_radix_str(&r(-3, 4), 100).unwrap(), "-1.9j");
    }

    #[test]
    fn the_radix_hubble_receipt() {
        // decimal 141/25 in base-38: +5.(oc631jsxgrdpvy_i94la), period 20
        let view = to_radix_str(&r(141, 25), 100).unwrap();
        assert_eq!(view, "+5.(oc631jsxgrdpvy_i94la)");
        let back = parse_radix_str(&view).expect("the view must re-read");
        assert_eq!(
            back,
            r(141, 25),
            "the Hubble fraction does not survive its own view"
        );
    }

    #[test]
    fn the_radix_view_and_back_are_an_identity() {
        for n in -15i128..=15 {
            for d in 1i128..=31 {
                if n == 0 {
                    continue;
                }
                let rat = r(n, d);
                let view = to_radix_str(&rat, 1 << 12).expect("short period");
                let back = parse_radix_str(&view).expect("must parse back");
                assert_eq!(back, rat, "radix round-trip broke at {n}/{d}: {view}");
            }
        }
    }

    #[test]
    fn radix_refusals_are_loud() {
        let bad = [
            "5.",
            ".5",
            "1.(2)(3)",
            "1.(2",
            "1.2)",
            "1.2(34)5",
            "5.()",
            "(cp)",
            ".",
            "007.5",
            "1.2.3",
            "1..2",
            "5.z!",
            "~..",
            "+",
            "-",
            "0.1(2)(3)",
        ];
        for s in bad {
            assert_eq!(parse_radix_str(s), None, "must refuse: {s:?}");
        }
    }

    #[test]
    fn the_period_horizon_refuses_loudly() {
        // 1/7 has period 6 — a tighter bound must refuse, never truncate
        assert_eq!(to_radix_str(&r(1, 7), 6).unwrap(), "0.(5gawlr)");
        assert_eq!(to_radix_str(&r(1, 7), 5), None, "the horizon refused");
    }

    #[test]
    fn beyond_shore_denominators_refuse_the_view() {
        // the walk's 38·r product leaves the i128 shore — the door
        // refuses loudly instead of wrapping. (1/2^68 would END: base-38
        // is even, so small powers of two are terminating; the shore
        // case needs a denominator near 2^127.)
        let huge = Rational38::from_i128s(1, 1i128 << 126).unwrap();
        assert_eq!(to_radix_str(&huge, 1 << 16), None, "the walk must refuse");
        // and the same tail cannot survive the fold _in_ either:
        // 38^30 crosses the shore somewhere in the ladder
        let long = format!("1{}", "0".repeat(30)); // 1.000... 30 digits → 38^30
        assert_eq!(
            parse_radix_str(&long),
            None,
            "the shore refused the closed form"
        );
    }

    /// Oracle-block: the digit stream folded back equals the universe's
    /// own arithmetic — 0.sj really is three quarters.
    #[test]
    fn the_radix_stream_folds_to_the_fraction() {
        let back = parse_radix_str("0.sj").unwrap();
        assert_eq!((back.num().to_i128(), back.den().to_i128()), (3, 4));
        let back2 = parse_radix_str("-1.9j").unwrap();
        assert_eq!((back2.num().to_i128(), back2.den().to_i128()), (-3, 4));
        let back3 = parse_radix_str("0.(cp)").unwrap();
        assert_eq!((back3.num().to_i128(), back3.den().to_i128()), (1, 3));
    }

    /// Helper: a fraction in the small band.
    fn r(n: i128, d: i128) -> Rational38 {
        Rational38::from_i128s(n, d).expect("in-shore")
    }
}
