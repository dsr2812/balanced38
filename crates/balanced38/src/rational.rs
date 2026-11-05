//! rational — THE PROMISE'S STORE: every exact rational as a reduced
//! pair of lane integers, the Void the only zero.
//!
//! Base-38 is a weak terminating base — of 1/2..1/100 only 9 have a
//! finite base-38 expansion (the Weighing's honest column). So a
//! rational here is NEVER a decimal-ish view; it is the fraction
//! itself, `num / den`, always reduced, always `den > 0`, the sign on
//! the numerator. The radix string with its repeating block is a VIEW
//! over this store (see libb38) — the fraction is the truth.
//!
//! The shore law, pre-registered: num and den each ride the integer
//! lane's proven shore (≤ 24 places at rest), and every composition —
//! products, cross-multiplications, common denominators — is checked
//! and refuses loudly (`None`) one step past the i128 shore. A
//! rational operation on two in-shore operands can therefore refuse
//! where a wider package would not; that is the honest shore, not a
//! bug. Numbers never lie; refusals are loud.

use crate::Balanced38;

/// THE PROMISE'S STORE: a reduced, signed fraction on the lane.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Rational38 {
    num: Balanced38,
    den: Balanced38,
}

impl Default for Rational38 {
    /// The Void — the empty fraction, [`Rational38::zero`].
    fn default() -> Self {
        Self::zero()
    }
}

impl Rational38 {
    /// The Void — zero as a fraction.
    pub fn zero() -> Self {
        Self {
            num: Balanced38::zero(),
            den: Balanced38::from_i128(1),
        }
    }

    /// Build from any two lane integers: refuses a zero denominator,
    /// flips the sign onto the numerator (`-3/-4` lands as `+3/+4`),
    /// and reduces by the lane's own Euclidean gcd. Nothing here
    /// grows past the inputs — reduction only shrinks — so the only
    /// refusal is the Void divisor (and the checked core, loudly).
    pub fn from_ints(n: Balanced38, d: Balanced38) -> Option<Self> {
        if d.is_zero() {
            return None; // the Void is not an operand
        }
        // Read the sign through the checked shore door: a beyond-shore
        // denominator refuses instead of wrapping into the wrong sign.
        let (n, d) = if d.checked_to_i128()? < 0 {
            (n.negate(), d.negate())
        } else {
            (n, d)
        };
        if !n.is_zero() {
            let g = gcd(n.clone(), d.clone())?;
            let num = n.checked_div(&g)?;
            let den = d.checked_div(&g)?;
            Some(Self { num, den })
        } else {
            Some(Self {
                num: Balanced38::zero(),
                den: Balanced38::from_i128(1),
            })
        }
    }

    /// Build from raw i128 numerator and denominator. Refuses a zero
    /// denominator.
    pub fn from_i128s(n: i128, d: i128) -> Option<Self> {
        Self::from_ints(Balanced38::from_i128(n), Balanced38::from_i128(d))
    }

    /// The numerator (signed).
    pub fn num(&self) -> &Balanced38 {
        &self.num
    }

    /// The denominator — positive, always.
    pub fn den(&self) -> &Balanced38 {
        &self.den
    }

    /// Is this the Void?
    pub fn is_zero(&self) -> bool {
        self.num.is_zero()
    }

    /// The mirror: the sign flips, the magnitude stays reduced.
    pub fn negate(&self) -> Self {
        Self {
            num: self.num.negate(),
            den: self.den.clone(),
        }
    }

    /// `a/b + c/d = (ad + cb) / bd`, reduced. The products ride the
    /// checked lane, so a common denominator beyond the shore refuses
    /// loudly — the pre-registered shore law.
    pub fn checked_add(&self, other: &Self) -> Option<Self> {
        let ad = self.num.checked_mul(&other.den)?;
        let cb = other.num.checked_mul(&self.den)?;
        let num = ad.checked_add(&cb);
        let den = self.den.checked_mul(&other.den)?;
        Self::from_ints(num, den)
    }

    /// `a/b − c/d` is the addition of the negation — the reflection
    /// law, as a fraction.
    pub fn checked_sub(&self, other: &Self) -> Option<Self> {
        self.checked_add(&other.negate())
    }

    /// `(a/b)·(c/d) = ac/bd`, reduced.
    pub fn checked_mul(&self, other: &Self) -> Option<Self> {
        let num = self.num.checked_mul(&other.num)?;
        let den = self.den.checked_mul(&other.den)?;
        Self::from_ints(num, den)
    }

    /// `(a/b)÷(c/d)` is multiplication by the reciprocal; a zero
    /// divisor refuses — the Void cannot divide.
    pub fn checked_div(&self, other: &Self) -> Option<Self> {
        if other.is_zero() {
            return None; // the Void is not an operand
        }
        let reciprocal = Self::from_ints(other.den.clone(), other.num.clone())?;
        self.checked_mul(&reciprocal)
    }

    /// Order two fractions by their cross-products: `ad vs cb`. The
    /// products are checked (beyond-shore refusals are loud), and
    /// every successful product is in-shore, so the numeric compare
    /// is the honest fold — never a wrapped reading.
    pub fn checked_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        let ad = self.num.checked_mul(&other.den)?;
        let cb = other.num.checked_mul(&self.den)?;
        Some(ad.to_i128().cmp(&cb.to_i128()))
    }
}

/// Exact base-60 reading of a signed rational: integer part, then
/// sexagesimal digits after a comma; when the digits do not terminate,
/// the remaining exact fraction is named, never rounded. This is the
/// same desk form the Hubble example prints — one implementation, one law.
pub fn desk_form(n: i128, d: i128) -> String {
    let r = Rational38::from_i128s(n, d).expect("in-shore");
    let num = r.num().to_i128();
    let den = r.den().to_i128();
    let int_part = num / den;
    let mut rem = num % den;
    let mut digits = Vec::new();
    while rem != 0 && digits.len() < 12 {
        let t = rem * 60;
        digits.push(t / den);
        rem = t % den;
    }
    let frac = if digits.is_empty() {
        String::new()
    } else {
        format!(
            ", {}",
            digits
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
                .join(",")
        )
    };
    if rem != 0 {
        format!("{}{} (residual {}/{}, exact)", int_part, frac, rem, den)
    } else {
        format!("{}{}", int_part, frac)
    }
}

/// The lane's own Euclidean gcd — a/b stays in-shore the whole way
/// (remainders only shrink), so this doors the Option just for the
/// checked core's signature.
fn gcd(mut a: Balanced38, mut b: Balanced38) -> Option<Balanced38> {
    while !b.is_zero() {
        let r = a.checked_rem(&b)?;
        a = b;
        b = r;
    }
    Some(a)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Reduce a raw i128 pair the way the lane should, for oracles.
    fn reduced(n: i128, d: i128) -> (i128, i128) {
        let (n, d) = if d < 0 { (-n, -d) } else { (n, d) };
        if n == 0 {
            return (0, 1);
        }
        let (mut a, mut b) = (n.abs(), d);
        while b != 0 {
            let r = a % b;
            a = b;
            b = r;
        }
        (n / a, d / a)
    }

    #[test]
    fn desk_form_says_the_hubble_truth() {
        assert_eq!(desk_form(141, 25), "5, 38,24");
        assert_eq!(desk_form(1826, 25), "73, 2,24");
        assert_eq!(desk_form(1, 3), "0, 20");
    }

    #[test]
    fn from_i128s_reduces_and_normalizes() {
        assert_eq!(from_pair(6, 8), (3, 4));
        assert_eq!(from_pair(-3, -4), (3, 4));
        assert_eq!(from_pair(3, -4), (-3, 4));
        assert_eq!(from_pair(-6, -8), (3, 4));
        for n in -20i128..=20 {
            for d in -20i128..=20 {
                if d == 0 {
                    continue;
                }
                assert_eq!(from_pair(n, d), reduced(n, d), "reduction broke at {n}/{d}");
            }
        }
    }

    /// The numerator/denominator as a raw pair, for assertions.
    fn from_pair(n: i128, d: i128) -> (i128, i128) {
        let r = Rational38::from_i128s(n, d).expect("in-shore");
        (r.num().to_i128(), r.den().to_i128())
    }

    #[test]
    fn the_void_is_the_only_zero() {
        let zero = Rational38::zero();
        assert!(zero.is_zero());
        assert_eq!((zero.num().to_i128(), zero.den().to_i128()), (0, 1));
        assert!(Rational38::from_i128s(0, -7).unwrap().is_zero());
        assert_eq!(
            Rational38::from_i128s(5, 0),
            None,
            "the Void divisor refused"
        );
    }

    #[test]
    fn the_negation_flips_the_sign_and_keeps_the_magnitude() {
        for n in -30i128..=30 {
            for d in 1i128..=30 {
                let r = Rational38::from_i128s(n, d).unwrap();
                let neg = r.negate();
                assert_eq!(
                    neg,
                    Rational38::from_i128s(-n, d).unwrap(),
                    "the mirror lied at {n}/{d}"
                );
                assert_eq!(neg.negate(), r, "the double mirror lied at {n}/{d}");
            }
        }
    }

    #[test]
    fn the_mul_identity_carries_through_the_lane() {
        let mut seed = 0x3bu64;
        let mut next = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for _ in 0..20_000 {
            let (a, b, c, d) = (
                (next() % 200) as i128 - 100,
                (next() % 100 + 1) as i128,
                ((next() % 200) as i128) - 100,
                (next() % 100 + 1) as i128,
            );
            let (x, y) = (make(a, b), make(c, d));
            let p = x.checked_mul(&y).expect("in-shore products");
            assert_eq!(
                (p.num().to_i128(), p.den().to_i128()),
                reduced(a * c, b * d),
                "mul identity broke at {a}/{b} * {c}/{d}"
            );
        }
    }

    #[test]
    fn the_add_identity_carries_through_the_lane() {
        for a in -40i128..=40 {
            for b in 1i128..=40 {
                for c in -40i128..=40 {
                    for d in 1i128..=40 {
                        if a * d + c * b == 0 || b * d == 0 {
                            continue;
                        }
                        let s = make(a, b).checked_add(&make(c, d)).expect("in-shore band");
                        assert_eq!(
                            (s.num().to_i128(), s.den().to_i128()),
                            reduced(a * d + c * b, b * d),
                            "add identity broke at {a}/{b} + {c}/{d}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn the_div_identity_carries_through_the_lane() {
        for a in -30i128..=30 {
            for b in 1i128..=30 {
                for c in -30i128..=30 {
                    for d in 1i128..=30 {
                        if c == 0 {
                            continue;
                        }
                        let x = make(a, b);
                        let y = make(c, d);
                        let q = x.checked_div(&y).expect("in-shore band");
                        assert_eq!(
                            (q.num().to_i128(), q.den().to_i128()),
                            reduced(a * d, b * c),
                            "div identity broke at {a}/{b} / {c}/{d}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn the_zero_divisor_refuses_everywhere() {
        assert_eq!(make(3, 4).checked_div(&Rational38::zero()), None);
        assert_eq!(make(3, 4).checked_div(&make(0, 9)), None);
    }

    #[test]
    fn the_cmp_orders_honestly() {
        for a in -30i128..=30 {
            for b in 1i128..=30 {
                for c in -30i128..=30 {
                    for d in 1i128..=30 {
                        let ord = make(a, b).checked_cmp(&make(c, d)).unwrap();
                        let want = (a * d).cmp(&(c * b));
                        assert_eq!(ord, want, "cmp broke at {a}/{b} vs {c}/{d}");
                    }
                }
            }
        }
    }

    /// The Hubble fraction, decimal 141/25, exactly — the promise's
    /// own receipt.
    #[test]
    fn the_hubble_fraction_is_exact() {
        let hubble = Rational38::from_i128s(141, 25).unwrap();
        assert_eq!((hubble.num().to_i128(), hubble.den().to_i128()), (141, 25));
        assert_eq!(
            hubble.num().as_digits().to_vec(),
            vec![-11, 4], // the residue walk: 27 reflects to −11 with the debt carried up; 4·38 − 11 = 141
        );
    }

    /// THE SHORE LAW: a beyond-shore composition refuses loudly. Each
    /// operand rides the integer shore fine, but the common
    /// denominator's product never lands — None, never a wrapped lie.
    #[test]
    fn beyond_shore_compositions_refuse() {
        // near-shore denominators, coprime, so the product is two
        // places past the shore: 2^62 * 2^62 = 2^124, in-shore;
        // 2^63 * 2^63 = 2^126 still in-shore; push harder:
        let big = 1i128 << 63;
        let x = make(1, big);
        let y = make(1, big);
        assert!(x.checked_mul(&y).is_some(), "2^126 product still fits");
        // the cross product of two 2^63 denominators is 2^126 — fits;
        // two 2^64s would be 2^128: from_i128s caps num/den at i128,
        // so build the refusal with direct products near the shore.
        let big2 = 1i128 << 64;
        let u = make(1, big2);
        let v = make(1, big2);
        // 2^64·2^64 = 2^128: the add's common denominator refuses
        assert_eq!(u.checked_add(&v), None, "2^128 common denominator refused");
        assert_eq!(u.checked_mul(&v), None, "2^128 product refused");
    }

    /// A beyond-shore denominator refuses at the sign read, not by a
    /// wrapped `to_i128`. The checked door is the only sign source.
    #[test]
    fn beyond_shore_denominators_refuse_at_the_sign_read() {
        let over = Balanced38::from_dense_digits(&[19; 25]);
        assert_eq!(Rational38::from_ints(Balanced38::from_i128(1), over), None);
    }

    /// Helper: an in-shore fraction from raw i128s.
    fn make(n: i128, d: i128) -> Rational38 {
        Rational38::from_i128s(n, d).expect("in-shore")
    }
}
