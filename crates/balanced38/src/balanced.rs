//! balanced — the signed reading of the dense base-38 store.
//!
//! The dense base-38 store refuses anything below the void; this lane
//! reads the dense digits SIGNED — d ≤ 19 is +d,
//! d ≥ 20 is d−38, the gap is 0 — and the set {−18..−1, 0, +1..+19}
//! is a COMPLETE RESIDUE SYSTEM mod 38. Therefore every integer,
//! positive or negative, has exactly one form here (the residue walk
//! is forced at every place), zero is the empty string, and no zero
//! VALUE is ever stored as a digit except the gaps the dense store
//! already carries. The Void is the only zero.
//!
//! The arithmetic is the carry law: digits within ±19 mean
//! a column sum sits in [−37, +39] — bounded by construction — so the
//! rebalance is compare and ±38, no division, no mod. Negation is the
//! digit-wise mirror; the reflection law (sub IS add-of-negation) is
//! proved for the Lean model and tested here.

/// The membrane's signed reading of a dense digit: 1..=19 above the
/// gate stay positive, 20..=37 reflect to −18..=−1, the gap is 0.
/// Panics on a byte outside 0..=37 — the dense alphabet is not a
/// wrapping input.
#[inline]
pub fn membrane_digit(dense: u8) -> i8 {
    assert!(dense < 38, "dense digit {dense} is outside 0..=37");
    if dense >= 20 {
        dense as i8 - 38
    } else {
        dense as i8
    }
}

/// The inverse map: a signed digit back to the dense alphabet
/// (0..=37). −18..=−1 reflect up to 20..=37; 0 and 1..=19 stand.
/// Panics outside the membrane [-18, 19].
#[inline]
pub fn dense_digit(signed: i8) -> u8 {
    assert!(
        (-18..=19).contains(&signed),
        "signed digit {signed} is outside the membrane [-18, 19]"
    );
    if signed < 0 {
        (signed + 38) as u8
    } else {
        signed as u8
    }
}

/// The reflected store: signed membrane digits, little-endian, the
/// Void (zero) the empty string. Every integer has exactly one form;
/// the string never ends on a gap. THE INLINE STORE: the digits ride
/// `SmallVec<[i8; 26]>` — every legal lane string fits the stack
/// (i128 values ≤ 25 places, add/negate results ≤ 26, mul/div
/// results shore-checked ≤ 25), and every construction STARTS EMPTY
/// (reserving capacity up front would only force the spill).
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct Balanced38 {
    digits: smallvec::SmallVec<[i8; 26]>,
}

impl Balanced38 {
    /// The Void — the additive identity, the empty string.
    pub fn zero() -> Self {
        Self {
            digits: smallvec::SmallVec::new(),
        }
    }

    /// The Void test: true only for the empty string (the canonical zero).
    pub fn is_zero(&self) -> bool {
        self.digits.is_empty()
    }

    /// The residue walk, chunked (13 Sep): every integer lands here
    /// exactly once — but instead of one i128 software division per
    /// place, the walk peels the low 12 places in chunks of 38^12
    /// (< 2^64): one u128÷64 constant division per chunk, then twelve
    /// cheap u64 ÷38 decodes. Digit-for-digit the same canonical
    /// string as the per-place walk (unique representation — swept
    /// and asserted).
    /// Negative values: build the mirror, then apply the documented
    /// `negate` debt walk (the set is asymmetric: +19 has no −19).
    pub fn from_i128(v: i128) -> Self {
        const CHUNK: u128 = 38u128.pow(12); // 9,065,737,908,494,995,456 < 2^64
        const N: usize = 12;
        let mut digits = smallvec::SmallVec::new();
        let mut n = v.unsigned_abs();
        let mut buf = [0i8; N];
        while n >= CHUNK {
            let r = (n % CHUNK) as u64;
            n /= CHUNK;
            let mut c = r;
            for b in buf.iter_mut() {
                let m = (c % 38) as u8;
                let d = if m <= 19 { m as i8 } else { m as i8 - 38 };
                *b = d;
                // (c − d) / 38: a negative digit carries a +1 into
                // the next place (the walk's exact step, not c / 38).
                c = c / 38 + u64::from(m > 19);
            }
            // The low-12 string's integer value can land one CHUNK
            // below zero (the set is asymmetric: +19 has no −19) —
            // fold the digits and pay that debt back into the high part.
            let mut s = 0i64;
            for &b in buf.iter().rev() {
                s = s * 38 + i64::from(b);
            }
            n += u128::from(s < 0);
            digits.extend_from_slice(&buf);
        }
        let mut c = n as u64; // < CHUNK: the top group, unpadded
        while c > 0 {
            let m = (c % 38) as u8;
            let d = if m <= 19 { m as i8 } else { m as i8 - 38 };
            digits.push(d);
            c = c / 38 + u64::from(m > 19);
        }
        let this = Self { digits };
        if v < 0 {
            this.negate()
        } else {
            this
        }
    }

    /// Read back by Horner, signed digits included.
    ///
    /// THE FAST FOLD, with its edge named: a string beyond the i128
    /// shore wraps here — in both debug and release — by explicit
    /// `wrapping_*` arithmetic. The honest door is
    /// [`Self::checked_to_i128`].
    pub fn to_i128(&self) -> i128 {
        let mut acc: i128 = 0;
        for &d in self.digits.iter().rev() {
            acc = acc.wrapping_mul(38).wrapping_add(i128::from(d));
        }
        acc
    }

    /// THE HONEST SHORE DOOR: the fold the lane can refuse. Every
    /// string of ≤ 24 places folds inside i128 by the proven bound
    /// (largest 19·(38²⁴−1)/37 ≈ 4.2e37 < 2¹²⁷−1) — the fast path,
    /// free. From 25 places up the fold is checked, and a string
    /// beyond the shore refuses (None) — never a wrapped lie. (The
    /// gap this closes: `checked_div_rem` folds its operands; a
    /// beyond-shore string would otherwise answer with a wrapped
    /// value, silently.)
    ///
    /// The digit guard is belt-and-braces: the public constructors
    /// keep the invariant, but an out-of-range digit refuses here
    /// rather than folding a lie.
    pub fn checked_to_i128(&self) -> Option<i128> {
        if self.digits.iter().any(|&d| !(-18..=19).contains(&d)) {
            return None;
        }
        if self.digits.len() <= 24 {
            return Some(self.to_i128()); // the proven shore
        }
        self.digits.iter().rev().try_fold(0i128, |acc, &d| {
            acc.checked_mul(38)?.checked_add(i128::from(d))
        })
    }

    /// THE REFLECTION: digit-wise negation with the mirror's debt
    /// walked up. The membrane set {−18..−1, 0, 1..19} is closed
    /// under negation EXCEPT for +19 (its mirror −19 is one past
    /// the gate) — so the mirror rebalances: −19 becomes 19 with
    /// the debt −38 carried to the next place, where it is ADDED
    /// (the debt is 38 removed from up there). Compare and ±38 —
    /// the law's own shape.
    pub fn negate(&self) -> Self {
        let mut out = smallvec::SmallVec::new();
        let mut carry = 0i8;
        for &d in &self.digits {
            let t = -d + carry; // the mirror, plus the debt from below
            let (digit, next) = if t < -18 {
                (t + 38, -1)
            } else if t > 19 {
                (t - 38, 1)
            } else {
                (t, 0)
            };
            out.push(digit);
            carry = next;
        }
        while carry != 0 {
            let t = carry;
            let (digit, next) = if t < -18 {
                (t + 38, -1)
            } else if t > 19 {
                (t - 38, 1)
            } else {
                (t, 0)
            };
            out.push(digit);
            carry = next;
        }
        while out.last() == Some(&0) {
            out.pop();
        }
        Self { digits: out }
    }

    /// THE SCRIBE'S SIGNED ADD: the Avizienis rebalance on membrane
    /// digits — t = a + b + carry sits in [−37, +39], bounded by
    /// construction, so one compare and ±38 settle every column.
    /// No division, no mod. The result never ends on a gap; the
    /// Void result is the empty string.
    pub fn checked_add(&self, other: &Self) -> Self {
        let len = self.digits.len().max(other.digits.len());
        let mut out = smallvec::SmallVec::new(); // starts inline
        let mut carry = 0i8;
        for i in 0..len {
            let t = i32::from(carry)
                + if i < self.digits.len() {
                    i32::from(self.digits[i])
                } else {
                    0
                }
                + if i < other.digits.len() {
                    i32::from(other.digits[i])
                } else {
                    0
                };
            // t ∈ [−37, 39]: one compare-and-add-38 settles the column
            let (digit, next) = if t > 19 {
                (t - 38, 1)
            } else if t < -18 {
                (t + 38, -1)
            } else {
                (t, 0)
            };
            debug_assert!((-18..=19).contains(&digit), "column out of the membrane");
            out.push(digit as i8);
            carry = next;
        }
        while carry != 0 {
            let (digit, next) = if carry > 19 {
                (carry - 38, 1)
            } else if carry < -18 {
                (carry + 38, -1)
            } else {
                (carry, 0)
            };
            out.push(digit);
            carry = next;
        }
        while out.last() == Some(&0) {
            out.pop();
        }
        Self { digits: out }
    }

    /// THE REFLECTION, AS AN OPERATION: subtraction IS addition of
    /// the negation — the law, wired as the definition. Never
    /// refuses: the reflected lane holds both shores.
    pub fn sub(&self, other: &Self) -> Self {
        self.checked_add(&other.negate())
    }

    /// THE SIGNED GRID: schoolbook mul on membrane digits — the
    /// signed column sums are SMALLER, ±19, so the accumulation
    /// bound tightens. The dense grid's cell takes a·b ≤ 37·37 =
    /// 1,369 per contribution (26 places → 35,594 before carries);
    /// the membrane's cell takes ≤ 19·19 = 361 (26 places → 9,386)
    /// — and the coefficients fit i32, half the traffic of the dense
    /// u64 row. The carry pass is the rebalance signed: digit =
    /// t mod 38 folded into [−18, +19], carry = the exact
    /// (t − digit)/38 — one division per cell, the same shape the
    /// dense pass pays. Refuses at the i128 shore (a product beyond
    /// it), and refuses an operand longer than 25 places before the
    /// grid — 26 places already sit past 2¹²⁷. None, loudly, never a
    /// wrapped lie.
    pub fn checked_mul(&self, other: &Self) -> Option<Self> {
        if self.is_zero() || other.is_zero() {
            return Some(Self::zero());
        }
        if self.digits.iter().any(|&d| !(-18..=19).contains(&d))
            || other.digits.iter().any(|&d| !(-18..=19).contains(&d))
        {
            return None;
        }
        let la = self.digits.len();
        let lb = other.digits.len();
        if la > 25 || lb > 25 {
            return None;
        }
        let mut buf: smallvec::SmallVec<[i32; 28]> = smallvec::SmallVec::new();
        buf.resize(la + lb, 0);
        for (i, &a) in self.digits.iter().enumerate() {
            if a == 0 {
                continue; // the gap contributes nothing
            }
            let av = i32::from(a);
            // the row window, tightened: cells bounded by 19·|av| per
            // contribution — proven once per row, the walk unchecked
            let row = &mut buf[i..i + lb];
            for (j, &o) in other.digits.iter().enumerate() {
                row[j] += av * i32::from(o);
            }
        }
        let mut digits: smallvec::SmallVec<[i8; 26]> = smallvec::SmallVec::new();
        let mut carry: i32 = 0;
        for &c in &buf {
            let t = c + carry;
            let r = t.rem_euclid(38); // 0..=37, the complete system
            let digit = if r > 19 { r - 38 } else { r };
            debug_assert!(
                (-18..=19).contains(&digit),
                "mul column out of the membrane"
            );
            digits.push(digit as i8);
            carry = (t - digit) / 38;
        }
        while carry != 0 {
            let r = carry.rem_euclid(38);
            let digit = if r > 19 { r - 38 } else { r };
            digits.push(digit as i8);
            carry = (carry - digit) / 38;
        }
        while digits.last() == Some(&0) {
            digits.pop(); // never end on a gap
        }
        // THE PROVEN SHORE (the row window's shore twin): every
        // balanced string of ≤ 24 places folds inside i128 — its
        // largest value, 19·(38²⁴−1)/37 ≈ 4.2e37, sits under
        // 2^127−1 ≈ 1.7e38. Only from 25 places up can the fold leave
        // the shore, so only those pay the checked walk — and refuse
        // loudly (None), never a wrapped lie.
        if digits.len() > 24 {
            let _ = digits.iter().rev().try_fold(0i128, |acc, &d| {
                acc.checked_mul(38)?.checked_add(i128::from(d))
            })?;
        }
        Some(Self { digits })
    }

    /// SCHOOLBOOK POWER: iterated multiplication via the lane's own
    /// `checked_mul`, refused beyond the i128 shore — `None`, never a
    /// panic on the long walk.
    pub fn checked_pow(&self, exp: u32) -> Option<Self> {
        if self.is_zero() {
            return Some(Self::zero());
        }
        if exp == 0 {
            return Some(Self::from_i128(1));
        }
        let mut result = self.clone();
        for _ in 1..exp {
            result = result.checked_mul(self)?;
        }
        Some(result)
    }

    /// THE SHORE ROAD: division on the balanced lane — folded to the
    /// i128 shore, one hardware division, walked back by the residue.
    /// The digit road (signed long division over membrane strings) is
    /// named for the day the lane grows past its shore: the estimate
    /// machinery assumes nonnegative digits and cannot read a signed
    /// string without folding it anyway. THE EUCLIDEAN REMAINDER: r
    /// sits in 0..|b| — the debt never signed — and the law
    /// a = q·b + r is carried through the lane's OWN mul and add,
    /// tested as a theorem. Refusals, both loud: the Void divisor
    /// (None — the Void cannot bind, divide, or amplify) and the one
    /// corner the shore holds (i128::MIN ÷ −1, whose quotient is
    /// 2^127 — one past the last honest digit).
    pub fn checked_div_rem(&self, other: &Self) -> Option<(Self, Self)> {
        if other.is_zero() {
            return None; // the Void is not an operand
        }
        // the honest shore door: a beyond-shore string is refused,
        // not folded into a wrapped lie
        let a = self.checked_to_i128()?;
        let b = other.checked_to_i128()?;
        // the truncated core, adjusted to Euclidean: r ≥ 0 always
        let mut q = a.checked_div(b)?;
        let mut r = a.checked_rem(b)?;
        if r < 0 {
            if b > 0 {
                q = q.checked_sub(1)?;
                r = r.checked_add(b)?;
            } else {
                q = q.checked_add(1)?;
                r = r.checked_sub(b)?;
            }
        }
        debug_assert!(
            r >= 0 && r.unsigned_abs() < b.unsigned_abs(),
            "remainder out of the Euclidean band"
        );
        Some((Self::from_i128(q), Self::from_i128(r)))
    }

    /// The quotient alone — the same road, the remainder dropped.
    pub fn checked_div(&self, other: &Self) -> Option<Self> {
        self.checked_div_rem(other).map(|(q, _)| q)
    }

    /// The remainder alone — the same road, the quotient dropped.
    pub fn checked_rem(&self, other: &Self) -> Option<Self> {
        self.checked_div_rem(other).map(|(_, r)| r)
    }

    /// THE ALPHABET'S REFLECTION: dense digits (LSB-first, the dense
    /// store's own order) read signed, place for place. NOT
    /// value-preserving for below-gate digits (a dense 20 reads −18
    /// — the instrument caught that claim within the hour): the
    /// canonical signed form of a VALUE comes from [`Self::from_i128`]'s
    /// residue walk. This map is the membrane's own mirror at the
    /// digit level, and it round-trips:
    /// `dense_digit(membrane_digit(d)) == d`.
    ///
    /// The checked door rejects a byte outside `0..=37` and trims
    /// trailing gaps, so the result is canonical — equal values have
    /// equal digits, and `Ord`/`Eq` agree. Use
    /// [`Self::try_from_dense_digits`] when the input is untrusted.
    pub fn try_from_dense_digits(dense: &[u8]) -> Option<Self> {
        if dense.iter().any(|&d| d >= 38) {
            return None;
        }
        let mut digits: smallvec::SmallVec<[i8; 26]> =
            dense.iter().map(|&d| membrane_digit(d)).collect();
        while digits.last() == Some(&0) {
            digits.pop();
        }
        Some(Self { digits })
    }

    /// Read a dense store's digits signed, place for place. Panics on
    /// a byte outside `0..=37`; use [`Self::try_from_dense_digits`]
    /// for the refusing door.
    pub fn from_dense_digits(dense: &[u8]) -> Self {
        Self::try_from_dense_digits(dense).expect("dense digits must lie in 0..=37")
    }

    /// The digit slice, for inspection and tests.
    pub fn as_digits(&self) -> &[i8] {
        &self.digits
    }
}

impl PartialOrd for Balanced38 {
    /// The lane's own order — computed by the PROVEN subtraction: the sign
    /// of `self − other` is the answer, exact at any legal width (the
    /// stack-fit theorem keeps the difference inside the store). No fold
    /// to `i128` — the shore does not bound this comparison.
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Balanced38 {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        let d = self.sub(other);
        match d.digits.last() {
            // the empty string: the Void — the values agree
            None => core::cmp::Ordering::Equal,
            Some(&top) if top > 0 => core::cmp::Ordering::Greater,
            Some(_) => core::cmp::Ordering::Less,
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn the_order_is_the_values_order() {
        for a in -400i128..=400 {
            for b in -400i128..=400 {
                let (x, y) = (Balanced38::from_i128(a), Balanced38::from_i128(b));
                assert_eq!(x.cmp(&y), a.cmp(&b), "value order at ({a}, {b})");
                assert_eq!(x < y, a < b);
            }
        }
        // beyond the fold's comfort zone: 25-place giants still order exactly
        let big = Balanced38 {
            digits: std::iter::repeat(19i8)
                .take(24)
                .chain(std::iter::once(1i8))
                .collect::<smallvec::SmallVec<[i8; 26]>>(),
        };
        let neg = big.negate();
        assert!(neg < Balanced38::zero());
        assert!(big > Balanced38::zero());
        assert!(neg < big);
        assert_eq!(big.cmp(&big.clone()), core::cmp::Ordering::Equal);
    }
    use super::*;

    /// THE REFLECTION LAW: sub IS add-of-negation — exhaustively,
    /// both shores, and the dense store's refusal (BelowTheVoid) is
    /// exactly the reflected lane's answer flowing back.
    #[test]
    fn sub_is_add_of_the_negation() {
        for a in -3000i128..=3000 {
            for b in -3000i128..=3000 {
                let (x, y) = (Balanced38::from_i128(a), Balanced38::from_i128(b));
                let diff = x.sub(&y).to_i128();
                assert_eq!(diff, a - b, "the reflection broke at {a} − {b}");
            }
        }
    }

    /// THE DOUBLE REFLECTION: negate∘negate is the identity — the
    /// store knows itself by coming back. Exhaustive.
    #[test]
    fn the_double_reflection_is_the_identity() {
        for a in -5000i128..=5000 {
            let x = Balanced38::from_i128(a);
            assert_eq!(x.negate().negate(), x, "the mirror lied at {a}");
            assert_eq!(x.negate().to_i128(), -a);
        }
    }

    /// THE UNIQUE FORM: the residue walk is forced at every place,
    /// so distinct integers never share a string — and the string
    /// never ends on a gap.
    #[test]
    fn every_integer_has_exactly_one_form() {
        let mut seen = std::collections::HashMap::new();
        for a in -20000i128..=20000 {
            let x = Balanced38::from_i128(a);
            assert_eq!(x.to_i128(), a, "fold-back broke at {a}");
            if a == 0 {
                assert!(x.is_zero(), "the Void is the empty string");
            } else {
                assert_ne!(x.as_digits().last(), Some(&0), "trailing gap at {a}");
            }
            assert_eq!(
                seen.insert(x.as_digits().to_vec(), a),
                None,
                "two values, one form at {a}"
            );
        }
    }

    /// CHUNKED DECODE SAFETY NET: the new chunked walk (13 Sep) is
    /// digit-for-digit identical to the per-place walk across a 500k
    /// sign-flipped LCG sweep covering the i128 shore, exact chunk
    /// boundaries, and the Void. Value-correctness is also asserted
    /// by the above tests (round-trip through to_i128); this test
    /// guards the exact form.
    #[test]
    fn chunked_from_i128_matches_legacy_digit_for_digit() {
        let legacy = |mut v: i128| {
            let mut digits = Vec::new();
            while v != 0 {
                let r = v.rem_euclid(38);
                let d = if r <= 19 { r as i8 } else { r as i8 - 38 };
                digits.push(d);
                v = (v - i128::from(d)) / 38;
            }
            digits
        };
        let mut s = 0x9E37_79B9_7F4A_7C15u64;
        for i in 0u64..500_000 {
            s = s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let v = match i {
                0 => i128::MAX,
                1 => i128::MIN,
                2 => -1,
                3 => 38i128 * 38 * 38,      // exact chunk boundary
                4 => -(38i128).pow(12) * 7, // multiple of CHUNK, negative
                _ => (s as i128) ^ if i % 5 == 0 { -1i128 } else { 0 },
            };
            assert_eq!(
                Balanced38::from_i128(v).as_digits().to_vec(),
                legacy(v),
                "chunk walk diverged at v = {v}"
            );
        }
    }

    /// THE MEMBRANE'S ALPHABET MIRROR: the digit map round-trips
    /// exactly (that is the reflection at the digit level), and for
    /// above-gate-only strings the signed view IS the value — the
    /// instrument's lesson: below-gate digits re-read as debts, so
    /// the canonical signed form goes through the residue walk.
    #[test]
    fn the_alphabet_mirror_round_trips() {
        // the digit-level law, every dense digit both ways
        for d in 0u8..=37 {
            assert_eq!(dense_digit(membrane_digit(d)), d, "mirror broke at {d}");
        }
        // the dense store's own digit walk, built here by the residue
        let dense_walk = |mut n: u128| {
            let mut out = Vec::new();
            while n > 0 {
                out.push((n % 38) as u8);
                n /= 38;
            }
            out
        };
        // above-gate-only strings: the signed view IS the value
        for a in 0u128..=50_000 {
            let digits = dense_walk(a);
            if digits.iter().all(|&d| d <= 19) {
                let v = Balanced38::from_dense_digits(&digits);
                assert_eq!(v.to_i128() as u128, a, "above-gate view broke at {a}");
            }
        }
        // and the canonical form: 20 lands below the gate as [−18]
        // with the debt walked up to [.., 1] — −18 + 38 = 20
        assert_eq!(Balanced38::from_i128(20).to_i128(), 20);
        assert_eq!(
            Balanced38::from_i128(20).as_digits(),
            &[-18, 1],
            "20's signed form carries the membrane's debt honestly"
        );
    }

    /// THE OPPOSING-PAIR RECEIPT: 1 + (−1) resolves to the Void
    /// through the rebalance. And the add law, exhaustive against
    /// the oracle over the tested ranges.
    #[test]
    fn the_opposing_pair_resolves_to_the_void() {
        // 1 + (−1): the opposing pair, resolved
        let one = Balanced38::from_i128(1);
        let minus_one = one.negate();
        assert!(one.checked_add(&minus_one).is_zero());
        // the exhaustive add law, five thousand either shore
        for a in -2500i128..=2500 {
            for b in -2500i128..=2500 {
                let (x, y) = (Balanced38::from_i128(a), Balanced38::from_i128(b));
                assert_eq!(x.checked_add(&y).to_i128(), a + b, "add broke at {a}+{b}");
            }
        }
    }

    /// THE SIGNED GRID: the product law, exhaustive — every pair of
    /// membrane values folds back to the exact product, the fold
    /// landing inside the i128 shore.
    #[test]
    fn the_signed_grid_folds_to_the_product() {
        for a in -1500i128..=1500 {
            for b in -1500i128..=1500 {
                let (x, y) = (Balanced38::from_i128(a), Balanced38::from_i128(b));
                let p = x.checked_mul(&y).expect("within the i128 shore");
                assert_eq!(p.to_i128(), a * b, "the grid broke at {a}·{b}");
            }
        }
    }

    /// THE REFLECTION HOLDS IN MULTIPLICATION: (−a)·b = −(a·b) = a·(−b),
    /// as strings — the mirror trades sides and the product follows.
    /// Exhaustive, both mirrors.
    #[test]
    fn the_reflection_holds_in_multiplication() {
        for a in -400i128..=400 {
            for b in -400i128..=400 {
                let (x, y) = (Balanced38::from_i128(a), Balanced38::from_i128(b));
                let direct = x.checked_mul(&y).unwrap();
                let through_mirror = x.negate().checked_mul(&y).unwrap();
                let other_mirror = y.negate().checked_mul(&x).unwrap();
                assert_eq!(
                    through_mirror.to_i128(),
                    -direct.to_i128(),
                    "the mul mirror lied at {a}·{b}"
                );
                assert_eq!(
                    other_mirror, through_mirror,
                    "the mirrors disagree at {a}·{b}"
                );
            }
        }
    }

    /// THE GATE DIGITS MULTIPLY HONESTLY: 19·19 = 361 carries the
    /// 9 up (the gate's own pair); 20·20 = 400 lands as [−18, 11] —
    /// the debt walk, mul's own; 38·38 = 1444 keeps its interior
    /// gaps; the Void binds nothing; 1 is the mul identity.
    #[test]
    fn the_gate_digits_multiply_honestly() {
        let n19 = Balanced38::from_i128(19);
        let p = n19.checked_mul(&n19).unwrap();
        assert_eq!(p.to_i128(), 361);
        assert_eq!(p.as_digits(), &[19, 9], "19·19 carries the 9 up");
        let n20 = Balanced38::from_i128(20);
        let p2 = n20.checked_mul(&n20).unwrap();
        assert_eq!(p2.to_i128(), 400);
        assert_eq!(
            p2.as_digits(),
            &[-18, 11],
            "20·20 carries the debt honestly"
        );
        let n38 = Balanced38::from_i128(38);
        let p3 = n38.checked_mul(&n38).unwrap();
        assert_eq!(p3.to_i128(), 1444);
        assert_eq!(
            p3.as_digits(),
            &[0, 0, 1],
            "the gaps ride inside the product"
        );
        assert!(Balanced38::zero().checked_mul(&n19).unwrap().is_zero());
        assert_eq!(
            Balanced38::from_i128(1)
                .checked_mul(&n19)
                .unwrap()
                .as_digits(),
            &[19],
            "1 is the mul identity"
        );
    }

    /// THE WIDE PRODUCT LAW: 20k signed pairs across the i128's
    /// middle span (products ≤ 2^124, inside the shore) — the
    /// exhaustive grid's reach extended by the deterministic walk.
    #[test]
    fn the_wide_product_law() {
        let mut seed = 0x1444u64;
        let mut next = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for _ in 0..20_000 {
            let mut a = (next() & ((1u64 << 62) - 1)) as i128;
            if next() & 1 == 1 {
                a = -a;
            }
            let mut b = (next() & ((1u64 << 62) - 1)) as i128;
            if next() & 1 == 1 {
                b = -b;
            }
            let (x, y) = (Balanced38::from_i128(a), Balanced38::from_i128(b));
            let p = x.checked_mul(&y).expect("within the i128 shore");
            assert_eq!(p.to_i128(), a * b, "the wide grid broke at {a}·{b}");
        }
    }

    /// THE SHORE REFUSES THE UNNAMEABLE PRODUCT: 2^64 · 2^64 = 2^128
    /// is one past the i128's last honest digit — None, loudly. And
    /// 2^63 · 2^63 = 2^126 lands exactly.
    #[test]
    fn the_shore_refuses_the_unnameable_product() {
        let big = Balanced38::from_i128(1i128 << 64);
        assert_eq!(big.checked_mul(&big), None, "2^128 must be refused");
        let fits = Balanced38::from_i128(1i128 << 63);
        assert_eq!(fits.checked_mul(&fits).unwrap().to_i128(), 1i128 << 126);
    }

    /// THE IDENTITY THROUGH THE LANE: a = q·b + r, with the product
    /// and the sum carried by the lane's OWN mul and add — the whole
    /// lane cooperating, not a shore shortcut. Exhaustive over the
    /// Euclidean band.
    #[test]
    fn the_identity_carries_through_the_lane() {
        for a in -1500i128..=1500 {
            for b in -1500i128..=1500 {
                if b == 0 {
                    continue; // the Void is not an operand
                }
                let (x, y) = (Balanced38::from_i128(a), Balanced38::from_i128(b));
                let (q, r) = x.checked_div_rem(&y).expect("within the shore");
                // the Euclidean band: r ≥ 0 and |r| < |b|, always
                let (rv, bv) = (r.to_i128(), b);
                assert!(rv >= 0 && rv < bv.abs(), "band broke at {a}÷{b}: r = {rv}");
                let back = q.checked_mul(&y).unwrap().checked_add(&r).to_i128();
                assert_eq!(back, a, "the identity broke at {a}÷{b}");
                // and the oracle: the same Euclidean answer on the shore
                let (eq, er) = {
                    let (mut q, mut r) = (a / b, a % b);
                    if r < 0 {
                        if b > 0 {
                            q -= 1;
                            r += b;
                        } else {
                            q += 1;
                            r -= b;
                        }
                    }
                    (q, r)
                };
                assert_eq!(q.to_i128(), eq, "quotient broke at {a}÷{b}");
                assert_eq!(r.to_i128(), er, "remainder broke at {a}÷{b}");
            }
        }
    }

    /// THE DEBT SHAPES: −7 ÷ 2 = −4 r 1 — the signed quotient with
    /// the debt carried positive, Euclid's own shape; −7 ÷ −2 = 4 r 1;
    /// the truncated world's r = −1 never lands here. And the shores:
    /// the Void divisor refused, i128::MIN ÷ −1 refused (its quotient
    /// is 2^127), 1 ÷ 38 = 0 r 1 (the quotient IS the empty string).
    #[test]
    fn the_debt_shapes_and_the_refusals() {
        let minus7 = Balanced38::from_i128(-7);
        let two = Balanced38::from_i128(2);
        let (q, r) = minus7.checked_div_rem(&two).unwrap();
        assert_eq!(q.to_i128(), -4, "the debt walks the quotient down");
        assert_eq!(r.to_i128(), 1, "the remainder never signs");
        let (q2, r2) = minus7.checked_div_rem(&two.negate()).unwrap();
        assert_eq!(q2.to_i128(), 4, "the mirror divisor flips the quotient");
        assert_eq!(r2.to_i128(), 1, "and the debt still carries positive");
        let minus_min = Balanced38::from_i128(i128::MIN);
        let minus_one = Balanced38::from_i128(-1);
        assert_eq!(minus_min.checked_div_rem(&minus_one), None, "2^127 refused");
        assert_eq!(
            two.checked_div_rem(&Balanced38::zero()),
            None,
            "the Void refused"
        );
        let (q3, r3) = Balanced38::from_i128(1)
            .checked_div_rem(&Balanced38::from_i128(38))
            .unwrap();
        assert!(q3.is_zero(), "the too-small quotient is the empty string");
        assert_eq!(r3.to_i128(), 1);
    }

    /// THE WIDE SHORE LAW: 20k signed pairs across the i128's middle
    /// span — the identity through the lane, the band held.
    #[test]
    fn the_wide_shore_law() {
        let mut seed = 0x4u64;
        let mut next = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for _ in 0..20_000 {
            let mut a = (next() & ((1u64 << 62) - 1)) as i128;
            if next() & 1 == 1 {
                a = -a;
            }
            let mut b = (next() & ((1u64 << 62) - 1)) as i128;
            if next() & 1 == 1 {
                b = -b;
            }
            if b == 0 {
                continue;
            }
            let (x, y) = (Balanced38::from_i128(a), Balanced38::from_i128(b));
            let (q, r) = x.checked_div_rem(&y).expect("within the shore");
            assert!(
                r.to_i128() >= 0 && r.to_i128() < b.abs(),
                "band broke at {a}÷{b}"
            );
            let back = q.checked_mul(&y).unwrap().checked_add(&r).to_i128();
            assert_eq!(back, a, "the wide identity broke at {a}÷{b}");
        }
    }

    /// THE HONEST SHORE DOOR, at its edges: the 25-place string that
    /// FITS (top digit 1, the minimum-magnitude form) folds Some;
    /// the 25-place string that DOESN'T (top digit 19) refuses None;
    /// a beyond-shore 27-place string refuses None — and div_rem
    /// refuses such operands loudly instead of folding a wrapped lie.
    #[test]
    fn the_honest_shore_door() {
        use smallvec::SmallVec;
        // the 25-place string that fits: places 0..23 = 19, the top
        // place 24 = 1 — the minimum-magnitude 25-place form
        let fits = Balanced38 {
            digits: std::iter::repeat_n(19i8, 24)
                .chain(std::iter::once(1i8))
                .collect::<SmallVec<[i8; 26]>>(),
        };
        assert_eq!(fits.as_digits().len(), 25);
        let v = fits.checked_to_i128().expect("the minimum 25-place fits");
        // fold back by Horner — the value itself, in-shore
        let hand: i128 = fits
            .as_digits()
            .iter()
            .rev()
            .fold(0i128, |acc, &d| acc * 38 + i128::from(d));
        assert_eq!(v, hand, "the door folds exactly");
        assert!(v > 0 && v < i128::MAX, "in-shore, as proven");
        // the 25-place string that does NOT fit: every digit 19
        let over = Balanced38 {
            digits: std::iter::repeat_n(19i8, 25).collect::<SmallVec<[i8; 26]>>(),
        };
        assert_eq!(over.checked_to_i128(), None, "beyond the shore refused");
        // a beyond-shore 27-place string: all −1
        let beyond = Balanced38 {
            digits: std::iter::repeat_n(-1i8, 27).collect::<SmallVec<[i8; 26]>>(),
        };
        assert_eq!(beyond.checked_to_i128(), None, "the wrapped lie refused");
        // and div_rem refuses the beyond-shore OPERAND loudly
        let in_shore = Balanced38::from_i128(12345);
        assert_eq!(
            in_shore.checked_div_rem(&beyond),
            None,
            "the wrap lie is closed"
        );
        assert_eq!(beyond.checked_div_rem(&in_shore), None, "both directions");
    }

    /// THE MIN DIVISOR: i128::MIN is a valid in-shore value, not a
    /// panic. The debug band check uses unsigned_abs, so the Euclidean
    /// identity holds at the edge.
    #[test]
    fn the_min_divisor_is_not_a_panic() {
        let min = Balanced38::from_i128(i128::MIN);
        let one = Balanced38::from_i128(1);
        let neg_one = Balanced38::from_i128(-1);
        let (q, r) = one.checked_div_rem(&min).expect("1 / MIN is in shore");
        assert_eq!((q.to_i128(), r.to_i128()), (0, 1));
        let (q, r) = min.checked_div_rem(&min).expect("MIN / MIN is in shore");
        assert_eq!((q.to_i128(), r.to_i128()), (1, 0));
        let (q, r) = neg_one.checked_div_rem(&min).expect("-1 / MIN is in shore");
        assert_eq!((q.to_i128(), r.to_i128()), (1, i128::MAX));
        assert_eq!(min.checked_div_rem(&neg_one), None, "MIN / -1 refused");
    }

    /// THE POWER DOOR: checked_pow refuses with None, never panics.
    #[test]
    fn checked_pow_refuses_instead_of_panicking() {
        let two = Balanced38::from_i128(2);
        assert_eq!(two.checked_pow(126).unwrap().to_i128(), 1i128 << 126);
        assert_eq!(two.checked_pow(127), None, "2^127 is past the shore");
        assert_eq!(two.checked_pow(200), None, "no panic on the long walk");
    }

    /// THE DENSE DOOR: bytes outside 0..=37 are refused; trailing gaps
    /// are trimmed, so the dense view and the canonical store agree.
    #[test]
    fn the_dense_door_validates_and_canonicalises() {
        assert!(Balanced38::from_dense_digits(&[0]).is_zero());
        assert_eq!(
            Balanced38::from_dense_digits(&[1, 0]),
            Balanced38::from_i128(1)
        );
        assert_eq!(Balanced38::from_dense_digits(&[20]).to_i128(), -18);
        assert_eq!(Balanced38::try_from_dense_digits(&[38]), None);
        assert_eq!(Balanced38::try_from_dense_digits(&[255]), None);
        let zero = Balanced38::from_dense_digits(&[0]);
        assert_eq!(zero, Balanced38::zero());
        assert_eq!(zero.cmp(&Balanced38::zero()), core::cmp::Ordering::Equal);
    }

    /// THE WRAP IS NAMED: to_i128 wraps beyond the shore in both debug
    /// and release; the checked door is the one that refuses.
    #[test]
    fn to_i128_wraps_beyond_the_shore() {
        use smallvec::SmallVec;
        let over = Balanced38 {
            digits: std::iter::repeat_n(19i8, 25).collect::<SmallVec<[i8; 26]>>(),
        };
        let mut expected: i128 = 0;
        for &d in over.as_digits().iter().rev() {
            expected = expected.wrapping_mul(38).wrapping_add(i128::from(d));
        }
        assert_eq!(over.to_i128(), expected);
        assert_eq!(over.checked_to_i128(), None);
    }

    /// THE INVALID DIGIT: the checked doors refuse an out-of-range
    /// digit instead of folding a lie; the public dense door validates.
    #[test]
    fn invalid_digits_refuse_the_checked_doors() {
        use smallvec::SmallVec;
        let bad = Balanced38 {
            digits: SmallVec::from_slice(&[20i8]),
        };
        assert_eq!(bad.checked_to_i128(), None);
        assert_eq!(bad.checked_mul(&Balanced38::from_i128(1)), None);
    }

    /// THE HUGE OPERAND: a string beyond the 25-place shore is refused
    /// before the grid can overflow; the checked door is loud.
    #[test]
    fn huge_operands_refuse_before_the_grid() {
        let huge = Balanced38::from_dense_digits(&[19; 40]);
        assert_eq!(huge.checked_mul(&Balanced38::from_i128(1)), None);
    }
}
