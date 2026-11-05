//! balanced38 — the balanced signed base-38 integer lane.
//!
//! A standalone exact-arithmetic lane: zero dependencies beyond
//! `smallvec`, so it can live anywhere.
//!
//! The design, in plain words: read the dense base-38 digits
//! SIGNED — d ≤ 19 is +d, d ≥ 20 is d−38, the gap digit is 0 — and the
//! set {−18..−1, 0, +1..+19} is a COMPLETE RESIDUE SYSTEM mod 38.
//! Therefore every integer, positive or negative, has exactly one form
//! here (the residue walk is forced at every place), zero is the empty
//! string, and no zero VALUE is ever stored as a digit except the gaps
//! the dense store already carries. The Void is the only zero.
//!
//! The arithmetic is the carry law at its simplest: digits within ±19
//! mean a column sum sits in [−37, +39] — bounded by construction — so
//! the rebalance is compare and ±38, no division, no mod when adding.
//! Negation is the digit-wise mirror with the debt walked up. The
//! checked doors refuse loudly (`None`); `to_i128` is the wrapping fast
//! door, and `checked_to_i128` is the honest one.
//!
//! Every operation's law is tested against the independent oracle and
//! the i128 shore edges (see the test module), and the same laws —
//! add, sub, mul, div, neg, canonical form — plus
//! the signed-i128 refusal contract are proven theorems in Lean 4
//! (`Balanced38.lean` + `Shore.lean`), core-only (`import Init`, no
//! Mathlib), 0 errors, 0 sorries. The proof is of the Lean model, not a
//! refinement proof of this Rust code; the crate is tested against both.
//! See `docs/THEOREM_LEDGER.md` and `docs/RIGHT_DOOR.md`.
//!
//! ## The membrane at a glance
//! - [`Balanced38`] — the signed store, little-endian, inline on the
//!   stack (every legal lane string fits `SmallVec<[i8; 26]>`).
//! - [`membrane_digit`] / [`dense_digit`] — the digit-level mirror,
//!   round-tripping exactly.
//! - [`Balanced38::from_i128`] / [`Balanced38::to_i128`] — the forced
//!   residue walk; `checked_to_i128` is the refusing fold, `to_i128`
//!   wraps beyond the shore.
//! - [`Balanced38::checked_to_i128`] — the honest shore door: strings
//!   beyond the i128 shore refuse, they never wrap.
//! - [`Balanced38::checked_add`], [`Balanced38::sub`],
//!   [`Balanced38::checked_mul`], [`Balanced38::checked_div_rem`] —
//!   the four laws, proved for the Lean model and tested here.
//! - [`Balanced38::try_from_dense_digits`] /
//!   [`Balanced38::from_dense_digits`] — read a dense store's digits
//!   signed; rejects bytes ≥ 38 and trims gaps.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod balanced;
pub mod rational;

pub use balanced::{dense_digit, membrane_digit, Balanced38};
pub use rational::{desk_form, Rational38};
