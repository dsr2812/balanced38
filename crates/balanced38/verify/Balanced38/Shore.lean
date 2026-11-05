import Balanced38.Balanced38

set_option maxRecDepth 10000

/-!
# The i128 shore contract

`Balanced38.lean` is an unbounded `Int` model: its `checked_to_i128`
and `checked_mul` are total. This module adds the **bounded contract**
the Rust crate implements at runtime:

* `inI128 z` — the signed i128 range, including `i128::MIN`.
* `checkedToI128 x` — `some v` exactly when `v = to_i128 x` is in range.
* `checkedMul x y` — zero is absorbing (as in the Rust lane); otherwise
  both operands and the product must be in the signed i128 shore.
* `checkedDivRem x y` — refuses the zero divisor, the `MIN / -1`
  corner, and any out-of-shore operand or result.

This proves the **contract**, not the Rust algorithm. The Rust code is
tested; this is the theorem the README can cite.
-/

namespace Shore

/-- The signed i128 range, including `i128::MIN`. -/
def i128Min : Int := -((2 : Int) ^ 127)
def i128Max : Int := ((2 : Int) ^ 127) - 1
def inI128 (z : Int) : Prop := i128Min ≤ z ∧ z ≤ i128Max

instance : DecidablePred inI128 := by
  intro z
  unfold inI128
  infer_instance

/-- The refusing fold: `some v` exactly when `v = to_i128 x` is in range. -/
def checkedToI128 (x : Balanced38) : Option Int :=
  if inI128 (to_i128 x) then some (to_i128 x) else none

theorem checkedToI128_eq_some_iff (x : Balanced38) :
    (checkedToI128 x = some (to_i128 x)) ↔ inI128 (to_i128 x) := by
  unfold checkedToI128
  by_cases h : inI128 (to_i128 x) <;> simp [h]

theorem checkedToI128_eq_none_iff (x : Balanced38) :
    checkedToI128 x = none ↔ ¬ inI128 (to_i128 x) := by
  unfold checkedToI128
  by_cases h : inI128 (to_i128 x) <;> simp [h]

theorem checkedToI128_isSome_iff (x : Balanced38) :
    (checkedToI128 x).isSome ↔ inI128 (to_i128 x) := by
  unfold checkedToI128
  by_cases h : inI128 (to_i128 x) <;> simp [h]

theorem checkedToI128_value {x : Balanced38} {v : Int}
    (h : checkedToI128 x = some v) : v = to_i128 x := by
  unfold checkedToI128 at h
  by_cases hin : inI128 (to_i128 x)
  · simp [hin] at h
    exact h.symm
  · simp [hin] at h

theorem to_i128_zero : to_i128 zero = 0 := by
  simp [zero, to_i128]

theorem inI128_zero : inI128 0 := by
  unfold inI128 i128Min i128Max
  native_decide

theorem checkedToI128_zero : checkedToI128 zero = some 0 := by
  unfold checkedToI128
  simp [to_i128_zero, inI128_zero]

/-- The refusing product: zero is the absorbing element (as in the
    Rust lane); otherwise both operands and the product must be in the
    signed i128 shore. -/
def checkedMul (x y : Balanced38) : Option Balanced38 :=
  if x = zero ∨ y = zero then
    some zero
  else
    match checkedToI128 x, checkedToI128 y with
    | some a, some b =>
        if inI128 (a * b) then some (from_i128_full (a * b)) else none
    | _, _ => none

theorem checkedMul_zero_left (y : Balanced38) : checkedMul zero y = some zero := by
  unfold checkedMul
  simp

theorem checkedMul_zero_right (x : Balanced38) : checkedMul x zero = some zero := by
  unfold checkedMul
  simp

theorem checkedMul_value {x y z : Balanced38}
    (h : checkedMul x y = some z) : to_i128 z = to_i128 x * to_i128 y := by
  unfold checkedMul at h
  by_cases hz : x = zero ∨ y = zero
  · rcases hz with hx | hy
    · subst x
      simp at h
      rw [← h]
      simp [zero, to_i128]
    · subst y
      simp at h
      rw [← h]
      simp [zero, to_i128]
  · simp [hz] at h
    cases hx : checkedToI128 x with
    | none => simp [hx] at h
    | some a =>
      cases hy : checkedToI128 y with
      | none => simp [hx, hy] at h
      | some b =>
        by_cases hp : inI128 (a * b)
        · simp [hx, hy, hp] at h
          rw [← h]
          rw [from_i128_full_value]
          rw [checkedToI128_value hx, checkedToI128_value hy]
        · simp [hx, hy, hp] at h

theorem checkedMul_none_of_left_out {x y : Balanced38}
    (hx : checkedToI128 x = none) (hy : y ≠ zero) : checkedMul x y = none := by
  unfold checkedMul
  by_cases hz : x = zero ∨ y = zero
  · rcases hz with h | h
    · subst x
      simp [checkedToI128_zero] at hx
    · exact absurd h hy
  · simp [hz, hx]

theorem checkedMul_none_of_right_out {x y : Balanced38}
    (hy : checkedToI128 y = none) (hx : x ≠ zero) : checkedMul x y = none := by
  unfold checkedMul
  by_cases hz : x = zero ∨ y = zero
  · rcases hz with h | h
    · exact absurd h hx
    · subst y
      simp [checkedToI128_zero] at hy
  · simp [hz, hy]

theorem checkedMul_none_of_product_out {x y : Balanced38} {a b : Int}
    (hx0 : x ≠ zero) (hy0 : y ≠ zero)
    (hx : checkedToI128 x = some a) (hy : checkedToI128 y = some b)
    (h : ¬ inI128 (a * b)) : checkedMul x y = none := by
  unfold checkedMul
  by_cases hz : x = zero ∨ y = zero
  · rcases hz with h0 | h0
    · exact absurd h0 hx0
    · exact absurd h0 hy0
  · simp [hz, hx, hy, h]

theorem checkedMul_some_in_shore {x y z : Balanced38}
    (h : checkedMul x y = some z) (hx : x ≠ zero) (hy : y ≠ zero) :
    ∃ a b, checkedToI128 x = some a ∧ checkedToI128 y = some b ∧ inI128 (a * b) := by
  unfold checkedMul at h
  by_cases hz : x = zero ∨ y = zero
  · rcases hz with h0 | h0
    · exact absurd h0 hx
    · exact absurd h0 hy
  · simp [hz] at h
    cases hx' : checkedToI128 x with
    | none => simp [hx'] at h
    | some a =>
      cases hy' : checkedToI128 y with
      | none => simp [hx', hy'] at h
      | some b =>
        by_cases hp : inI128 (a * b)
        · exact ⟨a, b, rfl, rfl, hp⟩
        · simp [hx', hy', hp] at h

/-- The Euclidean pair, adjusted so the remainder never signs. -/
def euclidPair (a b : Int) : Int × Int :=
  let q0 := a.tdiv b
  let r0 := a.tmod b
  if r0 < 0 then
    if b > 0 then (q0 - 1, r0 + b) else (q0 + 1, r0 - b)
  else (q0, r0)

/-- The refusing division: zero divisor, the `MIN / -1` corner, and
    any operand or result out of the signed i128 shore. -/
def checkedDivRem (x y : Balanced38) : Option (Balanced38 × Balanced38) :=
  if y = zero then none
  else
    match checkedToI128 x, checkedToI128 y with
    | some a, some b =>
        if a = i128Min ∧ b = -1 then none
        else
          let q := (euclidPair a b).1
          let r := (euclidPair a b).2
          if inI128 q ∧ inI128 r then
            some (from_i128_full q, from_i128_full r)
          else none
    | _, _ => none

theorem checkedDivRem_zero (x : Balanced38) : checkedDivRem x zero = none := by
  unfold checkedDivRem
  simp

theorem checkedDivRem_min_neg_one (x y : Balanced38)
    (hx : checkedToI128 x = some i128Min)
    (hy : checkedToI128 y = some (-1)) :
    checkedDivRem x y = none := by
  unfold checkedDivRem
  by_cases hz : y = zero
  · simp [hz]
  · simp [hz, hx, hy]

theorem checkedDivRem_none_of_left_out {x y : Balanced38}
    (hx : checkedToI128 x = none) (hy : y ≠ zero) : checkedDivRem x y = none := by
  unfold checkedDivRem
  by_cases hz : y = zero
  · exact absurd hz hy
  · simp [hz, hx]

theorem checkedDivRem_none_of_right_out {x y : Balanced38}
    (hy : checkedToI128 y = none) : checkedDivRem x y = none := by
  unfold checkedDivRem
  by_cases hz : y = zero
  · subst y
    simp [checkedToI128_zero] at hy
  · simp [hz, hy]

end Shore
