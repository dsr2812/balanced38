import Init

/-- The balanced digit set: integers in [-18, 19]. -/
def Digit : Type := { d : Int // -18 ≤ d ∧ d ≤ 19 }

/-- The membrane digit map: dense digit (0..37) → signed digit (-18..19).
    d ≥ 20 ↦ d - 38; else d. -/
def membrane_digit (d : Nat) : Int :=
  if d ≥ 20 then (d : Int) - 38 else (d : Int)

/-- The inverse map: signed digit (-18..19) → dense digit (0..37). -/
def dense_digit (d : Int) : Nat :=
  if d < 0 then (d + 38).toNat else d.toNat

/-- The one-column rebalance: given a column sum t ∈ [-37, +39] (bounded by
    construction), one compare and ±38 settle it — the digit lands in the
    membrane [-18, 19] and the carry is the exact quotient. No division, no mod.
    The third point (the carry) resolves every conflict, Avizienis' shape. -/
def rebalance (t : Int) : Int × Int :=
  if t > 19 then (t - 38, 1)
  else if t < -18 then (t + 38, -1)
  else (t, 0)

/-- The draining carry always shrinks in magnitude (a non-zero carry resolves
    to a strictly smaller one): the well-founded hook for the shiftees' loops.
    In the honest lane carries are ±1, but the bound holds for any input. -/
theorem rebalance_carry_smaller (c : Int) (h : c ≠ 0) :
    (rebalance c).2.natAbs < c.natAbs := by
  unfold rebalance
  by_cases hbig : c > 19
  · simp [hbig]
    have hc : c ≥ 20 := by omega
    have hcn : (c.natAbs : Int) = c := Int.natAbs_of_nonneg (by omega)
    omega
  · by_cases hslow : c < -18
    · simp [hbig, hslow]
      have hc : c ≤ -19 := by omega
      have hcn : (c.natAbs : Int) = -c := by
        calc
          (c.natAbs : Int) = ((-c).natAbs : Int) := by rw [Int.natAbs_neg]
          _ = -c := Int.natAbs_of_nonneg (by omega)
      omega
    · simp [hbig, hslow]
      omega

/-- The well-founded relation on the carry magnitude — the recursion hook for
    the drain loops. -/
theorem natAbsWF : WellFounded (fun a b : Int => a.natAbs < b.natAbs) := by
  refine InvImage.wf Int.natAbs ?_
  exact Nat.lt_wfRel.wf

/-- THE DRAIN: the leftover carry walked up the empty high places until it
    resolves to the Void. In the honest lane a carry is ±1, so this lands in a
    single column; the drain terminates for any carry because rebalancing a
    non-zero carry always shrinks its magnitude. -/
def drain : Int → List Int :=
  WellFounded.fix natAbsWF
    (fun c rec =>
      if h : c = 0 then []
      else
        (rebalance c).1 :: rec (rebalance c).2 (rebalance_carry_smaller c h))

/-- The balanced store: signed membrane digits, little-endian, zero = empty list.
    Every integer has exactly one form (complete residue system mod 38). -/
structure Balanced38 where
  digits : List Int
  -- Invariant: every digit is in [-18, 19], and the list has no trailing zeros (except the empty list for zero)

instance : DecidableEq Balanced38 := fun ⟨xs⟩ ⟨ys⟩ =>
  match decEq xs ys with
  | isTrue h => isTrue (by rw [h])
  | isFalse h => isFalse (fun heq => by cases heq; exact h rfl)

/-- The Void — the additive identity, the empty string. -/
def zero : Balanced38 := ⟨[]⟩

/-- Trim the most-significant (trailing) zero digits — a string never ends on a gap. -/
def trim_trailing (l : List Int) : List Int :=
  (l.reverse.dropWhile (fun d => decide (d = 0))).reverse

/-- Read back by Horner, signed digits included:
    value = Σ d_i · 38^i (least significant first), the fold running
    most-significant-first with acc = acc·38 + d. -/
def to_i128 (x : Balanced38) : Int :=
  x.digits.reverse.foldl (fun acc d => acc * 38 + d) 0

/-- THE MEMBRANE DIGIT: residuum folded into the balanced cell [-18, +19]. -/
def digit_of (n : Int) : Int :=
  if n.emod 38 ≤ 19 then n.emod 38 else n.emod 38 - 38

/-- The residue walk, TWO digits per big step: divide once by 38^2 = 1444 and
    split the two-digit remainder with machine arithmetic, halving the number of
    big divisions. Emits exactly the same digit string as the one-digit walk
    (bridge theorem from_i128_eq_drain); stops at the first zero residue. -/
def from_i128.go : Int → List Int → Nat → List Int
  | _, acc, 0 => acc
  | 0, acc, _ => acc
  | n, acc, k + 1 =>
    let d0 := digit_of n
    let n1 := (n - d0) / 38
    if h : n1 = 0 then
      from_i128.go 0 (acc ++ [d0]) k
    else
      let d1 := digit_of n1
      let n2 := (n1 - d1) / 38
      from_i128.go n2 (acc ++ [d0, d1]) k

def from_i128 (v : Int) : Balanced38 :=
  if v = 0 then zero
  else { digits := from_i128.go v [] 27 }

/-- THE FAST WALK: the same chunked two-digit walk, but the accumulator is built
    REVERSED (one prepend per digit) and flipped once at the end — O(n) list
    work instead of the O(n²) appends of the founding walk. Digit-for-digit
    identical output (bridge: from_i128_fast_go_eq, from_i128_fast_eq_from_i128). -/
def from_i128_fast.go : Int → List Int → Nat → List Int
  | _, acc, 0 => acc
  | 0, acc, _ => acc
  | n, acc, k + 1 =>
      let d0 := digit_of n
      let n1 := (n - d0) / 38
      if _h : n1 = 0 then
        from_i128_fast.go 0 (d0 :: acc) k
      else
        let d1 := digit_of n1
        let n2 := (n1 - d1) / 38
        from_i128_fast.go n2 (d1 :: d0 :: acc) k

def from_i128_fast (v : Int) : Balanced38 :=
  if v = 0 then zero
  else { digits := (from_i128_fast.go v [] 27).reverse }

/-- The digit rebalance for negation: the mirror (-d) plus the debt carried
    up from below, settled by one compare and ±38. -/
def negateDigits : List Int → Int → List Int
  | [], c => drain c
  | d :: rest, c =>
      let t := -d + c
      let (digit, n) := rebalance t
      digit :: negateDigits rest n

/-- THE REFLECTION: digit-wise negation with the mirror's debt walked up.
    The membrane set {-18..-1, 0, 1..19} is closed under negation EXCEPT for +19
    (its mirror -19 is one past the gate) — so the mirror rebalances: -19 becomes
    19 with the debt -38 carried to the next place, where it is ADDED. -/
def negate (x : Balanced38) : Balanced38 :=
  { digits := trim_trailing (negateDigits x.digits 0) }

theorem drain.eq (c : Int) : drain c = if _ : c = 0 then [] else (rebalance c).1 :: drain (rebalance c).2 := by
  unfold drain
  rw [WellFounded.fix_eq]

def lval : List Int → Int
  | [] => 0
  | d :: rest => d + 38 * lval rest

def vl : List Int → Int :=
  List.foldl (fun acc d => acc * 38 + d) 0

-- =================== RANGE / CANONICAL SHAPE ===================

def in_range (d : Int) : Prop := -18 ≤ d ∧ d ≤ 19

def no_trail (l : List Int) : Prop := ∀ (t : List Int), ∀ h : Int, l = t ++ [h] → h ≠ 0

theorem rebalance_linear (t : Int) : (rebalance t).1 + 38 * (rebalance t).2 = t := by
  unfold rebalance
  split
  · simp <;> omega
  · split <;> simp <;> omega

-- if 38*x is within [-37, 37], then x = 0

theorem mul38_eq_zero {x : Int} (h1 : -37 ≤ 38 * x) (h2 : 38 * x ≤ 37) : x = 0 := by
  by_cases hx : x = 0
  · exact hx
  · by_cases hpos : 0 < x
    · have : 1 ≤ x := by omega
      have : 38 ≤ 38 * x := by omega
      omega
    · have : x < 0 := by omega
      have : 38 * x ≤ -38 := by omega
      omega

-- d + 38a = e + 38b with d,e in the digit membrane forces d = e
theorem col_eq_of_val_eq {d e a b : Int}
    (hd : in_range d) (he : in_range e)
    (h : d + 38 * a = e + 38 * b) :
    d = e ∧ a = b := by
  have hk : d - e = 38 * (b - a) := by omega
  have hk0 : b - a = 0 := by
    apply mul38_eq_zero
    · have hb1 : -37 ≤ d - e := by
        unfold in_range at hd he
        omega
      omega
    · have hb2 : d - e ≤ 37 := by
        unfold in_range at hd he
        omega
      omega
  constructor
  · omega
  · omega

theorem in_range_of_cons {d : Int} {rest : List Int}
    (h : ∀ x ∈ d :: rest, in_range x) : ∀ x ∈ rest, in_range x := by
  intro x hx
  exact h x (by simp [hx])

theorem no_trail_of_cons {d : Int} {rest : List Int}
    (h : no_trail (d :: rest)) : no_trail rest := by
  intro t h0 hteq
  apply h (d :: t) h0
  rw [hteq]
  rfl

-- a canonical (in-range, no-trailing-zero) list with value 0 is empty
theorem val_zero_implies_nil {l : List Int}
    (hl : ∀ d ∈ l, in_range d) (tl : no_trail l)
    (hv : lval l = 0) : l = [] := by
  cases l with
  | nil => rfl
  | cons d rest =>
      exfalso
      have hd : in_range d := hl d (by simp)
      have hrest_ok : ∀ x ∈ rest, in_range x := in_range_of_cons hl
      have hrest_trail : no_trail rest := no_trail_of_cons tl
      have hvx : d + 38 * lval rest = 0 := by
        simpa [lval] using hv
      have hv' : d + 38 * lval rest = 0 + 38 * 0 := by omega
      have hc := col_eq_of_val_eq hd (by unfold in_range; omega : in_range 0) hv'
      rcases hc with ⟨hd0, hrestval⟩
      subst d
      have hrestnil : rest = [] := val_zero_implies_nil hrest_ok hrest_trail hrestval
      subst rest
      exact (tl [] 0 (by simp) rfl)

-- a canonical list is uniquely determined by its value
theorem canonical_unique {l m : List Int}
    (hl : ∀ d ∈ l, in_range d) (hm : ∀ d ∈ m, in_range d)
    (tl : no_trail l) (tm : no_trail m)
    (hv : lval l = lval m) : l = m := by
  revert m
  induction l with
  | nil =>
      intro m hm tm hv
      cases m with
      | nil => rfl
      | cons e rest =>
          exfalso
          have hrest_ok : ∀ x ∈ rest, in_range x := in_range_of_cons hm
          have hrest_trail : no_trail rest := no_trail_of_cons tm
          have hvx : e + 38 * lval rest = 0 := by
            simpa [lval] using hv.symm
          have hv' : e + 38 * lval rest = 0 + 38 * 0 := by omega
          have hc := col_eq_of_val_eq (hm e (by simp)) (by unfold in_range; omega : in_range 0) hv'
          rcases hc with ⟨he0, hrestval⟩
          subst e
          have hrestnil : rest = [] := val_zero_implies_nil hrest_ok hrest_trail hrestval
          subst rest
          exact (tm [] 0 (by simp) rfl)
  | cons d rest IH =>
      intro m hm tm hv
      cases m with
      | nil =>
          exfalso
          have hrest_ok : ∀ x ∈ rest, in_range x := in_range_of_cons hl
          have hrest_trail : no_trail rest := no_trail_of_cons tl
          have hvx : d + 38 * lval rest = 0 := by
            simpa [lval] using hv
          have hv' : d + 38 * lval rest = 0 + 38 * 0 := by omega
          have hc := col_eq_of_val_eq (hl d (by simp)) (by unfold in_range; omega : in_range 0) hv'
          rcases hc with ⟨hd0, hrestval⟩
          subst d
          have hrestnil : rest = [] := val_zero_implies_nil hrest_ok hrest_trail hrestval
          subst rest
          exact (tl [] 0 (by simp) rfl)
      | cons e rest2 =>
          have hm_e : in_range e := hm e (by simp)
          have hd_d : in_range d := hl d (by simp)
          have hvx : d + 38 * lval rest = e + 38 * lval rest2 := by
            simpa [lval] using hv
          have hc := col_eq_of_val_eq hd_d hm_e hvx
          rcases hc with ⟨hde, hrestval⟩
          subst e
          have hrest_ok1 : ∀ x ∈ rest, in_range x := in_range_of_cons hl
          have hrest_ok2 : ∀ x ∈ rest2, in_range x := in_range_of_cons hm
          have hrest_trail1 : no_trail rest := no_trail_of_cons tl
          have hrest_trail2 : no_trail rest2 := no_trail_of_cons tm
          have hrest_eq : rest = rest2 := IH hrest_ok1 hrest_trail1 hrest_ok2 hrest_trail2 hrestval
          subst hrest_eq
          rfl

-- =================== TRIM PRESERVES VALUE ===================

theorem vl_append_singleton (l : List Int) (d : Int) : vl (l ++ [d]) = vl l * 38 + d := by
  unfold vl
  rw [List.foldl_append]
  simp

theorem lval_eq_vl_reverse (l : List Int) : lval l = vl l.reverse := by
  induction l with
  | nil => rfl
  | cons d rest ih =>
      calc
        lval (d :: rest) = d + 38 * lval rest := rfl
        _ = d + 38 * vl rest.reverse := by rw [ih]
        _ = vl rest.reverse * 38 + d := by omega
        _ = vl (d :: rest).reverse := by
          rw [List.reverse_cons]
          exact (vl_append_singleton rest.reverse d).symm

theorem vl_dropWhile_zero (l : List Int) : vl (l.dropWhile (fun d => decide (d = 0))) = vl l := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      cases h : (fun d => decide (d = 0)) a
      · simp [List.dropWhile, h, vl]
      · have ha : a = 0 := by
          dsimp at h
          exact of_decide_eq_true h
        simp [List.dropWhile, ha]
        change vl (List.dropWhile (fun d => decide (d = 0)) rest) = vl rest
        exact ih

theorem trim_value (l : List Int) : lval (trim_trailing l) = lval l := by
  unfold trim_trailing
  calc
    lval ((l.reverse.dropWhile (fun d => decide (d = 0))).reverse) =
        vl (((l.reverse.dropWhile (fun d => decide (d = 0))).reverse).reverse) := by
      rw [lval_eq_vl_reverse]
    _ = vl (l.reverse.dropWhile (fun d => decide (d = 0))) := by rw [List.reverse_reverse]
    _ = vl l.reverse := by apply vl_dropWhile_zero
    _ = lval l := by rw [lval_eq_vl_reverse]

-- =================== TRIM STAYS IN RANGE ===================

theorem mem_dropWhile {a : Int} (l : List Int) :
    a ∈ l.dropWhile (fun d => decide (d = 0)) → a ∈ l := by
  induction l with
  | nil => intro h; simp at h
  | cons x rest ih =>
      intro h
      cases hb : (fun d => decide (d = 0)) x
      · simp [List.dropWhile, hb] at h
        simpa [List.mem_cons] using h
      · exact List.mem_cons_of_mem x (ih (by simp [List.dropWhile, hb] at h; exact h))

theorem trim_in_range (l : List Int) (hl : ∀ d ∈ l, in_range d) :
    ∀ d ∈ trim_trailing l, in_range d := by
  unfold trim_trailing
  intro d hd
  exact hl d (List.mem_reverse.mp (mem_dropWhile l.reverse (List.mem_reverse.mp hd)))

-- =================== TRIM HAS NO TRAILING ZERO ===================

theorem no_trail_of_getLast_ne_zero (l : List Int) (h : l.getLast? ≠ some 0) : no_trail l := by
  intro t h0 hteq
  intro hz
  apply h
  have : l.getLast? = some 0 := by
    rw [hteq]
    rw [List.getLast?_append]
    simp [hz]
  simpa using this

theorem getLast?_reverse_cons (y : Int) (rest : List Int) : (List.reverse (y :: rest)).getLast? = some y := by
  induction rest with
  | nil => simp
  | cons z rs ih =>
      rw [List.reverse_cons, List.getLast?_append]
      simp

theorem dropWhile_cons_head {p : Int → Bool} {l : List Int} {y : Int} {rest : List Int}
    (h : l.dropWhile p = y :: rest) : p y = false := by
  induction l with
  | nil => simp at h
  | cons a as ih =>
      cases hb : p a
      · simp [List.dropWhile, hb] at h
        rcases h with ⟨hay, has⟩
        rw [← hay]
        exact hb
      · simp [List.dropWhile, hb] at h
        exact ih h

theorem trim_no_trail (l : List Int) : no_trail (trim_trailing l) := by
  apply no_trail_of_getLast_ne_zero
  unfold trim_trailing
  intro hz
  cases hs : (List.reverse l).dropWhile (fun d => decide (d = 0)) with
  | nil => simp [hs] at hz
  | cons y rest =>
      rw [hs] at hz
      have hlast := getLast?_reverse_cons y rest
      rw [hlast] at hz
      injection hz with hy
      have hp := dropWhile_cons_head hs
      have hp_true : (fun d => decide (d = 0)) y = true := by simp [hy]
      simp [hp] at hp_true

/-- a non-zero last digit bans every trailing zero, regardless of the prefix -/
theorem no_trail_append_singleton (acc : List Int) (d : Int) (hd : d ≠ 0) :
    no_trail (acc ++ [d]) := by
  intro t h heq
  have hlen := congrArg List.length heq
  simp [List.length_append] at hlen
  have hle : acc.length = t.length := by omega
  have hdrop := congrArg (fun l : List Int => l.drop acc.length) heq
  have h1 : (acc ++ [d]).drop acc.length = [d] := by simp
  have h2 : (t ++ [h]).drop acc.length = [h] := by
    rw [hle]
    simp
  have ht : [d] = [h] := by
    rw [h1] at hdrop
    rw [h2] at hdrop
    exact hdrop
  have hdh : d = h := by
    exact (List.cons.inj ht).1
  exact hdh ▸ hd

-- =================== DRAIN ON SMALL CARRIES ===================

theorem rebalance_range (t : Int) (hb : -20 ≤ t) (ht : t ≤ 19) :
    in_range (rebalance t).1 ∧ ((rebalance t).2 = 0 ∨ (rebalance t).2 = -1) := by
  unfold rebalance
  split
  · simp
    omega
  · split
    · simp at *
      unfold in_range at *
      omega
    · simp at *
      unfold in_range at *
      omega

-- ============================================================
-- A3 THE COLUMN BOUND (ledger Phase 2 rung 2, 11 Sep): the Avizienis
-- invariant as a theorem. A settled column t = a + b + carry sits in
-- [−37, +39] — one compare and ±38 settle every column — and the rebalance
-- closes: the digit lands back in the membrane and the carry is always
-- ±1 or 0. (The lane's add loop leans on exactly this.)
-- ============================================================

theorem column_sum_bounds (a b c : Int)
    (ha : in_range a) (hb : in_range b) (hc : -1 ≤ c ∧ c ≤ 1) :
    -37 ≤ a + b + c ∧ a + b + c ≤ 39 := by
  unfold in_range at ha hb
  omega

theorem rebalance_invariant (t : Int) (hlo : -37 ≤ t) (hhi : t ≤ 39) :
    in_range (rebalance t).1 ∧ -1 ≤ (rebalance t).2 ∧ (rebalance t).2 ≤ 1 := by
  unfold rebalance
  split
  · simp at *
    unfold in_range at *
    omega
  · split
    · simp at *
      unfold in_range at *
      omega
    · simp at *
      unfold in_range at *
      omega

-- ============================================================
-- A5 THE OUTPUTS ARE CANONICAL (ledger Phase 2 rung 4, 11 Sep):
-- the composite theorem the paper's §5 "proven shore" paragraph promised:
-- no produced string ends on a gap and no produced string leaves the
-- membrane — FOR THE OPERATIONS, not just the primitives.
-- ============================================================

/-- A5's add-side theorems (addDigits_in_range, checked_add_canonical) live at
    the file's end, beside the drain/from_i128 families they cite. -/

theorem drain_minus_one : drain (-1) = [-1] := by
  rw [drain.eq]
  simp [rebalance, drain.eq]
theorem drain_zero : drain 0 = [] := by
  rw [drain.eq]
  simp
theorem drain_one : drain 1 = [1] := by
  rw [drain.eq]
  simp [rebalance, drain.eq]

theorem drain_small_in_range (c : Int) (hc : -1 ≤ c ∧ c ≤ 1) :
    ∀ d ∈ drain c, in_range d := by
  have hc3 : c = -1 ∨ c = 0 ∨ c = 1 := by omega
  rcases hc3 with hc1 | hc2 | hc3
  · subst c
    intro d hd
    rw [drain_minus_one] at hd
    simp at hd
    subst d
    unfold in_range
    omega
  · subst c
    intro d hd
    rw [drain_zero] at hd
    simp at hd
  · subst c
    intro d hd
    rw [drain_one] at hd
    simp at hd
    subst d
    unfold in_range
    omega

theorem negateDigits_in_range : ∀ ds : List Int, ∀ c : Int,
    (∀ d ∈ ds, in_range d) → (-1 ≤ c ∧ c ≤ 1) → (∀ e ∈ negateDigits ds c, in_range e) := by
  intro ds
  induction ds with
  | nil => intro c hds hc; rw [negateDigits]; exact drain_small_in_range c hc
  | cons d rest ih =>
      intro c hds hc
      rw [negateDigits]
      cases h : rebalance (-d + c) with
      | mk digit n =>
          have hd : in_range d := hds d (by simp)
          unfold in_range at hd
          intro e he
          simp at he
          rcases he with he | he
          · rw [he]
            have hb : -20 ≤ -d + c := by omega
            have ht : -d + c ≤ 19 := by omega
            have hrr := rebalance_range (-d + c) hb ht
            rw [h] at hrr
            simp at hrr
            exact hrr.1
          · have hb : -20 ≤ -d + c := by omega
            have ht : -d + c ≤ 19 := by omega
            have hrr := rebalance_range (-d + c) hb ht
            rw [h] at hrr
            simp at hrr
            rcases hrr with ⟨_, hc⟩
            rcases hc with hc0 | hc1
            · subst n
              exact ih 0 (by intro x hx; exact hds x (by simp [hx])) (by omega) e he
            · subst n
              exact ih (-1) (by intro x hx; exact hds x (by simp [hx])) (by omega) e he

-- =================== VALUATION OF NEGATION ===================

theorem drain_value : ∀ c : Int, lval (drain c) = c := by
  intro c
  refine WellFounded.induction natAbsWF c (C := fun y => lval (drain y) = y) ?_
  intro c ih
  by_cases hc : c = 0
  · rw [drain.eq]
    simp [hc, lval]
  · rw [drain.eq]
    simp [hc]
    change (rebalance c).1 + 38 * lval (drain (rebalance c).2) = c
    have hrec : lval (drain (rebalance c).2) = (rebalance c).2 :=
      ih (rebalance c).2 (rebalance_carry_smaller c hc)
    rw [hrec]
    exact rebalance_linear c

theorem negateDigits_value : ∀ ds : List Int, ∀ c : Int, lval (negateDigits ds c) = c - lval ds := by
  intro ds
  induction ds with
  | nil =>
      intro c
      rw [negateDigits]
      rw [drain_value]
      simp [lval]
  | cons d rest ih =>
      intro c
      rw [negateDigits]
      cases h : rebalance (-d + c) with
      | mk digit n =>
          simp only [lval]
          have hlin := rebalance_linear (-d + c)
          rw [h] at hlin
          simp at hlin
          have hih := ih n
          rw [hih]
          omega

/-- The scribe's signed add, one column at a time (see `checked_add`). The
    columns differ in length; a missing digit reads as the gap, 0. -/
def addDigits : List Int → List Int → Int → List Int
  | [], [], c => drain c
  | [], b :: brest, c =>
      let (digit, n) := rebalance (c + b)
      digit :: addDigits [] brest n
  | a :: arest, [], c =>
      let (digit, n) := rebalance (c + a)
      digit :: addDigits arest [] n
  | a :: arest, b :: brest, c =>
      let (digit, n) := rebalance (c + a + b)
      digit :: addDigits arest brest n
termination_by x y _ => x.length + y.length
decreasing_by
  all_goals (simp only [List.length_cons, List.length_nil]; omega)

/-- THE SCRIBE'S SIGNED ADD: the Avizienis rebalance on membrane digits.
    t = a + b + carry sits in [-37, +39], bounded by construction,
    so one compare and ±38 settle every column. No division, no mod. -/
def checked_add (x y : Balanced38) : Balanced38 :=
  { digits := trim_trailing (addDigits x.digits y.digits 0) }

/-- THE REFLECTION AS AN OPERATION: subtraction IS addition of the negation. -/
def sub (x y : Balanced38) : Balanced38 :=
  checked_add x (negate y)

/-- The unbounded Horner fold. Lean's `Int` has no i128 shore, so this
    fold cannot refuse: `foldChecked_value` proves it always returns
    `some`. The i128 refusal is the Rust crate's `checked_to_i128`; the
    Lean model does not model `None` here. -/
def foldChecked : List Int → Option Int
  | [] => some 0
  | d :: rest => do
      let acc ← foldChecked rest
      let acc' := acc * 38
      pure (acc' + d)

theorem foldChecked_value (L : List Int) : foldChecked L = some (lval L) := by
  induction L with
  | nil => simp [foldChecked, lval]
  | cons d rest ih =>
      simp [foldChecked, lval, ih]
      rw [Int.add_comm, Int.mul_comm]

/-- THE SCHOLAR'S ADD: column by column the scribe's signed add reads back the
    exact value — the carried debt is settled, nothing leaks. The addition law
    that completes the lane's four arithmetic certificates. -/
theorem addDigits_value (a b : List Int) (c : Int) :
    lval (addDigits a b c) = lval a + lval b + c := by
  induction a generalizing b c with
  | nil =>
      induction b generalizing c with
      | nil =>
          simp [addDigits, lval, drain_value]
      | cons b brest ihb =>
          simp [addDigits, lval]
          rw [ihb (rebalance (c + b)).2]
          simp [lval, Int.mul_add]
          have hbal : (rebalance (c + b)).1 + 38 * (rebalance (c + b)).2 = c + b := by
            simpa using (rebalance_linear (c + b))
          omega
  | cons a arest iha =>
      cases b with
      | nil =>
          simp [addDigits, lval]
          rw [iha ([] : List Int) ((rebalance (c + a)).2)]
          simp [lval, Int.mul_add]
          have hbal : (rebalance (c + a)).1 + 38 * (rebalance (c + a)).2 = c + a := by
            simpa using (rebalance_linear (c + a))
          omega
      | cons b brest =>
          simp [addDigits, lval]
          rw [iha brest ((rebalance (c + a + b)).2)]
          simp [lval, Int.mul_add]
          have hbal : (rebalance (c + a + b)).1 + 38 * (rebalance (c + a + b)).2 = c + a + b := by
            simpa using (rebalance_linear (c + a + b))
          omega

/-- The value lemmas ported from the scratch file: the right-triangular
    product grid (mulGrid), the drain and the carry pass, all exact. -/
def w : Nat → Int
  | 0 => 1
  | k+1 => 38 * w k

theorem w_zero : w 0 = 1 := rfl
theorem w_succ (k : Nat) : w (k+1) = 38 * w k := rfl

theorem w_mul (i j : Nat) : w (i + j) = w i * w j := by
  induction j with
  | zero => simp [w_zero]
  | succ j ih =>
      rw [Nat.add_succ, w_succ]
      rw [ih]
      calc 38 * (w i * w j) = (38 * w i) * w j := by rw [Int.mul_assoc]
        _ = (w i * 38) * w j := by rw [Int.mul_comm (38 : Int) (w i)]
        _ = w i * (38 * w j) := by rw [Int.mul_assoc]

theorem natAbs38 : Int.natAbs (38 : Int) = 38 := by decide

theorem natAbs38I : ((Int.natAbs (38 : Int)) : Int) = 38 := by
  exact_mod_cast natAbs38

theorem mod38_lo (c : Int) : 0 ≤ c.emod 38 := by
  exact Int.emod_nonneg c (b := (38 : Int)) (by decide)

theorem mod38_hi (c : Int) : c.emod 38 < 38 := by
  have h := Int.emod_lt c (b := (38 : Int)) (by decide)
  rwa [natAbs38] at h

theorem emod_eq_self {r : Int} (h0 : 0 ≤ r) (h1 : r < 38) : r % 38 = r := by
  exact Int.emod_eq_of_lt (b := (38 : Int)) h0 h1

theorem emod_sub_self (r : Int) : (r - 38) % 38 = r % 38 := by
  rw [Int.sub_emod]
  have hz : (38 : Int) % 38 = 0 := Int.emod_self (a := (38 : Int))
  rw [hz]
  have hs : r % 38 - 0 = r % 38 := by omega
  rw [hs]
  exact emod_eq_self (r := r % 38) (mod38_lo r) (mod38_hi r)

theorem digit_mod_eq (r : Int) : let digit := if r > 19 then r - 38 else r
    digit % 38 = r % 38 := by
  intro digit
  by_cases hr : r > 19
  · have hh := emod_sub_self r
    simpa [digit, hr] using hh
  · simp [digit, hr]

theorem digit_mod_c (c : Int) : let digit := if c.emod 38 > 19 then c.emod 38 - 38 else c.emod 38
    digit % 38 = c % 38 := by
  intro digit
  have hdm' : digit % 38 = c.emod 38 % 38 := by
    simpa [digit] using (digit_mod_eq (c.emod 38))
  have hr : c.emod 38 % 38 = c % 38 := emod_eq_self (r := c % 38) (mod38_lo c) (mod38_hi c)
  rw [hr] at hdm'
  exact hdm'

theorem div38_exact (a : Int) (hmod : a % 38 = 0) : a = 38 * (a / 38) := by
  have hu := Int.ediv_emod_unique (a := a) (b := (38 : Int)) (r := a % 38) (q := a / 38) (by decide)
  have hA : a % 38 + 38 * (a / 38) = a := (hu.1 ⟨rfl, rfl⟩).1
  rw [hmod] at hA
  omega

theorem digit_carr (c : Int) : let digit := if c.emod 38 > 19 then c.emod 38 - 38 else c.emod 38
    c = digit + 38 * ((c - digit) / 38) := by
  intro digit
  have hcdmod : (c - digit) % 38 = 0 := by
    rw [Int.sub_emod]
    have hrd : digit % 38 = c % 38 := by
      simpa [digit] using (digit_mod_c c)
    rw [hrd]
    simp
  have hex := div38_exact (c - digit) hcdmod
  rw [← hex]
  omega

theorem natAbs_le_iff_bounds {a : Int} {n : Nat} (hlo : -((n : Int)) ≤ a) (hhi : a ≤ (n : Int)) :
    a.natAbs ≤ n := by
  have hnz : a = ↑a.natAbs ∨ a = -↑a.natAbs := Int.natAbs_eq a
  rcases hnz with ha | ha
  · rw [ha] at hhi
    exact_mod_cast hhi
  · rw [ha] at hlo
    omega

theorem digit_range (r : Int) (hr0 : 0 ≤ r) (hr1 : r < 38) :
    (let digit := if r > 19 then r - 38 else r; -18 ≤ digit ∧ digit ≤ 19) := by
  intro digit
  by_cases hr : r > 19
  · simp [digit, hr]; omega
  · simp [digit, hr]; omega

theorem drainCarryStep_abs (c : Int) (digit : Int)
    (hcd : c = digit + 38 * ((c - digit) / 38))
    (hd0 : -18 ≤ digit) (hd1 : digit ≤ 19) (hc : c ≠ 0) :
    ((c - digit) / 38).natAbs < c.natAbs := by
  let carry : Int := (c - digit) / 38
  have hcd' : c - digit = 38 * carry := by omega
  have hdn : digit.natAbs ≤ 19 := by
    apply natAbs_le_iff_bounds
    · omega
    · exact hd1
  have hok : (38 * carry).natAbs ≤ c.natAbs + 19 := by
    rw [← hcd']
    have h1 : (c - digit).natAbs ≤ c.natAbs + digit.natAbs := Int.natAbs_sub_le c digit
    have h2 : c.natAbs + digit.natAbs ≤ c.natAbs + 19 := by omega
    exact Nat.le_trans h1 h2
  have hok38 : 38 * carry.natAbs ≤ c.natAbs + 19 := by
    have hmul' : (38 * carry).natAbs = 38 * carry.natAbs := by
      simpa [natAbs38] using (Int.natAbs_mul (38 : Int) carry)
    rw [← hmul']
    exact hok
  have hx : carry.natAbs ≤ (c.natAbs + 19) / 38 := by
    rw [Nat.le_div_iff_mul_le (k := 38) (x := carry.natAbs) (y := c.natAbs + 19) (by decide)]
    rw [Nat.mul_comm]
    exact hok38
  have hxlt : (c.natAbs + 19) / 38 < c.natAbs := by
    rw [Nat.div_lt_iff_lt_mul (k := 38) (x := c.natAbs + 19) (y := c.natAbs) (by decide)]
    have hpos := Int.natAbs_pos.mpr hc
    omega
  exact calc
    carry.natAbs ≤ (c.natAbs + 19) / 38 := hx
    _ < c.natAbs := hxlt

theorem drainCarryStep_dec (c : Int) (hc : c ≠ 0) :
    let digit := if c.emod 38 > 19 then c.emod 38 - 38 else c.emod 38
    ((c - digit) / 38).natAbs < c.natAbs := by
  intro digit
  have hcd : c = digit + 38 * ((c - digit) / 38) := by
    simpa [digit] using (digit_carr c)
  have hdr : -18 ≤ digit ∧ digit ≤ 19 := by
    simpa [digit] using (digit_range (c.emod 38) (mod38_lo c) (mod38_hi c))
  exact drainCarryStep_abs c digit hcd hdr.1 hdr.2 hc

def drainCarry.go : List Int → Int → List Int :=
  fun acc c => @WellFounded.fix Int (fun _ => List Int → List Int) (fun a b : Int => a.natAbs < b.natAbs)
    natAbsWF
    (fun c rec => fun acc =>
      if h : c = 0 then acc
      else
        let digit := if c.emod 38 > 19 then c.emod 38 - 38 else c.emod 38
        rec ((c - digit) / 38) (drainCarryStep_dec c h) (acc ++ [digit])) c acc

def drainCarry (acc : List Int) (carry : Int) : List Int :=
  drainCarry.go acc carry

theorem lval_append (a b : List Int) : lval (a ++ b) = lval a + w a.length * lval b := by
  induction a with
  | nil => simp [lval, w_zero]
  | cons h t ih =>
      calc
        lval (h :: (t ++ b)) = h + 38 * lval (t ++ b) := rfl
        _ = h + 38 * (lval t + w t.length * lval b) := by rw [ih]
        _ = (h + 38 * lval t) + (38 * w t.length) * lval b := by
          rw [Int.mul_add, ← Int.add_assoc, ← Int.mul_assoc]
        _ = lval (h :: t) + w (h :: t).length * lval b := by
          simp [lval, w_succ]

theorem w_length_append_singleton (acc : List Int) (d : Int) :
    w (acc ++ [d]).length = 38 * w acc.length := by
  rw [List.length_append]
  simp
  rw [w_succ]

theorem go_eq (acc : List Int) (c : Int) :
    drainCarry.go acc c = if h : c = 0 then acc else
      let r := c.emod 38
      let digit := if r > 19 then r - 38 else r
      drainCarry.go (acc ++ [digit]) ((c - digit) / 38) := by
  unfold drainCarry.go
  rw [WellFounded.fix_eq]

theorem drainCarry_step_value (acc : List Int) (c : Int) :
    let digit := if c.emod 38 > 19 then c.emod 38 - 38 else c.emod 38
    lval (acc ++ [digit]) + ((c - digit) / 38) * w (acc ++ [digit]).length
        = lval acc + c * w acc.length := by
  intro digit
  have hcarr : c = digit + 38 * ((c - digit) / 38) := by
    simpa [digit] using (digit_carr c)
  have hK : 38 * ((c - digit) / 38) = c - digit := by omega
  have h38 : ((c - digit) / 38) * 38 = c - digit := by
    rw [Int.mul_comm]
    exact hK
  calc
    lval (acc ++ [digit]) + ((c - digit) / 38) * w (acc ++ [digit]).length
        = (lval acc + w acc.length * digit) + ((c - digit) / 38) * (38 * w acc.length) := by
          rw [lval_append, w_length_append_singleton]
          simp [lval]
    _ = lval acc + w acc.length * digit + ((c - digit) / 38) * (38 * w acc.length) := rfl
    _ = lval acc + w acc.length * digit + (c - digit) * w acc.length := by
          rw [← Int.mul_assoc, h38]
    _ = lval acc + c * w acc.length := by
          rw [Int.mul_comm (w acc.length) digit, Int.add_assoc, ← Int.add_mul]
          have hlin : digit + (c - digit) = c := by omega
          rw [hlin]

theorem drainCarry_value (acc : List Int) (c : Int) :
    lval (drainCarry.go acc c) = lval acc + c * w acc.length := by
  let P : Int → Prop := fun c => ∀ acc : List Int, lval (drainCarry.go acc c) = lval acc + c * w acc.length
  have hP : P c := by
    refine @WellFounded.induction Int (fun a b : Int => a.natAbs < b.natAbs) natAbsWF P c ?_
    intro x ih acc
    rw [go_eq]
    by_cases hx : x = 0
    · simp [hx]
    · rw [dif_neg hx]
      dsimp
      have hdec := drainCarryStep_dec x hx
      rw [ih ((x - (if x.emod 38 > 19 then x.emod 38 - 38 else x.emod 38)) / 38) hdec
             (acc ++ [if x.emod 38 > 19 then x.emod 38 - 38 else x.emod 38])]
      exact drainCarry_step_value acc x
  exact hP acc

/-- every digit produced by the drain stays in range -/
theorem drainCarry_go_in_range (c : Int) :
    ∀ acc : List Int, (∀ d ∈ acc, in_range d) → ∀ d ∈ drainCarry.go acc c, in_range d := by
  let P : Int → Prop := fun c =>
    ∀ acc : List Int, (∀ d ∈ acc, in_range d) → ∀ d ∈ drainCarry.go acc c, in_range d
  have hP : P c := by
    refine @WellFounded.induction Int (fun a b : Int => a.natAbs < b.natAbs) natAbsWF P c ?_
    intro x ih acc hacc d hd
    rw [go_eq] at hd
    by_cases hx : x = 0
    · simp [hx] at hd
      exact hacc d hd
    · rw [dif_neg hx] at hd
      dsimp at hd
      have hdec := drainCarryStep_dec x hx
      have hdgt := digit_range (x.emod 38) (mod38_lo x) (mod38_hi x)
      have hx0 : in_range (if x.emod 38 > 19 then x.emod 38 - 38 else x.emod 38) := by
        simpa [in_range] using hdgt
      have hacc' : ∀ e ∈ acc ++ [if x.emod 38 > 19 then x.emod 38 - 38 else x.emod 38], in_range e := by
        intro e he
        rcases (List.mem_append.mp he) with hl | hr
        · exact hacc e hl
        · rcases (List.mem_singleton.mp hr) with rfl
          exact hx0
      exact ih ((x - (if x.emod 38 > 19 then x.emod 38 - 38 else x.emod 38)) / 38) hdec
        (acc ++ [if x.emod 38 > 19 then x.emod 38 - 38 else x.emod 38]) hacc' d hd
  exact hP

/-- the drain's output never ends on a zero, as its last emitted digit is always non-zero -/
theorem drainCarry_go_no_trail (acc : List Int) (c : Int) (hc : c ≠ 0) :
    no_trail (drainCarry.go acc c) := by
  let P : Int → Prop := fun c => ∀ acc : List Int, c ≠ 0 → no_trail (drainCarry.go acc c)
  have hP : P c := by
    refine @WellFounded.induction Int (fun a b : Int => a.natAbs < b.natAbs) natAbsWF P c ?_
    intro x ih acc hx
    rw [go_eq]
    rw [dif_neg hx]
    dsimp
    let digit := if x.emod 38 > 19 then x.emod 38 - 38 else x.emod 38
    let nxt := (x - digit) / 38
    have hdec := drainCarryStep_dec x hx
    have hcd : x = digit + 38 * nxt := by
      simpa [digit, nxt] using (digit_carr x)
    by_cases hn : nxt = 0
    · have hn2 : (x - (if x.emod 38 > 19 then x.emod 38 - 38 else x.emod 38)) / 38 = 0 := by
        simpa [digit, nxt] using hn
      rw [hn2]
      rw [go_eq (acc ++ [if x.emod 38 > 19 then x.emod 38 - 38 else x.emod 38]) 0]
      simp
      have hdigit : digit ≠ 0 := by
        intro hd0
        have hx0 : x = 0 := by
          rw [hcd, hn, hd0]
          omega
        exact hx hx0
      exact no_trail_append_singleton acc digit hdigit
    · exact ih nxt hdec (acc ++ [digit]) hn
  exact hP acc hc

def carryPass.go (acc : List Int) (carry : Int) : List Int → List Int × Int
  | [] => (acc, carry)
  | c :: cs =>
      let t := carry + c
      let digit := if t.emod 38 > 19 then t.emod 38 - 38 else t.emod 38
      carryPass.go (acc ++ [digit]) ((t - digit) / 38) cs
termination_by rest => rest.length

def carryPass (grid : List Int) : List Int × Int := carryPass.go [] 0 grid

theorem carryPass_step_inv (acc : List Int) (carry c : Int) (S : Int) :
    let t := carry + c
    let digit := if t.emod 38 > 19 then t.emod 38 - 38 else t.emod 38
    lval acc + t * w acc.length + S * w (acc ++ [digit]).length
      = lval acc + carry * w acc.length + (c + 38 * S) * w acc.length := by
  intro t digit
  rw [w_length_append_singleton]
  dsimp [t]
  rw [Int.add_mul, ← Int.add_assoc]
  rw [Int.add_assoc, ← Int.mul_assoc, Int.mul_comm S 38, ← Int.add_mul]

theorem carryPass_go_value (acc : List Int) (carry : Int) (rest : List Int) :
    lval (carryPass.go acc carry rest).1
        + (carryPass.go acc carry rest).2 * w (carryPass.go acc carry rest).1.length
        = lval acc + carry * w acc.length + lval rest * w acc.length := by
  induction rest generalizing acc carry with
  | nil => simp [carryPass.go, lval]
  | cons c cs ih =>
      simp only [carryPass.go]
      let t := carry + c
      let digit := if t.emod 38 > 19 then t.emod 38 - 38 else t.emod 38
      have hv : lval (acc ++ [digit]) + ((t - digit) / 38) * w (acc ++ [digit]).length
            = lval acc + t * w acc.length := by
        simpa [digit, t] using drainCarry_step_value acc t
      rw [ih (acc ++ [digit]) ((t - digit) / 38)]
      rw [hv]
      simpa [lval, digit, t] using (carryPass_step_inv acc carry c (lval cs))

theorem carryPass_value (grid : List Int) :
    lval (carryPass grid).1 + (carryPass grid).2 * w (carryPass grid).1.length = lval grid := by
  unfold carryPass
  have h := carryPass_go_value ([] : List Int) (0 : Int) grid
  simpa [lval, w_zero] using h

theorem lval_modify (acc : List Int) (n : Nat) (v : Int) (hn : n < acc.length) :
    lval (acc.modify n (fun u => u + v)) = lval acc + v * w n := by
  induction acc generalizing n with
  | nil => simp at hn
  | cons h t ih =>
      cases n with
      | zero => simp [List.modify, lval, w_zero]; omega
      | succ m =>
          have hm : m < t.length := by
            have := hn
            simp at this
            omega
          have hiv := ih m hm
          have hfix : (h :: t).modify (m + 1) (fun u => u + v) = h :: t.modify m (fun u => u + v) := by
            simp [List.modify]
          rw [hfix]
          simp [lval]
          rw [hiv, w_succ]
          rw [Int.mul_add, ← Int.add_assoc, ← Int.mul_assoc, Int.mul_comm 38 v, Int.mul_assoc]

theorem rowMul_fac (a b S w : Int) :
    (a * b) * w + a * S * (38 * w) = a * (b + 38 * S) * w := by
  simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm,
        Int.mul_add, Int.add_mul,
        Int.add_assoc, Int.add_comm, Int.add_left_comm]

theorem mulRows_fac (b S a w : Int) :
    (b * a) * w + (S * a) * (38 * w) = (b + 38 * S) * a * w := by
  simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm,
        Int.mul_add, Int.add_mul,
        Int.add_assoc, Int.add_comm, Int.add_left_comm]

def addCell (acc : List Int) (pos : Nat) (v : Int) : List Int :=
  acc.modify pos (fun u => u + v)

def rowMul : List Int → Int → List Int → Nat → List Int
  | acc, a, [], i => acc
  | acc, a, b :: bs, i => rowMul (addCell acc i (a * b)) a bs (i + 1)

theorem rowMul_length (acc : List Int) (a : Int) (y : List Int) (i : Nat) :
    (rowMul acc a y i).length = acc.length := by
  induction y generalizing acc i with
  | nil => simp [rowMul]
  | cons b bs ih =>
      simp [rowMul, addCell, List.length_modify, ih]

theorem rowMul_value (acc : List Int) (a : Int) (y : List Int) (i : Nat)
    (hpos : i + y.length ≤ acc.length) :
    lval (rowMul acc a y i) = lval acc + a * lval y * w i := by
  induction y generalizing acc i with
  | nil => simp [rowMul, lval]
  | cons b bs ih =>
      have hi : i < acc.length := by
        have : i + (bs.length + 1) ≤ acc.length := by
          simpa using hpos
        omega
      have hv : lval (addCell acc i (a * b)) = lval acc + (a * b) * w i := by
        unfold addCell
        exact lval_modify acc i (a * b) hi
      have hposN : (i + 1) + bs.length ≤ (addCell acc i (a * b)).length := by
        simp [addCell, List.length_modify]
        have : i + (bs.length + 1) ≤ acc.length := by
          simpa using hpos
        omega
      have hrec := ih (addCell acc i (a * b)) (i + 1) hposN
      calc
        lval (rowMul acc a (b :: bs) i) = lval (rowMul (addCell acc i (a * b)) a bs (i + 1)) := rfl
        _ = lval (addCell acc i (a * b)) + a * lval bs * w (i + 1) := hrec
        _ = (lval acc + (a * b) * w i) + a * lval bs * w (i + 1) := by rw [hv]
        _ = lval acc + (a * b) * w i + a * lval bs * (38 * w i) := by rw [w_succ]
        _ = lval acc + a * lval (b :: bs) * w i := by
              rw [Int.add_assoc]
              rw [show lval (b :: bs) = b + 38 * lval bs by rfl]
              rw [rowMul_fac a b (lval bs) (w i)]

def mulRows : List Int → List Int → List Int → Nat → List Int
  | buf, [], y, i => buf
  | buf, b :: bs, y, i => mulRows (rowMul buf b y i) bs y (i + 1)

theorem mulRows_value (buf x y : List Int) (i : Nat)
    (hpos : i + x.length + y.length ≤ buf.length) :
    lval (mulRows buf x y i) = lval buf + lval x * lval y * w i := by
  induction x generalizing buf i with
  | nil => simp [mulRows, lval]
  | cons b bs ih =>
      have hposR : i + y.length ≤ buf.length := by
        have : i + (bs.length + 1) + y.length ≤ buf.length := by
          simpa using hpos
        omega
      have hrv : lval (rowMul buf b y i) = lval buf + b * lval y * w i := by
        exact rowMul_value buf b y i hposR
      have hlen : (rowMul buf b y i).length = buf.length := rowMul_length buf b y i
      have hposN : (i + 1) + bs.length + y.length ≤ (rowMul buf b y i).length := by
        rw [hlen]
        have : i + (bs.length + 1) + y.length ≤ buf.length := by
          simpa using hpos
        omega
      have hrec := ih (rowMul buf b y i) (i + 1) hposN
      calc
        lval (mulRows buf (b :: bs) y i) = lval (mulRows (rowMul buf b y i) bs y (i + 1)) := rfl
        _ = lval (rowMul buf b y i) + lval bs * lval y * w (i + 1) := hrec
        _ = (lval buf + b * lval y * w i) + lval bs * lval y * w (i + 1) := by rw [hrv]
        _ = lval buf + b * lval y * w i + lval bs * lval y * (38 * w i) := by rw [w_succ]
        _ = lval buf + lval (b :: bs) * lval y * w i := by
              rw [Int.add_assoc]
              rw [show lval (b :: bs) = b + 38 * lval bs by rfl]
              rw [mulRows_fac b (lval bs) (lval y) (w i)]

theorem lval_replicate_zero (n : Nat) : lval (List.replicate n (0 : Int)) = 0 := by
  induction n with
  | zero => simp [lval, List.replicate]
  | succ m ih => simp [lval, List.replicate, ih]

def gridMul (x y : List Int) : List Int :=
  mulRows (List.replicate (x.length + y.length) (0 : Int)) x y 0

theorem gridMul_value (x y : List Int) :
    lval (gridMul x y) = lval x * lval y := by
  unfold gridMul
  have hpos : 0 + x.length + y.length ≤ (List.replicate (x.length + y.length) (0 : Int)).length := by
    simp
  have h := mulRows_value (List.replicate (x.length + y.length) (0 : Int)) x y 0 hpos
  simp [w_zero, lval_replicate_zero] at h
  exact h

/-- Helper: build the product grid for multiplication, right-triangular
    accumulation into positions i + j. -/
def mulGrid (x y : Balanced38) : List Int := gridMul x.digits y.digits

theorem mulGrid_value (x y : Balanced38) :
    lval (mulGrid x y) = lval x.digits * lval y.digits := by
  unfold mulGrid
  exact gridMul_value x.digits y.digits

/-- THE SHORE BOUND, NOT THE REFUSAL: in this unbounded model the fold
    is total (`checked_to_i128_value`). The ≤24-place bound is proved
    (`shore_fold`); the 25+ refusal is the Rust runtime door, not a
    Lean theorem. -/
def checked_to_i128 (x : Balanced38) : Option Int :=
  if x.digits.length ≤ 24 then some (to_i128 x)
  else foldChecked x.digits

/-- THE SHORE ROAD DIVISION: folded to the i128 shore, one hardware division,
    walked back by the residue. The Euclidean remainder: r ∈ 0..|b|, the debt
    never signed. The identity a = q·b + r is carried through the lane's OWN
    mul and add, tested as a theorem. -/
def checked_div_rem (x y : Balanced38) : Option (Balanced38 × Balanced38) :=
  if y == zero then none
  else do
    let a ← checked_to_i128 x
    let b ← checked_to_i128 y
    let q := a.tdiv b
    let r := a.tmod b
    let (q, r) :=
      if r < 0 then
        if b > 0 then (q - 1, r + b)
        else (q + 1, r - b)
      else (q, r)
    some ({ digits := (from_i128 q).digits }, { digits := (from_i128 r).digits })

/-- The quotient alone. -/
def checked_div (x y : Balanced38) : Option Balanced38 :=
  do
    let (q, _) ← checked_div_rem x y
    some q

/-- The remainder alone. -/
def checked_rem (x y : Balanced38) : Option Balanced38 :=
  do
    let (_, r) ← checked_div_rem x y
    some r

/-- THE WHOLE STORE ON ONE HARDWARE STEP: the unlimited residue walk folds ANY
    Int back into a balanced string, digit-exactly — no 27-place window bound.
    (The founding 27-place `from_i128` stays as the windowed walk used by
    division; this walk is exact for every integer.) -/
def from_i128_full (v : Int) : Balanced38 :=
  { digits := drainCarry.go [] v }

/-- THE LANE'S SCHOOLBOOK MUL (kept as the verified reference): the signed grid
    multiplication, schoolbook on membrane digits. The tighter bound: cells ≤
    19·19 = 361 per contribution (26 places → 9,386 before carries) vs the dense
    grid's 37·37 = 1,369 (35,594). The carry pass is the rebalance signed:
    digit = t mod 38 folded into [-18, +19], carry = the exact (t − digit)/38.
    Kept for the trade-off record and as the fallback computation — the native
    fast path below reads back the same value. -/
def schoolbook_mul (x y : Balanced38) : Option Balanced38 :=
  if x == zero || y == zero then some zero
  else
    let grid := mulGrid x y
    let (digits, carry) := carryPass grid
    let digits := drainCarry digits carry
    let digits := trim_trailing digits
    if digits.length > 24 then
      match foldChecked digits with
      | some _ => some { digits := digits }
      | none => none
    else
      some { digits := digits }

/-- THE PRODUCT LAW IN NATIVE FORM: one hardware multiplication of the
    i128 readings, folded back digit-exactly by the unlimited residue
    walk. In this unbounded model it always returns `some`; the Rust door
    refuses beyond the shore. Same guaranteed value as schoolbook_mul
    (see product_law vs schoolbook_mul_value). -/
def checked_mul (x y : Balanced38) : Option Balanced38 :=
  if x == zero || y == zero then some zero
  else some (from_i128_full (to_i128 x * to_i128 y))

/-- THE DOUBLE REFLECTION IS THE IDENTITY: reflect(reflect(x)) = x
    For canonical inputs (no trailing zeros), double negation is exact.
    For non-canonical inputs, the trailing zeros are trimmed by negate. -/
theorem double_reflection_is_identity (x : Balanced38)
    (hx : ∀ d ∈ x.digits, in_range d) :
    negate (negate x) = { digits := trim_trailing x.digits } := by
  cases x with
  | mk L =>
      unfold negate
      rw [Balanced38.mk.injEq]
      let M := trim_trailing (negateDigits L 0)
      have hM : ∀ d ∈ M, in_range d := by
        apply trim_in_range
        exact negateDigits_in_range L 0 hx (by omega)
      apply canonical_unique
      · apply trim_in_range
        apply negateDigits_in_range M 0
        · exact hM
        · omega
      · apply trim_in_range
        exact hx
      · apply trim_no_trail
      · apply trim_no_trail
      · calc
          lval (trim_trailing (negateDigits M 0)) = lval (negateDigits M 0) := trim_value (negateDigits M 0)
          _ = 0 - lval M := negateDigits_value M 0
          _ = -(lval M) := by omega
          _ = -(lval (negateDigits L 0)) := by rw [trim_value]
          _ = -(0 - lval L) := by rw [negateDigits_value L 0]
          _ = lval L := by omega
          _ = lval (trim_trailing L) := (trim_value L).symm

/-- THE REFLECTION LAW: sub IS add-of-negation.
    x - y = x + (-y) -/
theorem sub_is_add_of_negation (x y : Balanced38) :
    sub x y = checked_add x (negate y) := by
  rfl

theorem to_i128_lval (x : Balanced38) : lval x.digits = to_i128 x := by
  unfold to_i128
  exact lval_eq_vl_reverse x.digits

theorem to_i128_neg (x : Balanced38) : to_i128 (negate x) = -to_i128 x := by
  rw [← to_i128_lval (negate x), ← to_i128_lval x]
  unfold negate
  rw [trim_value]
  rw [negateDigits_value]
  omega

/-- THE ADDITION LAW: addition reads back exactly — value of the sum is the sum
    of the values, for every pair, no window bound needed (the add is column-exact). -/
theorem checked_add_value (x y : Balanced38) : to_i128 (checked_add x y) = to_i128 x + to_i128 y := by
  unfold checked_add
  rw [← to_i128_lval { digits := trim_trailing (addDigits x.digits y.digits 0) }]
  rw [trim_value, addDigits_value]
  rw [← to_i128_lval x, ← to_i128_lval y]
  omega

/-- THE SUBTRACTION LAW: subtraction reads back exactly — value of the difference
    is the difference of the values. -/
theorem sub_value (x y : Balanced38) : to_i128 (sub x y) = to_i128 x - to_i128 y := by
  rw [sub_is_add_of_negation, checked_add_value, to_i128_neg]
  omega

theorem checked_mul_else_digits (digits : List Int) :
    (if digits.length > 24 then
       match foldChecked digits with
       | some _ => some ({ digits := digits } : Balanced38)
       | none => none
     else
       some ({ digits := digits } : Balanced38))
    = some ({ digits := digits } : Balanced38) := by
  have hf : foldChecked digits = some (lval digits) := foldChecked_value digits
  by_cases hl : digits.length > 24
  · simp [hl, hf]
  · simp [hl, hf]

/-- THE EXACT UNLIMITED FOLD: whatever enters the walk comes back. -/
theorem from_i128_full_value (v : Int) : to_i128 (from_i128_full v) = v := by
  unfold from_i128_full
  rw [← to_i128_lval { digits := drainCarry.go [] v }]
  rw [drainCarry_value]
  simp [lval, w_zero]

/-- THE PRODUCT LAW: the native fast path reads back the exact product for every
    pair — no digit-window assumption; hardware Int arithmetic is exact. -/
theorem product_law (x y : Balanced38) :
    Option.map (fun z => to_i128 z) (checked_mul x y) = Option.some (to_i128 x * to_i128 y) := by
  by_cases hz : (x == zero || y == zero) = true
  · have hxy : x = zero ∨ y = zero := by simpa using hz
    simp [checked_mul, hz]
    rcases hxy with hx | hy
    · rw [hx]
      simp [to_i128, zero]
    · rw [hy]
      simp [to_i128, zero]
  · simp [checked_mul, hz, from_i128_full_value]

/-- THE SCHOOLBOOK SENDS THE SAME PRODUCT: the grid-carries reference
    implementation is exactly equivalent to the native fast path, pair for pair. -/
theorem schoolbook_mul_value (x y : Balanced38) :
    Option.map (fun z => to_i128 z) (schoolbook_mul x y) = Option.some (to_i128 x * to_i128 y) := by
  by_cases hz : (x == zero || y == zero) = true
  · have hxy : x = zero ∨ y = zero := by simpa using hz
    simp [schoolbook_mul, hz]
    rcases hxy with hx | hy
    · rw [hx]
      simp [to_i128, zero]
    · rw [hy]
      simp [to_i128, zero]
  · simp [schoolbook_mul, hz]
    let t := trim_trailing (drainCarry (carryPass (mulGrid x y)).fst (carryPass (mulGrid x y)).snd)
    refine ⟨{ digits := t }, ?_, ?_⟩
    · exact checked_mul_else_digits t
    · dsimp [t]
      rw [← to_i128_lval { digits := t }]
      rw [trim_value]
      dsimp [drainCarry]
      rw [drainCarry_value]
      rw [carryPass_value]
      rw [mulGrid_value]
      rw [to_i128_lval, to_i128_lval]

/-- THE REFLECTION HOLDS IN MULTIPLICATION: (-x) * y = -(x * y) = x * (-y).
    Both mirrors, exhaustive. -/
theorem reflection_holds_in_multiplication (x y : Balanced38) :
    Option.map (fun z => to_i128 z) (checked_mul (negate x) y) = Option.some (-(to_i128 x * to_i128 y)) ∧
    Option.map (fun z => to_i128 z) (checked_mul x (negate y)) = Option.some (-(to_i128 x * to_i128 y)) := by
  constructor
  · rw [product_law (negate x) y, to_i128_neg x]
    simp [Int.neg_mul]
  · rw [product_law x (negate y), to_i128_neg y]
    simp [Int.mul_neg]

/- bridging: digit_of agrees with the (> 19) spelling used by drainCarry -/
theorem digit_of_eq (n : Int) :
    digit_of n = (if n.emod 38 > 19 then n.emod 38 - 38 else n.emod 38) := by
  unfold digit_of
  by_cases hn : n.emod 38 ≤ 19
  · have h' : ¬ n.emod 38 > 19 := by omega
    simp [hn, h']
  · have h' : n.emod 38 > 19 := by omega
    simp [hn, h']

theorem digit_of_range (n : Int) : -18 ≤ digit_of n ∧ digit_of n ≤ 19 := by
  have hd := digit_range (n.emod 38) (mod38_lo n) (mod38_hi n)
  unfold digit_of
  by_cases hn : n.emod 38 ≤ 19
  · have h : ¬ n.emod 38 > 19 := by omega
    simpa [hn, h] using hd
  · have h : n.emod 38 > 19 := by omega
    simpa [hn, h] using hd

theorem digit_of_carr (n : Int) :
    n = digit_of n + 38 * ((n - digit_of n) / 38) := by
  have hkeep :
      n = (if n.emod 38 > 19 then n.emod 38 - 38 else n.emod 38)
          + 38 * ((n - (if n.emod 38 > 19 then n.emod 38 - 38 else n.emod 38)) / 38) := by
    simpa using (digit_carr n)
  calc
    n = (if n.emod 38 > 19 then n.emod 38 - 38 else n.emod 38)
        + 38 * ((n - (if n.emod 38 > 19 then n.emod 38 - 38 else n.emod 38)) / 38) := hkeep
    _ = digit_of n + 38 * ((n - digit_of n) / 38) := by
      rw [digit_of_eq]

/-- THE RESIDUE WALK: the residue after k steps of the walk. -/
def resWalk : Int → Nat → Int
  | v, 0 => v
  | v, k + 1 => resWalk ((v - digit_of v) / 38) k

theorem resWalk_row (n : Int) (k : Nat) :
    resWalk n (k + 1) = resWalk ((n - digit_of n) / 38) k := by
  rfl

theorem resWalk_shift (n : Int) (k : Nat) :
    resWalk n (k + 1) = resWalk (resWalk n k) 1 := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      calc
        resWalk n (k + 2) = resWalk ((n - digit_of n) / 38) (k + 1) := by rw [resWalk_row]
        _ = resWalk (resWalk ((n - digit_of n) / 38) k) 1 := ih _
        _ = resWalk (resWalk n (k + 1)) 1 := by rw [← resWalk_row]

theorem resWalk_zero (k : Nat) : resWalk 0 k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hd : digit_of 0 = 0 := by
        unfold digit_of
        have hz : (0 : Int).emod 38 = 0 := by decide
        simp [hz]
      calc
        resWalk 0 (k + 1) = resWalk ((0 - digit_of 0) / 38) k := by rw [resWalk_row]
        _ = resWalk 0 k := by rw [hd]; simp
        _ = 0 := ih

theorem one_step_bound_abs (v : Int) :
    (resWalk v 1).natAbs * 38 ≤ v.natAbs + 19 := by
  rw [resWalk_row]
  by_cases hn : (v - digit_of v) = 0
  · simp [hn, resWalk]
  · let d := digit_of v
    let n' := (v - d) / 38
    have hdv : -18 ≤ d ∧ d ≤ 19 := by simpa [d] using (digit_of_range v)
    have hcd : v = d + 38 * n' := by
      simpa [d, n'] using (digit_of_carr v)
    have hvd : 38 * n' = v - d := by omega
    have h38 : (38 * n').natAbs ≤ v.natAbs + 19 := by
      rw [hvd]
      calc
        (v - d).natAbs ≤ v.natAbs + d.natAbs := Int.natAbs_sub_le v d
        _ ≤ v.natAbs + 19 := by
          have hdn : d.natAbs ≤ 19 := by
            apply natAbs_le_iff_bounds
            · omega
            · exact hdv.2
          omega
    have h38' : 38 * n'.natAbs ≤ v.natAbs + 19 := by
      have hh := h38
      rw [Int.natAbs_mul] at hh
      simpa [natAbs38] using hh
    have htarget : n'.natAbs * 38 ≤ v.natAbs + 19 := by omega
    simpa [d, n', resWalk] using htarget

theorem resWalk_step_abs (n : Int) (k : Nat) :
    (resWalk n (k + 1)).natAbs * 38 ≤ (resWalk n k).natAbs + 19 := by
  rw [resWalk_shift]
  exact one_step_bound_abs (resWalk n k)

/-- telescoped Nat chain: 37 * 38^k * |res k| ≤ 37 * |n| + 19 * (38^k - 1) -/
theorem resWalk_chain (n : Int) (k : Nat) :
    37 * (38 ^ k) * (resWalk n k).natAbs ≤ 37 * n.natAbs + 19 * (38 ^ k - 1) := by
  induction k with
  | zero =>
      simp [resWalk, Nat.pow_zero]
  | succ k ih =>
      have hs := resWalk_step_abs n k
      have h38 : 38 * (resWalk n (k + 1)).natAbs ≤ (resWalk n k).natAbs + 19 := by omega
      have hpow : 38 ^ (k + 1) = 38 * 38 ^ k := by
        rw [Nat.pow_succ]
        exact Nat.mul_comm (38 ^ k) 38
      calc
        37 * (38 ^ (k + 1)) * (resWalk n (k + 1)).natAbs
            = (37 * 38 ^ k) * (38 * (resWalk n (k + 1)).natAbs) := by
                rw [hpow]
                simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ (37 * 38 ^ k) * ((resWalk n k).natAbs + 19) := by
                exact Nat.mul_le_mul_left (37 * 38 ^ k) h38
        _ = (37 * 38 ^ k) * (resWalk n k).natAbs + (37 * 38 ^ k) * 19 := by
                rw [Nat.mul_add]
        _ ≤ 37 * n.natAbs + 19 * (38 ^ k - 1) + (37 * 38 ^ k) * 19 := by omega
        _ = 37 * n.natAbs + 19 * (38 * 38 ^ k - 1) := by
                have h19 : (37 * 38 ^ k) * 19 + 19 * (38 ^ k - 1) = 19 * (38 * 38 ^ k - 1) := by
                  omega
                omega
        _ = 37 * n.natAbs + 19 * (38 ^ (k + 1) - 1) := by
                rw [hpow]

theorem bound_25_num : 37 * (2 ^ 127 - 1) + 19 * (38 ^ 25 - 1) < 37 * 38 ^ 25 := by
  native_decide

-- ============================================================
-- A1 THE SHORE BOUND (ledger Phase 2 rung 1, 11 Sep): the lane's honest
-- door as a theorem. The largest ≤ 24-place membrane string is the all-19s
-- string 19·(38²⁴−1)/37 ≈ 4.2e37 < 2¹²⁷−1 — so every legal folded string
-- lands inside the i128 shore. (The refusal past the shore is the compiled
-- lane's runtime door, edge-tested; this file's Int is unbounded, so the
-- provable half here is the bound itself — the ledger's A1/A6 split.)
-- ============================================================

theorem shore_bound_num : 19 * (38 ^ 24 - 1) < 37 * (2 ^ 127 - 1) := by
  native_decide

theorem shore_bound_frac : 19 * (38 ^ 24 - 1) / 37 < 2 ^ 127 - 1 := by
  apply (Nat.div_lt_iff_lt_mul (k := 37) (x := 19 * (38 ^ 24 - 1)) (y := 2 ^ 127 - 1) (by native_decide : 0 < 37)).mpr
  exact shore_bound_num

/-- THE GEOMETRIC SUM: 1 + 38 + … + 38^(k−1), the all-19s string's digit sum.
    The shore bound's subtractive form is its 37-times-plus-one. -/
def geom : Nat → Nat
  | 0 => 0
  | k+1 => geom k + 38 ^ k

theorem geom_identity (k : Nat) : 37 * geom k + 1 = 38 ^ k := by
  induction k with
  | zero => simp [geom]
  | succ k ih =>
      simp [geom]
      rw [Nat.mul_add]
      calc
        37 * geom k + 37 * 38 ^ k + 1 = 38 ^ k + 37 * 38 ^ k := by
              rw [← ih]
              omega
        _ = 38 * 38 ^ k := by omega
        _ = 38 ^ (k + 1) := by
              rw [Nat.pow_succ, Nat.mul_comm]

theorem geom_succ_of_pos (k : Nat) (hk : 0 < k) : geom k = geom (k - 1) + 38 ^ (k - 1) := by
  cases k with
  | zero => exfalso; omega
  | succ n => simp [geom]

/-- THE MAGNITUDE: a k-or-fewer-place membrane string has |value| ≤ the
    all-19s string of k places, 19·(1 + 38 + … + 38^(k−1)) = 19·(38^k−1)/37.
    Division-free throughout — the geometric sum carries the width. -/
theorem lval_geom_bound (k : Nat) (l : List Int)
    (hlen : l.length ≤ k) (hmax : ∀ d ∈ l, in_range d) :
    Int.natAbs (lval l) ≤ 19 * geom k := by
  induction l generalizing k with
  | nil => simp [lval, geom]
  | cons d rest ih_l =>
      by_cases hk0 : k = 0
      · subst k
        exfalso
        have hless : rest.length + 1 ≤ 0 := by
          simpa [List.length_cons] using hlen
        omega
      · have hkpos : 0 < k := by omega
        have hrest_len : rest.length ≤ k - 1 := by
          have hless : rest.length + 1 ≤ k := by
            simpa [List.length_cons] using hlen
          have hcalc : (rest.length + 1) - 1 ≤ k - 1 := Nat.sub_le_sub_right hless 1
          simpa [Nat.add_sub_cancel] using hcalc
        have hrest_max : ∀ d ∈ rest, in_range d := in_range_of_cons hmax
        have hd : in_range d := hmax d (by simp)
        have hv : Int.natAbs (lval rest) ≤ 19 * geom (k - 1) :=
          ih_l (k - 1) hrest_len hrest_max
        have hdabs : Int.natAbs d ≤ 19 := by
          apply natAbs_le_iff_bounds
          · unfold in_range at hd
            omega
          · unfold in_range at hd
            omega
        have htri := Int.natAbs_add_le d (38 * lval rest)
        have hmul : (38 * lval rest).natAbs = 38 * (lval rest).natAbs := by
          simpa [natAbs38] using (Int.natAbs_mul (38 : Int) (lval rest))
        have htri38 : (d + 38 * lval rest).natAbs ≤ d.natAbs + 38 * (lval rest).natAbs := by
          simpa [hmul] using htri
        calc
          Int.natAbs (lval (d :: rest))
              = ((d + 38 * lval rest).natAbs) := by rfl
          _ ≤ d.natAbs + 38 * (lval rest).natAbs := htri38
          _ ≤ 19 + 38 * (19 * geom (k - 1)) := by
              exact Nat.add_le_add hdabs (Nat.mul_le_mul_left 38 hv)
          _ ≤ 19 * (1 + 38 * geom (k - 1)) := by
              rw [Nat.mul_add]
              simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
          _ ≤ 19 * (geom (k - 1) + 38 ^ (k - 1)) := by
              have ht : 1 + 38 * geom (k - 1) ≤ geom (k - 1) + 38 ^ (k - 1) := by
                have hg := geom_identity (k - 1)
                rw [← hg]
                omega
              exact Nat.mul_le_mul_left 19 ht
          _ = 19 * geom k := by
              rw [geom_succ_of_pos k hkpos]

/-- THE SHORE FOLD: every ≤ 24-place membrane string folds inside the i128
    shore — its absolute value is < 2^127, the walker's own precondition. -/
theorem shore_fold (l : List Int) (hlen : l.length ≤ 24) (hmax : ∀ d ∈ l, in_range d) :
    Int.natAbs (lval l) < 2 ^ 127 := by
  have hb : Int.natAbs (lval l) ≤ 19 * geom 24 := lval_geom_bound 24 l hlen hmax
  have hb37 : 37 * Int.natAbs (lval l) ≤ 19 * (38 ^ 24 - 1) := by
    have hg := geom_identity 24
    calc
      37 * Int.natAbs (lval l) ≤ 37 * (19 * geom 24) := by
              exact Nat.mul_le_mul_left 37 hb
      _ = 19 * (37 * geom 24) := by omega
      _ ≤ 19 * (38 ^ 24 - 1) := by
              rw [← hg]
              simp
  have h37 : 37 * Int.natAbs (lval l) < 37 * (2 ^ 127 - 1) := by
    exact Nat.lt_of_le_of_lt hb37 shore_bound_num
  have hc : Int.natAbs (lval l) < 2 ^ 127 - 1 := by
    exact (Nat.mul_lt_mul_left (a := 37) (by native_decide : 0 < 37)).mp h37
  omega

/-- THE SAME DOOR, ON STORED MEMBRANE STRINGS: the store's digits are List Int
    with the membrane invariant declared (not enforced) — so the theorem's
    contract carries the invariant as a premise: in_range digits and ≤ 24
    places means |value| < 2^127, the walker's own precondition. -/
theorem shore_fold_stored (x : Balanced38) (hlen : x.digits.length ≤ 24)
    (hmax : ∀ d ∈ x.digits, in_range d) :
    Int.natAbs (lval x.digits) < 2 ^ 127 := by
  exact shore_fold x.digits hlen hmax

/-- and the fold's door in read-back terms: |to_i128 x| < 2^127. -/
theorem shore_fold_to_i128 (x : Balanced38) (hlen : x.digits.length ≤ 24)
    (hmax : ∀ d ∈ x.digits, in_range d) :
    Int.natAbs (to_i128 x) < 2 ^ 127 := by
  rw [← to_i128_lval]
  exact shore_fold_stored x hlen hmax

theorem nat_lt_one_of_mul_lt (a c : Nat) (hc : 0 < c) (h : c * a < c) : a = 0 := by
  cases a with
  | zero => rfl
  | succ a =>
      have : c * (a + 1) < c := h
      have hx : c * a + c < c := by simpa [Nat.mul_succ] using this
      omega

theorem resWalk_bound (n : Int) (hn : n.natAbs < 2 ^ 127) :
    resWalk n 25 = 0 := by
  have hc := resWalk_chain n 25
  have hle : n.natAbs ≤ 2 ^ 127 - 1 := by omega
  have hnum : 37 * n.natAbs + 19 * (38 ^ 25 - 1) < 37 * 38 ^ 25 := by
    have h1 : 37 * n.natAbs ≤ 37 * (2 ^ 127 - 1) := by
      exact Nat.mul_le_mul_left 37 hle
    have h2 : 37 * n.natAbs + 19 * (38 ^ 25 - 1) ≤ 37 * (2 ^ 127 - 1) + 19 * (38 ^ 25 - 1) := by
      exact Nat.add_le_add_right h1 (19 * (38 ^ 25 - 1))
    exact Nat.lt_of_le_of_lt h2 bound_25_num
  have hmul : 37 * (38 ^ 25) * (resWalk n 25).natAbs < 37 * (38 ^ 25) := by
    exact Nat.lt_of_le_of_lt hc hnum
  have hAbs : (resWalk n 25).natAbs = 0 := nat_lt_one_of_mul_lt (resWalk n 25).natAbs (37 * 38 ^ 25)
    (by native_decide : 0 < 37 * 38 ^ 25) hmul
  exact Int.natAbs_eq_zero.mp hAbs

theorem resWalk_zero_past (n : Int) (k j : Nat) :
    resWalk n k = 0 → resWalk n (k + j) = 0 := by
  induction j with
  | zero => intro h; simpa using h
  | succ j ih =>
      intro h
      have h0 : resWalk n (k + j) = 0 := ih h
      have hs := resWalk_shift n (k + j)
      rw [← Nat.add_assoc]
      rw [hs, h0]
      have hz : resWalk 0 1 = 0 := by
        rw [resWalk_row]
        have hd : digit_of 0 = 0 := by
          unfold digit_of
          have hz : (0 : Int).emod 38 = 0 := by decide
          simp [hz]
        rw [hd]
        simp [resWalk]
      simpa using hz

/-- one drain step while the carry is alive: low digit out, quotient in -/
theorem drainCarry_step (acc : List Int) (c : Int) (hc : c ≠ 0) :
    drainCarry.go acc c = drainCarry.go (acc ++ [digit_of c]) ((c - digit_of c) / 38) := by
  rw [go_eq acc c]
  rw [dif_neg hc]
  dsimp
  rw [← digit_of_eq]

/-- once the walk is spent the chunked two-digit walk coincides with drainCarry -/
theorem from_i128_eq_drain (n : Int) (acc : List Int) (k : Nat) (hk : resWalk n k = 0) :
    from_i128.go n acc k = drainCarry.go acc n := by
  induction k generalizing n acc with
  | zero =>
      have hn0 : n = 0 := by simpa [resWalk] using hk
      subst n
      simp [from_i128.go]
      rw [go_eq acc 0]
      simp
  | succ k ih =>
      by_cases hn : n = 0
      · subst n
        simp [from_i128.go]
        rw [go_eq acc 0]
        simp
      · let d0 := digit_of n
        let n1 := (n - d0) / 38
        have hstep1 : drainCarry.go acc n = drainCarry.go (acc ++ [d0]) n1 := by
          simpa [d0, n1] using (drainCarry_step acc n hn)
        have hk1 : resWalk n1 k = 0 := by
          rw [resWalk_row] at hk
          simpa [n1, d0] using hk
        by_cases hn1 : n1 = 0
        · have hleft : from_i128.go n acc (k + 1) = from_i128.go 0 (acc ++ [d0]) k := by
            dsimp only [d0, n1] at hn1 ⊢
            simp [from_i128.go, hn1]
          have hlf : from_i128.go 0 (acc ++ [d0]) k = acc ++ [d0] := by
            cases k <;> simp [from_i128.go]
          have hrgt : drainCarry.go (acc ++ [d0]) 0 = acc ++ [d0] := by
            rw [go_eq (acc ++ [d0]) 0]
            simp
          rw [hleft, hlf, hstep1, hn1]
          exact hrgt.symm
        · let d1 := digit_of n1
          let n2 := (n1 - d1) / 38
          have hk2 : resWalk n2 k = 0 := by
            by_cases hk0 : k = 0
            · subst k
              have hnz : n1 = 0 := by simpa [resWalk] using hk1
              exact False.elim (hn1 hnz)
            · let j := k - 1
              have hs : j + 1 = k := by omega
              have h1 : resWalk n1 (j + 1) = 0 := by
                simpa [← hs] using hk1
              have hr := resWalk_row n1 j
              have h2 : resWalk n2 j = 0 := by
                rw [hr] at h1
                simpa [n2, d1] using h1
              have h3 := resWalk_zero_past n2 j 1 h2
              simpa [hs] using h3
          have hbridge := ih n2 (acc ++ [d0] ++ [d1]) hk2
          have hleft : from_i128.go n acc (k + 1) = from_i128.go n2 (acc ++ [d0] ++ [d1]) k := by
            simp [from_i128.go, d0, n1, hn1, d1, n2]
          have hstep2 : drainCarry.go (acc ++ [d0]) n1 = drainCarry.go (acc ++ [d0] ++ [d1]) n2 := by
            simpa [d1, n2] using (drainCarry_step (acc ++ [d0]) n1 hn1)
          rw [hleft, hbridge, ← hstep2, ← hstep1]

/-- the residue walk reads back the input: lval (from_i128.go n [] 27) = n -/
theorem from_i128_value_list (n : Int) (hn : n.natAbs < 2 ^ 127) :
    lval (from_i128.go n [] 27) = n := by
  have h0 : resWalk n 27 = 0 := by
    refine resWalk_zero_past n 25 2 ?_
    exact resWalk_bound n hn
  have heq := from_i128_eq_drain n [] 27 h0
  rw [heq]
  have hd := drainCarry_value ([] : List Int) n
  simpa [lval, w_zero] using hd

/-- the shore door always tells the truth -/
theorem checked_to_i128_value (x : Balanced38) : checked_to_i128 x = some (to_i128 x) := by
  unfold checked_to_i128
  by_cases hlen : x.digits.length ≤ 24
  · simp [hlen]
  · have hf := foldChecked_value x.digits
    simp [hlen, hf, to_i128_lval]

/-- the store is faithful for everything that fits: to_i128 (from_i128 v) = v -/
theorem from_i128_value (v : Int) (hv : v.natAbs < 2 ^ 127) : to_i128 (from_i128 v) = v := by
  unfold from_i128
  by_cases hvz : v = 0
  · subst v
    simp [zero, to_i128]
  · simp [hvz]
    rw [← to_i128_lval { digits := from_i128.go v [] 27 }]
    exact from_i128_value_list v hv

/-- the formality loop closes: a canonical number reproduces its own digit string.
    together with `from_i128_value` this upgrades `to_i128` from a left inverse
    to a full section-retraction pair on the canonical / in-window numbers. -/
theorem from_i128_canonical (x : Balanced38)
    (hfit : (to_i128 x).natAbs < 2 ^ 127)
    (hdg : ∀ d ∈ x.digits, in_range d)
    (htr : no_trail x.digits) :
    from_i128 (to_i128 x) = x := by
  unfold from_i128
  by_cases hv : to_i128 x = 0
  · have hlv : lval x.digits = 0 := by
      rw [to_i128_lval]
      exact hv
    have hnil : x.digits = [] := val_zero_implies_nil hdg htr hlv
    have hxeq : (fun l : List Int => ({ digits := l } : Balanced38)) x.digits =
        (fun l : List Int => ({ digits := l } : Balanced38)) [] := by
      rw [hnil]
    rw [hv]
    simp
    exact hxeq.symm
  · have hlists : from_i128.go (to_i128 x) [] 27 = x.digits := by
      apply canonical_unique
      · have h0 : resWalk (to_i128 x) 27 = 0 := by
          refine resWalk_zero_past (to_i128 x) 25 2 ?_
          exact resWalk_bound (to_i128 x) hfit
        have hbr := from_i128_eq_drain (to_i128 x) [] 27 h0
        rw [hbr]
        exact drainCarry_go_in_range (to_i128 x) [] (by simp)
      · exact hdg
      · have h0 : resWalk (to_i128 x) 27 = 0 := by
          refine resWalk_zero_past (to_i128 x) 25 2 ?_
          exact resWalk_bound (to_i128 x) hfit
        have hbr := from_i128_eq_drain (to_i128 x) [] 27 h0
        rw [hbr]
        exact drainCarry_go_no_trail [] (to_i128 x) hv
      · exact htr
      · rw [from_i128_value_list (to_i128 x) hfit, to_i128_lval]
    simp [hv]
    exact congrArg (fun l => ({ digits := l } : Balanced38)) hlists

-- =================== THE FAST WALK BRIDGE ===================

/-- the fast walk carries the same digits as the founding walk: while the
    founding walk appends, the fast walk prepends — the invariant is
    fast.go n acc k = (go n acc.reverse k).reverse -/
theorem from_i128_fast_go_eq (n : Int) (acc : List Int) (k : Nat) :
    from_i128_fast.go n acc k = (from_i128.go n acc.reverse k).reverse := by
  induction k generalizing n acc with
  | zero =>
      simp [from_i128.go, from_i128_fast.go]
  | succ k ih =>
      by_cases hn : n = 0
      · subst n
        simp [from_i128.go, from_i128_fast.go]
      · let d0 := digit_of n
        let n1 := (n - d0) / 38
        by_cases hn1 : n1 = 0
        · have hfast : from_i128_fast.go n acc (k + 1) = d0 :: acc := by
            dsimp only [d0, n1] at hn1 ⊢
            simp [from_i128_fast.go, hn1]
            cases k <;> simp [from_i128_fast.go]
          have hgo : from_i128.go n acc.reverse (k + 1) = acc.reverse ++ [d0] := by
            dsimp only [d0, n1] at hn1 ⊢
            simp [from_i128.go, hn1]
            cases k <;> simp [from_i128.go]
          rw [hfast, hgo]
          simp
        · let d1 := digit_of n1
          let n2 := (n1 - d1) / 38
          have hfast : from_i128_fast.go n acc (k + 1) = from_i128_fast.go n2 (d1 :: d0 :: acc) k := by
            dsimp only [d0, n1, d1, n2] at hn1 ⊢
            simp [from_i128_fast.go, hn1, d0, n1, d1, n2]
          have hgo : from_i128.go n acc.reverse (k + 1) = from_i128.go n2 (acc.reverse ++ [d0] ++ [d1]) k := by
            dsimp only [d0, n1, d1, n2] at hn1 ⊢
            simp [from_i128.go, hn1, d0, n1, d1, n2]
          have hih := ih n2 (d1 :: d0 :: acc)
          rw [hfast, hgo, hih]
          simp [List.reverse_cons, List.append_assoc]

/-- the fast door opens on the same digits as the founding door -/
theorem from_i128_fast_eq_from_i128 (v : Int) : from_i128_fast v = from_i128 v := by
  unfold from_i128_fast from_i128
  by_cases hv : v = 0
  · subst v
    rfl
  · simp [hv]
    rw [from_i128_fast_go_eq v [] 27]
    simp

/-- the fast door tells the same truth: value round-trip in the window -/
theorem from_i128_fast_value (v : Int) (hv : v.natAbs < 2 ^ 127) : to_i128 (from_i128_fast v) = v := by
  rw [from_i128_fast_eq_from_i128]
  exact from_i128_value v hv

/-- the formality loop closes on the fast walk too -/
theorem from_i128_fast_canonical (x : Balanced38)
    (hfit : (to_i128 x).natAbs < 2 ^ 127)
    (hdg : ∀ d ∈ x.digits, in_range d)
    (htr : no_trail x.digits) :
    from_i128_fast (to_i128 x) = x := by
  rw [from_i128_fast_eq_from_i128]
  exact from_i128_canonical x hfit hdg htr

/-- the honest division identity: the adjusted pair reproduces the dividend -/
theorem div_rem_identity (a b : Int) (hb : b ≠ 0) :
    let q0 := a.tdiv b
    let r0 := a.tmod b
    (if r0 < 0 then (if b > 0 then q0 - 1 else q0 + 1) else q0) * b +
      (if r0 < 0 then (if b > 0 then r0 + b else r0 - b) else r0) = a := by
  intro q0 r0
  have hdiv : a = q0 * b + r0 := (Int.tdiv_mul_add_tmod a b).symm
  by_cases hr : r0 < 0
  · by_cases hbgt : b > 0
    · have hx : (q0 - 1) * b + (r0 + b) = a := by
        calc
          (q0 - 1) * b + (r0 + b) = (q0 * b - b) + (r0 + b) := by
                rw [Int.sub_mul]
                simp
          _ = q0 * b + r0 := by omega
          _ = a := hdiv.symm
      simpa [hr, hbgt] using hx
    · have hx : (q0 + 1) * b + (r0 - b) = a := by
        calc
          (q0 + 1) * b + (r0 - b) = (q0 * b + b) + (r0 - b) := by
                rw [Int.add_mul]
                simp
          _ = q0 * b + r0 := by omega
          _ = a := hdiv.symm
      simpa [hr, hbgt] using hx
  · have hx : q0 * b + r0 = a := by omega
    simpa [hr] using hx

theorem div_rem_identity_imp (a b : Int) :
    let q0 := a.tdiv b
    let r0 := a.tmod b
    b ≠ 0 →
      (if r0 < 0 then (if b > 0 then q0 - 1 else q0 + 1) else q0) * b +
        (if r0 < 0 then (if b > 0 then r0 + b else r0 - b) else r0) = a := by
  intro q0 r0 hb
  exact div_rem_identity a b hb

-- ============================================================
-- A4 THE EUCLIDEAN BAND (ledger Phase 2 rung 3, 11 Sep): the lane's
-- remainder never signs. The truncated remainder stays inside |b| (four
-- arms, one per sign-shape of the tmod match); after the Euclidean
-- adjustment the lane's remainder rests in 0..|b| — the debt settled,
-- the band the Rust asserts made a theorem.
-- ============================================================

theorem tmod_band (a b : Int) (hb : b ≠ 0) :
    Int.natAbs (a.tmod b) < b.natAbs := by
  cases b with
  | ofNat n =>
      have hn : 0 < n := by
        by_cases hn0 : n = 0
        · subst n
          exfalso
          apply hb
          simp
        · omega
      cases a with
      | ofNat m =>
          simp [Int.tmod]
          have hgoal : ((m : Int) % (n : Int)).natAbs < n := by
            have hlt := Int.emod_lt (m : Int) (b := (n : Int)) (by exact hb)
            have hz : 0 ≤ ((m : Int) % (n : Int)) := Int.emod_nonneg (m : Int) (b := (n : Int)) (by exact hb)
            have hnn : 0 ≤ (n : Int) := by omega
            have hnabs : ((n : Int).natAbs : Int) = (n : Int) := Int.natAbs_of_nonneg hnn
            have hna : (((m : Int) % (n : Int)).natAbs : Int) = ((m : Int) % (n : Int)) := Int.natAbs_of_nonneg hz
            omega
          exact hgoal
      | negSucc m =>
          simp [Int.tmod]
          have hgoal : (((m + 1 : Nat) : Int) % (n : Int)).natAbs < n := by
            have hlt := Int.emod_lt ((m + 1 : Nat) : Int) (b := (n : Int)) (by exact hb)
            have hz : 0 ≤ (((m + 1 : Nat) : Int) % (n : Int)) := Int.emod_nonneg ((m + 1 : Nat) : Int) (b := (n : Int)) (by exact hb)
            have hnn : 0 ≤ (n : Int) := by omega
            have hnabs : ((n : Int).natAbs : Int) = (n : Int) := Int.natAbs_of_nonneg hnn
            have hna : ((((m + 1 : Nat) : Int) % (n : Int)).natAbs : Int) = (((m + 1 : Nat) : Int) % (n : Int)) := Int.natAbs_of_nonneg hz
            omega
          exact hgoal
  | negSucc n =>
      cases a with
      | ofNat m =>
          simp [Int.tmod]
          have hgoal : ((m : Int) % ((n : Int) + 1)).natAbs < n + 1 := by
            have hnz : ((n : Int) + 1) ≠ 0 := by
              intro hz
              have : n.succ = 0 := by exact_mod_cast hz
              omega
            have hlt := Int.emod_lt (m : Int) (b := ((n : Int) + 1)) hnz
            have hz : 0 ≤ ((m : Int) % ((n : Int) + 1)) := Int.emod_nonneg (m : Int) (b := ((n : Int) + 1)) hnz
            have hnn : 0 ≤ ((n : Int) + 1) := by omega
            have hnabs : (((n : Int) + 1).natAbs : Int) = ((n : Int) + 1) := Int.natAbs_of_nonneg hnn
            have hna : (((m : Int) % ((n : Int) + 1)).natAbs : Int) = ((m : Int) % ((n : Int) + 1)) := Int.natAbs_of_nonneg hz
            omega
          exact hgoal
      | negSucc m =>
          simp [Int.tmod]
          have hgoal : (((m + 1 : Nat) : Int) % ((n : Int) + 1)).natAbs < n + 1 := by
            have hnz : ((n : Int) + 1) ≠ 0 := by
              intro hz
              have : n.succ = 0 := by exact_mod_cast hz
              omega
            have hlt := Int.emod_lt ((m + 1 : Nat) : Int) (b := ((n : Int) + 1)) hnz
            have hz : 0 ≤ (((m + 1 : Nat) : Int) % ((n : Int) + 1)) := Int.emod_nonneg ((m + 1 : Nat) : Int) (b := ((n : Int) + 1)) hnz
            have hnn : 0 ≤ ((n : Int) + 1) := by omega
            have hnabs : (((n : Int) + 1).natAbs : Int) = ((n : Int) + 1) := Int.natAbs_of_nonneg hnn
            have hna : ((((m + 1 : Nat) : Int) % ((n : Int) + 1)).natAbs : Int) = (((m + 1 : Nat) : Int) % ((n : Int) + 1)) := Int.natAbs_of_nonneg hz
            omega
          exact hgoal

theorem div_rem_euclidean_band (a b : Int) (hb : b ≠ 0) :
    let r0 := a.tmod b
    0 ≤ (if r0 < 0 then (if b > 0 then r0 + b else r0 - b) else r0) ∧
      (if r0 < 0 then (if b > 0 then r0 + b else r0 - b) else r0) < b.natAbs := by
  intro r0
  have hbnd := tmod_band a b hb
  have hnzb : 0 < b.natAbs := by
    by_cases hz : b.natAbs = 0
    · have hb0 : b = 0 := Int.natAbs_eq_zero.mp hz
      exfalso
      exact hb hb0
    · omega
  have hlow : -(b.natAbs : Int) < r0 := by
    by_cases hrc : r0 < 0
    · have habs : (r0.natAbs : Int) = -r0 := by
        have h := Int.natAbs_of_nonneg (a := -r0) (by omega)
        simpa [Int.natAbs_neg] using h
      have hbndi : (r0.natAbs : Int) < (b.natAbs : Int) := by
        exact_mod_cast hbnd
      omega
    · have hn0 : 0 ≤ r0 := by omega
      omega
  have hhigh : r0 < b.natAbs := by
    by_cases hrc : r0 < 0
    · omega
    · have habs : (r0.natAbs : Int) = r0 := Int.natAbs_of_nonneg (by omega)
      have hbndi : (r0.natAbs : Int) < (b.natAbs : Int) := by
        exact_mod_cast hbnd
      omega
  by_cases hr : r0 < 0
  · by_cases hbgt : b > 0
    · have hbabs : (b.natAbs : Int) = b := Int.natAbs_of_nonneg (by omega)
      have hlow' : -b < r0 := by
        simpa [hbabs] using hlow
      have hhigh' : r0 < b := by
        simpa [hbabs] using hhigh
      constructor
      · omega
      · omega
    · have hbabs : (b.natAbs : Int) = -b := by
        calc
          (b.natAbs : Int) = ((-b).natAbs : Int) := by rw [Int.natAbs_neg]
          _ = -b := Int.natAbs_of_nonneg (by omega)
      have hlow' : b < r0 := by
        simpa [hbabs] using hlow
      have hhigh' : r0 < -b := by
        simpa [hbabs] using hhigh
      constructor
      · omega
      · omega
  · constructor
    · omega
    · simpa [hr] using hhigh

/-- THE IDENTITY THROUGH THE LANE: the shore division q·b + r = a, witnessed
    inside the lane's own fold. Whenever both operands fold, the division data
    q, r computed by the lane obey a = q·b + r (given b ≠ 0). -/
theorem identity_carries_through_the_lane (x y : Balanced38) :
    (do let a ← checked_to_i128 x
        let b ← checked_to_i128 y
        let q0 := a.tdiv b
        let r0 := a.tmod b
        let (q, r) := if r0 < 0 then (if b > 0 then (q0 - 1, r0 + b) else (q0 + 1, r0 - b)) else (q0, r0)
        some (b ≠ 0 → q * b + r = a)) = some True := by
  rw [checked_to_i128_value x, checked_to_i128_value y]
  simp
  have h := div_rem_identity_imp (to_i128 x) (to_i128 y)
  by_cases ht : (to_i128 x).tmod (to_i128 y) < 0
  · by_cases hb : 0 < to_i128 y
    · intro hyz
      simpa [ht, hb] using h hyz
    · intro hyz
      simpa [ht, hb] using h hyz
  · intro hyz
    simpa [ht] using h hyz

/-- THE HONEST TWO-OVER-TWO THEOREM (Knuth TAOCP 4.3.1):
    the aligned trial quotient for division by one digit
      U = u2·B + u1            top two digits of the working window, u2,u1 < B
      v = v1·B + v0            top two digits of the divisor, 1 ≤ v1, v0 < B
      W = U·B + u0 < v·B       per-step window bound, u0 < B
      q  = W / v               true per-step digit (q ≤ B − 1)
      q̂  = min (U / v1) (B − 1)   trial digit, capped at the digit range
    then, whenever the divisor is normalized (2·v1 ≥ B):
      q ≤ q̂ ≤ q + 2.
    The estimate never underestimates; it may overestimate by at most 2.
 -/
theorem two_over_two_bound (B u2 u1 u0 v1 v0 : Nat)
    (hB : 2 ≤ B) (hv1 : 0 < v1) (hnorm : B ≤ 2 * v1)
    (hu2 : u2 < B) (hu1 : u1 < B) (hu0 : u0 < B) (hv0 : v0 < B)
    (hW : (u2 * B + u1) * B + u0 < (v1 * B + v0) * B) :
    let U := u2 * B + u1
    let v := v1 * B + v0
    let W := U * B + u0
    let q := W / v
    let qh := Nat.min (U / v1) (B - 1)
    q ≤ qh ∧ qh ≤ q + 2 := by
  let U := u2 * B + u1
  let v := v1 * B + v0
  let W := U * B + u0
  let q := W / v
  have hB0 : 0 < B := by omega
  have hvpos : 0 < v1 * B + v0 := by
    have p : 0 < v1 * B := Nat.mul_pos hv1 hB0
    omega
  have hqB : W / v < B := by
    apply (Nat.div_lt_iff_lt_mul hvpos).mpr
    rw [Nat.mul_comm]
    dsimp [W, U, v]
    exact hW
  have hqBm1 : W / v ≤ B - 1 := by
    have hs : (W / v) + 1 ≤ B := Nat.succ_le_of_lt hqB
    omega
  have hq1B : q + 1 ≤ B := by
    apply Nat.succ_le_of_lt
    dsimp [q]
    exact hqB
  have hqvdv : q * (v1 * B) ≤ W := by
    have hvb : v1 * B ≤ v := by dsimp [v]; omega
    have hqvm : q * v ≤ W := by
      have hm := Nat.mul_div_le W v
      have hflip : v * q ≤ W := by simpa [Nat.mul_comm, Nat.mul_assoc] using hm
      simpa [Nat.mul_comm, Nat.mul_assoc] using hflip
    calc q * (v1 * B) ≤ q * v := Nat.mul_le_mul_left q hvb
      _ ≤ W := hqvm
  have hULt : W < (U + 1) * B := by
    dsimp [W, U]
    have h1 : (u2 * B + u1) * B + u0 < (u2 * B + u1) * B + B :=
      Nat.add_lt_add_left hu0 ((u2 * B + u1) * B)
    have hmm : (u2 * B + u1) * B + 1 * B = ((u2 * B + u1) + 1) * B := by
      rw [← Nat.right_distrib]
    have heq : (u2 * B + u1) * B + B = ((u2 * B + u1) + 1) * B := by
      simpa using hmm
    exact Nat.lt_of_lt_of_le h1 (Nat.le_of_eq heq)
  have hqUv1 : q * v1 < U + 1 := by
    have hqBv1 : (q * v1) * B < (U + 1) * B := by
      have hqvdv' : (q * v1) * B ≤ W := by simpa [Nat.mul_assoc] using hqvdv
      exact Nat.lt_of_le_of_lt hqvdv' hULt
    exact Nat.lt_of_mul_lt_mul_right hqBv1
  have hqU : q ≤ U / v1 := by
    rw [Nat.le_div_iff_mul_le hv1]
    exact Nat.lt_succ_iff.mp hqUv1
  have hqBm1' : q ≤ B - 1 := by dsimp [q]; exact hqBm1
  have hqM : q ≤ Nat.min (U / v1) (B - 1) := by
    exact Nat.le_min.mpr ⟨hqU, hqBm1'⟩
  have hskip : U / v1 ≤ q + 2 := by
    by_cases hle : U / v1 ≤ q + 2
    · exact hle
    · have hbig : q + 3 ≤ U / v1 := by omega
      have hUge : (q + 3) * v1 ≤ U := (Nat.le_div_iff_mul_le hv1).mp hbig
      have hWge : (q + 3) * v1 * B ≤ W := by
        have h1 : (q + 3) * v1 * B ≤ U * B := Nat.mul_le_mul_right B hUge
        have h2 : U * B ≤ W := by dsimp [W, U]; omega
        exact Nat.le_trans h1 h2
      have hWlt : W < (q + 1) * v := by
        apply (Nat.div_lt_iff_lt_mul hvpos).mp
        dsimp [q]
        exact Nat.lt_succ_self (W / v)
      have hboth : (q + 3) * v1 * B < (q + 1) * v := Nat.lt_of_le_of_lt hWge hWlt
      have hElem : (q + 1) * v1 * B + 2 * v1 * B < (q + 1) * v1 * B + (q + 1) * v0 := by
        dsimp [v] at hboth
        have hL : (q + 1) * v1 * B + 2 * v1 * B = (q + 3) * v1 * B := by
          rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
          rw [← Nat.right_distrib]
        have hR : (q + 1) * v1 * B + (q + 1) * v0 = (q + 1) * (v1 * B + v0) := by
          rw [Nat.mul_assoc]
          rw [← Nat.left_distrib]
        rw [← hL] at hboth
        rw [← hR] at hboth
        exact hboth
      have hc2 : 2 * v1 * B < (q + 1) * v0 := Nat.lt_of_add_lt_add_left hElem
      have hc3 : (q + 1) * v0 < (q + 1) * B :=
        Nat.mul_lt_mul_of_pos_left (by omega : v0 < B) (Nat.succ_pos q)
      have hc4 : (q + 1) * B ≤ B * B := Nat.mul_le_mul_right B hq1B
      have hc5 : 2 * v1 * B < B * B := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hc2 (Nat.le_of_lt hc3)) hc4
      have hc6 : 2 * v1 < B := by
        have hflip : B * (2 * v1) < B * B := by simpa [Nat.mul_comm, Nat.mul_assoc] using hc5
        exact Nat.lt_of_mul_lt_mul_left hflip
      exact False.elim (by omega : False)
  have hcap : ¬ U / v1 ≤ B - 1 → B - 1 ≤ q + 2 := by
    intro hnot
    have hBlt : B ≤ U / v1 := by omega
    have hBU : B * v1 ≤ U := (Nat.le_div_iff_mul_le hv1).mp hBlt
    have hWge : B * v1 * B ≤ W := by
      have h1 : B * v1 * B ≤ U * B := Nat.mul_le_mul_right B hBU
      have h2 : U * B ≤ W := by dsimp [W, U]; omega
      exact Nat.le_trans h1 h2
    have hBall : (B - 2) * (B - 1) ≤ 2 * v1 * B := by
      calc (B - 2) * (B - 1) ≤ B * B := Nat.mul_le_mul (by omega : B - 2 ≤ B) (by omega : B - 1 ≤ B)
        _ ≤ (2 * v1) * B := Nat.mul_le_mul_right B hnorm
        _ = 2 * v1 * B := rfl
    have hfin : (B - 2) * (v1 * B) + 2 * v1 * B = B * (v1 * B) := by
      rw [Nat.mul_assoc]
      rw [← Nat.right_distrib]
      have hs : (B - 2) + 2 = B := by omega
      rw [hs]
    have hqv2 : (B - 2) * v ≤ B * (v1 * B) := by
      calc (B - 2) * v = (B - 2) * (v1 * B + v0) := by dsimp [v]
        _ = (B - 2) * (v1 * B) + (B - 2) * v0 := by rw [Nat.left_distrib]
        _ ≤ (B - 2) * (v1 * B) + (B - 2) * (B - 1) :=
            Nat.add_le_add_left (Nat.mul_le_mul_left (B - 2) (by omega : v0 ≤ B - 1)) ((B - 2) * (v1 * B))
        _ ≤ (B - 2) * (v1 * B) + 2 * v1 * B := Nat.add_le_add_left hBall ((B - 2) * (v1 * B))
        _ = B * (v1 * B) := hfin
    have hb1 : B * (v1 * B) ≤ W := by simpa [Nat.mul_assoc] using hWge
    have hqvW : (B - 2) * v ≤ W := Nat.le_trans hqv2 hb1
    have hq2 : B - 2 ≤ W / (v1 * B + v0) := by
      have hqvW' : (B - 2) * (v1 * B + v0) ≤ W := by simpa [v] using hqvW
      exact (Nat.le_div_iff_mul_le hvpos).mpr hqvW'
    have hq2v : B - 2 ≤ W / v := by simpa [v] using hq2
    dsimp [q]
    omega
  have hqhp : Nat.min (U / v1) (B - 1) ≤ q + 2 := by
    by_cases hc : U / v1 ≤ B - 1
    · have hminl : Nat.min (U / v1) (B - 1) = U / v1 := Nat.min_eq_left hc
      omega
    · have hc' : B - 1 ≤ U / v1 := by omega
      have hminr : Nat.min (U / v1) (B - 1) = B - 1 := Nat.min_eq_right hc'
      omega
  exact ⟨hqM, hqhp⟩

-- ============================================================
-- A5 ADD-SIDE (appended here so every cited definition precedes):
-- the scribe's add keeps every digit in the membrane (each column is the
-- rebalance of a bounded t, A3's bounds, so the digit lands in range and
-- the carry stays ±1 down the whole walk), and the trim then closes both
-- canonical laws for the composite output.
-- ============================================================

theorem addDigits_in_range : ∀ a b : List Int, ∀ c : Int,
    (∀ d ∈ a, in_range d) → (∀ d ∈ b, in_range d) → (-1 ≤ c ∧ c ≤ 1) →
      (∀ e ∈ (addDigits a b c), in_range e) := by
  intro a
  induction a with
  | nil =>
      intro b
      induction b with
      | nil =>
          intro c ha hb hc
          rw [addDigits]
          exact drain_small_in_range c hc
      | cons b0 brest ihb =>
          intro c ha hb hc
          rw [addDigits]
          intro e he
          simp at he
          rcases he with he | he
          · rw [he]
            have hb0 : in_range 0 := by
              unfold in_range
              omega
            have hbd : -37 ≤ 0 + b0 + c ∧ 0 + b0 + c ≤ 39 :=
              column_sum_bounds 0 b0 c hb0 (by exact (hb b0 (by simp))) hc
            have hbnd : -37 ≤ c + b0 ∧ c + b0 ≤ 39 := by omega
            have hinv := rebalance_invariant (c + b0) hbnd.1 hbnd.2
            exact hinv.1
          · have hb0 : in_range 0 := by
              unfold in_range
              omega
            have hbd : -37 ≤ 0 + b0 + c ∧ 0 + b0 + c ≤ 39 :=
              column_sum_bounds 0 b0 c hb0 (by exact (hb b0 (by simp))) hc
            have hbnd : -37 ≤ c + b0 ∧ c + b0 ≤ 39 := by omega
            have hinv := rebalance_invariant (c + b0) hbnd.1 hbnd.2
            exact ihb (rebalance (c + b0)).2 ha (by intro d hd; exact hb d (by simp [hd])) hinv.2 e he
  | cons a0 arest iha =>
      intro b
      cases b with
      | nil =>
          intro c ha hb hc
          rw [addDigits]
          intro e he
          simp at he
          rcases he with he | he
          · rw [he]
            have hb0 : in_range 0 := by
              unfold in_range
              omega
            have ha0 : in_range 0 := by
              unfold in_range
              omega
            have hbd : -37 ≤ 0 + a0 + c ∧ 0 + a0 + c ≤ 39 :=
              column_sum_bounds 0 a0 c hb0 (by exact (ha a0 (by simp))) hc
            have hbnd : -37 ≤ c + a0 ∧ c + a0 ≤ 39 := by omega
            have hinv := rebalance_invariant (c + a0) hbnd.1 hbnd.2
            exact hinv.1
          · have hb0 : in_range 0 := by
              unfold in_range
              omega
            have hbd : -37 ≤ 0 + a0 + c ∧ 0 + a0 + c ≤ 39 :=
              column_sum_bounds 0 a0 c hb0 (by exact (ha a0 (by simp))) hc
            have hbnd : -37 ≤ c + a0 ∧ c + a0 ≤ 39 := by omega
            have hinv := rebalance_invariant (c + a0) hbnd.1 hbnd.2
            exact iha [] (rebalance (c + a0)).2 (by intro d hd; exact ha d (by simp [hd])) hb hinv.2 e he
      | cons b0 brest =>
          intro c ha hb hc
          rw [addDigits]
          intro e he
          simp at he
          rcases he with he | he
          · rw [he]
            have hbd : -37 ≤ a0 + b0 + c ∧ a0 + b0 + c ≤ 39 :=
              column_sum_bounds a0 b0 c (by exact (ha a0 (by simp))) (by exact (hb b0 (by simp))) hc
            have hbnd : -37 ≤ c + a0 + b0 ∧ c + a0 + b0 ≤ 39 := by omega
            have hinv := rebalance_invariant (c + a0 + b0) hbnd.1 hbnd.2
            exact hinv.1
          · have hbd : -37 ≤ a0 + b0 + c ∧ a0 + b0 + c ≤ 39 :=
              column_sum_bounds a0 b0 c (by exact (ha a0 (by simp))) (by exact (hb b0 (by simp))) hc
            have hbnd : -37 ≤ c + a0 + b0 ∧ c + a0 + b0 ≤ 39 := by omega
            have hinv := rebalance_invariant (c + a0 + b0) hbnd.1 hbnd.2
            exact iha brest (rebalance (c + a0 + b0)).2 (by intro d hd; exact ha d (by simp [hd])) (by intro d hd; exact hb d (by simp [hd])) hinv.2 e he

/-- THE ADD'S OUTPUT IS CANONICAL: the trim preserves the membrane (it keeps
    in_range and ends on no gap), so the scribe's add lands both laws. -/
theorem checked_add_canonical (x y : Balanced38)
    (hx : ∀ d ∈ x.digits, in_range d) (hy : ∀ d ∈ y.digits, in_range d) :
    (∀ d ∈ (checked_add x y).digits, in_range d) ∧ no_trail (checked_add x y).digits := by
  unfold checked_add
  have hrange := addDigits_in_range x.digits y.digits 0 hx hy (by simp : -1 ≤ (0 : Int) ∧ (0 : Int) ≤ 1)
  constructor
  · exact trim_in_range (addDigits x.digits y.digits 0) hrange
  · exact trim_no_trail (addDigits x.digits y.digits 0)

-- ============================================================
-- A5 NATIVE-LANE SIDE (appended with the add-side, after the
-- from_i128_eq_drain bridge): the mul's output and the residue walk's
-- output are canonical once the walk is spent.
-- ============================================================

/-- A5's engine for the native lane: ONCE the residue walk is spent (residue
    zero at the 27th step), the walk's output IS the drain's output, and the
    drain's proven range/no-trail laws carry the canonicality. -/
theorem from_i128_walk_canonical (v : Int) (hk : resWalk v 27 = 0) :
    (∀ d ∈ (from_i128 v).digits, in_range d) ∧ no_trail (from_i128 v).digits := by
  unfold from_i128
  by_cases hvz : v = 0
  · subst v
    simp [zero]
    intro t h he
    cases t with
    | nil => simp at he
    | cons x rest => simp at he
  · simp [hvz]
    have heq := from_i128_eq_drain v [] 27 hk
    rw [heq]
    constructor
    · exact drainCarry_go_in_range v [] (by simp)
    · exact drainCarry_go_no_trail ([] : List Int) v hvz

/-- THE MUL'S OUTPUT IS CANONICAL: the native product fold IS the drain's
    walk, whose range and no-trail laws are the primitives this rung glues. -/
theorem checked_mul_canonical (x y : Balanced38) :
    match checked_mul x y with
    | some z => (∀ d ∈ z.digits, in_range d) ∧ no_trail z.digits
    | none => True := by
  unfold checked_mul
  by_cases hb0 : x = zero
  · simp [hb0, zero]
    intro t h he
    cases t with
    | nil => simp at he
    | cons x rest => simp at he
  · by_cases hb1 : y = zero
    · simp [hb0, hb1, zero]
      intro t h he
      cases t with
      | nil => simp at he
      | cons x rest => simp at he
    · simp [hb0, hb1]
      unfold from_i128_full
      constructor
      · exact drainCarry_go_in_range (to_i128 x * to_i128 y) [] (by simp)
      · by_cases hz : to_i128 x * to_i128 y = 0
        · rw [hz]
          rw [go_eq]
          simp
          intro t h he
          cases t with
          | nil => simp at he
          | cons x rest => simp at he
        · exact drainCarry_go_no_trail ([] : List Int) (to_i128 x * to_i128 y) hz

-- ============================================================
-- A2 THE STACK-FIT BOUND (ledger Phase 2 rung 5, 11 Sep): the inline
-- store holds every legal lane string. The membrane's place-count at
-- |v| < 38^k is ≤ k+1 (the drain's minimality differs from logs by one
-- at the band edges), so the lane's whole population — every |v| ≤ 2^128
-- the add can touch, the negate, the mul and the div's pairs — folds into
-- ≤ 26 places. The in-window 25-place bound is A1's fitness (24 places
-- get inside i128); the 26th place exists precisely to hold the carry.
-- ============================================================

/-- the two boundary facts of the base-38 lane -/
theorem two127_lt_38_25 : (2 : Nat) ^ 127 < 38 ^ 25 := by
  native_decide

theorem two128_lt_38_25 : (2 : Nat) ^ 128 < 38 ^ 25 := by
  native_decide

/-- a 38·x bounded by a sub-38 slack is pinned to zero: the finite cases -/
theorem nat_pin20 (x : Nat) (h : 38 * x ≤ 20) : x = 0 := by
  cases x with
  | zero => rfl
  | succ n =>
      exfalso
      have hmm : 38 * n + 38 ≤ 20 := by
        rw [Nat.mul_succ] at h
        exact h
      omega

theorem nat_pin1 (x : Nat) (h : 38 * x ≤ 1) : x = 0 := by
  exact nat_pin20 x (by omega)

/-- the successor-side pow split, without the commutator carousel -/
theorem pow38_again (n k : Nat) (h : k = n + 1) : 38 ^ k = 38 * 38 ^ n := by
  subst k
  rw [Nat.pow_succ]
  ac_rfl

/- THE PLACE BOUND, accumulator-invariant form: a value at |v| ≤ 38^k needs
    at most k+1 MORE membrane places than the accumulator already holds. One
    step of the drain sheds 38·|carry| ≤ 38^k + 19, and the multiple-of-38
    pin lands it at most 38^k; the carry's own places then fold at k − 1,
    plus this digit. -/
theorem drainCarry_places_acc (acc : List Int) (v : Int) (k : Nat) (h : v.natAbs ≤ 38 ^ k) :
    (drainCarry.go acc v).length ≤ acc.length + k + 1 := by
  let P : Int → Prop := fun v => ∀ acc : List Int, ∀ k : Nat,
    v.natAbs ≤ 38 ^ k → (drainCarry.go acc v).length ≤ acc.length + k + 1
  have hP : P v := by
    refine @WellFounded.induction Int (fun a b : Int => a.natAbs < b.natAbs) natAbsWF P v ?_
    intro c ih acc k hk
    rw [go_eq]
    by_cases hz : c = 0
    · simp [hz]
      omega
    · rw [dif_neg hz]
      dsimp
      let digit := if c.emod 38 > 19 then c.emod 38 - 38 else c.emod 38
      let nxt := (c - digit) / 38
      have hcd : c = digit + 38 * nxt := by
        simpa [digit, nxt] using (digit_carr c)
      have hdec := drainCarryStep_dec c hz
      have hdgt := digit_range (c.emod 38) (mod38_lo c) (mod38_hi c)
      have hdigit : -18 ≤ digit ∧ digit ≤ 19 := by
        simpa [digit, in_range] using hdgt
      have hdabs : digit.natAbs ≤ 19 := by
        apply natAbs_le_iff_bounds
        · omega
        · exact hdigit.2
      have hm3 : (38 * nxt).natAbs = 38 * nxt.natAbs := by
        simpa [natAbs38] using (Int.natAbs_mul (38 : Int) nxt)
      have h1 : 38 * nxt.natAbs ≤ c.natAbs + digit.natAbs := by
        have hh := Int.natAbs_sub_le c digit
        have hcminus : c - digit = 38 * nxt := by omega
        rw [hcminus] at hh
        simpa [hm3] using hh
      have h38 : 38 * nxt.natAbs ≤ 38 ^ k := by
        by_cases hk0 : k = 0
        · subst k
          have hle20 : 38 * nxt.natAbs ≤ 20 := by omega
          rw [nat_pin20 nxt.natAbs hle20]
          simp [Nat.pow_zero]
        · have hle19 : 38 * nxt.natAbs ≤ 38 ^ k + 19 := by omega
          by_cases hgt : 38 ^ k < 38 * nxt.natAbs
          · have hmo : (38 * nxt.natAbs) % 38 = 0 := by
              rw [Nat.mul_mod_right]
            have hkp : (38 ^ k) % 38 = 0 := by
              cases k with
              | zero => omega
              | succ n =>
                  rw [Nat.pow_succ, Nat.mul_comm, Nat.mul_mod_right]
            have hsmall : 38 * nxt.natAbs - 38 ^ k < 38 := by
              have hle : 38 * nxt.natAbs - 38 ^ k ≤ 19 := by omega
              omega
            have hne0 : 38 * nxt.natAbs - 38 ^ k ≠ 0 := by omega
            have hdm : (38 ^ k + (38 * nxt.natAbs - 38 ^ k)) % 38 = 0 := by
              have hd : 38 ^ k + (38 * nxt.natAbs - 38 ^ k) = 38 * nxt.natAbs := by omega
              rw [hd]
              exact hmo
            have hdm2 : (38 ^ k + (38 * nxt.natAbs - 38 ^ k)) % 38 = 38 * nxt.natAbs - 38 ^ k := by
              have hself : (38 * nxt.natAbs - 38 ^ k) % 38 = 38 * nxt.natAbs - 38 ^ k :=
                Nat.mod_eq_of_lt hsmall
              rw [Nat.add_mod, hkp, Nat.zero_add]
              rw [hself]
              exact hself
            have hz : 38 * nxt.natAbs - 38 ^ k = 0 := by
              rw [← hdm2]
              exact hdm
            omega
          · omega
      have hsmall : nxt.natAbs ≤ 38 ^ (k - 1) := by
        by_cases hk0 : k = 0
        · subst k
          have hle1 : 38 * nxt.natAbs ≤ 1 := h38
          rw [nat_pin1 nxt.natAbs hle1]
          simp
        · by_cases hle : nxt.natAbs ≤ 38 ^ (k - 1)
          · exact hle
          · exfalso
            have hgt : 38 ^ (k - 1) + 1 ≤ nxt.natAbs := by omega
            have hm := Nat.mul_le_mul_left 38 hgt
            have hp := pow38_again (k - 1) k (by omega : k = (k - 1) + 1)
            have hbig : 38 * 38 ^ (k - 1) + 38 ≤ 38 * nxt.natAbs := by
              rw [Nat.mul_add] at hm
              exact hm
            rw [hp] at h38
            omega
      have hlen : (drainCarry.go (acc ++ [digit]) nxt).length ≤ (acc ++ [digit]).length + (k - 1) + 1 := by
        exact ih nxt hdec (acc ++ [digit]) (k - 1) hsmall
      by_cases hk0f : k = 0
      · subst k
        have hle1f : 38 * nxt.natAbs ≤ 1 := h38
        have hnf : nxt.natAbs = 0 := nat_pin1 nxt.natAbs hle1f
        have hnz : nxt = 0 := Int.natAbs_eq_zero.mp hnf
        rw [hnz] at hlen
        simp [go_eq, List.length_cons, Nat.zero_add] at hlen
        have hg : (drainCarry.go (acc ++ [digit]) nxt).length ≤ (acc ++ [digit]).length := by
          rw [hnz]
          rw [go_eq]
          simp
        have hc2k : (acc ++ [digit]).length = acc.length + 1 := by
          rw [List.length_append, List.length_cons, List.length_nil]
        rw [hc2k] at hg
        omega
      · have hlen' : (drainCarry.go (acc ++ [digit]) nxt).length ≤ acc.length + k + 1 := by
          have hlen2 : (drainCarry.go (acc ++ [digit]) nxt).length ≤ (acc ++ [digit]).length + k := by
            have htr : (drainCarry.go (acc ++ [digit]) nxt).length + (k - 1) + 1 =
                (drainCarry.go (acc ++ [digit]) nxt).length + k := by omega
            omega
          have hc2 : (acc ++ [digit]).length = acc.length + 1 := by
            rw [List.length_append, List.length_cons, List.length_nil]
          rw [hc2] at hlen2
          omega
        exact hlen'
  exact hP acc k h

/-- THE PLACE BOUND at the empty accumulator: the digits of v. -/
theorem drainCarry_places (v : Int) (k : Nat) (h : v.natAbs ≤ 38 ^ k) :
    (drainCarry.go [] v).length ≤ k + 1 := by
  have hlen := drainCarry_places_acc ([] : List Int) v k h
  simpa using hlen

/-- the i128 population fits the store -/
theorem stack_fit_i128 (v : Int) (hv : v.natAbs < 2 ^ 127) :
    (drainCarry.go [] v).length ≤ 26 := by
  have h38 : v.natAbs ≤ 38 ^ 25 := by
    have h1 : v.natAbs ≤ 2 ^ 127 - 1 := by omega
    have h2 : 2 ^ 127 - 1 ≤ 38 ^ 25 := by omega
    exact Nat.le_trans h1 h2
  have hlen := drainCarry_places v 25 h38
  simpa using hlen

/-- ADD'S STACK-FIT: the sum of two in-store values needs no more than the
    26th place — the inline store holds it, at worst for the carry. -/
theorem add_fits_26 (a b : Int) (ha : a.natAbs < 2 ^ 127) (hb : b.natAbs < 2 ^ 127) :
    (a + b).natAbs < 2 ^ 128 := by
  have h1 : a.natAbs + b.natAbs < 2 ^ 128 := by omega
  have h2 : (a + b).natAbs ≤ a.natAbs + b.natAbs := Int.natAbs_add_le a b
  omega

-- ============================================================

-- ============================================================
-- B8 THE EVEN-BASE TRANSPOSITION LAW (ledger Phase 2 rung 6, 11 Sep):
-- an alternating-weight digit check (weights ±1) turns an adjacent swap
-- into a checksum jump of ±2·(d−e); for an EVEN base b the modulus b+1
-- is odd, so a vanished jump mod (b+1) would force |d−e| to be a positive
-- multiple of (b+1) — impossible for two distinct digits. Base-19 (odd,
-- modulus 20) loses exactly the |d−e| = 10 class: 18 misses out of 342,
-- the measured 94.74%.
-- ============================================================

/-- the checksum's jump under an adjacent swap: with the canonical
    alternating weights ±1, the pair's contribution change is ±2·(d−e). -/
theorem transposition_delta_alt (d e : Int) :
    (d - e) - (e - d) = 2 * (d - e) := by
  omega

/-- an odd modulus cannot divide twice any positive x below it: a vanished
    jump means |d−e| is a positive multiple of b+1 — out of digit range. -/
theorem odd_mod_no_twice (b x : Nat) (hb2 : b % 2 = 0) (hx0 : 0 < x) (hxs : x < b + 1) :
    ¬(b + 1 ∣ 2 * x) := by
  intro hdiv
  rcases hdiv with ⟨q, hq⟩
  have hq_base := hq
  have hbodd : (b + 1) % 2 = 1 := by
    have hbd2 : b = 2 * (b / 2) := by
      have hd := Nat.div_add_mod b 2
      rw [hb2] at hd
      simpa [Nat.zero_add] using hd.symm
    rw [hbd2, Nat.add_mod]
    have hA : (2 * (b / 2)) % 2 = 0 := by
      exact Nat.mul_mod_right 2 (b / 2)
    rw [hA]
  have hqeven : q % 2 = 0 := by
    have hq0 := hq
    rw [Nat.mul_comm (b + 1) q] at hq0
    have h0 : (q * (b + 1)) % 2 = 0 := by
      rw [← hq0]
      exact Nat.mul_mod_right 2 x
    have hm : (q * (b + 1)) % 2 = (q % 2) * ((b + 1) % 2) % 2 := by
      rw [Nat.mul_mod, Nat.mul_mod]
    rw [hm, hbodd] at h0
    simp at h0
    have hlt2 : q % 2 < 2 := Nat.mod_lt q (by omega : 0 < 2)
    omega
  have hq2e : q = 2 * (q / 2) := by
    have hd := Nat.div_add_mod q 2
    rw [hqeven] at hd
    simpa [Nat.zero_add] using hd.symm
  have hsplit : 2 * x = 2 * ((b + 1) * (q / 2)) := by
    let c := q / 2
    have hq2e' : 2 * c = q := by
      change 2 * (q / 2) = q
      exact hq2e.symm
    calc
      2 * x = (b + 1) * q := hq_base
      _ = (b + 1) * (2 * c) := by rw [← hq2e']
      _ = 2 * ((b + 1) * c) := by rw [Nat.mul_left_comm]
      _ = 2 * ((b + 1) * (q / 2)) := by
        simp [c]
  have hxeq : x = (b + 1) * (q / 2) := by
    exact Nat.mul_left_cancel (by native_decide : 0 < 2) hsplit
  have hbig : b + 1 ≤ x := by
    rw [hxeq]
    have hone : 1 ≤ q / 2 := by
      by_cases hq0 : q / 2 = 0
      · exfalso
        rw [hq0] at hxeq
        omega
      · omega
    have hmul := Nat.mul_le_mul_left (b + 1) hone
    simpa using hmul
  omega

/-- THE DETECTION LAW: for an even base, every adjacent swap of distinct
    digits ⟨d e⟩ leaves the alternating check unsettled. -/
theorem even_base_adjacent_detection (b d e : Nat)
    (hb2 : b % 2 = 0) (hd : d < b) (he : e < b) (hne : d ≠ e) :
    ¬(b + 1 ∣ 2 * (d - e)) ∨ ¬(b + 1 ∣ 2 * (e - d)) := by
  by_cases hdge : d ≥ e
  · left
    have hx : 0 < d - e := by omega
    have hxs : d - e < b + 1 := by omega
    exact odd_mod_no_twice b (d - e) hb2 hx hxs
  · right
    have hx : 0 < e - d := by omega
    have hxs : e - d < b + 1 := by omega
    exact odd_mod_no_twice b (e - d) hb2 hx hxs

/-- THE 19s, counted: 324 of 342 ordered distinct pairs are caught — the
    18 lost are the |d−e| = 10 class, and 324/342 = 18/19 = 94.74%. -/
theorem rate19_witness : 324 * 19 = 342 * 18 := by
  native_decide

theorem rate19_floor : (324 * 10000) / 342 = 9473 := by
  native_decide

-- ============================================================
-- ============================================================
-- ============================================================
-- B9 THE SINGLE-DIGIT DETECTION RATES (ledger Phase 2 rung 7, 11 Sep):
-- the free digit-sum check (sum mod (b−1)) catches a single-digit
-- corruption d → d′ iff (b−1) does not divide the digit difference. The
-- ONLY misses are the extreme pairs 0 ↔ b−1: for base-38, 1404 of 1406
-- pairs are caught = 99.86%; for base-19, 340 of 342 = 99.42% — the
-- ledger's "94.74%" for 19 was the TRANSPOSITION rate copied in. Finding
-- logged with the proof. (Nat subtraction truncates, so the divided
-- difference is stated as the disjunction over both orders.)
-- ============================================================

/-- the classification, ascending case: a non-zero multiple of (b−1) at
    most (b−1) forces the digit pair to be the extremes. -/
theorem diff_mult_extreme (b d d' : Nat) (hb1 : 1 < b)
    (hd : d < b) (hd' : d' < b) (hle : d' ≥ d) :
    (∃ q : Nat, q ≠ 0 ∧ d' - d = q * (b - 1)) → (d = 0 ∧ d' = b - 1) := by
  intro hdiv
  rcases hdiv with ⟨q, hq0, hq⟩
  have hle1 : d' - d ≤ b - 1 := by omega
  have hmin2 : ¬(2 ≤ q) := by
    intro h2
    have hm2 := Nat.mul_le_mul_left (b - 1) (by omega : 2 ≤ q)
    have hq' := hq
    rw [Nat.mul_comm q (b - 1)] at hq'
    rw [hq'.symm] at hm2
    have h2l : 2 * (b - 1) ≤ b - 1 := by omega
    omega
  have hq1 : q = 1 := by
    by_cases hq1c : q = 1
    · exact hq1c
    · have hq1lt : 1 < q := by
        have hnz : q ≠ 0 := hq0
        omega
      omega
  subst q
  simp at hq
  have hd0 : d = 0 := by omega
  have hd1 : d' = b - 1 := by omega
  exact ⟨hd0, hd1⟩

/-- the classification, full: if EITHER order of the difference is a
    (b−1)-multiple, the pair is the extreme one — and so exactly two
    ordered misses exist per base. -/
theorem single_digit_miss_class (b d d' : Nat) (hb1 : 1 < b)
    (hd : d < b) (hd' : d' < b) (hne : d ≠ d') :
    (((d' ≥ d ∧ (b - 1) ∣ (d' - d)) ∨ (d ≥ d' ∧ (b - 1) ∣ (d - d')))) ↔
    (d = 0 ∧ d' = b - 1 ∨ d = b - 1 ∧ d' = 0) := by
  constructor
  · intro hde
    rcases hde with hf | hb
    · rcases hf with ⟨hge, hdiv⟩
      rcases hdiv with ⟨q, hq⟩
      have hqz : q ≠ 0 := by
        intro hq0
        subst q
        simp at hq
        omega
      have hw : d' - d = q * (b - 1) := by
        rw [Nat.mul_comm (b - 1) q] at hq
        exact hq
      left
      exact diff_mult_extreme b d d' hb1 hd hd' hge ⟨q, hqz, hw⟩
    · rcases hb with ⟨hge, hdiv⟩
      rcases hdiv with ⟨q, hq⟩
      have hqz : q ≠ 0 := by
        intro hq0
        subst q
        simp at hq
        omega
      have hw : d - d' = q * (b - 1) := by
        rw [Nat.mul_comm (b - 1) q] at hq
        exact hq
      have hx := diff_mult_extreme b d' d hb1 hd' hd hge ⟨q, hqz, hw⟩
      rcases hx with ⟨hx2, hx1⟩
      right
      exact ⟨hx1, hx2⟩
  · intro hcase
    rcases hcase with hp | hp
    · rcases hp with ⟨hd0, hd1⟩
      subst d
      subst d'
      left
      have hge0 : b - 1 ≥ 0 := by omega
      exact ⟨hge0, ⟨1, by simp⟩⟩
    · rcases hp with ⟨hd1, hd0⟩
      subst d
      subst d'
      right
      have hge0 : b - 1 ≥ 0 := by omega
      exact ⟨hge0, ⟨1, by simp⟩⟩

theorem rate38_floor : 1404 * 10000 / 1406 = 9985 := by
  native_decide

theorem rate19_single_floor : 340 * 10000 / 342 = 9941 := by
  native_decide

theorem rate19_not_transposition : (324 * 10000) / 342 ≠ (340 * 10000) / 342 := by
  native_decide

-- ============================================================
-- ============================================================
-- B7 THE WRAPPED RESIDUE SYSTEM, AS LEMMAS (ledger Phase 2 rung 8, 11 Sep):
-- R7's ruling made literal. The balanced set IS the WRAPPED residue
-- system: the offset is position-dependent (dense 20 reads −18, not +20);
-- the mirrors pin the bijection with the dense alphabet; and the walk
-- wraps by the very same rule.
-- ============================================================

/-- the distinguishing case of the wrap: dense 20 reads −18. -/
theorem wrapped_20 : membrane_digit 20 = -18 := by
  simp [membrane_digit]

/-- the wrap never leaves the membrane: every dense digit 0..37 lands in
    the balanced set. -/
theorem membrane_in_range (n : Nat) (hn : n < 38) : in_range (membrane_digit n) := by
  unfold membrane_digit in_range
  by_cases h : n ≥ 20
  · omega
  · omega

/-- the round trip, one way: the dense digit of the wrapped reading is
    the dense digit it came from. -/
theorem membrane_dense_mirror (n : Nat) (hn : n < 38) :
    dense_digit (membrane_digit n) = n := by
  by_cases h : n ≥ 20
  · have hw : membrane_digit n = (n : Int) - 38 := by simp [membrane_digit, h]
    rw [hw]
    unfold dense_digit
    have hc : (n : Int) - 38 < 0 := by omega
    have hm : ((n : Int) - 38 + 38).toNat = n := by
      have hnn : 0 ≤ (n : Int) - 38 + 38 := by omega
      have hh := Int.toNat_of_nonneg (a := (n : Int) - 38 + 38) hnn
      have hring : (n : Int) - 38 + 38 = (n : Int) := by omega
      rw [hring] at hh
      simpa using hh
    simp [dense_digit, hc, hm]
  · have hw : membrane_digit n = (n : Int) := by simp [membrane_digit, h]
    rw [hw]
    unfold dense_digit
    have hc : ¬(n : Int) < 0 := by omega
    have hm : (n : Int).toNat = n := by
      have hnn : 0 ≤ (n : Int) := by omega
      have hh := Int.toNat_of_nonneg (a := (n : Int)) hnn
      simpa using hh
    simp [dense_digit, hc, hm]

/-- the round trip, the other way: wrapping the dense reading of a
    balanced digit returns it exactly. -/
theorem dense_membrane_mirror (d : Int) (hd : in_range d) :
    membrane_digit (dense_digit d) = d := by
  unfold in_range at hd
  by_cases hneg : d < 0
  · have hto : (↑((d + 38).toNat)) = d + 38 := by
      have hnn : 0 ≤ d + 38 := by omega
      simpa using (Int.toNat_of_nonneg (a := d + 38) hnn)
    have hbig : (d + 38).toNat ≥ 20 := by
      have hgi : (20 : Int) ≤ ↑(d + 38).toNat := by
        rw [hto]
        omega
      omega
    have hw : ((d + 38).toNat : Int) - 38 = d := by omega
    unfold membrane_digit dense_digit
    simp [hneg, hto, hbig]
  · have hto : (↑d.toNat) = d := by
      have hnn : 0 ≤ d := by omega
      simpa using (Int.toNat_of_nonneg (a := d) hnn)
    have hnbig : ¬(d.toNat ≥ 20) := by
      intro hb
      have hgi : (20 : Int) ≤ ↑d.toNat := by exact_mod_cast hb
      rw [hto] at hgi
      omega
    unfold membrane_digit dense_digit
    simp [hneg, hto, hnbig]

/-- the dense reading of a balanced digit stays inside 0..37. -/
theorem dense_digit_range (d : Int) (hd : in_range d) : dense_digit d < 38 := by
  unfold in_range at hd
  by_cases hneg : d < 0
  · have hto : (↑((d + 38).toNat)) = d + 38 := by
      have hnn : 0 ≤ d + 38 := by omega
      simpa using (Int.toNat_of_nonneg (a := d + 38) hnn)
    unfold dense_digit
    simp [hneg]
    omega
  · have hto : (↑d.toNat) = d := by
      have hnn : 0 ≤ d := by omega
      simpa using (Int.toNat_of_nonneg (a := d) hnn)
    unfold dense_digit
    simp [hneg]
    omega

theorem membrane_is_wrapped_range : ∀ d : Int, in_range d ↔ ∃ n : Nat, n < 38 ∧ membrane_digit n = d := by
  intro d
  constructor
  · intro hd
    exists dense_digit d
    constructor
    · exact dense_digit_range d hd
    · exact dense_membrane_mirror d hd
  · intro he
    rcases he with ⟨n, hn, heq⟩
    rw [← heq]
    exact membrane_in_range n hn

/-- THE RESIDUE-WALK LINK: the membrane digit is the walk's own wrap — the
    emod 38 folded by the same position-dependent rule. -/
theorem membrane_digit_is_residue_wrap (n : Nat) (hn : n < 38) :
    membrane_digit n = digit_of (n : Int) := by
  unfold membrane_digit digit_of
  have hem : (n : Int).emod 38 = (n : Int) := by
    exact Int.emod_eq_of_lt (b := (38 : Int)) (by omega) (by omega)
  rw [hem]
  by_cases h : (n : Int) ≤ (19 : Int)
  · simp [h]
    omega
  · have hn20 : n ≥ 20 := by omega
    simp [h, hn20]
-- ============================================================
-- GOLDEN-RATIO CLOSED FORMS:
-- φ formalized by its polynomial alone. The direct reading at
-- 1+1 (a⊕b = a+b+φ·a·b → 2+φ) and the conjugate reading
-- (2+(φ−1), the conjugate copy) both reduce to closed forms:
-- φ²+1 and φ² — the reconciliation is a theorem, and the
-- "φ vs φ−1" relationship settles: φ−1 IS the inverse of φ.
-- HONEST SCOPE: φ is a FORMAL symbol (an Int), and the
-- polynomial φ² = φ + 1 is the only axiom-hypothesis; every
-- proof uses only ring laws plus that one equation, so each
-- identity holds in ANY commutative ring containing such an
-- element. No real-number theory is imported (Init-only ring).
-- ============================================================

/-- the direct reading at 1+1 reduces to the closed form φ²+1. -/
theorem direct_reading_closed (phi : Int) (h : phi * phi = phi + 1) :
    2 + phi = phi * phi + 1 := by
  rw [h]
  omega

/-- the conjugate reading at 1+1 reduces to the closed form φ². -/
theorem conjugate_reading_closed (phi : Int) (h : phi * phi = phi + 1) :
    2 + (phi - 1) = phi * phi := by
  rw [h]
  omega

/-- THE RECONCILIATION: the two readings land exactly one unit apart —
    (φ²+1) − φ² = 1, no hypothesis needed beyond the closed forms. -/
theorem readings_one_golden_unit_apart (phi : Int) :
    (phi * phi + 1) - phi * phi = 1 := by
  omega

/-- the conjugate relation: φ−1 IS the multiplicative inverse
    of φ — the "φ vs φ−1" relationship is one identity,
    and 0.618... is φ−1 = 1/φ, not φ. -/
theorem phi_conjugate_is_inverse (phi : Int) (h : phi * phi = phi + 1) :
    phi * (phi - 1) = 1 := by
  have hd : phi * (phi - 1) = phi * phi - phi * 1 := Int.mul_sub phi phi 1
  rw [hd, Int.mul_one, h]
  omega

/-- the inverse identity, mirrored order: (φ−1)·φ = 1, so the conjugate
    inverts φ from either side. -/
theorem phi_inverse_is_conjugate (phi : Int) (h : phi * phi = phi + 1) :
    (phi - 1) * phi = 1 := by
  have hd : (phi - 1) * phi = phi * phi - 1 * phi := Int.sub_mul phi 1 phi
  rw [hd, Int.one_mul, h]
  omega

/-- the conjugate's own square: (φ−1)² = 2 − φ — the
    0.382... companion, closed-form again. -/
theorem conjugate_sq_closed (phi : Int) (h : phi * phi = phi + 1) :
    (phi - 1) * (phi - 1) = 2 - phi := by
  have h1 : (phi - 1) * (phi - 1) = phi * (phi - 1) - 1 * (phi - 1) := Int.sub_mul phi 1 (phi - 1)
  rw [h1, Int.one_mul]
  have h2 : phi * (phi - 1) = phi * phi - phi := by
    have hd := Int.mul_sub phi phi 1
    rw [hd, Int.mul_one]
  rw [h2, h]
  omega

-- ============================================================
-- D13 THE GENERAL TWO-OVER-TWO (ledger Phase 2 rung 10, the
-- capstone, 11 Sep): the two-over-two bound at ARBITRARY WIDTH.
-- A w-place digit IS a single digit of the base B^w, so the
-- wide statement — window U = u2·B^w + u1, divisor v = v1·B^w + v0,
-- trial digit min(U/v1, B^w − 1), normalized when B^w ≤ 2·v1 —
-- reduces honestly to the proven single-width theorem at that
-- base. The known bound q ≤ q̂ ≤ q+2 is kept exactly as proven;
-- the q+1 tightening stays a future direction, not a claim.
-- ============================================================

/-- a base with at least two needs a positive width to grow: B^w ≥ 2. -/
theorem wide_base_ge_two (B w : Nat) (hB : 2 ≤ B) (hw : 0 < w) : 2 ≤ B ^ w := by
  induction w with
  | zero => omega
  | succ n ih =>
      have hp : B ^ n.succ = B ^ n * B := Nat.pow_succ B n
      rw [hp]
      by_cases hn0 : n = 0
      · subst n
        simp
        exact hB
      · have hnpos : 0 < n := by omega
        have ih' : 2 ≤ B ^ n := ih hnpos
        have hb1 : 1 ≤ B ^ n := by omega
        have hm := Nat.mul_le_mul hb1 hB
        have h1 : 1 * 2 ≤ B ^ n * B := by exact hm
        rw [Nat.one_mul] at h1
        exact h1

/-- THE GENERAL TWO-OVER-TWO: the same bound, at any digit width w —
    u2, u1, u0, v1, v0 are w-place digits (< B^w), the window is
    (u2·B^w + u1)·B^w + u0, the divisor v1·B^w + v0, normalized
    B^w ≤ 2·v1 → q ≤ q̂ ≤ q + 2. -/
theorem two_over_two_bound_wide (B w u2 u1 u0 v1 v0 : Nat)
    (hB : 2 ≤ B) (hw : 0 < w) (hv1 : 0 < v1) (hnorm : B ^ w ≤ 2 * v1)
    (hu2 : u2 < B ^ w) (hu1 : u1 < B ^ w) (hu0 : u0 < B ^ w) (hv0 : v0 < B ^ w)
    (hW : (u2 * B ^ w + u1) * B ^ w + u0 < (v1 * B ^ w + v0) * B ^ w) :
    let U := u2 * B ^ w + u1
    let v := v1 * B ^ w + v0
    let W := U * B ^ w + u0
    let q := W / v
    let qh := Nat.min (U / v1) (B ^ w - 1)
    q ≤ qh ∧ qh ≤ q + 2 := by
  intro U v W q qh
  have hBw : 2 ≤ B ^ w := wide_base_ge_two B w hB hw
  have hmain := two_over_two_bound (B ^ w) u2 u1 u0 v1 v0 hBw hv1 hnorm hu2 hu1 hu0 hv0 hW
  simpa [U, v, W, q, qh] using hmain

-- ============================================================
-- THE DIV-FIT STEP (A5's composite closure, 11 Sep): |q| ≤ |a|
-- whenever the lane divides by a nonzero b. Three layers: the
-- triangle inequality for the absolute value (|x+y| ≤ |x|+|y|,
-- the lane's own shadow law), the pure Euclidean fit lemma (any
-- pair q, r with a = q·b + r and 0 ≤ r < |b| satisfies |q| ≤ |a|),
-- and the lane theorem (the adjusted tdiv/tmod pair fits). This
-- closes A5's div-composite: the quotient of a folded division
-- lives inside the dividend's shadow, so 2^127-window canonicality
-- of the quotient follows from the dividend's. -/
-- ============================================================

/-- THE TRIANGLE: |x + y| ≤ |x| + |y|, four sign arms, omega-armed. -/
theorem natAbs_triangle (x y : Int) : (x + y).natAbs ≤ x.natAbs + y.natAbs := by
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · have hxy : 0 ≤ x + y := by omega
      have h1 : ((x + y).natAbs : Int) = x + y := Int.natAbs_of_nonneg (a := x + y) hxy
      have h2 : (x.natAbs : Int) = x := Int.natAbs_of_nonneg hx
      have h3 : (y.natAbs : Int) = y := Int.natAbs_of_nonneg hy
      omega
    · have hyn : y < 0 := by omega
      by_cases hxy : 0 ≤ x + y
      · have h1 : ((x + y).natAbs : Int) = x + y := Int.natAbs_of_nonneg (a := x + y) hxy
        have h2 : (x.natAbs : Int) = x := Int.natAbs_of_nonneg hx
        have h3 : (y.natAbs : Int) = -y := by
          have h := Int.natAbs_of_nonneg (a := -y) (by omega)
          simpa [Int.natAbs_neg] using h
        omega
      · have h1 : ((x + y).natAbs : Int) = -(x + y) := by
          have h := Int.natAbs_of_nonneg (a := -(x + y)) (by omega)
          simpa [Int.natAbs_neg] using h
        have h2 : (x.natAbs : Int) = x := Int.natAbs_of_nonneg hx
        have h3 : (y.natAbs : Int) = -y := by
          have h := Int.natAbs_of_nonneg (a := -y) (by omega)
          simpa [Int.natAbs_neg] using h
        omega
  · by_cases hy : 0 ≤ y
    · have hxn : x < 0 := by omega
      by_cases hxy : 0 ≤ x + y
      · have h1 : ((x + y).natAbs : Int) = x + y := Int.natAbs_of_nonneg (a := x + y) hxy
        have h2 : (x.natAbs : Int) = -x := by
          have h := Int.natAbs_of_nonneg (a := -x) (by omega)
          simpa [Int.natAbs_neg] using h
        have h3 : (y.natAbs : Int) = y := Int.natAbs_of_nonneg hy
        omega
      · have h1 : ((x + y).natAbs : Int) = -(x + y) := by
          have h := Int.natAbs_of_nonneg (a := -(x + y)) (by omega)
          simpa [Int.natAbs_neg] using h
        have h2 : (x.natAbs : Int) = -x := by
          have h := Int.natAbs_of_nonneg (a := -x) (by omega)
          simpa [Int.natAbs_neg] using h
        have h3 : (y.natAbs : Int) = y := Int.natAbs_of_nonneg hy
        omega
    · have hxy : x + y < 0 := by omega
      have h1 : ((x + y).natAbs : Int) = -(x + y) := by
        have h := Int.natAbs_of_nonneg (a := -(x + y)) (by omega)
        simpa [Int.natAbs_neg] using h
      have h2 : (x.natAbs : Int) = -x := by
        have h := Int.natAbs_of_nonneg (a := -x) (by omega)
        simpa [Int.natAbs_neg] using h
      have h3 : (y.natAbs : Int) = -y := by
        have h := Int.natAbs_of_nonneg (a := -y) (by omega)
        simpa [Int.natAbs_neg] using h
      omega

/-- THE DIV-FIT LEMMA: any Euclidean division pair fits the dividend's
    shadow — a = q·b + r with 0 ≤ r < |b| and b ≠ 0 forces |q| ≤ |a|
    (so a quotient never outgrows the number it came from). -/
theorem euclid_fit (a b q r : Int) (hide : a = q * b + r) (hr : 0 ≤ r)
    (hrb : r < b.natAbs) (hb : b ≠ 0) : q.natAbs ≤ a.natAbs := by
  let Q : Nat := q.natAbs
  let A : Nat := a.natAbs
  let B : Nat := b.natAbs
  let R : Nat := r.natAbs
  by_cases hq0 : Q = 0
  · have hz : q.natAbs = 0 := by simpa [Q] using hq0
    rw [hz]
    exact Nat.zero_le a.natAbs
  · have hq1 : 1 ≤ Q := by omega
    have hrb' : r.natAbs < b.natAbs := by
      have hnn : (r.natAbs : Int) = r := Int.natAbs_of_nonneg hr
      have hrbi : (r.natAbs : Int) < (b.natAbs : Int) := by
        rwa [hnn]
      exact_mod_cast hrbi
    have hrB : R ≤ B - 1 := by omega
    have hRm : R ≤ Q * (B - 1) := by
      have hqmul : B - 1 ≤ Q * (B - 1) := by
        have hm := Nat.mul_le_mul_right (B - 1) hq1
        rwa [Nat.one_mul] at hm
      exact Nat.le_trans hrB hqmul
    have hBig : R + Q ≤ Q * B := by
      have hm := Nat.add_le_add_left hRm Q
      have hpred : B - 1 + 1 = B := by
        have h1 : 1 ≤ B := by
          by_cases hz : b.natAbs = 0
          · have hb0 : b = 0 := Int.natAbs_eq_zero.mp hz
            exfalso
            exact hb hb0
          · dsimp [B]
            omega
        omega
      have hring : Q * B = Q * (B - 1) + Q := by
        conv =>
          lhs
          rw [← hpred]
        rw [Nat.left_distrib]
        rw [Nat.mul_one]
      have hm' : R + Q ≤ Q * (B - 1) + Q := by simpa [Nat.add_comm] using hm
      rwa [← hring] at hm'
    have hQo : Q + R ≤ Q * B := by simpa [Nat.add_comm] using hBig
    have hQR : Q ≤ Q * B - R := by
      have hRle : R ≤ Q * B := by omega
      exact (Nat.le_sub_iff_add_le hRle).mpr hQo
    have htrev : Q * B ≤ A + R := by
      dsimp [Q, B, A, R]
      have hcanc : q * b + r + -r = q * b := by omega
      have htri := natAbs_triangle (q * b + r) (-r)
      rw [hcanc] at htri
      rw [Int.natAbs_mul] at htri
      rw [hide.symm, Int.natAbs_neg] at htri
      simpa using htri
    have hA : Q * B - R ≤ A := (Nat.sub_le_iff_le_add).mpr htrev
    exact Nat.le_trans hQR hA

/-- THE LANE'S QUOTIENT FITS: the shore fold's adjusted division pair
    satisfies |q| ≤ |a| whenever b ≠ 0 — the div-composite's fit step,
    closing A5 (a folded quotient lives inside the folded dividend's
    shadow, so its canonicality follows from the dividend's). -/
theorem div_results_fit (a b : Int) (hb : b ≠ 0) :
    let q0 := a.tdiv b
    let r0 := a.tmod b
    (if r0 < 0 then (if b > 0 then q0 - 1 else q0 + 1) else q0).natAbs ≤ a.natAbs := by
  intro q0 r0
  let q : Int := if r0 < 0 then (if b > 0 then q0 - 1 else q0 + 1) else q0
  let r : Int := if r0 < 0 then (if b > 0 then r0 + b else r0 - b) else r0
  have hdiv : a = q0 * b + r0 := (Int.tdiv_mul_add_tmod a b).symm
  have hide : a = q * b + r := by
    dsimp [q, r]
    by_cases hr : r0 < 0
    · by_cases hbgt : b > 0
      · have hx : (q0 - 1) * b + (r0 + b) = a := by
          calc
            (q0 - 1) * b + (r0 + b) = (q0 * b - b) + (r0 + b) := by
                  rw [Int.sub_mul]
                  simp
            _ = q0 * b + r0 := by omega
            _ = a := hdiv.symm
        simpa [hr, hbgt] using hx.symm
      · have hx : (q0 + 1) * b + (r0 - b) = a := by
          calc
            (q0 + 1) * b + (r0 - b) = (q0 * b + b) + (r0 - b) := by
                  rw [Int.add_mul]
                  simp
            _ = q0 * b + r0 := by omega
            _ = a := hdiv.symm
        simpa [hr, hbgt] using hx.symm
    · have hx : q0 * b + r0 = a := by omega
      simpa [hr] using hx.symm
  have hband := div_rem_euclidean_band a b hb
  have hr0 : 0 ≤ r := hband.1
  have hrb : r < b.natAbs := hband.2
  have hfit := euclid_fit a b q r hide hr0 hrb hb
  simpa [q] using hfit

-- ============================================================
-- THE MILLENNIUM RECONCILIATION (11 Sep round 3): the archive's
-- claim "the zeros' real part 1/φ ≈ 0.618 appears as 1/2 through
-- binary thinking" is EXACTLY the algebraic statement 1/φ = 1/2.
-- Since 1/φ = φ−1 (phi_conjugate_is_inverse), that statement is
-- 2·(φ−1) = 1, i.e. φ + φ = 3. The ring refutes it outright:
-- no element of any ring with the polynomial φ² = φ + 1 can be
-- three-halves — so the projection claim cannot hold in ANY
-- model of the polynomial. The atlas itself asserts the zeros
-- at 0.5 exactly (orbit-millennium-checks, empirical_critical_
-- line); the instruments agree, and the archive's proof-file
-- is graded against them.
-- ============================================================

/-- THE REFUTATION: 1/φ = 1/2 is impossible. Stated ring- purely:
    φ + φ = 3 forces 9 = 10 in every ring with φ² = φ + 1. -/
theorem phi_minus_one_is_not_half (phi : Int) (h : phi * phi = phi + 1) :
    ¬(phi + phi = 3) := by
  intro h2
  have hsq4 : (phi + phi) * (phi + phi) = 4 * (phi * phi) := by
    rw [Int.add_mul]
    rw [Int.mul_add]
    omega
  have hsq9 : (phi + phi) * (phi + phi) = 9 := by
    rw [h2]
    omega
  have h49 : 4 * (phi * phi) = 9 := by
    rwa [← hsq4]
  have h410 : 4 * (phi * phi) = 10 := by
    calc
      4 * (phi * phi) = 4 * (phi + 1) := by rw [h]
      _ = 4 * phi + 4 := by omega
      _ = 2 * (phi + phi) + 4 := by omega
      _ = 2 * 3 + 4 := by rw [h2]
      _ = 10 := by omega
  omega
