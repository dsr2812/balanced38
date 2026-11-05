import Balanced38.Balanced38

/- SMOKE TEST / BENCHMARK HARNESS
   Cross-checks the lane's checked arithmetic (checked_mul, checked_div_rem,
   from_i128 round trips, negation) against native Int arithmetic at runtime. -/

/-- a signed string: build a Balanced38 straight from shell digits -/
def shell (ds : List Int) : Balanced38 :=
  { digits := ds }

def read (x : Balanced38) : Int := to_i128 x

/-- the store must round-trip: any i128 with |v| < 2^127 reads back exactly v -/
def rtOk (v : Int) : Bool :=
  v.natAbs < 2 ^ 127 → read (from_i128 v) == v

/-- checked_mul must agree with native Int multiplication -/
def mulOk (x : Int) (y : Int) : Bool :=
  match checked_mul (from_i128 x) (from_i128 y) with
  | some z => read z == x * y
  | none => false

/-- checked_div_rem must satisfy the division identity a = q·b + r -/
def divOk (a : Int) (b : Int) : Bool :=
  if b = 0 then true
  else
    match checked_div_rem (from_i128 a) (from_i128 b) with
    | some (q, r) => read q * b + read r == a
    | none => false

/-- negation must double back -/
def negOk (v : Int) : Bool :=
  read (negate (from_i128 v)) == -v

/-- A1 THE SHORE BOUND receipts (11 Sep): the door's edge, measured — the
    24-place all-19s maximum folds inside the shore and reads back exactly
    19·(38²⁴−1)/37; the 25-place string's value sits past 2^127−1 (the walker's
    own precondition fails). The theorem shore_fold is the provable half; this
    is the compiled lane's runtime edge. -/
def shore24 : Balanced38 := { digits := List.replicate 24 19 }

def shore25 : Balanced38 := { digits := List.replicate 25 19 }

def shoreOk : Bool :=
  (Int.natAbs (to_i128 shore24) < (2 : Int) ^ 127) &&
  (to_i128 shore24 == 19 * ((38 ^ 24 - 1 : Nat) : Int) / 37) &&
  (!(Int.natAbs (to_i128 shore25) < (2 : Int) ^ 127))

/-- B7 THE WRAPPED RESIDUE receipt (11 Sep): all 38 dense digits round-trip
    through the wrap and its mirror — membrane_digit then dense_digit. -/
def wrappedOk : IO Bool := do
  let mut ok := true
  for n in List.range 38 do
    if !(dense_digit (membrane_digit n) == n) then
      ok := false
  return ok

/-- B8 THE TRANSPOSITION SWEEP, base-19 (11 Sep): the alternating-weight
    check (modulus 20) catches every adjacent swap of distinct digits —
    the 18 lost pairs are the |d−e| = 10 class, so 324 of 342 = 94.74%,
    the transposition rate the ledger's "94.74%" was really counting. -/
def transpositionSweepOk : IO Bool := do
  let mut total := 0
  let mut catches := 0
  for d in List.range 19 do
    for d' in List.range 19 do
      if !(d == d') then
        total := total + 1
        if !((2 * (d' - d) % 20 == 0) && (2 * (d - d') % 20 == 0)) then
          catches := catches + 1
  return (total == 342) && (catches == 324)

/-- B9 THE SINGLE-DIGIT SWEEP, base-19 (11 Sep): the free digit-sum check
    (modulus 18) misses only the two extreme pairs 0↔18, so 340 of 342 =
    99.42% — the true single-digit rate. -/
def singleDigitSweepOk : IO Bool := do
  let mut total := 0
  let mut catches := 0
  for d in List.range 19 do
    for d' in List.range 19 do
      if !(d == d') then
        total := total + 1
        if !((d' >= d && ((d' - d) % 18 == 0)) || (d >= d' && ((d - d') % 18 == 0))) then
          catches := catches + 1
  return (total == 342) && (catches == 340)

/-- the F9 floors, mirroring the theorems: the two rates are different. -/
def ratesOk : Bool :=
  (324 * 10000) / 342 == 9473 &&
  (340 * 10000) / 342 == 9941 &&
  (324 * 10000) / 342 != (340 * 10000) / 342

/-- a battery over small, boundary and random-ish values -/
def interesting : List Int :=
  [0, 1, -1, 2, -2, 3, -3, 18, 19, 20, -18, -19, -20, 37, 38, 39, -37, -38, -39,
   37 * 37, 38 * 38, 38 * 38 - 1, 1443, 1444, -1443, -1444,
   27435, 27436, 27437, -27435, -27436, -27437,
   123456, -123456, 987654321, -987654321, 1000000000000, -1000000000000]

def M := (2 : Int) ^ 127 - 1

def batteries : List Int :=
  interesting ++ [M, -M, M - 1, -M + 1, 0 - M, -(M - 1),
                  (2 : Int) ^ 126, -(2 : Int) ^ 126]

/-- run every pair through the whole suite, counting failures -/
def runSuite : IO (Nat × Nat) := do
  let mut total := 0
  let mut failed := 0
  for v in batteries do
    for w in batteries do
      total := total + 1
      if !(mulOk v w) then
        failed := failed + 1
        IO.println s!"MUL FAIL v={v} w={w}"
      if !(divOk v w) then
        failed := failed + 1
        IO.println s!"DIV FAIL v={v} w={w}"
    if !(rtOk v) then
      failed := failed + 1
      IO.println s!"RT FAIL v={v}"
    if !(negOk v) then
      failed := failed + 1
      IO.println s!"NEG FAIL v={v}"
  return (total, failed)

/-- a timed loop: 24-digit × 24-digit multiplications -/
def timedMul (iters : Nat) : IO Nat := do
  let x : Balanced38 := { digits := (List.replicate 24 19) }  -- all-max 19 shell
  let y : Balanced38 := { digits := (List.replicate 24 18) }
  let start ← IO.monoMsNow
  for _ in List.range iters do
    if let some _ := checked_mul x y then
      pure ()
    else
      IO.println "TIMED: none"
  let fin ← IO.monoMsNow
  return fin - start

def timedDiv (iters : Nat) : IO Nat := do
  let x : Balanced38 := { digits := (List.replicate 24 19) }
  let y : Balanced38 := { digits := (List.replicate 12 3) }
  let start ← IO.monoMsNow
  for _ in List.range iters do
    if let some _ := checked_div_rem x y then
      pure ()
    else
      IO.println "TIMED: none"
  let fin ← IO.monoMsNow
  return fin - start

def main : IO Unit := do
  let (total, failed0) ← runSuite
  let shoreVerdict := shoreOk
  let wrapped ← wrappedOk
  let sweep ← transpositionSweepOk
  let single ← singleDigitSweepOk
  let failed := failed0 + (if shoreVerdict then 0 else 1) + (if wrapped then 0 else 1) + (if sweep then 0 else 1) + (if single then 0 else 1) + (if ratesOk then 0 else 1)
  IO.println s!"suite: {total} pairs x mul+div, plus {batteries.length} roundtrips+negs"
  IO.println s!"shore: 24x19 folds ({to_i128 shore24}), 25x19 refuses — {if shoreVerdict then "OK" else "FAIL"}"
  IO.println s!"wrapped: 38/38 membrane round-trips — {if wrapped then "OK" else "FAIL"}"
  IO.println s!"transposition: 324/342 caught (94.74%), single-digit 340/342 (99.42%) — {if sweep && single then "OK" else "FAIL"}"
  IO.println s!"FAILURES: {failed}"
  let msM ← timedMul 3000
  IO.println s!"checked_mul  24x24-digit x3000: {msM} ms"
  let msD ← timedDiv 3000
  IO.println s!"checked_div_rem 24x12-digit x3000: {msD} ms"

#eval main