import Mathlib.Tactic

/-!
# *Which Way Is Forward?*: the coordinate signature scan

Source: Daniel Toupin, *Which Way Is Forward?* (v26), §"One time axis, two
microscopic orientations" (signature subsection), and its check script
`verify_wwif.py`, function `verify_coordinate_signature_scan`.

Blades of the coordinate Clifford algebra on four generators are encoded as
masks (`bit i` set = generator `i` present). `bladeMul` is the script's
`blade_multiply` under the metric of signature `(p, 4 - p)`. A *coordinate
normal form* is a triple `(a, b, c)` of coordinate bivectors with
`a^2 = b^2 = -1`, `ab = ba`, `c^2 = +1` and `{c, a} = {c, b} = 0` — the
orientation algebra of `OrientationCliffordCore`, searched over coordinate
blades only.

Checked claim: the solution counts by signature are exactly
`(0,4): 0, (1,3): 0, (2,2): 8, (3,1): 0, (4,0): 0`. Coordinate normal forms
occur **only in signature `(2, 2)`**.

Scope: coordinate blades in dimension four, signatures `(p, 4 - p)` only.
Nothing is claimed about non-coordinate bivectors or other dimensions.
-/

namespace GppWhichWayForwardSignatureScan

/-- Metric sign of generator `i` in signature `(p, 4 - p)`. -/
def msign (p i : Nat) : Int := if i < p then 1 else -1

/-- One step of the script's blade multiplication loop, at generator `i`:
state is `(sign, mask)`. -/
def bladeStep (p B : Nat) (st : Int × Nat) (i : Nat) : Int × Nat :=
  let sign := st.1
  let mask := st.2
  if B.testBit i then
    let greater := ((List.range 4).filter (fun j => i < j && mask.testBit j)).length
    let sign := if greater % 2 = 1 then -sign else sign
    if mask.testBit i then
      (sign * msign p i, mask ^^^ (1 <<< i))
    else
      (sign, mask ||| (1 <<< i))
  else st

/-- Blade product in `Cl(p, 4 - p)`, as a `(sign, mask)` pair. -/
def bladeMul (p A B : Nat) : Int × Nat :=
  [0, 1, 2, 3].foldl (bladeStep p B) (1, A)

/-- The six coordinate bivectors (masks of popcount two). -/
def bivectors : List Nat := [3, 5, 6, 9, 10, 12]

/-- `x^2 = s` as a blade equation, for `s = ±1`. -/
def sqEq (p x : Nat) (s : Int) : Bool := bladeMul p x x == (s, 0)

/-- `a` and `b` commute as blades. -/
def commutes (p a b : Nat) : Bool := bladeMul p a b == bladeMul p b a

/-- `c` and `a` anticommute as blades: same mask, opposite sign. -/
def anticommutes (p c a : Nat) : Bool :=
  let ca := bladeMul p c a
  let ac := bladeMul p a c
  ca.2 == ac.2 && ca.1 == -ac.1

/-- All coordinate normal forms in signature `(p, 4 - p)`. -/
def solutions (p : Nat) : List (Nat × Nat × Nat) :=
  bivectors.flatMap fun a => bivectors.flatMap fun b => bivectors.filterMap fun c =>
    if a != b && sqEq p a (-1) && sqEq p b (-1) && commutes p a b &&
        sqEq p c 1 && anticommutes p c a && anticommutes p c b then
      some (a, b, c)
    else
      none

/-- **The scan.** Solution counts by signature `(p, 4 - p)` for `p = 0..4`
are exactly `[0, 0, 8, 0, 0]`, matching the script. -/
theorem signature_scan_counts :
    (List.range 5).map (fun p => (solutions p).length) = [0, 0, 8, 0, 0] := by
  decide

/-- **Coordinate normal forms occur only in signature `(2, 2)`.** -/
theorem signature_scan_only_22 (p : Nat) (hp : p ≤ 4)
    (h : (solutions p).length ≠ 0) : p = 2 := by
  interval_cases p <;> revert h <;> decide

end GppWhichWayForwardSignatureScan
