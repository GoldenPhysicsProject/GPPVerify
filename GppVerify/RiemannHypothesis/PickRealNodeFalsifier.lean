import Mathlib.Tactic

/-!
# A real-Euler-node Pick falsifier for an off-axis spectral quartet

Astra's 2026-10-10 Pick continuation notes an off-axis synthetic polynomial
whose complex-node Pick matrix fails, but did not compute a witness on the
REAL Euler-region nodes s>1 that are sufficient in her RH criterion.

For the even polynomial G(k)=((k-14)^2+(1/5)^2)*((k+14)^2+(1/5)^2),
set k=i*x, where s=1/2+x.  Its logarithmic derivative along this
imaginary axis gives the following exact rational function F(x).

We certify at x=1,3,14, i.e. s=3/2,7/2,29/2 (ALL s>1),
that *each diagonal and each two-by-two principal minor is positive*
while the three-by-three Pick determinant is NEGATIVE.

Thus three jointly chosen real Euler nodes can detect synthetic off-axis
spectral poles although each pair of those nodes passes. This is an
exact falsifier/control, NOT a zeta calculation or proof of RH.

The finite Pick matrix has entries (F(x)+F(y))/(x+y). The polynomial
G has off-real spectral poles at ±14±i/5. All arithmetic is rational.
-/

namespace GppPickRealNodeFalsifier

def syntheticF (x : ℚ) : ℚ :=
  100 * x * (25 * x ^ 2 + 4899) /
    ((25 * x ^ 2 - 10 * x + 4901) *
     (25 * x ^ 2 + 10 * x + 4901))

def pick (x y : ℚ) : ℚ := (syntheticF x + syntheticF y) / (x + y)

private theorem pick11 : pick 1 1 = (30775 : ℚ) / 1516586 := by
  norm_num [pick, syntheticF]
private theorem pick13 : pick 1 3 = (7008724075 : ℚ) / 355788042428 := by
  norm_num [pick, syntheticF]
private theorem pick114 : pick 1 14 = (1584071182025 : ℚ) / 145652920956586 := by
  norm_num [pick, syntheticF]
private theorem pick33 : pick 3 3 = (4575 : ℚ) / 234598 := by
  norm_num [pick, syntheticF]
private theorem pick314 : pick 3 14 = (266853243325 : ℚ) / 22530792154598 := by
  norm_num [pick, syntheticF]
private theorem pick1414 : pick 14 14 = (979900 : ℚ) / 96040001 := by
  norm_num [pick, syntheticF]

/-- The three diagonal entries are positive, so scalar positive-real tests pass. -/
theorem synthetic_pick_positive_diagonal :
    0 < pick 1 1 ∧ 0 < pick 3 3 ∧ 0 < pick 14 14 := by
  rw [pick11, pick33, pick1414]
  norm_num

/-- All three two-point tests on these particular real nodes pass. -/
theorem synthetic_pick_positive_pair_minors :
    0 < pick 1 1 * pick 3 3 - pick 1 3 ^ 2 ∧
    0 < pick 1 1 * pick 14 14 - pick 1 14 ^ 2 ∧
    0 < pick 3 3 * pick 14 14 - pick 3 14 ^ 2 := by
  rw [pick11, pick13, pick114, pick33, pick314, pick1414]
  norm_num

/-- The exact symmetric 3-by-3 Pick determinant. -/
def det3 : ℚ :=
  pick 1 1 * (pick 3 3 * pick 14 14 - pick 3 14 ^ 2) -
  pick 1 3 * (pick 1 3 * pick 14 14 - pick 1 14 * pick 3 14) +
  pick 1 14 * (pick 1 3 * pick 3 14 - pick 1 14 * pick 3 3)

/-- The real Euler-region nodes x=1,3,14 give a strict 3-point failure. -/
theorem synthetic_pick_det3_exact :
    det3 = -(3995025526004205322265625 : ℚ) /
      493483080809652320286918417738322424 := by
  unfold det3
  rw [pick11, pick13, pick114, pick33, pick314, pick1414]
  norm_num

/-- A finite three-point real-node Pick matrix is NOT PSD, despite all
    three diagonals and all three principal 2x2 minors being positive. -/
theorem synthetic_pick_three_point_failure : det3 < 0 := by
  rw [synthetic_pick_det3_exact]
  norm_num

end GppPickRealNodeFalsifier
