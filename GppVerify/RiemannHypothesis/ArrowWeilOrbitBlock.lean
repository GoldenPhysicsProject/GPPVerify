import Mathlib.Tactic
import GppVerify.RiemannHypothesis.OrientationCriticalRealStructureBridge

/-!
# Arrow/Weil two-point orbit block

Finite exact lemmas for the WWIF-to-Weil dictionary.

For an off-critical zero rho, complete reversal sends it to
  D rho = 1 - conj rho.
The centered real displacement from the critical line changes sign.

On the two-point orbit {rho, D rho}, the D-twisted real pairing is represented
by the swap matrix sigma_1.  The coherent vector (a,a) has positive form
2 a^2 and the anti-coherent vector (a,-a) has negative form -2 a^2.

These lemmas are finite algebra only.  They do not assert positivity of the
global Weil form and do not prove RH.
-/

namespace GppArrowWeilOrbitBlock

open Complex

/-- Complete arithmetic reversal in the uncentered s-coordinate. -/
def arithmeticReverse (rho : ℂ) : ℂ :=
  1 - starRingEnd ℂ rho

/-- Signed displacement from the critical line. -/
def orientationBias (rho : ℂ) : ℝ :=
  rho.re - (1 / 2 : ℝ)

/-- Complete reversal negates the signed displacement. -/
theorem orientationBias_reverse (rho : ℂ) :
    orientationBias (arithmeticReverse rho) = - orientationBias rho := by
  simp [orientationBias, arithmeticReverse]
  ring

/-- Zero orientation bias is exactly the critical line. -/
theorem orientationBias_eq_zero_iff (rho : ℂ) :
    orientationBias rho = 0 ↔ rho.re = (1 / 2 : ℝ) := by
  unfold orientationBias
  constructor <;> intro h <;> linarith

/-- The finite two-point reversal operator: swap the two orbit coordinates. -/
def orbitReverse (v : ℝ × ℝ) : ℝ × ℝ :=
  (v.2, v.1)

/-- The orbit reversal is an involution. -/
theorem orbitReverse_sq (v : ℝ × ℝ) :
    orbitReverse (orbitReverse v) = v := by
  rcases v with ⟨x,y⟩
  rfl

/-- Real form of the D-twisted pairing on one two-point orbit. -/
def orbitForm (v : ℝ × ℝ) : ℝ :=
  2 * v.1 * v.2

/-- The D-even/coherent direction has positive square. -/
theorem orbitForm_coherent (a : ℝ) :
    orbitForm (a,a) = 2 * a^2 := by
  simp [orbitForm]
  ring

/-- The D-odd/anti-coherent direction has negative square. -/
theorem orbitForm_anticoherent (a : ℝ) :
    orbitForm (a,-a) = -2 * a^2 := by
  simp [orbitForm]
  ring

/-- A nontrivial two-point orbit block is indefinite. -/
theorem orbitForm_indefinite :
    (∃ v : ℝ × ℝ, 0 < orbitForm v) ∧
    (∃ v : ℝ × ℝ, orbitForm v < 0) := by
  constructor
  · refine ⟨(1,1), ?_⟩
    norm_num [orbitForm]
  · refine ⟨(1,-1), ?_⟩
    norm_num [orbitForm]

/-- D-even vectors are fixed by the swap. -/
theorem orbitReverse_coherent (a : ℝ) :
    orbitReverse (a,a) = (a,a) := by
  rfl

/-- D-odd vectors change sign under the swap. -/
theorem orbitReverse_anticoherent (a : ℝ) :
    orbitReverse (a,-a) = (-a,a) := by
  rfl

/-- A reversed arithmetic point is fixed exactly on the critical line. -/
theorem arithmeticReverse_fixed_iff (rho : ℂ) :
    arithmeticReverse rho = rho ↔ rho.re = (1 / 2 : ℝ) := by
  simpa [arithmeticReverse] using
    GppOrientationCriticalRealStructureBridge.s_fixed_iff_critical rho

end GppArrowWeilOrbitBlock

#print axioms GppArrowWeilOrbitBlock.orientationBias_reverse
#print axioms GppArrowWeilOrbitBlock.orientationBias_eq_zero_iff
#print axioms GppArrowWeilOrbitBlock.orbitForm_indefinite
#print axioms GppArrowWeilOrbitBlock.arithmeticReverse_fixed_iff
