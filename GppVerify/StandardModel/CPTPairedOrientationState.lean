import Mathlib.Tactic
import Mathlib.Data.Complex.Basic

/-!
# CPT-paired microscopic orientation state

This module formalizes a minimal two-sector model for the possibility that the two
microscopic orientation representatives

    |++>  and  |-->

are not separate classical populations but the two components of one CPT-paired quantum
state.

On the two-dimensional orientation carrier C x C define the anti-linear swap

    Theta(a,b) = (conj b, conj a).

This is deliberately only the orientation-sector core of a CPT pairing, not the full
Lorentz/gauge/spin CPT operator.  It satisfies Theta^2 = 1.  A state fixed by Theta obeys

    b = conj a,

so the two sectors necessarily have equal Born weight.  If the state is normalized,

    |a|^2 + |b|^2 = 1,

then each sector has weight exactly 1/2.

Thus an equal (++/--) decomposition is not an arbitrary 50-50 ansatz: it is forced in
this minimal model by exact anti-linear diagonal-pair symmetry.  Whether the two
components are physically distinct, gauge-equivalent, superselected, or coherently
interfering depends on the observable algebra and is intentionally left open.
-/

namespace GppCPTPairedOrientationState

open scoped ComplexConjugate

abbrev OrientationPair := ℂ × ℂ

/-- Anti-linear swap of the two diagonal orientation lifts. -/
def theta (psi : OrientationPair) : OrientationPair :=
  (conj psi.2, conj psi.1)

/-- The orientation-sector anti-linear swap is involutive. -/
theorem theta_sq (psi : OrientationPair) : theta (theta psi) = psi := by
  rcases psi with ⟨a,b⟩
  simp [theta]

/-- Exact Theta invariance forces the second amplitude to be the conjugate of the first. -/
theorem theta_fixed_partner (psi : OrientationPair)
    (hfix : theta psi = psi) :
    psi.2 = conj psi.1 := by
  have h := congrArg Prod.snd hfix
  simpa [theta] using h.symm

/-- Hence the two diagonal sectors have equal Born weight. -/
theorem theta_fixed_equal_normSq (psi : OrientationPair)
    (hfix : theta psi = psi) :
    Complex.normSq psi.1 = Complex.normSq psi.2 := by
  rw [theta_fixed_partner psi hfix]
  simp

/-- For a normalized Theta-fixed state, each orientation sector has weight exactly 1/2. -/
theorem theta_fixed_half_weights (psi : OrientationPair)
    (hfix : theta psi = psi)
    (hnorm : Complex.normSq psi.1 + Complex.normSq psi.2 = 1) :
    Complex.normSq psi.1 = (1 / 2 : ℝ) ∧
    Complex.normSq psi.2 = (1 / 2 : ℝ) := by
  have heq := theta_fixed_equal_normSq psi hfix
  constructor <;> nlinarith

/-- Every state of the form `(a, conj a)` is exactly Theta invariant. -/
theorem canonical_theta_fixed (a : ℂ) :
    theta (a, conj a) = (a, conj a) := by
  simp [theta]

end GppCPTPairedOrientationState
