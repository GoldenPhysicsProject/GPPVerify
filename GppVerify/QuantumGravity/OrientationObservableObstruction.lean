import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import GppVerify.GeneralRelativity.OrientationYorkMomentMap

/-!
# An operational obstruction: anti-symplectic orientation quotient versus York reduction

If an involution T is anti-symplectic and a bilinear 2-form were the
pullback of a 2-form on the orientation quotient, the same form would
have to be T-invariant. Over the reals this forces the form to vanish.
Thus a nonzero physical symplectic form cannot be descended unchanged
to a quotient by anti-symplectic time reversal.

This is DIFFERENT from the continuous York Hamiltonian quotient,
which descends the restricted form on the fixed-moment-map level set.

A separate two-term Schmidt toy exhibits another often conflated
distinction: opposite global relative phases can yield exactly the
same reduced probability data, but an interference observable separates
the two global states. The full ray's Fubini--Study phase metric can
therefore be nonzero when the reduced-state Fisher metric is zero.

No claim is made that Wigner's antiunitary time reversal is the user's
microscopic orientation sign t or their diagonal four-lift involution D.
-/

namespace GppOrientationObservableObstruction

section Symplectic

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Anti-symplectic orientation reversal and invariant descent of a
real bilinear 2-form are compatible only for the zero form. -/
theorem antisymplectic_invariant_form_zero
    (omega : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (T : E →ₗ[ℝ] E)
    (hAnti : ∀ u v, omega (T u) (T v) = -omega u v)
    (hDesc : ∀ u v, omega (T u) (T v) = omega u v) :
    ∀ u v, omega u v = 0 := by
  intro u v
  have h : omega u v = -omega u v :=
    (hDesc u v).symm.trans (hAnti u v)
  linarith

/-- Nonvanishing canonical symplectic geometry excludes simply
identifying an anti-symplectic orientation quotient with a symplectic
phase-space quotient. -/
theorem antisymplectic_nonzero_obstructs_descent
    (omega : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (T : E →ₗ[ℝ] E)
    (hAnti : ∀ u v, omega (T u) (T v) = -omega u v)
    (u v : E) (hNonzero : omega u v ≠ 0) :
    ¬ (∀ x y, omega (T x) (T y) = omega x y) := by
  intro hDesc
  exact hNonzero (antisymplectic_invariant_form_zero
    omega T hAnti hDesc u v)

end Symplectic

section CanonicalWitness

/-- Time orientation reversal of the ADM q-p toy model has a
nonzero symplectic form; it cannot be an ordinary symplectic quotient
with this unchanged canonical form. -/
theorem canonical_anti_symplectic_cannot_descend :
    ¬ (∀ a b : ℝ × ℝ,
      GppOrientationYorkMomentMap.omega
        (GppOrientationYorkMomentMap.reverse a)
        (GppOrientationYorkMomentMap.reverse b) =
      GppOrientationYorkMomentMap.omega a b) := by
  intro h
  have heq := h (0, 1) (1, 0)
  norm_num [GppOrientationYorkMomentMap.omega,
    GppOrientationYorkMomentMap.reverse] at heq

end CanonicalWitness

section SchmidtPhase

/-- The two nonzero Schmidt amplitudes are 1/sqrt(2), with a
relative phase of +i or -i. Their reduced density operators on A
are both diagonal with these probabilities. -/
noncomputable def reducedSchmidtProbability (z : ℂ) : ℝ × ℝ :=
  ((1 : ℝ) / 2, Complex.normSq z / 2)

/-- The opposite relative phases have exactly the same reduced
Schmidt data; in this orthogonal-support model the reduced density
matrices, not merely their entropies, coincide. -/
theorem opposite_relative_phase_same_reduced_state :
    reducedSchmidtProbability Complex.I =
      reducedSchmidtProbability (-Complex.I) := by
  simp [reducedSchmidtProbability, Complex.normSq_neg]

/-- A global interference observable can distinguish the phases
even though the one-party reduced state cannot. -/
theorem opposite_relative_phase_distinguished_globally :
    Complex.I.im ≠ (-Complex.I).im := by
  norm_num

/-- The full projective ray can have positive Fubini--Study metric
on a phase direction despite no change in the reduced density matrix.
This is the normalized ratio for psi=(1,1), dpsi=(0,i):
||dpsi||²/||psi||² - |<psi,dpsi>|²/||psi||⁴=1/4. -/
noncomputable def fullRayPhaseFSMetric : ℝ :=
  (Complex.normSq (0 : ℂ) + Complex.normSq Complex.I) /
    (Complex.normSq (1 : ℂ) + Complex.normSq (1 : ℂ)) -
  Complex.normSq Complex.I /
    (Complex.normSq (1 : ℂ) + Complex.normSq (1 : ℂ)) ^ 2

theorem full_ray_phase_fs_positive :
    fullRayPhaseFSMetric = (1 / 4 : ℝ) := by
  norm_num [fullRayPhaseFSMetric, Complex.normSq]

end SchmidtPhase

end GppOrientationObservableObstruction

#print axioms GppOrientationObservableObstruction.antisymplectic_invariant_form_zero
#print axioms GppOrientationObservableObstruction.antisymplectic_nonzero_obstructs_descent
#print axioms GppOrientationObservableObstruction.canonical_anti_symplectic_cannot_descend
#print axioms GppOrientationObservableObstruction.opposite_relative_phase_same_reduced_state
#print axioms GppOrientationObservableObstruction.full_ray_phase_fs_positive
