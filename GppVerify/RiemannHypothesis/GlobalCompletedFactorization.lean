import GppVerify.RiemannHypothesis.GlobalVonMangoldtBridge
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Tactic

/-!
# Global completed zeta factorization and zero mechanism

Mathlib's analytically continued completed zeta function satisfies, away from `s = 0`,

  ζ(s) = Λ(s) / Γℝ(s).

On the open right half-plane `Re s > 0`, Deligne's Archimedean factor `Γℝ(s)` is nonzero.
Hence there is no zero creation or zero cancellation at the infinite place there:

  Λ(s) = Γℝ(s) ζ(s),
  Λ(s) = 0 ↔ ζ(s) = 0.

In particular this applies throughout the nontrivial critical strip. Combined with the
von Mangoldt theorem on `Re s > 1`, this cleanly separates the two roles:

* the prime-power Dirichlet series represents `-ζ'/ζ` only in its convergence half-plane;
* the Archimedean factor is globally nonvanishing in the critical strip;
* therefore nontrivial zeros belong to the analytically continued global zeta component,
  not to any finite Euler factor or to the Gamma factor.

No RH claim is made here.
-/

namespace GppGlobalCompleted

open Complex

/-- In the open right half-plane, the analytically continued completed zeta factors exactly
as Deligne's real Gamma factor times the analytically continued Riemann zeta function. -/
theorem completedRiemannZeta_eq_GammaR_mul_zeta {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst h
    norm_num at hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  rw [riemannZeta_def_of_ne_zero hs0]
  field_simp

/-- **Global zero equivalence in the right half-plane.** The Archimedean Gamma factor
neither creates nor cancels zeros for `Re s > 0`. -/
theorem completedRiemannZeta_eq_zero_iff_zeta_eq_zero {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = 0 ↔ riemannZeta s = 0 := by
  rw [completedRiemannZeta_eq_GammaR_mul_zeta hs, mul_eq_zero]
  exact or_iff_right (Gammaℝ_ne_zero_of_re_pos hs)

/-- In the nontrivial critical strip, completed-zeta zeros are exactly Riemann-zeta zeros. -/
theorem criticalStrip_completed_zero_iff_zeta_zero {s : ℂ}
    (hs : 0 < s.re ∧ s.re < 1) :
    completedRiemannZeta s = 0 ↔ riemannZeta s = 0 :=
  completedRiemannZeta_eq_zero_iff_zeta_eq_zero hs.1

/-- The same exact zero equivalence on the critical line. -/
theorem criticalLine_completed_zero_iff_zeta_zero (t : ℝ) :
    let s : ℂ := (1 / 2 : ℂ) + Complex.I * t
    completedRiemannZeta s = 0 ↔ riemannZeta s = 0 := by
  dsimp
  apply completedRiemannZeta_eq_zero_iff_zeta_eq_zero
  norm_num

end GppGlobalCompleted

#print axioms GppGlobalCompleted.completedRiemannZeta_eq_GammaR_mul_zeta
#print axioms GppGlobalCompleted.completedRiemannZeta_eq_zero_iff_zeta_eq_zero
#print axioms GppGlobalCompleted.criticalStrip_completed_zero_iff_zeta_zero
#print axioms GppGlobalCompleted.criticalLine_completed_zero_iff_zeta_zero
