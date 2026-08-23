import GppVerify.RHSpectralMultiplicity
import GppVerify.RiemannHypothesis.FunctionalEquation
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Tactic

/-!
# Reality of the completed zeta function on the critical line

The completed zeta function has two exact symmetries:

* functional-equation reflection `s -> 1-s`;
* complex-conjugation reality `s -> conj s`.

On `Re s = 1/2` these two involutions coincide. Consequently the completed zeta value is
real on the critical line. This is the exact algebraic content behind the equilibrium / detailed-
balance analogy used in the thermal bridge.
-/

namespace GppCompletedZetaReality

open Complex

private lemma conj_two_eq : conj (2 : ℂ) = 2 := by
  have h : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
  rw [h, conj_ofReal]

/-- Deligne's real Archimedean Gamma factor respects complex conjugation. -/
theorem GammaR_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  simp only [Gammaℝ]
  have harg : (↑Real.pi : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (le_of_lt Real.pi_pos)]
    exact Real.pi_pos.ne
  have hcd : conj s / 2 = conj (s / 2) := by rw [map_div₀, conj_two_eq]
  have hne : -(conj s) / 2 = conj (-(s / 2)) := by
    rw [map_neg, map_div₀, conj_two_eq, neg_div]
  simp only [hne, hcd, map_mul, ← Complex.Gamma_conj]
  congr 1
  rw [cpow_conj (↑Real.pi : ℂ) (-(s / 2)) harg, conj_ofReal]
  congr 1
  ring

/-- In the positive real half-plane, completed zeta is the Archimedean Gamma factor times zeta. -/
theorem completedZeta_eq_GammaR_mul_zeta {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hz := riemannZeta_def_of_ne_zero hs0
  calc
    completedRiemannZeta s = (completedRiemannZeta s / Gammaℝ s) * Gammaℝ s := by
      rw [div_mul_cancel₀ _ hG]
    _ = riemannZeta s * Gammaℝ s := by rw [← hz]
    _ = Gammaℝ s * riemannZeta s := by ring

/-- Completed zeta respects conjugation throughout the positive real half-plane. -/
theorem completedRiemannZeta_conj {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  have hcs : 0 < (conj s).re := by simpa using hs
  rw [completedZeta_eq_GammaR_mul_zeta hcs, completedZeta_eq_GammaR_mul_zeta hs]
  rw [GammaR_conj, GppRH.riemannZeta_conj]
  exact (map_mul (starRingEnd ℂ) (Gammaℝ s) (riemannZeta s)).symm

/-- **Critical-line reality.** The completed zeta function is real-valued on `Re s = 1/2`. -/
theorem completedRiemannZeta_im_eq_zero_of_re_half {s : ℂ} (hs : s.re = 1 / 2) :
    (completedRiemannZeta s).im = 0 := by
  have hspos : 0 < s.re := by rw [hs]; norm_num
  have heq : conj s = 1 - s := by
    exact GppFE.critical_line_is_fixed_locus s |>.2 hs
  have hreal : completedRiemannZeta s = conj (completedRiemannZeta s) := by
    calc
      completedRiemannZeta s = completedRiemannZeta (1 - s) :=
        (completedRiemannZeta_one_sub s).symm
      _ = completedRiemannZeta (conj s) := by rw [heq]
      _ = conj (completedRiemannZeta s) := completedRiemannZeta_conj hspos
  have him := congrArg Complex.im hreal
  simp [Complex.conj_im] at him
  linarith

end GppCompletedZetaReality

#print axioms GppCompletedZetaReality.GammaR_conj
#print axioms GppCompletedZetaReality.completedRiemannZeta_conj
#print axioms GppCompletedZetaReality.completedRiemannZeta_im_eq_zero_of_re_half
