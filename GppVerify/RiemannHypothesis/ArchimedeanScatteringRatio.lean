import GppVerify.RiemannHypothesis.CompletedZetaReality
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The real-place Gamma factor: shadow-paired magnitude, oriented scattering ratio, log-derivative

Source: Codex, GPPDiscovery2 `research/2026-09-20_casimir_square_root_gamma_bridge.md`, §§1–5
(the exact Gamma identities; the Beta-integral and Casimir-resolvent readings are not formalized).

With `γ_ℝ(s) = π^{-s/2} Γ(s/2)` (Mathlib `Complex.Gammaℝ`) and `S_∞(s) = γ_ℝ(1−s)/γ_ℝ(s)`:

* `gamma_pair`: `γ_ℝ(s) γ_ℝ(1−s) = π^{-1/2} Γ(s/2) Γ((1−s)/2)`, the shadow-paired magnitude;
* `scattering_inv`: `S_∞(1−s) = S_∞(s)⁻¹`;
* `scattering_unimodular`: `|S_∞(1/2 + it)| = 1`;
* `functional_equation_ratio`: `ζ(1−s) γ_ℝ(1−s) = ζ(s) γ_ℝ(s)`, i.e. `ζ(1−s)/ζ(s) = S_∞(s)⁻¹`
  away from zeros: the arithmetic and real-place scattering ratios cancel (note §5);
* `logDeriv_gammaR`: `γ_ℝ'(s)/γ_ℝ(s) = −½ log π + ½ ψ(s/2)` (`g_∞`), where `ψ` is Mathlib's digamma.

## Checks and scope

All claims check (the note's `S_∞` is `γ_ℝ(1−s)/γ_ℝ(s)` as here). **Not formalized:** the Beta-integral
representation `γ_ℝ(s) γ_ℝ(1−s) = 2 ∫₀^∞ r^{s−1}(1+r²)^{-1/2} dr` (Mathlib has the Beta integral on
`[0,1]`, not on `(0,∞)`), the identification with the Casimir resolvent and the `H_C^{-1/2}` graph norm
(§§1, 6), and the endpoint-pole decomposition of the completed log-derivative. The cancellation in the
functional equation holds independently of RH and does not eliminate any zero. No RH claim.
-/

open Complex
open scoped Real ComplexConjugate

namespace GppArchimedeanScattering

/-- The oriented Archimedean scattering ratio `S_∞(s) = γ_ℝ(1−s)/γ_ℝ(s)`. -/
noncomputable def S (s : ℂ) : ℂ := Gammaℝ (1 - s) / Gammaℝ s

/-- **Shadow-paired magnitude.** -/
theorem gamma_pair (s : ℂ) :
    Gammaℝ s * Gammaℝ (1 - s) = (Real.pi : ℂ) ^ (-(1 / 2 : ℂ)) * (Gamma (s / 2) * Gamma ((1 - s) / 2)) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [Gammaℝ_def, Gammaℝ_def]
  have : (Real.pi : ℂ) ^ (-s / 2) * (Real.pi : ℂ) ^ (-(1 - s) / 2) = (Real.pi : ℂ) ^ (-(1 / 2 : ℂ)) := by
    rw [← cpow_add _ _ hπ]; congr 1; ring
  rw [← this]; ring

/-- **Reciprocal orientation**: `S(1−s) = S(s)⁻¹`. -/
theorem scattering_inv (s : ℂ) : S (1 - s) = (S s)⁻¹ := by
  unfold S
  rw [sub_sub_cancel, inv_div]

/-- **Unimodularity on the critical line.** -/
theorem scattering_unimodular (t : ℝ) : ‖S (1 / 2 + t * I)‖ = 1 := by
  unfold S
  have hre : 0 < (1 / 2 + (t : ℂ) * I).re := by simp
  have hne := Gammaℝ_ne_zero_of_re_pos hre
  have h1 : (1 : ℂ) - (1 / 2 + t * I) = conj (1 / 2 + t * I) := by
    apply Complex.ext
    · simp; norm_num
    · simp
  rw [h1, GppCompletedZetaReality.GammaR_conj, norm_div, Complex.norm_conj, div_self]
  exact norm_ne_zero_iff.mpr hne

/-- **The functional equation in `γ_ℝ`-form.** -/
theorem functional_equation_ratio (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) (hg : Gammaℝ s ≠ 0)
    (hg' : Gammaℝ (1 - s) ≠ 0) :
    riemannZeta (1 - s) * Gammaℝ (1 - s) = riemannZeta s * Gammaℝ s := by
  have h1' : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [riemannZeta_def_of_ne_zero h1', riemannZeta_def_of_ne_zero h0, div_mul_cancel₀ _ hg',
    div_mul_cancel₀ _ hg, completedRiemannZeta_one_sub]

/-- The arithmetic ratio is the reciprocal scattering ratio. -/
theorem zeta_ratio (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) (hg : Gammaℝ s ≠ 0)
    (hg' : Gammaℝ (1 - s) ≠ 0) (hz : riemannZeta s ≠ 0) :
    riemannZeta (1 - s) / riemannZeta s = (S s)⁻¹ := by
  have h := functional_equation_ratio s h0 h1 hg hg'
  unfold S
  rw [inv_div, div_eq_div_iff hz hg']
  linear_combination h

/-- The real-place logarithmic derivative `g_∞(s) = −½ log π + ½ ψ(s/2)`. -/
noncomputable def gInf (s : ℂ) : ℂ := -(1 / 2) * Complex.log Real.pi + (1 / 2) * digamma (s / 2)

/-- **`g_∞ = d log γ_ℝ`.** -/
theorem logDeriv_gammaR (s : ℂ) (hs : ∀ m : ℕ, s / 2 ≠ -m) :
    deriv Gammaℝ s / Gammaℝ s = gInf s := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hG : Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hs
  have hGd : HasDerivAt Gamma (deriv Gamma (s / 2)) (s / 2) :=
    (Complex.differentiableAt_Gamma _ hs).hasDerivAt
  have h2 : HasDerivAt (fun x : ℂ => x / 2) (1 / 2) s := (hasDerivAt_id s).div_const 2
  have hGc : HasDerivAt (fun x : ℂ => Gamma (x / 2)) (deriv Gamma (s / 2) * (1 / 2)) s :=
    hGd.comp s h2
  have hP : HasDerivAt (fun x : ℂ => (Real.pi : ℂ) ^ (-x / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-1 / 2)) s := by
    have := ((hasDerivAt_id s).neg.div_const 2).const_cpow (c := (Real.pi : ℂ)) (Or.inl hπ)
    simpa using this
  have hall : HasDerivAt (fun x : ℂ => (Real.pi : ℂ) ^ (-x / 2) * Gamma (x / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-1 / 2) * Gamma (s / 2) +
        (Real.pi : ℂ) ^ (-s / 2) * (deriv Gamma (s / 2) * (1 / 2))) s := hP.mul hGc
  have e : Gammaℝ = fun x : ℂ => (Real.pi : ℂ) ^ (-x / 2) * Gamma (x / 2) := rfl
  rw [e, hall.deriv]
  have hdig : deriv Gamma (s / 2) = Gamma (s / 2) * digamma (s / 2) := by
    unfold digamma
    rw [logDeriv_apply, mul_div_cancel₀ _ hG]
  have hpz : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [cpow_def_of_ne_zero hπ]; exact exp_ne_zero _
  rw [hdig]
  unfold gInf
  field_simp

end GppArchimedeanScattering
