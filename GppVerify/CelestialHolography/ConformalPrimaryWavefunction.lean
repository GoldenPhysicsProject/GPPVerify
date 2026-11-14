import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Massless conformal primary wavefunctions (PSS File 1)

Pasterski–Shao, arXiv:1705.01027, §2 and §4.1; Pasterski–Shao–Strominger, arXiv:1701.00049.
This is File 1 of the PSS formalisation package
(GPP-bridge `MuseResearch/turbo-pss-inventory-spec-2026-11-13.md`, §3).

## Conventions (the paper's)

* Spacetime `ℝ^{1,d+1}` is `Fin (d+2) → ℝ`, signature `(− + ⋯ +)` (1705.01027, footnote to §2):
  `X · Y = Σ_μ η_μ X^μ Y^μ` with `η_0 = −1` and `η_μ = 1` otherwise.
* The null vector of a boundary point `w̃ ∈ ℝ^d` is (2.9):
  `q(w̃) = (1 + |w̃|², 2 w̃, 1 − |w̃|²)`.
* The massless conformal primary wavefunction (4.4) is the regularised Mellin transform of the
  plane wave,
  `φ^σ_Δ(X; w̃) = ∫_0^∞ dω ω^{Δ−1} e^{σ i ω q·X − ε ω}`, `σ = ±1`, `ε > 0`.

## Main results

* `minkowski_null_vector`: `q(w̃) · q(w̃) = 0`.
* `integral_cpow_mul_cexp_neg_mul_Ioi`: for `Re a > 0` and `Re r > 0`,
  `∫_0^∞ t^{a−1} e^{−r t} dt = (1/r)^a Γ(a)`. Mathlib has this for real `r > 0`. The complex
  case follows by the identity theorem: both sides are holomorphic in `r` on `Re r > 0`.
* `mellin_planeWave_eq`: the regularised Mellin integral of the plane wave equals
  `Γ(Δ) (ε − σ i q·X)^{−Δ}`. That closed form is the definition `conformalPrimary`. It agrees
  with the paper's right-hand side `(∓i)^Δ Γ(Δ)/(−q·X ∓ iε)^Δ` up to the bookkeeping of the
  complex power, which is not formalised here.
* `box_conformalPrimary`: for every null `q`, `φ^σ_Δ` solves the massless Klein–Gordon
  equation `□ φ = Σ_μ η_μ ∂_μ² φ = 0` at every spacetime point. Because `ε > 0`, the argument
  `ε − σ i q·X` has positive real part, so there is no singular set.

The massive wavefunction (1701.00049 (2.10), a hyperboloid integral) is deferred.

No import from `GppVerify/RiemannHypothesis/`, directly or transitively (`scripts/check_pss_wall.py`).
Nothing here mentions `ξ` or `ζ`.
-/

open Complex MeasureTheory Set Filter Topology

namespace GppConformalPrimaryWavefunction

/-! ## Minkowski space and the null vector -/

/-- Spacetime `ℝ^{1,d+1}`. Index `0` is time. -/
abbrev Spacetime (d : ℕ) := Fin (d + 2) → ℝ

/-- The metric signature `η = diag(−1, 1, …, 1)`. -/
def eta (d : ℕ) (μ : Fin (d + 2)) : ℝ := if μ = 0 then -1 else 1

theorem eta_sq (d : ℕ) (μ : Fin (d + 2)) : eta d μ ^ 2 = 1 := by
  unfold eta; split_ifs <;> norm_num

/-- The Minkowski product `X · Y = Σ_μ η_μ X^μ Y^μ`. -/
def mink {d : ℕ} (X Y : Spacetime d) : ℝ := ∑ μ, eta d μ * X μ * Y μ

/-- `|w̃|²` for a boundary point. -/
def normSqW {d : ℕ} (w : Fin d → ℝ) : ℝ := ∑ i, w i ^ 2

/-- The null vector of a boundary point (1705.01027 (2.9)):
`q(w̃) = (1 + |w̃|², 2w̃, 1 − |w̃|²)`. -/
def nullVec {d : ℕ} (w : Fin d → ℝ) : Spacetime d :=
  Fin.cons (1 + normSqW w) (Fin.snoc (fun i => 2 * w i) (1 - normSqW w))

/-- **`q(w̃)` is null.** -/
theorem minkowski_null_vector {d : ℕ} (w : Fin d → ℝ) : mink (nullVec w) (nullVec w) = 0 := by
  unfold mink nullVec
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.snoc_castSucc, Fin.snoc_last, eta,
    Fin.succ_ne_zero, if_true, if_false]
  have h : ∑ i : Fin d, (1 : ℝ) * (2 * w i) * (2 * w i) = 4 * normSqW w := by
    unfold normSqW; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [h]; ring

/-! ## The complex-rate Gamma integral -/

/-- The integrand `t^{a−1} e^{−r t}`. -/
noncomputable def gammaIntegrand (a r : ℂ) (t : ℝ) : ℂ := (t : ℂ) ^ (a - 1) * cexp (-(r * t))

theorem norm_gammaIntegrand (a r : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖gammaIntegrand a r t‖ = t ^ (a.re - 1) * Real.exp (-(r.re * t)) := by
  unfold gammaIntegrand
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  simp

theorem integrableOn_gammaIntegrand {a r : ℂ} (ha : 0 < a.re) (hr : 0 < r.re) :
    IntegrableOn (gammaIntegrand a r) (Ioi 0) := by
  have hb : IntegrableOn (fun t : ℝ => t ^ (a.re - 1) * Real.exp (-r.re * t ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) (by norm_num) hr
  have hcont : ContinuousOn (gammaIntegrand a r) (Ioi 0) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    refine ContinuousAt.continuousWithinAt ?_
    unfold gammaIntegrand
    refine ContinuousAt.mul ?_ (by fun_prop)
    exact continuous_ofReal.continuousAt.cpow continuousAt_const (ofReal_mem_slitPlane.mpr ht')
  refine Integrable.mono' hb (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
  rw [norm_gammaIntegrand a r ht, Real.rpow_one, neg_mul]

/-- The open right half-plane. -/
def rightHalfPlane : Set ℂ := {r | 0 < r.re}

theorem isOpen_rightHalfPlane : IsOpen rightHalfPlane :=
  isOpen_lt continuous_const continuous_re

/-- The Gamma integral is complex-differentiable in the rate on `Re r > 0`. -/
theorem hasDerivAt_gammaIntegral {a r₀ : ℂ} (ha : 0 < a.re) (hr₀ : 0 < r₀.re) :
    HasDerivAt (fun r => ∫ t in Ioi (0 : ℝ), gammaIntegrand a r t)
      (∫ t in Ioi (0 : ℝ), -(t : ℂ) * gammaIntegrand a r₀ t) r₀ := by
  set c : ℝ := r₀.re / 2 with hc
  have hc0 : 0 < c := by positivity
  have hball : Metric.ball r₀ c ∈ 𝓝 r₀ := Metric.ball_mem_nhds r₀ hc0
  have hre : ∀ r ∈ Metric.ball r₀ c, c < r.re := by
    intro r hr
    have h1 : |r.re - r₀.re| < c := by
      have := Complex.abs_re_le_norm (r - r₀)
      rw [Metric.mem_ball, dist_eq_norm] at hr
      simp only [sub_re] at this; linarith
    have := (abs_lt.mp h1).1; linarith
  have hmeas : ∀ r : ℂ, AEStronglyMeasurable (gammaIntegrand a r) (volume.restrict (Ioi 0)) := by
    intro r
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    refine ContinuousAt.continuousWithinAt ?_
    unfold gammaIntegrand
    exact (continuous_ofReal.continuousAt.cpow continuousAt_const (ofReal_mem_slitPlane.mpr ht')).mul
      (by fun_prop)
  have hbound_int : Integrable (fun t : ℝ => t ^ ((a.re + 1) - 1) * Real.exp (-c * t ^ (1 : ℝ)))
      (volume.restrict (Ioi 0)) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) (by norm_num) hc0
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun r t => -(t : ℂ) * gammaIntegrand a r t) hball
    (Filter.Eventually.of_forall hmeas) (integrableOn_gammaIntegrand ha hr₀) ?_ ?_ hbound_int
    ?_).2
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    refine ContinuousAt.continuousWithinAt ?_
    unfold gammaIntegrand
    exact (by fun_prop : ContinuousAt (fun t : ℝ => -(t : ℂ)) t).mul
      ((continuous_ofReal.continuousAt.cpow continuousAt_const (ofReal_mem_slitPlane.mpr ht')).mul
        (by fun_prop))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht r hr => ?_)
    have ht' : (0 : ℝ) < t := ht
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg ht'.le,
      norm_gammaIntegrand a r ht', Real.rpow_one]
    have hexp : Real.exp (-(r.re * t)) ≤ Real.exp (-c * t) :=
      Real.exp_le_exp.mpr (by nlinarith [hre r hr])
    have hpow : t * t ^ (a.re - 1) = t ^ ((a.re + 1) - 1) := by
      rw [show (a.re + 1) - 1 = (a.re - 1) + 1 by ring, Real.rpow_add_one ht'.ne']; ring
    calc t * (t ^ (a.re - 1) * Real.exp (-(r.re * t)))
        = t ^ ((a.re + 1) - 1) * Real.exp (-(r.re * t)) := by rw [← hpow]; ring
      _ ≤ t ^ ((a.re + 1) - 1) * Real.exp (-c * t) :=
        mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg ht'.le _)
  · refine Filter.Eventually.of_forall fun t r _ => ?_
    unfold gammaIntegrand
    have h1 : HasDerivAt (fun r : ℂ => -(r * t)) (-(t : ℂ)) r := by
      exact (hasDerivAt_mul_const (t : ℂ)).neg
    have h2 := h1.cexp
    have h3 := h2.const_mul ((t : ℂ) ^ (a - 1))
    exact h3.congr_deriv (by ring)

/-- **The complex-rate Gamma integral.** For `Re a > 0` and `Re r > 0`,
`∫_0^∞ t^{a−1} e^{−r t} dt = (1/r)^a Γ(a)`. -/
theorem integral_cpow_mul_cexp_neg_mul_Ioi {a r : ℂ} (ha : 0 < a.re) (hr : 0 < r.re) :
    ∫ t in Ioi (0 : ℝ), gammaIntegrand a r t = (1 / r) ^ a * Gamma a := by
  have hF : AnalyticOnNhd ℂ (fun r => ∫ t in Ioi (0 : ℝ), gammaIntegrand a r t) rightHalfPlane :=
    DifferentiableOn.analyticOnNhd (fun r hr =>
      (hasDerivAt_gammaIntegral ha hr).differentiableAt.differentiableWithinAt)
      isOpen_rightHalfPlane
  have hG : AnalyticOnNhd ℂ (fun r : ℂ => (1 / r) ^ a * Gamma a) rightHalfPlane := by
    refine DifferentiableOn.analyticOnNhd (fun r hr => ?_) isOpen_rightHalfPlane
    have hr' : 0 < r.re := hr
    have hr0 : r ≠ 0 := fun h => by simp [h] at hr'
    have hslit : 1 / r ∈ slitPlane := by
      refine Or.inl ?_
      rw [one_div, inv_re]
      exact div_pos hr' (normSq_pos.mpr hr0)
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (((differentiableAt_const (1 : ℂ)).div differentiableAt_id hr0).cpow_const hslit).mul_const _
  have hpre : IsPreconnected rightHalfPlane := (convex_halfSpace_re_gt 0).isPreconnected
  have h1 : (1 : ℂ) ∈ rightHalfPlane := by show (0 : ℝ) < (1 : ℂ).re; simp
  have hreal : ∀ᶠ x : ℝ in 𝓝[≠] (1 : ℝ),
      (∫ t in Ioi (0 : ℝ), gammaIntegrand a (x : ℂ) t) = (1 / (x : ℂ)) ^ a * Gamma a := by
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))] with x hx
    have := Complex.integral_cpow_mul_exp_neg_mul_Ioi ha (show (0 : ℝ) < x from hx)
    simpa [gammaIntegrand] using this
  have htend : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] ((1 : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (Complex.continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact fun h => hx (Complex.ofReal_injective h)
  have hfreq := htend.frequently
    (p := fun z : ℂ => (∫ t in Ioi (0 : ℝ), gammaIntegrand a z t) = (1 / z) ^ a * Gamma a)
    hreal.frequently
  simp only [ofReal_one] at hfreq
  exact hF.eqOn_of_preconnected_of_frequently_eq hG hpre h1 hfreq hr

/-! ## The wavefunction -/

/-- The regularised plane wave `e^{σ i ω q·X − ε ω}`. -/
noncomputable def planeWave {d : ℕ} (σ ε : ℝ) (q X : Spacetime d) (ω : ℝ) : ℂ :=
  cexp (σ * I * ω * mink q X - ε * ω)

/-- The argument `ε − σ i q·X`. -/
noncomputable def arg' {d : ℕ} (σ ε : ℝ) (q X : Spacetime d) : ℂ := ε - σ * I * mink q X

theorem arg'_re {d : ℕ} (σ ε : ℝ) (q X : Spacetime d) : (arg' σ ε q X).re = ε := by
  simp [arg']

/-- **The massless conformal primary wavefunction** (closed form of 1705.01027 (4.4)),
`φ^σ_Δ(X) = Γ(Δ) (ε − σ i q·X)^{−Δ}`. -/
noncomputable def conformalPrimary {d : ℕ} (σ ε : ℝ) (Δ : ℂ) (q X : Spacetime d) : ℂ :=
  Gamma Δ * arg' σ ε q X ^ (-Δ)

/-- **The Mellin representation (4.4).** For `Re Δ > 0` and `ε > 0`, the regularised Mellin
transform of the plane wave is the conformal primary wavefunction. -/
theorem mellin_planeWave_eq {d : ℕ} (σ : ℝ) {ε : ℝ} (hε : 0 < ε) {Δ : ℂ} (hΔ : 0 < Δ.re)
    (q X : Spacetime d) :
    ∫ ω in Ioi (0 : ℝ), (ω : ℂ) ^ (Δ - 1) * planeWave σ ε q X ω = conformalPrimary σ ε Δ q X := by
  have hr : 0 < (arg' σ ε q X).re := by rw [arg'_re]; exact hε
  have hint := integral_cpow_mul_cexp_neg_mul_Ioi hΔ hr
  have hcongr : (fun ω : ℝ => (ω : ℂ) ^ (Δ - 1) * planeWave σ ε q X ω) =
      gammaIntegrand Δ (arg' σ ε q X) := by
    funext ω; unfold planeWave gammaIntegrand arg'; congr 2; ring
  rw [hcongr, hint]
  unfold conformalPrimary
  have hne : (arg' σ ε q X).arg ≠ Real.pi := by
    intro h; rw [arg_eq_pi_iff] at h; linarith [h.1]
  rw [one_div, inv_cpow _ _ hne, ← cpow_neg, mul_comm]

/-! ## The Klein–Gordon equation -/

/-- The second partial derivative `∂_μ² Φ` at `X`, along the coordinate line. -/
noncomputable def partial2 {d : ℕ} (μ : Fin (d + 2)) (Φ : Spacetime d → ℂ) (X : Spacetime d) : ℂ :=
  iteratedDeriv 2 (fun t : ℝ => Φ (X + t • Pi.single μ 1)) 0

/-- The d'Alembertian `□ Φ = Σ_μ η_μ ∂_μ² Φ`. -/
noncomputable def box {d : ℕ} (Φ : Spacetime d → ℂ) (X : Spacetime d) : ℂ :=
  ∑ μ, (eta d μ : ℂ) * partial2 μ Φ X

theorem mink_add_single {d : ℕ} (q X : Spacetime d) (μ : Fin (d + 2)) (t : ℝ) :
    mink q (X + t • Pi.single μ 1) = mink q X + t * (eta d μ * q μ) := by
  unfold mink
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single μ]
  · simp; ring
  · intro ν _ hν; simp [hν]
  · simp

/-- Second derivative of `t ↦ (A + B t)^c` along a line kept in the slit plane. -/
theorem iteratedDeriv_two_cpow_line {A B c : ℂ} (hslit : ∀ t : ℝ, A + B * t ∈ slitPlane) :
    iteratedDeriv 2 (fun t : ℝ => (A + B * t) ^ c) 0 = c * (c - 1) * B ^ 2 * A ^ (c - 2) := by
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => A + B * (s : ℂ)) B t := by
    intro t
    have := ((hasDerivAt_id t).ofReal_comp).const_mul B
    simpa using this.const_add A
  have hpow : ∀ (e : ℂ) (t : ℝ), HasDerivAt (fun s : ℝ => (A + B * (s : ℂ)) ^ e)
      (e * (A + B * (t : ℂ)) ^ (e - 1) * B) t := fun e t =>
    HasDerivAt.comp t (h₂ := fun z : ℂ => z ^ e)
      (Complex.hasStrictDerivAt_cpow_const (c := e) (hslit t)).hasDerivAt (hline t)
  have h1 : deriv (fun t : ℝ => (A + B * (t : ℂ)) ^ c) =
      fun t : ℝ => c * (A + B * (t : ℂ)) ^ (c - 1) * B := by
    funext t; exact (hpow c t).deriv
  have h2 : deriv (fun t : ℝ => c * (A + B * (t : ℂ)) ^ (c - 1) * B) 0 =
      c * ((c - 1) * (A + B * ((0 : ℝ) : ℂ)) ^ (c - 1 - 1) * B) * B := by
    have := ((hpow (c - 1) 0).const_mul c).mul_const B
    exact this.deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1, h2]
  simp only [ofReal_zero, mul_zero, add_zero]
  rw [show c - 1 - 1 = c - 2 by ring]
  ring

/-- **The massless Klein–Gordon equation.** For every null `q`, every real `σ`, `ε > 0` and
every `Δ`, the conformal primary wavefunction satisfies `□ φ^σ_Δ = 0` at every point. -/
theorem box_conformalPrimary {d : ℕ} (σ : ℝ) {ε : ℝ} (hε : 0 < ε) (Δ : ℂ) {q : Spacetime d}
    (hq : mink q q = 0) (X : Spacetime d) :
    box (conformalPrimary σ ε Δ q) X = 0 := by
  have hμ : ∀ μ : Fin (d + 2), partial2 μ (conformalPrimary σ ε Δ q) X =
      Gamma Δ * ((-Δ) * (-Δ - 1) * (-(σ : ℂ) * I * (eta d μ * q μ)) ^ 2 *
        arg' σ ε q X ^ (-Δ - 2)) := by
    intro μ
    unfold partial2 conformalPrimary
    have hline : (fun t : ℝ => Gamma Δ * arg' σ ε q (X + t • Pi.single μ 1) ^ (-Δ)) =
        fun t : ℝ => Gamma Δ * (arg' σ ε q X + (-(σ : ℂ) * I * (eta d μ * q μ)) * t) ^ (-Δ) := by
      funext t; unfold arg'; rw [mink_add_single]; push_cast; ring_nf
    rw [hline, iteratedDeriv_const_mul_field]
    congr 1
    refine iteratedDeriv_two_cpow_line (fun t => Or.inl ?_)
    simp [arg', hε]
  unfold box
  simp_rw [hμ]
  have hsum : ∑ μ : Fin (d + 2), (eta d μ : ℂ) * (eta d μ * q μ : ℂ) ^ 2 = (mink q q : ℂ) := by
    unfold mink; push_cast
    refine Finset.sum_congr rfl fun μ _ => ?_
    have he : (eta d μ : ℂ) ^ 2 = 1 := by exact_mod_cast eta_sq d μ
    linear_combination (q μ : ℂ) ^ 2 * eta d μ * he
  have hfactor : ∀ μ : Fin (d + 2), (eta d μ : ℂ) * (Gamma Δ * ((-Δ) * (-Δ - 1) *
      (-(σ : ℂ) * I * (eta d μ * q μ)) ^ 2 * arg' σ ε q X ^ (-Δ - 2))) =
      (Gamma Δ * ((-Δ) * (-Δ - 1) * (-(σ : ℂ) * I) ^ 2 * arg' σ ε q X ^ (-Δ - 2))) *
        ((eta d μ : ℂ) * (eta d μ * q μ : ℂ) ^ 2) := by
    intro μ; ring
  simp_rw [hfactor, ← Finset.mul_sum, hsum, hq]
  simp

/-- The PSS wavefunction of a boundary point solves the massless Klein–Gordon equation. -/
theorem box_conformalPrimary_nullVec {d : ℕ} (σ : ℝ) {ε : ℝ} (hε : 0 < ε) (Δ : ℂ)
    (w : Fin d → ℝ) (X : Spacetime d) :
    box (conformalPrimary σ ε Δ (nullVec w)) X = 0 :=
  box_conformalPrimary σ hε Δ (minkowski_null_vector w) X

end GppConformalPrimaryWavefunction

#print axioms GppConformalPrimaryWavefunction.minkowski_null_vector
#print axioms GppConformalPrimaryWavefunction.integral_cpow_mul_cexp_neg_mul_Ioi
#print axioms GppConformalPrimaryWavefunction.mellin_planeWave_eq
#print axioms GppConformalPrimaryWavefunction.box_conformalPrimary
#print axioms GppConformalPrimaryWavefunction.box_conformalPrimary_nullVec
