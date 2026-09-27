import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# The Archimedean channel of the completed Weil form has a uniform floor

Source: Codex, GPPDiscovery2 `discovery/rh/RH_ARCHIMEDEAN_UNIFORM_STABILITY_2026-09-24.md`
(formalized here 2026-09-27).

For an admissible convolution square `g = f * f̃` normalized by `g(0) = ‖f‖² = 1`, the assembled
real-place term of the explicit formula is

  A∞(g) = -(γ + log π) g(0) + 2 ∫₀^∞ (e^{-2u} g(0) - e^{-u/2} Re g(u)) / (1 - e^{-2u}) du.

Writing `r u = Re g(u)`, splitting `e^{-2u} - e^{-u/2} r u = (e^{-2u} - e^{-u/2}) + e^{-u/2}(1 - r u)`
gives

  A∞ = C∞ + 2 ∫₀^∞ e^{-u/2} (1 - r u) / (1 - e^{-2u}) du,

with the state-independent constant

  C∞ = -γ - log π - π/2 - 3 log 2   (≈ -5.37218).

The second term is a nonnegative Dirichlet form once `r u ≤ 1`, which for `r u = Re⟨f, T_u f⟩`
with `‖f‖ = 1` is Cauchy–Schwarz for the unitary translation `T_u`. Hence `A∞ ≥ C∞`, uniformly in
the support of `f`.

## What is proved here

* `archimedean_constant_integral`: the improper integral
  `∫_{(0,∞)} 2 (e^{-2u} - e^{-u/2}) / (1 - e^{-2u}) du = -π/2 - 3 log 2`, by the explicit
  antiderivative `2 log(1 + e^{-u/2}) + log(1 + e^{-u}) + 2 arctan(e^{-u/2})`. The discovery note
  obtains the same value through `ψ(1/4) - ψ(1)`; no digamma value is needed here.
* `archimedean_decomposition`: the exact split `A∞ = C∞ + 2 · (Dirichlet form)`.
* `archimedean_floor`: `A∞ ≥ C∞` for every normalized `r` with `r ≤ 1` on `(0, ∞)`.

## What is not proved here

The bound `Re g(u) ≤ 1` is taken as a hypothesis rather than derived from an `L²` model of `f`;
integrability of the `A∞` integrand is likewise a hypothesis (it fails for `r` discontinuous at
`0`, so it cannot be dropped). The identification of `A∞` with the Archimedean term of Weil's
explicit formula is the discovery note's input and is not formalized. Nothing here bears on RH
directly: the note's conclusion is that the remaining instability must live in the pole–prime
channel, and this file certifies only the Archimedean half of that reduction.
-/

open Real MeasureTheory Set Filter Topology

namespace GppArchimedeanFloor

/-- The state-independent Archimedean floor `C∞ = -γ - log π - π/2 - 3 log 2`. -/
noncomputable def archimedeanFloor : ℝ :=
  -eulerMascheroniConstant - Real.log π - π / 2 - 3 * Real.log 2

/-- The kernel of the constant part: `2 (e^{-2u} - e^{-u/2}) / (1 - e^{-2u})`. -/
noncomputable def constKernel (u : ℝ) : ℝ :=
  2 * (Real.exp (-2 * u) - Real.exp (-u / 2)) / (1 - Real.exp (-2 * u))

/-- Explicit antiderivative of `constKernel`. -/
noncomputable def antideriv (u : ℝ) : ℝ :=
  2 * Real.log (1 + Real.exp (-u / 2)) + Real.log (1 + Real.exp (-u)) +
    2 * Real.arctan (Real.exp (-u / 2))

lemma antideriv_zero : antideriv 0 = 3 * Real.log 2 + π / 2 := by
  simp only [antideriv, neg_zero, zero_div, Real.exp_zero, Real.arctan_one]
  have h : (1 : ℝ) + 1 = 2 := by norm_num
  rw [h]
  ring

lemma continuous_antideriv : Continuous antideriv := by
  unfold antideriv
  have h1 : ∀ v : ℝ, 1 + Real.exp v ≠ 0 := fun v => by positivity
  refine ((continuous_const.mul ?_).add ?_).add
    (continuous_const.mul (Real.continuous_arctan.comp (by fun_prop)))
  · exact (continuous_const.add (by fun_prop)).log (fun u => h1 _)
  · exact (continuous_const.add (by fun_prop)).log (fun u => h1 _)

lemma hasDerivAt_antideriv (u : ℝ) (hu : 0 < u) :
    HasDerivAt antideriv (constKernel u) u := by
  set x := Real.exp (-u / 2) with hx
  have hxpos : 0 < x := Real.exp_pos _
  have hxlt : x < 1 := by rw [hx]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hx2 : Real.exp (-u) = x ^ 2 := by
    rw [hx, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hx4 : Real.exp (-2 * u) = x ^ 4 := by
    rw [hx, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  -- derivatives of the three inner functions
  have dA : HasDerivAt (fun v : ℝ => Real.exp (-v / 2)) (x * (-1 / 2)) u := by
    have := ((hasDerivAt_id u).neg.div_const 2).exp
    simpa [hx] using this
  have dB : HasDerivAt (fun v : ℝ => Real.exp (-v)) (x ^ 2 * (-1)) u := by
    have := (hasDerivAt_id u).neg.exp
    simpa [hx2] using this
  have h1 := ((dA.const_add 1).log (by positivity)).const_mul 2
  have h2 := (dB.const_add 1).log (by rw [hx2]; positivity)
  have h3 := (dA.arctan).const_mul 2
  have hsum : HasDerivAt antideriv
      (2 * (x * (-1 / 2) / (1 + Real.exp (-u / 2))) + x ^ 2 * -1 / (1 + Real.exp (-u)) +
        2 * (1 / (1 + Real.exp (-u / 2) ^ 2) * (x * (-1 / 2)))) u :=
    (h1.add h2).add h3
  refine hsum.congr_deriv ?_
  rw [hx2, ← hx]
  unfold constKernel
  rw [hx4, ← hx]
  have hd : 1 - x ^ 4 ≠ 0 := by
    have : x ^ 4 < 1 := pow_lt_one₀ hxpos.le hxlt (by norm_num)
    linarith
  have h1x : 1 + x ≠ 0 := by positivity
  have h1x2 : 1 + x ^ 2 ≠ 0 := by positivity
  have h1mx : 1 - x ≠ 0 := by linarith
  have hfac : 1 - x ^ 4 = (1 - x) * (1 + x) * (1 + x ^ 2) := by ring
  rw [hfac]
  field_simp
  ring

lemma constKernel_nonpos (u : ℝ) (hu : 0 < u) : constKernel u ≤ 0 := by
  unfold constKernel
  have hlt : Real.exp (-2 * u) < Real.exp (-u / 2) := Real.exp_lt_exp.mpr (by linarith)
  have hden : 0 < 1 - Real.exp (-2 * u) := by
    have : Real.exp (-2 * u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le

lemma tendsto_antideriv : Tendsto antideriv atTop (𝓝 0) := by
  have he : Tendsto (fun u : ℝ => Real.exp (-u / 2)) atTop (𝓝 0) := by
    have : Tendsto (fun u : ℝ => -u / 2) atTop atBot :=
      (tendsto_neg_atTop_atBot).atBot_div_const (by norm_num)
    exact Real.tendsto_exp_atBot.comp this
  let Φ : ℝ → ℝ := fun x =>
    2 * Real.log (1 + x) + Real.log (1 + x ^ 2) + 2 * Real.arctan x
  have hΦ : ContinuousAt Φ 0 := by
    have c1 : ContinuousAt (fun x : ℝ => Real.log (1 + x)) 0 :=
      (continuousAt_const.add continuousAt_id).log (by norm_num)
    have c2 : ContinuousAt (fun x : ℝ => Real.log (1 + x ^ 2)) 0 :=
      (continuousAt_const.add (continuousAt_id.pow 2)).log (by norm_num)
    exact ((continuousAt_const.mul c1).add c2).add
      (continuousAt_const.mul Real.continuous_arctan.continuousAt)
  have hΦ0 : Φ 0 = 0 := by simp [Φ]
  have hcomp : antideriv = Φ ∘ fun u => Real.exp (-u / 2) := by
    funext u
    simp only [antideriv, Φ, Function.comp]
    congr 3
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring_nf
  rw [hcomp, ← hΦ0]
  exact hΦ.tendsto.comp he

/-- **The constant integral.**
`∫_{(0,∞)} 2 (e^{-2u} - e^{-u/2}) / (1 - e^{-2u}) du = -π/2 - 3 log 2`. -/
theorem archimedean_constant_integral :
    ∫ u in Ioi (0 : ℝ), constKernel u = -π / 2 - 3 * Real.log 2 := by
  rw [integral_Ioi_of_hasDerivAt_of_nonpos continuous_antideriv.continuousWithinAt
    hasDerivAt_antideriv constKernel_nonpos tendsto_antideriv, antideriv_zero]
  ring

lemma integrableOn_constKernel : IntegrableOn constKernel (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonpos continuous_antideriv.continuousWithinAt
    hasDerivAt_antideriv constKernel_nonpos tendsto_antideriv

/-! ## The Archimedean term and its floor -/

/-- The integrand of the real-place term, with `r u` standing for `Re g(u)`. -/
noncomputable def archimedeanIntegrand (r : ℝ → ℝ) (u : ℝ) : ℝ :=
  (Real.exp (-2 * u) * r 0 - Real.exp (-u / 2) * r u) / (1 - Real.exp (-2 * u))

/-- The assembled real-place term
`A∞ = -(γ + log π) r(0) + 2 ∫₀^∞ (e^{-2u} r(0) - e^{-u/2} r(u)) / (1 - e^{-2u}) du`. -/
noncomputable def archimedeanTerm (r : ℝ → ℝ) : ℝ :=
  -(eulerMascheroniConstant + Real.log π) * r 0 +
    2 * ∫ u in Ioi (0 : ℝ), archimedeanIntegrand r u

/-- The integrand of the translation Dirichlet form, `e^{-u/2} (1 - r u) / (1 - e^{-2u})`. -/
noncomputable def dirichletIntegrand (r : ℝ → ℝ) (u : ℝ) : ℝ :=
  Real.exp (-u / 2) * (1 - r u) / (1 - Real.exp (-2 * u))

/-- The translation Dirichlet form `∫₀^∞ e^{-u/2} (1 - r u) / (1 - e^{-2u}) du`. -/
noncomputable def dirichletForm (r : ℝ → ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), dirichletIntegrand r u

lemma archimedeanIntegrand_split (r : ℝ → ℝ) (h0 : r 0 = 1) (u : ℝ) :
    archimedeanIntegrand r u = constKernel u / 2 + dirichletIntegrand r u := by
  unfold archimedeanIntegrand constKernel dirichletIntegrand
  rw [h0]
  ring

/-- **Exact decomposition.** For a normalized state (`r 0 = 1`) whose real-place integrand is
integrable, `A∞ = C∞ + 2 · (translation Dirichlet form)`. -/
theorem archimedean_decomposition (r : ℝ → ℝ) (h0 : r 0 = 1)
    (hint : IntegrableOn (archimedeanIntegrand r) (Ioi 0)) :
    archimedeanTerm r = archimedeanFloor + 2 * dirichletForm r := by
  have hc : IntegrableOn (fun u => constKernel u / 2) (Ioi 0) :=
    integrableOn_constKernel.div_const 2
  have hsplit : archimedeanIntegrand r =
      fun u => constKernel u / 2 + dirichletIntegrand r u :=
    funext (archimedeanIntegrand_split r h0)
  have hd : IntegrableOn (dirichletIntegrand r) (Ioi 0) := by
    have := hint.sub hc
    refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, archimedeanIntegrand_split r h0 u]
    ring
  have hI : ∫ u in Ioi (0 : ℝ), archimedeanIntegrand r u =
      (∫ u in Ioi (0 : ℝ), constKernel u) / 2 + dirichletForm r := by
    rw [hsplit, integral_add hc hd, integral_div]
    rfl
  rw [archimedeanTerm, hI, archimedean_constant_integral, h0, archimedeanFloor]
  ring

/-- **The Archimedean floor.** If `r 0 = 1` and `r u ≤ 1` for `u > 0` (Cauchy–Schwarz for
`r u = Re⟨f, T_u f⟩` with `‖f‖ = 1`), the real-place term is bounded below by the
state-independent constant `C∞ = -γ - log π - π/2 - 3 log 2`, whatever the support of `f`. -/
theorem archimedean_floor (r : ℝ → ℝ) (h0 : r 0 = 1) (hle : ∀ u, 0 < u → r u ≤ 1)
    (hint : IntegrableOn (archimedeanIntegrand r) (Ioi 0)) :
    archimedeanFloor ≤ archimedeanTerm r := by
  rw [archimedean_decomposition r h0 hint]
  have : 0 ≤ dirichletForm r := by
    refine setIntegral_nonneg measurableSet_Ioi (fun u hu => ?_)
    have hu : (0 : ℝ) < u := hu
    have hden : 0 < 1 - Real.exp (-2 * u) := by
      have : Real.exp (-2 * u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    unfold dirichletIntegrand
    have := hle u hu
    positivity
  linarith

end GppArchimedeanFloor
