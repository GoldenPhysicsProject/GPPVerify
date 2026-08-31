import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# `∫₀^∞ u/cosh²u du = log 2` — the eta value in integral disguise

Thread C2 of `docs/FORMALIZATION_PLAN.md`: the exact improper integral

  `∫_{(0,∞)} u / cosh²(u) du = log 2`,

which is `η(1) = log 2` (the alternating harmonic series) in its Mellin disguise — the
normalization constant behind the biorthogonality relation (eq. (50)) of Yakaboylu,
*Nontrivial Riemann Zeros as Spectrum* (arXiv:2408.15135v14), and the base case of the
`sech²` Mellin transform used in Proposition 5.2 of the Abel-Cesàro companion paper
(`rh_cesaro_v2.tex`) to evaluate the eigenstate norm `N_{1/2}`.

**No series interchange is used.** The route is the antiderivative trick: `F(u) =
u·tanh(u) − log(cosh u)` satisfies `F' (u) = u/cosh²(u)` exactly, and `F(u) → log 2` at
infinity (from `cosh u = eᵘ(1+e^{−2u})/2`, the polynomially-killed exponential
`u·e^{−2u} → 0`, and continuity of `log` at `1`). Since the integrand is nonnegative,
Mathlib's `MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg` (verified present at the
pinned commit) yields **both** integrability and the value in one step:
`∫ = log 2 − F(0) = log 2`.

Along the way, `hasDerivAt_tanh` — `tanh'(x) = 1/cosh²(x)`, absent from the pinned
Mathlib — is derived from the `sinh/cosh` quotient rule and `cosh² − sinh² = 1`.
-/

namespace GppSechIntegral

open Filter MeasureTheory

/-- `tanh'(x) = 1/cosh²(x)`: the quotient rule on `sinh/cosh`, closed by
    `cosh² − sinh² = 1`. (The pinned Mathlib has derivative lemmas for `sinh`/`cosh` but
    not `tanh`.) -/
theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  have heq : (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2 =
      1 / Real.cosh x ^ 2 := by
    rw [show Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x =
        Real.cosh x ^ 2 - Real.sinh x ^ 2 by ring, Real.cosh_sq_sub_sinh_sq]
  rw [heq] at h
  have hfun : Real.tanh = Real.sinh / Real.cosh :=
    funext fun y => Real.tanh_eq_sinh_div_cosh y
  rw [hfun]
  exact h

/-- The antiderivative: `F(u) = u·tanh(u) − log(cosh u)`. -/
noncomputable def sechSqAntideriv (u : ℝ) : ℝ := u * Real.tanh u - Real.log (Real.cosh u)

/-- `F'(x) = x/cosh²(x)` exactly, everywhere. -/
theorem hasDerivAt_sechSqAntideriv (x : ℝ) :
    HasDerivAt sechSqAntideriv (x / Real.cosh x ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have h1 : HasDerivAt (fun y : ℝ => y * Real.tanh y)
      (1 * Real.tanh x + x * (1 / Real.cosh x ^ 2)) x :=
    (hasDerivAt_id x).mul (hasDerivAt_tanh x)
  have h2 : HasDerivAt (fun y : ℝ => Real.log (Real.cosh y))
      (Real.sinh x / Real.cosh x) x :=
    (Real.hasDerivAt_cosh x).log hc
  have h := h1.sub h2
  -- 4.33: `convert` strands defeq instance-path goals here. Rewrite the derivative
  -- value explicitly and let defeq match the function.
  have hval : (1 * Real.tanh x + x * (1 / Real.cosh x ^ 2)) - Real.sinh x / Real.cosh x
      = x / Real.cosh x ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    ring
  rw [← hval]
  exact h

/-- The closed-form rewrite of the antiderivative in terms of `E = e^{−2u}`:
    `F(u) = log 2 − 2u·E/(1+E) − log(1+E)`, valid for every `u`. This is the form whose
    limit at `+∞` is visible term by term. -/
theorem sechSqAntideriv_eq (u : ℝ) :
    sechSqAntideriv u =
      Real.log 2 - 2 * u * Real.exp (-(2 * u)) / (1 + Real.exp (-(2 * u))) -
        Real.log (1 + Real.exp (-(2 * u))) := by
  have hepos : (0 : ℝ) < Real.exp (-(2 * u)) := Real.exp_pos _
  have h1e : (0 : ℝ) < 1 + Real.exp (-(2 * u)) := by linarith
  have hsplit : Real.exp (-u) = Real.exp u * Real.exp (-(2 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have htanh : Real.tanh u = (1 - Real.exp (-(2 * u))) / (1 + Real.exp (-(2 * u))) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, hsplit]
    have hd : Real.exp u + Real.exp u * Real.exp (-(2 * u)) ≠ 0 := by positivity
    field_simp
  have hcosh : Real.cosh u = Real.exp u * (1 + Real.exp (-(2 * u))) / 2 := by
    rw [Real.cosh_eq, hsplit]
    ring
  have hlogcosh : Real.log (Real.cosh u) =
      u + Real.log (1 + Real.exp (-(2 * u))) - Real.log 2 := by
    rw [hcosh, Real.log_div (by positivity) two_ne_zero,
      Real.log_mul (Real.exp_ne_zero u) h1e.ne', Real.log_exp]
  show u * Real.tanh u - Real.log (Real.cosh u) = _
  rw [htanh, hlogcosh]
  field_simp
  ring

/-- `F(u) → log 2` as `u → ∞`: the `2u·e^{−2u}/(1+e^{−2u})` term dies (polynomial times
    decaying exponential over a denominator tending to `1`) and `log(1+e^{−2u}) → log 1 = 0`. -/
theorem tendsto_sechSqAntideriv_log_two :
    Tendsto sechSqAntideriv atTop (nhds (Real.log 2)) := by
  rw [tendsto_congr sechSqAntideriv_eq]
  have h2u : Tendsto (fun u : ℝ => 2 * u) atTop atTop :=
    Tendsto.const_mul_atTop two_pos tendsto_id
  have hnum : Tendsto (fun u : ℝ => 2 * u * Real.exp (-(2 * u))) atTop (nhds 0) := by
    have h : Tendsto (fun u : ℝ => (2 * u) ^ 1 * Real.exp (-(2 * u))) atTop (nhds 0) :=
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp h2u
    simpa only [pow_one] using h
  have hexp : Tendsto (fun u : ℝ => Real.exp (-(2 * u))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp h2u
  have hden : Tendsto (fun u : ℝ => 1 + Real.exp (-(2 * u))) atTop (nhds 1) := by
    have h : Tendsto (fun u : ℝ => 1 + Real.exp (-(2 * u))) atTop (nhds (1 + 0)) :=
      tendsto_const_nhds.add hexp
    simpa only [add_zero] using h
  have hA : Tendsto
      (fun u : ℝ => 2 * u * Real.exp (-(2 * u)) / (1 + Real.exp (-(2 * u))))
      atTop (nhds 0) := by
    have h := hnum.div hden one_ne_zero
    simpa only [Pi.div_def, zero_div] using h
  have hB : Tendsto (fun u : ℝ => Real.log (1 + Real.exp (-(2 * u)))) atTop (nhds 0) := by
    have h : Tendsto (fun u : ℝ => Real.log (1 + Real.exp (-(2 * u)))) atTop
        (nhds (Real.log 1)) :=
      (Real.continuousAt_log one_ne_zero).tendsto.comp hden
    rw [Real.log_one] at h
    exact h
  have h := (tendsto_const_nhds (x := Real.log 2) (f := (atTop : Filter ℝ))).sub hA |>.sub hB
  simpa only [sub_zero] using h

/-- `F(0) = 0`. -/
theorem sechSqAntideriv_zero : sechSqAntideriv 0 = 0 := by
  show (0 : ℝ) * Real.tanh 0 - Real.log (Real.cosh 0) = 0
  rw [Real.cosh_zero, Real.log_one, zero_mul, sub_zero]

/-- **`∫₀^∞ u/cosh²(u) du = log 2`** — Thread C2. The nonnegative integrand has the
    explicit antiderivative `F` with `F(∞) = log 2` and `F(0) = 0`, so
    `integral_Ioi_of_hasDerivAt_of_nonneg` delivers integrability and the value at once.
    This is `η(1) = log 2` in integral form: the normalization constant of Yakaboylu's
    biorthogonality relation, obtained with no series interchange. -/
theorem integral_id_div_cosh_sq :
    ∫ u in Set.Ioi (0 : ℝ), u / Real.cosh u ^ 2 = Real.log 2 := by
  have hcont : ContinuousWithinAt sechSqAntideriv (Set.Ici 0) 0 :=
    (hasDerivAt_sechSqAntideriv 0).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt sechSqAntideriv (x / Real.cosh x ^ 2) x :=
    fun x _ => hasDerivAt_sechSqAntideriv x
  have hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ x / Real.cosh x ^ 2 :=
    fun x hx => div_nonneg (le_of_lt hx) (by positivity)
  have h := integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos
    tendsto_sechSqAntideriv_log_two
  simpa [sechSqAntideriv_zero] using h

end GppSechIntegral
