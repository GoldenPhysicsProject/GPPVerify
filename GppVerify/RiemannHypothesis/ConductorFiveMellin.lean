import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.PSeries
import GppVerify.RiemannHypothesis.QuarticGaussFive

/-!
# The conductor-five Gaussian Mellin period: odd theta → completed `L(s, χ)`

Source: Codex, GPP-bridge `work/codex/2026-10-13_quartic_bc_to_tate_odd_gamma_exact_mellin.md` §2.

With the odd real-place test `f(x) = x e^{−πx²/5}` and coefficients `c_n`, the theta period
`Θ(y) = Σ_{n≥1} c_n f(n y)` has the exact Mellin transform (real `s > 1`, bounded `c`)
`∫₀^∞ Θ(y) y^{s−1} dy = ½ (5/π)^{(s+1)/2} Γ((s+1)/2) Σ_{n≥1} c_n n^{−s}`.
For Codex's Gauss operator, `c_n = 2 B_χ(n) = 2 χ(n) τ̄/4` (the ±n terms add, because `χ(−1) = −1`
and `f` is odd). That gives `(τ̄/4) Λ(s, χ)` with `Λ(s,χ) = (5/π)^{(s+1)/2} Γ((s+1)/2) L(s,χ)`,
the completed odd conductor-5 Dirichlet L-function.
* `term_mellin`: the single-term identity
  `∫₀^∞ (n y) e^{−π n² y²/5} y^{s−1} dy = ½ (5/π)^{(s+1)/2} Γ((s+1)/2) n^{−s}` for `s > −1`, `n ≥ 1`.
* `theta_mellin`: the series identity, with the termwise interchange justified by absolute
  summability (`s > 1`).

Real `s` only; the complex continuation is classical and **not formalized**. This is a
Tate-type identity, not Weil positivity. **No RH claim.**
-/

namespace GppConductorFiveMellin

open Real MeasureTheory Set

/-- The real-place odd Gaussian `f(x) = x e^{−πx²/5}`. -/
noncomputable def f (x : ℝ) : ℝ := x * Real.exp (-(π / 5) * x ^ 2)

/-- The common Archimedean factor `½ (5/π)^{(s+1)/2} Γ((s+1)/2)`. -/
noncomputable def arch (s : ℝ) : ℝ := (1 / 2) * (5 / π) ^ ((s + 1) / 2) * Real.Gamma ((s + 1) / 2)

theorem integrand_eq (n : ℝ) {s y : ℝ} (hy : 0 < y) :
    f (n * y) * y ^ (s - 1) = n * (y ^ s * Real.exp (-(π / 5 * n ^ 2) * y ^ (2 : ℝ))) := by
  unfold f
  have hys : y ^ s = y * y ^ (s - 1) := by
    conv_lhs => rw [show s = 1 + (s - 1) by ring]
    rw [Real.rpow_add hy, Real.rpow_one]
  rw [hys, Real.rpow_two]
  ring_nf

/-- **Single-term Mellin identity**. -/
theorem term_mellin {n : ℝ} (hn : 0 < n) {s : ℝ} (hs : -1 < s) :
    ∫ y in Ioi (0 : ℝ), f (n * y) * y ^ (s - 1) = arch s * n ^ (-s) := by
  have hb : 0 < π / 5 * n ^ 2 := by positivity
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy => integrand_eq n hy), integral_const_mul,
    integral_rpow_mul_exp_neg_mul_rpow (by norm_num) hs hb]
  unfold arch
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast n 2,
    ← Real.rpow_mul hn.le, Real.div_rpow (by positivity) (by positivity),
    Real.div_rpow (by positivity) (by positivity)]
  have h5 : (0 : ℝ) < 5 := by norm_num
  have hpi : 0 < π := Real.pi_pos
  have e1 : (π : ℝ) ^ (-(s + 1) / 2) = (π ^ ((s + 1) / 2))⁻¹ := by
    rw [neg_div, Real.rpow_neg hpi.le]
  have e2 : (5 : ℝ) ^ (-(s + 1) / 2) = ((5 : ℝ) ^ ((s + 1) / 2))⁻¹ := by
    rw [neg_div, Real.rpow_neg h5.le]
  have e3 : n ^ ((2 : ℕ) * (-(s + 1) / 2) : ℝ) = n ^ (-s) * n⁻¹ := by
    rw [show ((2 : ℕ) : ℝ) * (-(s + 1) / 2) = -s + -1 by push_cast; ring,
      Real.rpow_add hn, Real.rpow_neg_one]
  push_cast at e3 ⊢
  rw [e1, e2, e3]
  have hp1 : 0 < π ^ ((s + 1) / 2) := by positivity
  have hp5 : 0 < (5 : ℝ) ^ ((s + 1) / 2) := by positivity
  field_simp

theorem integrableOn_term {n : ℝ} (hn : 0 < n) {s : ℝ} (hs : -1 < s) :
    IntegrableOn (fun y => f (n * y) * y ^ (s - 1)) (Ioi 0) := by
  have hb : 0 < π / 5 * n ^ 2 := by positivity
  exact IntegrableOn.congr_fun
    (Integrable.const_mul (integrableOn_rpow_mul_exp_neg_mul_rpow hs (by norm_num : (0 : ℝ) < 2) hb) n)
    (fun y hy => (integrand_eq n hy).symm) measurableSet_Ioi

/-- **Theta–Mellin period**: for real `s > 1` and bounded coefficients,
`∫₀^∞ (Σ_{n≥1} c_n f(n y)) y^{s−1} dy = arch(s) · Σ_{n≥1} c_n n^{−s}`. -/
theorem theta_mellin {c : ℕ → ℂ} {C : ℝ} (hc : ∀ n, ‖c n‖ ≤ C) {s : ℝ} (hs : 1 < s) :
    ∫ y in Ioi (0 : ℝ), (∑' n : ℕ, c n * (f ((n + 1 : ℝ) * y) : ℂ)) * ((y ^ (s - 1) : ℝ) : ℂ) =
      (arch s : ℂ) * ∑' n : ℕ, c n * ((n + 1 : ℝ) ^ (-s) : ℝ) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < n + 1 := fun n => by positivity
  set F : ℕ → ℝ → ℂ := fun n y => c n * ((f ((n + 1 : ℝ) * y) * y ^ (s - 1) : ℝ) : ℂ) with hF
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := fun n =>
    ((integrableOn_term (hpos n) (by linarith)).ofReal).const_mul (c n)
  have hnorm : ∀ n, ∫ y in Ioi (0 : ℝ), ‖F n y‖ = ‖c n‖ * (arch s * (n + 1 : ℝ) ^ (-s)) := by
    intro n
    have habs : ∀ y ∈ Ioi (0 : ℝ), ‖F n y‖ = ‖c n‖ * (f ((n + 1 : ℝ) * y) * y ^ (s - 1)) := by
      intro y hy
      simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      congr 1
      rw [← abs_mul]
      apply abs_of_nonneg
      unfold f
      have := hpos n
      have hy' : (0 : ℝ) < y := hy
      positivity
    rw [setIntegral_congr_fun measurableSet_Ioi habs, integral_const_mul,
      term_mellin (hpos n) (by linarith)]
  have hsum : Summable fun n => ∫ y in Ioi (0 : ℝ), ‖F n y‖ := by
    simp_rw [hnorm]
    have hp : Summable fun n : ℕ => ((n + 1 : ℝ)) ^ (-s) := by
      have := ((Real.summable_nat_rpow (p := -s)).mpr (by linarith))
      exact (summable_nat_add_iff 1).mpr this |>.congr fun n => by push_cast; ring_nf
    refine Summable.of_nonneg_of_le (fun n => by
      have : 0 ≤ arch s := by unfold arch; positivity
      positivity) (fun n => ?_) ((hp.mul_left (arch s)).mul_left C)
    have ha : 0 ≤ arch s * (n + 1 : ℝ) ^ (-s) := by
      have : 0 ≤ arch s := by unfold arch; positivity
      positivity
    calc ‖c n‖ * (arch s * (n + 1 : ℝ) ^ (-s)) ≤ C * (arch s * (n + 1 : ℝ) ^ (-s)) :=
          mul_le_mul_of_nonneg_right (hc n) ha
      _ = C * (arch s * (n + 1 : ℝ) ^ (-s)) := rfl
  have key := integral_tsum_of_summable_integral_norm hint hsum
  have hlhs : ∀ y, (∑' n : ℕ, c n * (f ((n + 1 : ℝ) * y) : ℂ)) * ((y ^ (s - 1) : ℝ) : ℂ) =
      ∑' n, F n y := by
    intro y
    rw [← tsum_mul_right]
    congr 1; funext n
    simp only [hF]; push_cast; ring
  simp_rw [hlhs]
  rw [← key]
  rw [← tsum_mul_left]
  congr 1; funext n
  simp only [hF]
  rw [integral_const_mul, integral_complex_ofReal, term_mellin (hpos n) (by linarith)]
  push_cast; ring

open GppQuarticGaussFive in
theorem norm_B_le (x : ℕ) : ‖B x‖ ≤ 1 := by
  have hz : ∀ k : ℕ, ‖ζ ^ k‖ = 1 := fun k => by
    rw [norm_pow, zeta_prim.norm'_eq_one (by norm_num), one_pow]
  unfold B
  rw [norm_mul]
  have h4 : ‖ζ ^ x - Complex.I * ζ ^ (2 * x) + Complex.I * ζ ^ (3 * x) - ζ ^ (4 * x)‖ ≤ 4 := by
    calc _ ≤ ‖ζ ^ x - Complex.I * ζ ^ (2 * x) + Complex.I * ζ ^ (3 * x)‖ + ‖ζ ^ (4 * x)‖ :=
          norm_sub_le _ _
      _ ≤ ‖ζ ^ x - Complex.I * ζ ^ (2 * x)‖ + ‖Complex.I * ζ ^ (3 * x)‖ + ‖ζ ^ (4 * x)‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ ‖ζ ^ x‖ + ‖Complex.I * ζ ^ (2 * x)‖ + ‖Complex.I * ζ ^ (3 * x)‖ + ‖ζ ^ (4 * x)‖ := by
          gcongr; exact norm_sub_le _ _
      _ = 4 := by simp only [norm_mul, Complex.norm_I, hz]; norm_num
  have : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
  rw [this]; linarith

open GppQuarticGaussFive in
/-- **Codex's conductor-5 bridge**: with `c_n = 2 B_χ(n)`, the theta period's Mellin transform is
`(τ̄/4) (5/π)^{(s+1)/2} Γ((s+1)/2) Σ_{n≥1} χ(n) n^{−s} = (τ̄/4) Λ(s, χ)` for real `s > 1`. -/
theorem gauss_theta_mellin {s : ℝ} (hs : 1 < s) :
    ∫ y in Ioi (0 : ℝ), (∑' n : ℕ, (2 * B (n + 1)) * (f ((n + 1 : ℝ) * y) : ℂ)) *
        ((y ^ (s - 1) : ℝ) : ℂ) =
      taubar / 4 * (((5 / π) ^ ((s + 1) / 2) * Real.Gamma ((s + 1) / 2) : ℝ) : ℂ) *
        ∑' n : ℕ, chi ((n + 1) % 5) * (((n + 1 : ℝ) ^ (-s) : ℝ) : ℂ) := by
  have hc : ∀ n : ℕ, ‖(2 : ℂ) * B (n + 1)‖ ≤ 2 := fun n => by
    rw [norm_mul]; have := norm_B_le (n + 1); norm_num; linarith
  rw [theta_mellin hc hs]
  simp_rw [B_eq]
  rw [show (fun n : ℕ => 2 * (chi ((n + 1) % 5) * taubar / 4) * (((n + 1 : ℝ) ^ (-s) : ℝ) : ℂ)) =
      fun n : ℕ => (taubar / 2) * (chi ((n + 1) % 5) * (((n + 1 : ℝ) ^ (-s) : ℝ) : ℂ)) by
    funext n; ring]
  rw [tsum_mul_left]
  unfold arch
  push_cast
  ring

end GppConductorFiveMellin
