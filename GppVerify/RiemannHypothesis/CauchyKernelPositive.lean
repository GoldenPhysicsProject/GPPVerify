import GppVerify.RiemannHypothesis.ConvolutionSquarePositive
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The Cauchy kernel is positive-type: the on-line half of the finite-ε Gram positivity

Thread K of `docs/FORMALIZATION_PLAN.md`, companion to the form-domain note on Yakaboylu
(arXiv:2408.15135 v15) Theorem 5.1. On the critical line the regularized matrix element
(the paper's eqs. (50)/(52)) `⟨Ψ_s|V̂_{R,ε}|Ψ_{s'}⟩ = ε²/(ε² − (s̄+s'−1)²)` reduces to the
**Cauchy kernel** `ε²/(ε² + (γ'−γ)²)`, and this file proves that kernel is positive-type
in the exact `PositiveType` sense of `HaarPositivityWeil.lean`: every finite Gram matrix
built from on-line points is PSD, at every `ε > 0`. Together with the −2 test-vector
mechanism (`YakaboyluPositivityKernel.lean`, `WeilPositivityCriterion.lean`) this splits
the finite-ε structure of the paper's eq. (75) exactly as the note does:

* **on the line** (`cauchy_kernel_positive_type`): every bracket is a genuine PSD
  quadratic form — via the Bochner representation
  `ε²/(ε²+x²) = ε·∫₀^∞ e^{−εt}·cos(xt) dt` (the damped-cosine integral, proved here by
  explicit antiderivative) and a Gram square in the amplitudes `cos(xᵢt)`, `sin(xᵢt)`;
* **the reduction itself** (`matrix_element_on_line`): for `s = 1/2 + iγ`,
  `s' = 1/2 + iγ'` the complex matrix element equals the real Cauchy kernel — exact
  algebra, no analysis;
* **off the line** (`matrix_element_off_line_diag`, `off_line_diag_neg` — the note's
  Proposition 2.1): for `ρ₀ = 1/2 + δ + iγ₀` the diagonal element is `ε²/(ε²−4δ²)`,
  strictly negative for every `ε ∈ (0, 2δ)` — positivity fails below the form-domain
  threshold `ε = 2δ`;
* **the limiting eigenvalue** (`tendsto_offline_min_eigenvalue` — the note's eq. (7)):
  the smallest eigenvalue `d(ε) − 1` of the off-line 2×2 block tends to `−1` as
  `ε → 0⁺`.

What is deliberately NOT claimed: any uniformity of the `ε → 0⁺` limit over infinite
zero configurations. By `rh_iff_weil_pairedForm_nonneg` that uniformity is equivalent
to RH itself, and it stays open here — this file fences the provable finite-ε skeleton
on both sides of the form-domain boundary and nothing more.
-/

namespace GppCauchyKernel

open MeasureTheory Set Filter GppHaarPositivityWeil

/-! ## K1: the damped-cosine integral `∫₀^∞ e^{−bt}·cos(xt) dt = b/(b²+x²)` -/

/-- The damped cosine is integrable on `(0,∞)`, dominated by `e^{−bt}`. -/
theorem integrableOn_exp_neg_mul_cos {b : ℝ} (hb : 0 < b) (x : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-b*t) * Real.cos (x*t)) (Ioi (0:ℝ)) := by
  refine (exp_neg_integrableOn_Ioi 0 hb).mono' ?_ ?_
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    apply Filter.Eventually.of_forall
    intro t _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-b*t) * |Real.cos (x*t)|
        ≤ Real.exp (-b*t) * 1 :=
          mul_le_mul_of_nonneg_left
            (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩) (Real.exp_pos _).le
      _ = Real.exp (-b*t) := mul_one _

/-- The explicit antiderivative `e^{−bt}·(x·sin(xt) − b·cos(xt))/(b²+x²)` of the damped
    cosine. -/
theorem hasDerivAt_dampedCosAntideriv {b x : ℝ} (hden : b^2 + x^2 ≠ 0) (t : ℝ) :
    HasDerivAt
      (fun u => Real.exp (-b*u) * (x * Real.sin (x*u) - b * Real.cos (x*u)) / (b^2 + x^2))
      (Real.exp (-b*t) * Real.cos (x*t)) t := by
  have hlinb : HasDerivAt (fun u : ℝ => -b*u) (-b) t := by
    simpa using (hasDerivAt_id t).const_mul (-b)
  have hlinx : HasDerivAt (fun u : ℝ => x*u) x t := by
    simpa using (hasDerivAt_id t).const_mul x
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (-b*u)) (Real.exp (-b*t) * (-b)) t :=
    hlinb.exp
  have hsin : HasDerivAt (fun u : ℝ => Real.sin (x*u)) (Real.cos (x*t) * x) t := hlinx.sin
  have hcos : HasDerivAt (fun u : ℝ => Real.cos (x*u)) (-Real.sin (x*t) * x) t := hlinx.cos
  have hnum : HasDerivAt (fun u : ℝ => x * Real.sin (x*u) - b * Real.cos (x*u))
      (x * (Real.cos (x*t) * x) - b * (-Real.sin (x*t) * x)) t :=
    (hsin.const_mul x).sub (hcos.const_mul b)
  have h : HasDerivAt
      (fun u => Real.exp (-b*u) * (x * Real.sin (x*u) - b * Real.cos (x*u)) / (b^2 + x^2))
      ((Real.exp (-b*t) * (-b) * (x * Real.sin (x*t) - b * Real.cos (x*t)) +
        Real.exp (-b*t) * (x * (Real.cos (x*t) * x) - b * (-Real.sin (x*t) * x))) /
          (b^2 + x^2)) t := (hexp.mul hnum).div_const (b^2 + x^2)
  have hval : (Real.exp (-b*t) * (-b) * (x * Real.sin (x*t) - b * Real.cos (x*t)) +
      Real.exp (-b*t) * (x * (Real.cos (x*t) * x) - b * (-Real.sin (x*t) * x))) /
        (b^2 + x^2) = Real.exp (-b*t) * Real.cos (x*t) := by
    rw [div_eq_iff hden]
    ring
  rw [hval] at h
  exact h

/-- The antiderivative vanishes at infinity, squeezed by `±(|x|+b)·e^{−bt}/(b²+x²)`. -/
theorem tendsto_dampedCosAntideriv {b x : ℝ} (hb : 0 < b) :
    Tendsto
      (fun t : ℝ => Real.exp (-b*t) * (x * Real.sin (x*t) - b * Real.cos (x*t)) / (b^2 + x^2))
      atTop (nhds 0) := by
  have hden : (0:ℝ) < b^2 + x^2 := by positivity
  have hexp0 : Tendsto (fun t : ℝ => Real.exp (-b*t)) atTop (nhds 0) := by
    have h : Tendsto (fun t : ℝ => Real.exp (-(b*t))) atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop hb tendsto_id)
    simpa only [neg_mul] using h
  have hupper : Tendsto (fun t : ℝ => Real.exp (-b*t) * (|x| + b) / (b^2 + x^2))
      atTop (nhds 0) := by
    have h := (hexp0.mul_const (|x| + b)).div_const (b^2 + x^2)
    simpa only [zero_mul, zero_div] using h
  have hlower : Tendsto (fun t : ℝ => -(Real.exp (-b*t) * (|x| + b) / (b^2 + x^2)))
      atTop (nhds 0) := by
    have h := hupper.neg
    simpa only [neg_zero] using h
  have key : ∀ t : ℝ,
      |Real.exp (-b*t) * (x * Real.sin (x*t) - b * Real.cos (x*t)) / (b^2 + x^2)|
        ≤ Real.exp (-b*t) * (|x| + b) / (b^2 + x^2) := by
    intro t
    have hnum : |x * Real.sin (x*t) - b * Real.cos (x*t)| ≤ |x| + b := by
      have h1 : |x * Real.sin (x*t) - b * Real.cos (x*t)|
          ≤ |x * Real.sin (x*t)| + |b * Real.cos (x*t)| := by
        rw [sub_eq_add_neg]
        calc |x * Real.sin (x*t) + -(b * Real.cos (x*t))|
            ≤ |x * Real.sin (x*t)| + |-(b * Real.cos (x*t))| := abs_add_le _ _
          _ = |x * Real.sin (x*t)| + |b * Real.cos (x*t)| := by rw [abs_neg]
      have hs : |x * Real.sin (x*t)| ≤ |x| := by
        rw [abs_mul]
        calc |x| * |Real.sin (x*t)| ≤ |x| * 1 :=
              mul_le_mul_of_nonneg_left
                (abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩) (abs_nonneg x)
          _ = |x| := mul_one _
      have hc : |b * Real.cos (x*t)| ≤ b := by
        rw [abs_mul, abs_of_pos hb]
        calc b * |Real.cos (x*t)| ≤ b * 1 :=
              mul_le_mul_of_nonneg_left
                (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩) hb.le
          _ = b := mul_one _
      linarith
    rw [abs_div, abs_of_pos hden, abs_mul, abs_of_pos (Real.exp_pos _)]
    gcongr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper
  · exact fun t => (abs_le.mp (key t)).1
  · exact fun t => (abs_le.mp (key t)).2

/-- **The damped-cosine integral**: `∫₀^∞ e^{−bt}·cos(xt) dt = b/(b²+x²)` for `b > 0` —
    the Fourier half of the Bochner representation of the Cauchy kernel. -/
theorem integral_exp_neg_mul_cos {b : ℝ} (hb : 0 < b) (x : ℝ) :
    ∫ t in Ioi (0:ℝ), Real.exp (-b*t) * Real.cos (x*t) = b / (b^2 + x^2) := by
  have hden : (0:ℝ) < b^2 + x^2 := by positivity
  have key := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0:ℝ))
    (fun t _ => hasDerivAt_dampedCosAntideriv hden.ne' t)
    (integrableOn_exp_neg_mul_cos hb x)
    (tendsto_dampedCosAntideriv hb)
  rw [key]
  norm_num [Real.sin_zero, Real.cos_zero, Real.exp_zero, neg_div]

/-! ## K2: the Cauchy kernel is positive-type -/

/-- The Bochner representation `ε²/(ε²+x²) = ∫₀^∞ ε·e^{−εt}·cos(xt) dt`. -/
theorem cauchy_kernel_eq_integral {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    ε^2 / (ε^2 + x^2) = ∫ t in Ioi (0:ℝ), ε * (Real.exp (-ε*t) * Real.cos (x*t)) := by
  rw [integral_const_mul, integral_exp_neg_mul_cos hε x, pow_two, mul_div_assoc]

/-- **The Cauchy kernel is positive-type**: for every `ε > 0`, all finite Gram matrices
    `[ε²/(ε² + (xᵢ−xⱼ)²)]` are PSD — the kernel-checked on-line half of the finite-ε
    positivity in Yakaboylu's eq. (75). -/
theorem cauchy_kernel_positive_type {ε : ℝ} (hε : 0 < ε) :
    PositiveType (fun x => ε^2 / (ε^2 + x^2)) := by
  -- The kernel is even in `x` (it depends on `x` only through `x^2`), which is
  -- what `positiveType_of_even_of_re` needs. The Bochner argument below is the
  -- original real-part proof, unchanged.
  refine positiveType_of_even_of_re (fun t => by ring_nf) (fun n x c => ?_)
  -- Step 1: rewrite each matrix entry through the Bochner representation.
  have hentry : ∀ i j : Fin n,
      (((fun y => ε^2 / (ε^2 + y^2)) (x i - x j) : ℝ) : ℂ) =
        ((∫ t in Ioi (0:ℝ), ε * (Real.exp (-ε*t) * Real.cos ((x i - x j)*t)) : ℝ) : ℂ) := by
    intro i j
    norm_cast
    exact cauchy_kernel_eq_integral hε (x i - x j)
  simp only [hentry]
  -- Step 2: push `.re` through the double sum and strip the real coercion.
  rw [Complex.re_sum]
  have hterm : ∀ i : Fin n,
      (∑ j : Fin n, (starRingEnd ℂ) (c i) * c j *
        ((∫ t in Ioi (0:ℝ), ε * (Real.exp (-ε*t) * Real.cos ((x i - x j)*t)) : ℝ) : ℂ)).re =
      ∑ j : Fin n, ((starRingEnd ℂ) (c i) * c j).re *
        ∫ t in Ioi (0:ℝ), ε * (Real.exp (-ε*t) * Real.cos ((x i - x j)*t)) := by
    intro i
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_ofReal_re]
  simp only [hterm]
  -- Step 3: interchange the finite double sum with the integral.
  have hint : ∀ i j : Fin n,
      IntegrableOn (fun t : ℝ => ((starRingEnd ℂ) (c i) * c j).re *
        (ε * (Real.exp (-ε*t) * Real.cos ((x i - x j)*t)))) (Ioi (0:ℝ)) :=
    fun i j => ((integrableOn_exp_neg_mul_cos hε (x i - x j)).const_mul ε).const_mul _
  have hswap : ∑ i : Fin n, ∑ j : Fin n, ((starRingEnd ℂ) (c i) * c j).re *
      ∫ t in Ioi (0:ℝ), ε * (Real.exp (-ε*t) * Real.cos ((x i - x j)*t)) =
      ∫ t in Ioi (0:ℝ), ∑ i : Fin n, ∑ j : Fin n, ((starRingEnd ℂ) (c i) * c j).re *
        (ε * (Real.exp (-ε*t) * Real.cos ((x i - x j)*t))) := by
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro j _
        simp only [integral_const_mul]
      · exact fun j _ => hint i j
    · exact fun i _ => integrable_finset_sum _ fun j _ => hint i j
  rw [hswap]
  -- Step 4: pointwise, the integrand splits into two Gram squares via cos(A−B).
  apply setIntegral_nonneg measurableSet_Ioi
  intro t _
  have hsplit : ∀ i j : Fin n, ((starRingEnd ℂ) (c i) * c j).re *
      (ε * (Real.exp (-ε*t) * Real.cos ((x i - x j)*t))) =
      ε * Real.exp (-ε*t) *
        (((starRingEnd ℂ) (c i) * c j).re * (Real.cos (x i * t) * Real.cos (x j * t))) +
      ε * Real.exp (-ε*t) *
        (((starRingEnd ℂ) (c i) * c j).re * (Real.sin (x i * t) * Real.sin (x j * t))) := by
    intro i j
    rw [sub_mul, Real.cos_sub]
    ring
  simp only [hsplit]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  apply add_nonneg
  · exact mul_nonneg (mul_nonneg hε.le (Real.exp_pos _).le)
      (gram_square_nonneg c fun i => Real.cos (x i * t))
  · exact mul_nonneg (mul_nonneg hε.le (Real.exp_pos _).le)
      (gram_square_nonneg c fun i => Real.sin (x i * t))

/-! ## K3: the form-domain dichotomy of the note, as exact algebra -/

/-- **On the critical line the matrix element IS the Cauchy kernel**: for
    `s = 1/2 + iγ`, `s' = 1/2 + iγ'`, one has `s̄ + s' − 1 = i(γ'−γ)` and hence
    `ε²/(ε² − (s̄+s'−1)²) = ε²/(ε² + (γ'−γ)²)` — the provable half of the dichotomy. -/
theorem matrix_element_on_line (ε γ γ' : ℝ) :
    (ε:ℂ)^2 / ((ε:ℂ)^2 - ((starRingEnd ℂ) (((1/2 : ℝ) : ℂ) + (γ:ℂ) * Complex.I) +
      (((1/2 : ℝ) : ℂ) + (γ':ℂ) * Complex.I) - 1)^2) =
      ((ε^2 / (ε^2 + (γ' - γ)^2) : ℝ) : ℂ) := by
  have h1 : (starRingEnd ℂ) (((1/2 : ℝ) : ℂ) + (γ:ℂ) * Complex.I) +
      (((1/2 : ℝ) : ℂ) + (γ':ℂ) * Complex.I) - 1 = ((γ' - γ : ℝ) : ℂ) * Complex.I := by
    rw [map_add, Complex.conj_ofReal, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have h2 : (((γ' - γ : ℝ) : ℂ) * Complex.I)^2 = -(((γ' - γ)^2 : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_sq]
    push_cast
    ring
  rw [h1, h2, sub_neg_eq_add]
  push_cast
  ring

/-- **The note's Proposition 2.1, computational half**: for `ρ₀ = 1/2 + δ + iγ₀` the
    diagonal combination is real — `ρ̄₀ + ρ₀ − 1 = 2δ` — so the diagonal matrix element
    is `ε²/(ε² − 4δ²)`, exactly. -/
theorem matrix_element_off_line_diag (ε δ γ0 : ℝ) :
    (ε:ℂ)^2 / ((ε:ℂ)^2 - ((starRingEnd ℂ) (((1/2 + δ : ℝ) : ℂ) + (γ0:ℂ) * Complex.I) +
      (((1/2 + δ : ℝ) : ℂ) + (γ0:ℂ) * Complex.I) - 1)^2) =
      ((ε^2 / (ε^2 - 4*δ^2) : ℝ) : ℂ) := by
  have h1 : (starRingEnd ℂ) (((1/2 + δ : ℝ) : ℂ) + (γ0:ℂ) * Complex.I) +
      (((1/2 + δ : ℝ) : ℂ) + (γ0:ℂ) * Complex.I) - 1 = ((2*δ : ℝ) : ℂ) := by
    rw [map_add, Complex.conj_ofReal, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [h1]
  push_cast
  ring

/-- **The note's Proposition 2.1, sign half**: the off-line diagonal `ε²/(ε²−4δ²)` is
    strictly negative for every `ε ∈ (0, 2δ)` — a positive operator admits no negative
    diagonal form value, so positivity fails below the form-domain threshold `ε = 2δ`. -/
theorem off_line_diag_neg {ε δ : ℝ} (hε : 0 < ε) (hδ : ε < 2*δ) :
    ε^2 / (ε^2 - 4*δ^2) < 0 :=
  div_neg_of_pos_of_neg (by positivity) (by nlinarith)

/-- **The note's eq. (7)**: the smallest eigenvalue `d(ε) − 1` of the off-line 2×2 Gram
    block tends to exactly `−1` as `ε → 0⁺`, for every off-line displacement `δ ≠ 0` —
    the scale-free limiting negativity confirmed numerically at `δ = 10⁻², 10⁻⁴, 10⁻⁶`. -/
theorem tendsto_offline_min_eigenvalue {δ : ℝ} (hδ : δ ≠ 0) :
    Tendsto (fun ε : ℝ => ε^2 / (ε^2 - 4*δ^2) - 1) (nhdsWithin 0 (Ioi 0)) (nhds (-1)) := by
  have hden : (0:ℝ)^2 - 4*δ^2 ≠ 0 := by
    have h : (0:ℝ)^2 - 4*δ^2 = -(4*δ^2) := by ring
    rw [h]
    exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (pow_ne_zero 2 hδ))
  have hc : ContinuousAt (fun ε : ℝ => ε^2 / (ε^2 - 4*δ^2) - 1) 0 := by
    have h1 : ContinuousAt (fun ε : ℝ => ε^2) 0 := (continuous_pow 2).continuousAt
    have h2 : ContinuousAt (fun ε : ℝ => ε^2 - 4*δ^2) 0 :=
      ((continuous_pow 2).sub continuous_const).continuousAt
    exact (h1.div h2 hden).sub continuousAt_const
  have h0 : (0:ℝ)^2 / ((0:ℝ)^2 - 4*δ^2) - 1 = -1 := by norm_num
  have h := hc.tendsto
  rw [h0] at h
  exact h.mono_left nhdsWithin_le_nhds

end GppCauchyKernel
