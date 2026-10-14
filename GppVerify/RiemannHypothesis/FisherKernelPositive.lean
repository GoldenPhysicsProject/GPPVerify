import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# The zeta Fisher kernel is positive definite along vertical lines

Source: Claude Code probe of Codex's GPP-bridge PR #11 question ("what property forces the
completed nodes onto the mirror?"), following `ZetaFisherMetric` (GPPVerify #344) and the Arb
certificate `work/claude-code/2026-10-14_dh_fisher_sign/`.

`ZetaFisherMetric.fisher_pos` proves that `(log ζ)''(β) > 0` on the real axis. This file proves the
complex version, as a positive-definite kernel:
* `logDeriv_deriv_eq`: for `Re s > 1`, `(ζ'/ζ)'(s) = L(log · Λ)(s)`, the L-series of `Λ(n) log n`.
* `quad_form_eq`: for weights `w ≥ 0` and frequencies `ℓ`, the kernel
  `K(τ) = Σ w_n e^{−iτℓ_n}` satisfies
  `Σ_{i,j} c_i c̄_j K(t_i − t_j) = Σ_n w_n |Σ_i c_i e^{−i t_i ℓ_n}|²`.
* `fisher_kernel_posDef`: for every real `σ > 1`, the kernel `τ ↦ (ζ'/ζ)'(σ + iτ)` is positive
  definite. Every Hermitian quadratic form in it is real and `≥ 0`.

The `1 × 1` case at `τ = 0` is Fisher positivity. The Davenport–Heilbronn function has a
functional equation but no Euler product with `Λ ≥ 0`, and it already fails that `1 × 1` test:
`(log DH)''(2) = −0.058464823 ± 4·10⁻¹⁰` (Arb). So the positivity comes from `Λ ≥ 0`, not from the
mirror symmetry. Proved here only for `σ > 1`. Whether a version survives continuation to the
strip is Weil-positivity territory. **No RH claim.**
-/

namespace GppFisherKernelPositive

open Complex LSeries ArithmeticFunction
open scoped LSeries.notation

theorem abscissa_vonMangoldt_le_one : abscissaOfAbsConv ↗Λ ≤ 1 := by
  refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦ ?_
  exact LSeriesSummable_vonMangoldt <| show 1 < (y : ℂ).re by simp only [ofReal_re, hy]

/-- **Fisher kernel as an L-series**: `(ζ'/ζ)'(s) = L(log · Λ)(s)` for `Re s > 1`. -/
theorem logDeriv_deriv_eq {s : ℂ} (hs : 1 < s.re) :
    deriv (fun z => deriv riemannZeta z / riemannZeta z) s = L (logMul ↗Λ) s := by
  have hev : (fun z => deriv riemannZeta z / riemannZeta z) =ᶠ[nhds s] fun z => -L ↗Λ z := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz, neg_div, neg_neg]
  have hab : abscissaOfAbsConv ↗Λ < s.re :=
    lt_of_le_of_lt abscissa_vonMangoldt_le_one (by exact_mod_cast hs)
  rw [hev.deriv_eq]
  exact ((LSeries_hasDerivAt hab).neg.deriv).trans (neg_neg _)

theorem exp_split (a b r : ℝ) :
    exp (-(I * ((a - b) * r))) = exp (-(I * (a * r))) * (starRingEnd ℂ) (exp (-(I * (b * r)))) := by
  have hc : (starRingEnd ℂ) (exp (-(I * ((b : ℂ) * r)))) = exp (I * ((b : ℂ) * r)) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_neg, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
    ring
  rw [hc, ← Complex.exp_add]
  congr 1
  ring

/-- **Bochner form**: a nonnegative-weight trigonometric kernel gives a sum of squares. -/
theorem quad_form_eq {ι : Type*} (S : Finset ι) (c : ι → ℂ) (t : ι → ℝ) (w ℓ : ℕ → ℝ)
    (hw0 : ∀ n, 0 ≤ w n) (hw : Summable w) :
    ∑ i ∈ S, ∑ j ∈ S, c i * (starRingEnd ℂ) (c j) *
        ∑' n, (w n : ℂ) * exp (-(I * ((t i - t j) * ℓ n))) =
      ((∑' n, w n * Complex.normSq (∑ i ∈ S, c i * exp (-(I * (t i * ℓ n))))) : ℝ) := by
  have hsum : ∀ x : ℝ, Summable fun n => (w n : ℂ) * exp (-(I * (x * ℓ n))) := by
    intro x
    refine Summable.of_norm ?_
    have : (fun n => ‖(w n : ℂ) * exp (-(I * (x * ℓ n)))‖) = w := by
      funext n
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw0 n)]
      have : -(I * ((x : ℂ) * (ℓ n : ℂ))) = ((-(x * ℓ n) : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I, mul_one]
    rw [this]; exact hw
  set F : ι → ι → ℕ → ℂ := fun i j n =>
    c i * (starRingEnd ℂ) (c j) * ((w n : ℂ) * exp (-(I * ((t i - t j) * ℓ n)))) with hFdef
  have hF : ∀ i j, Summable (F i j) := by
    intro i j
    have := (hsum (t i - t j)).mul_left (c i * (starRingEnd ℂ) (c j))
    push_cast at this
    exact this
  have h1 : ∀ i j, c i * (starRingEnd ℂ) (c j) *
      ∑' n, (w n : ℂ) * exp (-(I * ((t i - t j) * ℓ n))) = ∑' n, F i j n := fun i j =>
    (tsum_mul_left).symm
  simp_rw [h1]
  rw [Finset.sum_congr rfl fun i _ => (Summable.tsum_finsetSum fun j _ => hF i j).symm,
    ← Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => hF i j, Complex.ofReal_tsum]
  congr 1; funext n
  rw [Complex.ofReal_mul, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [hFdef, map_mul, exp_split]
  ring

/-- Spectral weight `w_σ(n) = Λ(n) log n · n^{−σ} ≥ 0`. -/
noncomputable def w (σ : ℝ) (n : ℕ) : ℝ :=
  Real.log n * ArithmeticFunction.vonMangoldt n * Real.exp (-σ * Real.log n)

theorem w_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ w σ n :=
  mul_nonneg (mul_nonneg (Real.log_natCast_nonneg n) vonMangoldt_nonneg) (Real.exp_pos _).le

theorem term_eq (σ τ : ℝ) (n : ℕ) :
    term (logMul ↗Λ) (σ + τ * I) n = (w σ n : ℂ) * exp (-(I * (τ * Real.log n))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [term, w]
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [term_of_ne_zero hn.ne', cpow_def_of_ne_zero hn0, ← natCast_log]
    simp only [logMul, w]
    rw [← natCast_log]
    push_cast
    rw [div_eq_mul_inv, ← Complex.exp_neg,
      show -(Complex.log ↑n * (↑σ + ↑τ * I)) =
        -↑σ * Complex.log ↑n + -(I * (↑τ * Complex.log ↑n)) by ring, Complex.exp_add]
    ring

theorem summable_w {σ : ℝ} (hσ : 1 < σ) : Summable (w σ) := by
  have hab : abscissaOfAbsConv ↗Λ < ((σ : ℂ) + ((0 : ℝ) : ℂ) * I).re := by
    simp only [ofReal_zero, zero_mul, add_zero, ofReal_re]
    exact lt_of_le_of_lt abscissa_vonMangoldt_le_one (by exact_mod_cast hσ)
  have h := LSeriesSummable_logMul_of_lt_re hab
  refine Complex.summable_ofReal.mp (h.congr fun n => ?_)
  rw [term_eq]
  simp

/-- **The zeta Fisher kernel is positive definite** on every vertical line `Re s = σ > 1`:
`Σ_{i,j} c_i c̄_j (ζ'/ζ)'(σ + i(t_i − t_j)) = Σ_n Λ(n) log n · n^{−σ} |Σ_i c_i n^{−i t_i}|² ≥ 0`. -/
theorem fisher_kernel_posDef {σ : ℝ} (hσ : 1 < σ) {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (t : ι → ℝ) :
    ∑ i ∈ S, ∑ j ∈ S, c i * (starRingEnd ℂ) (c j) *
        deriv (fun z => deriv riemannZeta z / riemannZeta z) (σ + (t i - t j) * I) =
      ((∑' n, w σ n * Complex.normSq (∑ i ∈ S, c i * exp (-(I * (t i * Real.log n))))) : ℝ) ∧
    0 ≤ ∑' n, w σ n * Complex.normSq (∑ i ∈ S, c i * exp (-(I * (t i * Real.log n)))) := by
  refine ⟨?_, tsum_nonneg fun n => mul_nonneg (w_nonneg σ n) (Complex.normSq_nonneg _)⟩
  rw [← quad_form_eq S c t (w σ) (fun n => Real.log n) (w_nonneg σ) (summable_w hσ)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hre : 1 < ((σ : ℂ) + ((t i - t j : ℝ) : ℂ) * I).re := by simpa using hσ
  have h := logDeriv_deriv_eq hre
  push_cast at h
  rw [h, LSeries]
  congr 1
  refine tsum_congr fun n => ?_
  rw [show ((σ : ℂ) + ((t i : ℂ) - t j) * I) = σ + ((t i - t j : ℝ) : ℂ) * I by push_cast; ring,
    term_eq]
  push_cast
  ring_nf

end GppFisherKernelPositive
