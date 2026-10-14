import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# A real-trace Sobolev completion: exact scale norm, trace DtN block, and zero blindness

Source: Codex, GPP-bridge `research/codex/2026-09-29_scale_completion_attempt.md` (first note §§2, 4,
5; second note §2). The note itself records the outcome as an explicit *failed* RH closure.

* `ratio_le`, `ratio_attained`: on `H¹(ℝ)` with `‖f‖² = ∫ |f'|² + κ²|f|²`, modulation by `e^{−itλ}`
  has squared operator norm `sup_x [κ² + (x − t)²]/[κ² + x²] = R²` with
  `R = (√(t² + 4κ²) + |t|)/(2κ)`, and the supremum is attained. `R_root`: `R − 1/R = |t|/κ`, so
  `R ≤ 1 + |t|/κ`. This is polynomial (subexponential) scale growth (§2).
* `dtn_det`, `dtn_eig_minus`, `dtn_eig_plus`: the interval trace block
  `κ[[coth κℓ, −csch κℓ], [−csch κℓ, coth κℓ]]` has determinant `κ²` and eigenvalues
  `κ (1 − r)/(1 + r)` and `κ (1 + r)/(1 − r)` with `r = e^{−κℓ}` (§4).
* `blind_mult_pos`, `blind_mult_root`: `q(z) = ((z − b)² + a²)((z + b)² + a²)` is strictly positive on
  `ℝ` but vanishes at `b + ia`. Multiplying `ξ` by `q` inserts four off-line zeros without changing
  the real-trace quotient, so this completion is blind to them (§5).
* `nonclosable_witness`: `h_N = (1/N) Σ_{n ≤ N} e_n` has `‖h_N‖² = 1/N → 0` but coefficient sum
  `1`. So a vacuum term `a(s)·E(c)` with `a(s) ≠ 0` is not closable (second note §2).

Not formalized: the quotient characterization `N_F = {f : f|_{Z_ℝ} = 0}` (Sobolev cutoffs), the
off-real evaluation blow-up (§6) and the graph-distance formula `d(s) = |A(s)|`. **No RH claim.**
-/

namespace GppScaleCompletionTrace

open Real

/-- Exact modulation norm `R_κ(t)`. -/
noncomputable def R (κ t : ℝ) : ℝ := (sqrt (t ^ 2 + 4 * κ ^ 2) + |t|) / (2 * κ)

theorem R_root {κ : ℝ} (hκ : 0 < κ) (t : ℝ) : R κ t ^ 2 = |t| / κ * R κ t + 1 := by
  have hs := sq_sqrt (by positivity : (0 : ℝ) ≤ t ^ 2 + 4 * κ ^ 2)
  have ht : |t| ^ 2 = t ^ 2 := sq_abs t
  unfold R
  field_simp
  nlinarith [hs, ht]

theorem R_pos {κ : ℝ} (hκ : 0 < κ) (t : ℝ) : 0 < R κ t := by
  unfold R
  have : 0 < sqrt (t ^ 2 + 4 * κ ^ 2) := sqrt_pos.mpr (by positivity)
  positivity

/-- `R ≤ 1 + |t|/κ`: polynomial scale growth. -/
theorem R_le {κ : ℝ} (hκ : 0 < κ) (t : ℝ) : R κ t ≤ 1 + |t| / κ := by
  have h := R_root hκ t
  have hp := R_pos hκ t
  have hu : 0 ≤ |t| / κ := by positivity
  nlinarith

/-- Key discriminant identity: with `a = R² − 1`, `a² κ² − a t² = t²`. -/
theorem disc_zero {κ : ℝ} (hκ : 0 < κ) (t : ℝ) :
    (R κ t ^ 2 - 1) ^ 2 * κ ^ 2 - (R κ t ^ 2 - 1) * t ^ 2 = t ^ 2 := by
  have h := R_root hκ t
  have ha : R κ t ^ 2 - 1 = |t| / κ * R κ t := by linarith
  rw [ha, ← sq_abs t]
  have e : (|t| / κ * R κ t) ^ 2 * κ ^ 2 = |t| ^ 2 * R κ t ^ 2 := by field_simp
  rw [e]
  have : |t| ^ 2 * R κ t ^ 2 - |t| / κ * R κ t * |t| ^ 2 =
      |t| ^ 2 * (R κ t ^ 2 - |t| / κ * R κ t) := by ring
  rw [this, show R κ t ^ 2 - |t| / κ * R κ t = 1 by linarith]; ring

theorem t_eq_zero_of {κ : ℝ} (hκ : 0 < κ) {t : ℝ} (h0 : R κ t ^ 2 - 1 = 0) : t = 0 := by
  have hd := disc_zero hκ t
  rw [h0] at hd
  have : t ^ 2 = 0 := by linarith
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

/-- **Modulation bound**: `κ² + (x − t)² ≤ R² (κ² + x²)` for every frequency `x`. -/
theorem ratio_le {κ : ℝ} (hκ : 0 < κ) (t x : ℝ) :
    κ ^ 2 + (x - t) ^ 2 ≤ R κ t ^ 2 * (κ ^ 2 + x ^ 2) := by
  have hd := disc_zero hκ t
  set a := R κ t ^ 2 - 1 with ha
  have hR : R κ t ^ 2 = a + 1 := by rw [ha]; ring
  have ha0 : 0 ≤ a := by
    have := R_root hκ t; have := R_pos hκ t
    have : 0 ≤ |t| / κ * R κ t := by positivity
    rw [ha]; linarith
  rw [hR]
  rcases ha0.lt_or_eq with hpos | hzero
  · have key : a * ((a + 1) * (κ ^ 2 + x ^ 2) - (κ ^ 2 + (x - t) ^ 2)) = (a * x + t) ^ 2 := by
      linear_combination hd
    have hE : 0 ≤ (a + 1) * (κ ^ 2 + x ^ 2) - (κ ^ 2 + (x - t) ^ 2) := by
      by_contra hneg
      push Not at hneg
      have := mul_neg_of_pos_of_neg hpos hneg
      nlinarith [sq_nonneg (a * x + t)]
    linarith
  · have ht : t = 0 := t_eq_zero_of hκ (by rw [← ha, ← hzero])
    rw [← hzero, ht]; ring_nf; rfl

/-- **The bound is attained**: the supremum is exactly `R²`. -/
theorem ratio_attained {κ : ℝ} (hκ : 0 < κ) (t : ℝ) :
    ∃ x : ℝ, κ ^ 2 + (x - t) ^ 2 = R κ t ^ 2 * (κ ^ 2 + x ^ 2) := by
  have hd := disc_zero hκ t
  set a := R κ t ^ 2 - 1 with ha
  have hR : R κ t ^ 2 = a + 1 := by rw [ha]; ring
  by_cases h0 : a = 0
  · have ht : t = 0 := t_eq_zero_of hκ (by rw [← ha, h0])
    refine ⟨0, ?_⟩
    rw [hR, h0, ht]; ring
  · refine ⟨-t / a, ?_⟩
    rw [hR]
    have : κ ^ 2 + (-t / a - t) ^ 2 - (a + 1) * (κ ^ 2 + (-t / a) ^ 2) =
        -(a ^ 2 * κ ^ 2 - a * t ^ 2 - t ^ 2) / a := by
      field_simp; ring
    have hz : a ^ 2 * κ ^ 2 - a * t ^ 2 - t ^ 2 = 0 := by linarith [hd]
    rw [hz, neg_zero, zero_div] at this
    linarith

/-- Interval trace block determinant `κ²`. -/
theorem dtn_det {κ ℓ : ℝ} (hκℓ : 0 < κ * ℓ) :
    (κ * (cosh (κ * ℓ) / sinh (κ * ℓ))) ^ 2 - (κ * (1 / sinh (κ * ℓ))) ^ 2 = κ ^ 2 := by
  have hs : sinh (κ * ℓ) ≠ 0 := (sinh_pos_iff.mpr hκℓ).ne'
  field_simp
  nlinarith [cosh_sq (κ * ℓ)]

theorem dtn_eig_minus {κ ℓ : ℝ} (hκℓ : 0 < κ * ℓ) :
    κ * (cosh (κ * ℓ) / sinh (κ * ℓ)) - κ * (1 / sinh (κ * ℓ)) =
      κ * ((1 - exp (-(κ * ℓ))) / (1 + exp (-(κ * ℓ)))) := by
  have hs : sinh (κ * ℓ) ≠ 0 := (sinh_pos_iff.mpr hκℓ).ne'
  rw [sinh_eq, cosh_eq] at *
  have he : 0 < exp (κ * ℓ) := exp_pos _
  have hlt : exp (-(κ * ℓ)) < exp (κ * ℓ) := exp_lt_exp.mpr (by linarith)
  have hne : exp (κ * ℓ) - exp (-(κ * ℓ)) ≠ 0 := by linarith
  have h1 : 1 + exp (-(κ * ℓ)) ≠ 0 := by positivity
  have hm : exp (κ * ℓ) * exp (-(κ * ℓ)) = 1 := by rw [← exp_add]; simp
  field_simp
  linear_combination (2 * κ) * hm

theorem dtn_eig_plus {κ ℓ : ℝ} (hκℓ : 0 < κ * ℓ) :
    κ * (cosh (κ * ℓ) / sinh (κ * ℓ)) + κ * (1 / sinh (κ * ℓ)) =
      κ * ((1 + exp (-(κ * ℓ))) / (1 - exp (-(κ * ℓ)))) := by
  have hs : sinh (κ * ℓ) ≠ 0 := (sinh_pos_iff.mpr hκℓ).ne'
  rw [sinh_eq, cosh_eq] at *
  have hlt : exp (-(κ * ℓ)) < 1 := by
    have := exp_lt_exp.mpr (show -(κ * ℓ) < 0 by linarith); simpa using this
  have hne : exp (κ * ℓ) - exp (-(κ * ℓ)) ≠ 0 := by
    have : exp (-(κ * ℓ)) < exp (κ * ℓ) := exp_lt_exp.mpr (by linarith)
    linarith
  have h1 : 1 - exp (-(κ * ℓ)) ≠ 0 := by linarith
  have hm : exp (κ * ℓ) * exp (-(κ * ℓ)) = 1 := by rw [← exp_add]; simp
  field_simp
  linear_combination (-2 * κ) * hm

/-- The blindness multiplier is strictly positive on the real line. -/
theorem blind_mult_pos {a : ℝ} (ha : a ≠ 0) (b x : ℝ) :
    0 < ((x - b) ^ 2 + a ^ 2) * ((x + b) ^ 2 + a ^ 2) := by
  have : 0 < a ^ 2 := by positivity
  positivity

/-- …yet it vanishes at the off-line point `b + ia`. -/
theorem blind_mult_root (a b : ℝ) :
    (((b : ℂ) + a * Complex.I - b) ^ 2 + (a : ℂ) ^ 2) * (((b : ℂ) + a * Complex.I + b) ^ 2 + (a : ℂ) ^ 2) = 0 := by
  have : ((b : ℂ) + a * Complex.I - b) ^ 2 + (a : ℂ) ^ 2 = 0 := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [this, zero_mul]

/-- **Nonclosability witness**: `h_N = (1/N) Σ_{n<N} e_n` has `‖h_N‖² = 1/N` and coefficient sum `1`. -/
theorem nonclosable_witness {N : ℕ} (hN : 0 < N) :
    (∑ _n ∈ Finset.range N, ((1 : ℝ) / N) ^ 2) = 1 / N ∧ (∑ _n ∈ Finset.range N, (1 : ℝ) / N) = 1 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  constructor <;> field_simp

end GppScaleCompletionTrace
