import Mathlib.Tactic

/-!
# The continued Abel kernel is indefinite off its convergence strip

Finite, exact facts accompanying `GppAbelCesaroPoleBarrier`.  Source: Astra,
`work/2026-10-20_astra_signed_tail_and_abel_domain.md` (GPP-bridge), a critique of an external
Cesàro draft; formalized by Claude Code, with AI assistance, for Daniel Toupin / Golden Physics
Project.

The Abel character formula `ε²/(ε²-α²)` is the value of a positive integral only for
`|α| < ε`.  Outside that strip the same rational function is a *continuation*, and the
continuation is not positive:

* for real `0 < |α| < ε` the formula is `> 1` (so "maximum 1 at `α = 0`" is false);
* for the exponents `±1/4` at `ε = 1/4` the continued Gram matrix is
  `[[-1/3, 1], [1, -1/3]]` with eigenvalues `2/3` and `-4/3`; the vector `(1,-1)` has quadratic
  value `-8/3`;
* a normalized positive translation-invariant mean cannot exist on a function algebra
  containing `exp(a u)` and `exp(-a u)` (`a ≠ 0`): the Cauchy–Schwarz product
  `M(f²) M(f⁻²) ≥ M(1)² = 1` is contradicted by invariance.

Scope: this does NOT show that zeta has off-line zeros and does NOT claim RH.  It only records
why positivity of the genuine integral cannot be transported through the continuation.
-/

namespace GppAbelContinuedKernel

/-- The rational continuation of the Abel character formula. -/
noncomputable def abelCont (ε α : ℝ) : ℝ := ε ^ 2 / (ε ^ 2 - α ^ 2)

/-- Inside the strip, off `α = 0`, the formula exceeds `1`. -/
theorem abelCont_gt_one {ε α : ℝ} (hα0 : α ≠ 0) (hα : |α| < ε) : 1 < abelCont ε α := by
  have hε : 0 < ε := lt_of_le_of_lt (abs_nonneg α) hα
  have hsq : α ^ 2 < ε ^ 2 := by
    have := sq_lt_sq' (abs_lt.mp hα).1 (abs_lt.mp hα).2
    simpa using this
  have hpos : 0 < ε ^ 2 - α ^ 2 := by linarith
  have hα2 : 0 < α ^ 2 := by positivity
  unfold abelCont
  rw [lt_div_iff₀ hpos]
  linarith

/-- At `α = 0` the value is exactly `1`. -/
theorem abelCont_zero {ε : ℝ} (hε : 0 < ε) : abelCont ε 0 = 1 := by
  unfold abelCont
  rw [show ε ^ 2 - (0 : ℝ) ^ 2 = ε ^ 2 by ring]
  exact div_self (by positivity)

/-- For a purely imaginary exponent `α = iγ` (`α² = -γ²`) the value is at most `1`. -/
theorem abelCont_imag_le_one {ε γ : ℝ} (hε : 0 < ε) : ε ^ 2 / (ε ^ 2 + γ ^ 2) ≤ 1 := by
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg γ]

/-- Diagonal entry for exponent `±1/4` (`α = 1/2`, outside the strip `|α| < 1/4`). -/
theorem diag_value : abelCont (1 / 4) (1 / 2) = -1 / 3 := by
  unfold abelCont; norm_num

/-- Off-diagonal entry (`α = 0`). -/
theorem offdiag_value : abelCont (1 / 4) 0 = 1 := abelCont_zero (by norm_num)

/-- The continued Gram matrix `[[-1/3,1],[1,-1/3]]` has `(1,1)` as eigenvector with value `2/3`
and `(1,-1)` as eigenvector with value `-4/3`. -/
theorem eigen_pair :
    (-1 / 3 * 1 + 1 * 1 = (2 / 3 : ℝ) * 1 ∧ 1 * 1 + -1 / 3 * 1 = (2 / 3 : ℝ) * 1) ∧
    (-1 / 3 * 1 + 1 * (-1) = (-4 / 3 : ℝ) * 1 ∧ 1 * 1 + -1 / 3 * (-1) = (-4 / 3 : ℝ) * (-1)) := by
  norm_num

/-- The quadratic form of the continued kernel on `(a,b)`. -/
noncomputable def contForm (a b : ℝ) : ℝ :=
  abelCont (1 / 4) (1 / 2) * a ^ 2 + 2 * abelCont (1 / 4) 0 * a * b +
    abelCont (1 / 4) (1 / 2) * b ^ 2

/-- The continued kernel is indefinite: `(1,-1)` gives `-8/3`, `(1,1)` gives `4/3`. -/
theorem contForm_indefinite : contForm 1 (-1) = -8 / 3 ∧ contForm 1 1 = 4 / 3 := by
  unfold contForm
  rw [diag_value, offdiag_value]
  constructor <;> norm_num

/-- No normalized positive translation-invariant mean: if `p = M(f²)` and `q = M(f⁻²)` are
each scaled by `exp(±2ah)` under translation by `h` (with `a h ≠ 0`), then the Cauchy–Schwarz
requirement `1 = M(1)² ≤ p q` fails.  Invariance of `p` alone already forces `p = 0`; the
symmetric invariance of `q` is not needed. -/
theorem no_invariant_mean {a h p q : ℝ} (hah : a * h ≠ 0)
    (hp : p = Real.exp (2 * a * h) * p) :
    ¬ (1 ≤ p * q) := by
  have hne : Real.exp (2 * a * h) ≠ 1 := by
    intro h1
    have := Real.exp_eq_one_iff _ |>.mp h1
    apply hah
    linarith
  have hp0 : p = 0 := by
    have : (1 - Real.exp (2 * a * h)) * p = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (by linarith) hne
    · exact h0
  intro hle
  rw [hp0] at hle
  simp at hle
  linarith

end GppAbelContinuedKernel
