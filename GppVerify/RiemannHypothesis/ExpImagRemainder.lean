import GppVerify.RiemannHypothesis.FiniteIndexAbstract
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The sharp Taylor remainder of `e^{iθ}`

For real `θ` and `N : ℕ`,

`‖e^{iθ} − Σ_{k<N} (iθ)^k / k!‖ ≤ |θ|^N / N!`.

Mathlib has the cases `N = 0, 1` and the weaker `Complex.exp_bound`; this file proves the sharp constant by
induction on `N`, using the derivative identity `R_{N+1}' = i R_N` and Mathlib's fencing lemma
`image_norm_le_of_norm_deriv_right_le_deriv_boundary`. It is the elementary ingredient of the low-band
Fourier bound for functions with vanishing moments in GPP's all-width finite-index theorem
(Turbo relay `458ba0f`, §4): for `f` supported in `[−L/2, L/2]` with `∫ xᵏ f = 0` for `k < N`,
`|f̂(λ)| ≤ (|λ|L/2)^N/N! · ∫|f|`.

**Scope.** Only the scalar remainder bound. The Fourier-side estimate itself, Cauchy–Schwarz to
`√L ‖f‖`, and Plancherel are not here.

No `sorry`, no axiom.
-/

open Complex Finset

noncomputable section

namespace GppExpRemainder

/-- The `N`-th Taylor polynomial of `x ↦ e^{ix}`. -/
def S (N : ℕ) (x : ℝ) : ℂ := ∑ k ∈ range N, (Complex.I * x) ^ k / (k.factorial : ℂ)

/-- The remainder `R_N(x) = e^{ix} − S_N(x)`. -/
def R (N : ℕ) (x : ℝ) : ℂ := Complex.exp (Complex.I * x) - S N x

theorem hasDerivAt_S (N : ℕ) (x : ℝ) :
    HasDerivAt (S (N + 1)) (Complex.I * S N x) x := by
  unfold S
  have hterm : ∀ k ∈ range (N + 1), HasDerivAt (fun y : ℝ => (Complex.I * y) ^ k / (k.factorial : ℂ))
      (if k = 0 then 0 else Complex.I * ((Complex.I * x) ^ (k - 1) / ((k - 1).factorial : ℂ))) x := by
    intro k _
    have h1 : HasDerivAt (fun y : ℝ => (Complex.I * (y : ℂ))) Complex.I x := by
      have := (hasDerivAt_id (x : ℂ)).const_mul Complex.I
      have h2 := this.comp_ofReal
      simpa using h2
    have h3 := (h1.pow k).div_const (k.factorial : ℂ)
    refine h3.congr_deriv ?_
    rcases k with _ | k
    · simp
    · have hk : ((k + 1).factorial : ℂ) = ((k + 1 : ℕ) : ℂ) * (k.factorial : ℂ) := by
        push_cast [Nat.factorial_succ]; ring
      have hne : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
      rw [hk]
      push_cast
      field_simp
  have hsum := HasDerivAt.fun_sum hterm
  refine hsum.congr_deriv ?_
  rw [Finset.sum_range_succ']
  simp [Finset.mul_sum]

theorem hasDerivAt_R (N : ℕ) (x : ℝ) :
    HasDerivAt (R (N + 1)) (Complex.I * R N x) x := by
  unfold R
  have h1 : HasDerivAt (fun y : ℝ => Complex.exp (Complex.I * (y : ℂ))) (Complex.I * Complex.exp (Complex.I * x)) x := by
    have h := ((hasDerivAt_id (x : ℂ)).const_mul Complex.I).cexp
    have h2 := h.comp_ofReal
    simpa [mul_comm] using h2
  have := h1.sub (hasDerivAt_S N x)
  refine this.congr_deriv ?_
  ring

theorem continuous_R (N : ℕ) : Continuous (R N) := by
  unfold R S
  fun_prop

/-- **Sharp remainder bound for `θ ≥ 0`.** -/
theorem norm_R_le_nonneg (N : ℕ) : ∀ θ : ℝ, 0 ≤ θ → ‖R N θ‖ ≤ θ ^ N / (N.factorial : ℝ) := by
  induction N with
  | zero =>
    intro θ _
    simp [R, S, Complex.norm_exp_I_mul_ofReal]
  | succ N ih =>
    intro θ hθ
    have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := R (N + 1)) (f' := fun x => Complex.I * R N x) (a := 0) (b := θ)
      (continuous_R (N + 1)).continuousOn
      (fun x _ => (hasDerivAt_R N x).hasDerivWithinAt)
      (B := fun x => x ^ (N + 1) / ((N + 1).factorial : ℝ))
      (B' := fun x => x ^ N / (N.factorial : ℝ))
      (by simp [R, S, Finset.sum_range_succ'])
      (fun x => by
        have h := (hasDerivAt_pow (N + 1) x).div_const ((N + 1).factorial : ℝ)
        refine h.congr_deriv ?_
        rw [Nat.factorial_succ]
        push_cast
        have : ((N + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
        field_simp)
      (fun x hx => by
        rw [norm_mul, Complex.norm_I, one_mul]
        exact ih x hx.1)
    exact hmain ⟨hθ, le_rfl⟩

theorem R_neg (N : ℕ) (θ : ℝ) : R N (-θ) = (starRingEnd ℂ) (R N θ) := by
  unfold R S
  rw [map_sub, map_sum]
  congr 1
  · rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [Complex.conj_ofReal, mul_pow]
    rw [← neg_mul, mul_pow]

/-- **Sharp Taylor remainder of `e^{iθ}`, all real `θ`:**
`‖e^{iθ} − Σ_{k<N}(iθ)^k/k!‖ ≤ |θ|^N / N!`. -/
theorem norm_exp_I_sub_sum_le (N : ℕ) (θ : ℝ) :
    ‖Complex.exp (Complex.I * θ) - ∑ k ∈ range N, (Complex.I * θ) ^ k / (k.factorial : ℂ)‖ ≤
      |θ| ^ N / (N.factorial : ℝ) := by
  show ‖R N θ‖ ≤ _
  rcases le_total 0 θ with h | h
  · rw [abs_of_nonneg h]; exact norm_R_le_nonneg N θ h
  · have := norm_R_le_nonneg N (-θ) (by linarith)
    rw [R_neg, Complex.norm_conj] at this
    rwa [abs_of_nonpos h]

end GppExpRemainder

#print axioms GppExpRemainder.norm_exp_I_sub_sum_le
