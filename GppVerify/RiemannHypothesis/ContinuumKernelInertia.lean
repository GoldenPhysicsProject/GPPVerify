import GppVerify.RiemannHypothesis.ContinuumPoleCancellation
import Mathlib.Tactic

/-!
# The PNT continuum kernel has at most one positive direction

The kernel `K(x,y) = exp(|x-y|/2)` is the continuum model of the prime-power sum. Writing
`2 cosh((x-y)/2) = e^{(x-y)/2} + e^{-(x-y)/2}` as the pole kernel, `GppContinuumPoleCancellation`
shows `2 cosh((x-y)/2) - K(x,y) = exp(-|x-y|/2)` has nonnegative finite Gram forms. Since the pole form
is `2 ℓ₊(c) ℓ₋(c)` with `ℓ_±(c) = Σ c_i e^{±x_i/2}`, the continuum form satisfies

  `Σ c_i c_j K(x_i,x_j) ≤ 2 ℓ₊(c) ℓ₋(c)`,

so it is `≤ 0` on the hyperplane `ℓ₊ = 0`. Hence no two-dimensional space of coefficient vectors carries a
strictly positive continuum form: the continuum form has at most one positive direction (equivalently,
minus it has at most one negative direction), for arbitrary finite point sets with no window bound.

**Scope.** This is the inertia of the *continuum* kernel only, a rank-two `(1,1)` piece minus a positive
form. The actual prime-power sum differs from the continuum by a signed remainder that is not controlled
here, so nothing is said about the inertia of the actual Weil form, positivity of that form, or RH.
Companion to the numerical observation in `work/claude-code/2026-10-17_weil_inertia_split` (bridge).
-/

namespace GppContinuumInertia

open Real

/-- The continuum form `Σ c_i c_j exp(|x_i - x_j|/2)`. -/
noncomputable def contForm {n : ℕ} (x c : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * exp (|x i - x j| / 2)

/-- The pole functionals `ℓ_±(c) = Σ c_i exp(± x_i / 2)`. -/
noncomputable def ell {n : ℕ} (s : ℝ) (x c : Fin n → ℝ) : ℝ :=
  ∑ i, c i * exp (s * x i / 2)

/-- The pole form `Σ c_i c_j 2cosh((x_i - x_j)/2)` equals `2 ℓ₊(c) ℓ₋(c)`. -/
theorem pole_form_eq {n : ℕ} (x c : Fin n → ℝ) :
    ∑ i, ∑ j, c i * c j * (2 * cosh ((x i - x j) / 2)) =
      2 * (ell 1 x c * ell (-1) x c) := by
  have h : ∀ i j : Fin n, c i * c j * (2 * cosh ((x i - x j) / 2)) =
      (c i * exp (1 * x i / 2)) * (c j * exp (-1 * x j / 2)) +
      (c i * exp (-1 * x i / 2)) * (c j * exp (1 * x j / 2)) := by
    intro i j
    rw [Real.cosh_eq]
    have e1 : exp ((x i - x j) / 2) = exp (1 * x i / 2) * exp (-1 * x j / 2) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : exp (-((x i - x j) / 2)) = exp (-1 * x i / 2) * exp (1 * x j / 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [e1, e2]; ring
  simp_rw [h, Finset.sum_add_distrib, ← Finset.sum_mul_sum]
  unfold ell
  ring

/-- The continuum form is bounded above by the pole form. -/
theorem contForm_le_pole {n : ℕ} (x c : Fin n → ℝ) :
    contForm x c ≤ 2 * (ell 1 x c * ell (-1) x c) := by
  rw [← pole_form_eq]
  have h := GppContinuumPoleCancellation.completed_continuum_nonneg x c
  have hsub : ∑ i, ∑ j, c i * c j * (2 * cosh ((x i - x j) / 2) - exp (|x i - x j| / 2)) =
      (∑ i, ∑ j, c i * c j * (2 * cosh ((x i - x j) / 2))) - contForm x c := by
    unfold contForm
    simp_rw [mul_sub, Finset.sum_sub_distrib]
  linarith

/-- On the hyperplane `ℓ₊(c) = 0` the continuum form is nonpositive. -/
theorem contForm_nonpos_on_hyperplane {n : ℕ} (x c : Fin n → ℝ) (h : ell 1 x c = 0) :
    contForm x c ≤ 0 := by
  have := contForm_le_pole x c
  rw [h] at this
  simpa using this

theorem ell_add_smul {n : ℕ} (s : ℝ) (x c d : Fin n → ℝ) (a b : ℝ) :
    ell s x (fun i => a * c i + b * d i) = a * ell s x c + b * ell s x d := by
  unfold ell
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **At most one positive direction.** For any two coefficient vectors `c, d` there is a nontrivial
combination `a c + b d` (with `(a, b) ≠ (0, 0)`) on which the continuum form is nonpositive. So the form
is not strictly positive on any two-dimensional space of coefficient vectors. -/
theorem no_two_dim_positive {n : ℕ} (x c d : Fin n → ℝ) :
    ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ contForm x (fun i => a * c i + b * d i) ≤ 0 := by
  by_cases h : ell 1 x c = 0 ∧ ell 1 x d = 0
  · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
    apply contForm_nonpos_on_hyperplane
    rw [ell_add_smul]; simp [h.1]
  · refine ⟨ell 1 x d, -(ell 1 x c), ?_, ?_⟩
    · by_contra hne
      simp only [not_or, not_not] at hne
      apply h
      exact ⟨by simpa using hne.2, hne.1⟩
    · apply contForm_nonpos_on_hyperplane
      rw [ell_add_smul]; ring

#print axioms GppContinuumInertia.pole_form_eq
#print axioms GppContinuumInertia.contForm_le_pole
#print axioms GppContinuumInertia.contForm_nonpos_on_hyperplane
#print axioms GppContinuumInertia.no_two_dim_positive

end GppContinuumInertia
