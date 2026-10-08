import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The fixed-window prime source as a discrete curvature

Source: Codex, `research/codex/2026-10-05_fixed_window_second_difference_euler_ratio.md`, §§1, 4
(the exact identities; the arithmetic estimate they are used for is open).

For `ℓ > 0`, finitely many weights `a_n` at positions `x_n = log n`, and `B(t) = Σ a_n (t − x_n)₊`:

* `hinge_second_diff`: `(y + ℓ)₊ − 2 y₊ + (y − ℓ)₊ = (ℓ − |y|)₊`;
* `curvature_hinge_sum`: `(B(t+ℓ) − 2B(t) + B(t−ℓ))/ℓ = Σ a_n (1 − |x_n − t|/ℓ)₊ =: S_ℓ(t)`, the triangular
  window (pointwise exact);
* `curvature_exp`: `(4e^{(t+ℓ)/2} − 8e^{t/2} + 4e^{(t−ℓ)/2})/ℓ = A_ℓ e^{t/2}` with
  `A_ℓ = 8 (cosh(ℓ/2) − 1)/ℓ`;
* `curvature_discrepancy`: for `R(t) = 4e^{t/2} − B(t)`, `(R(t+ℓ) − 2R(t) + R(t−ℓ))/ℓ = A_ℓ e^{t/2} − S_ℓ(t)`,
  so if `C_ℓ = A_ℓ e^{t/2} − S_ℓ − D_ℓ` then `C_ℓ + D_ℓ` is the discrete curvature of `R`
  (`fixed_window_identity`);
* `coefficient_split`: `Λ/√n = Λ(1 − 1/n)/√n + Λ/n^{3/2}` (the totient-ratio split at coefficient level).

## Checks and scope

All claims check. **Not formalized:** the definition of `C_ℓ`, `D_ℓ` from the Weil form (they enter only
through the stated identity), the infinite sum over all `n ≥ 2`, the Dirichlet series `ζ(s)/ζ(s+1)` and its
logarithmic derivative, and — above all — the arithmetic bound `C_ℓ = e^{o(t)}`, which is the **open**
step; the note stresses that symmetry alone cannot give it (the Davenport–Heilbronn control has the same
reflection picture). No RH claim.
-/

open Real Finset

namespace GppFixedWindowCurvature

/-- **Second difference of the hinge is the triangle.** -/
theorem hinge_second_diff (ℓ y : ℝ) (hℓ : 0 < ℓ) :
    max (y + ℓ) 0 - 2 * max y 0 + max (y - ℓ) 0 = max (ℓ - |y|) 0 := by
  rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> simp only [max_def] <;> split_ifs <;> linarith

/-- The hinge sum `B(t) = Σ a_n (t − x_n)₊`. -/
noncomputable def hingeSum {ι : Type*} (s : Finset ι) (a x : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ n ∈ s, a n * max (t - x n) 0

/-- The triangular window `S_ℓ(t) = Σ a_n (1 − |x_n − t|/ℓ)₊`. -/
noncomputable def triSum {ι : Type*} (s : Finset ι) (a x : ι → ℝ) (ℓ t : ℝ) : ℝ :=
  ∑ n ∈ s, a n * max (1 - |x n - t| / ℓ) 0

theorem curvature_hinge_sum {ι : Type*} (s : Finset ι) (a x : ι → ℝ) (ℓ t : ℝ) (hℓ : 0 < ℓ) :
    (hingeSum s a x (t + ℓ) - 2 * hingeSum s a x t + hingeSum s a x (t - ℓ)) / ℓ =
      triSum s a x ℓ t := by
  unfold hingeSum triSum
  have key : ∀ n ∈ s, a n * max (t + ℓ - x n) 0 - 2 * (a n * max (t - x n) 0) +
      a n * max (t - ℓ - x n) 0 = ℓ * (a n * max (1 - |x n - t| / ℓ) 0) := by
    intro n _
    have h := hinge_second_diff ℓ (t - x n) hℓ
    have e1 : t + ℓ - x n = t - x n + ℓ := by ring
    have e2 : t - ℓ - x n = t - x n - ℓ := by ring
    have e3 : max (ℓ - |t - x n|) 0 = ℓ * max (1 - |x n - t| / ℓ) 0 := by
      rw [abs_sub_comm, mul_max_of_nonneg _ _ hℓ.le, mul_zero]
      congr 1; field_simp
    rw [e1, e2]
    calc a n * max (t - x n + ℓ) 0 - 2 * (a n * max (t - x n) 0) + a n * max (t - x n - ℓ) 0
        = a n * (max (t - x n + ℓ) 0 - 2 * max (t - x n) 0 + max (t - x n - ℓ) 0) := by ring
      _ = a n * max (ℓ - |t - x n|) 0 := by rw [h]
      _ = ℓ * (a n * max (1 - |x n - t| / ℓ) 0) := by rw [e3]; ring
  have h2 : ∑ n ∈ s, a n * max (t + ℓ - x n) 0 - 2 * ∑ n ∈ s, a n * max (t - x n) 0 +
      ∑ n ∈ s, a n * max (t - ℓ - x n) 0 = ∑ n ∈ s, ℓ * (a n * max (1 - |x n - t| / ℓ) 0) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl key
  rw [h2, ← Finset.mul_sum]
  field_simp

/-- `A_ℓ = 8 (cosh(ℓ/2) − 1)/ℓ`. -/
noncomputable def AA (ℓ : ℝ) : ℝ := 8 * (Real.cosh (ℓ / 2) - 1) / ℓ

theorem curvature_exp (ℓ t : ℝ) (hℓ : 0 < ℓ) :
    (4 * Real.exp ((t + ℓ) / 2) - 2 * (4 * Real.exp (t / 2)) + 4 * Real.exp ((t - ℓ) / 2)) / ℓ =
      AA ℓ * Real.exp (t / 2) := by
  have e1 : Real.exp ((t + ℓ) / 2) = Real.exp (t / 2) * Real.exp (ℓ / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp ((t - ℓ) / 2) = Real.exp (t / 2) * Real.exp (-(ℓ / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e3 : Real.exp (ℓ / 2) * Real.exp (-(ℓ / 2)) = 1 := by rw [← Real.exp_add]; simp
  unfold AA
  rw [e1, e2, Real.cosh_eq]
  field_simp
  nlinarith [e3]

/-- **The discrepancy `R = 4e^{t/2} − B` has curvature `A_ℓ e^{t/2} − S_ℓ`.** -/
theorem curvature_discrepancy {ι : Type*} (s : Finset ι) (a x : ι → ℝ) (ℓ t : ℝ) (hℓ : 0 < ℓ) :
    ((4 * Real.exp ((t + ℓ) / 2) - hingeSum s a x (t + ℓ)) -
        2 * (4 * Real.exp (t / 2) - hingeSum s a x t) +
        (4 * Real.exp ((t - ℓ) / 2) - hingeSum s a x (t - ℓ))) / ℓ =
      AA ℓ * Real.exp (t / 2) - triSum s a x ℓ t := by
  rw [← curvature_hinge_sum s a x ℓ t hℓ, ← curvature_exp ℓ t hℓ]
  ring

/-- **The fixed-window identity as a curvature.** If `C = A e^{t/2} − S − D` then `C + D` is the
discrete curvature of `R`. -/
theorem fixed_window_identity {ι : Type*} (s : Finset ι) (a x : ι → ℝ) (ℓ t C D : ℝ) (hℓ : 0 < ℓ)
    (h : C = AA ℓ * Real.exp (t / 2) - triSum s a x ℓ t - D) :
    C + D = ((4 * Real.exp ((t + ℓ) / 2) - hingeSum s a x (t + ℓ)) -
        2 * (4 * Real.exp (t / 2) - hingeSum s a x t) +
        (4 * Real.exp ((t - ℓ) / 2) - hingeSum s a x (t - ℓ))) / ℓ := by
  rw [curvature_discrepancy s a x ℓ t hℓ, h]; ring

/-- **Coefficient split** `Λ/√n = Λ(1 − 1/n)/√n + Λ/n^{3/2}`. -/
theorem coefficient_split (L n : ℝ) (hn : 0 < n) :
    L / Real.sqrt n = L * (1 - 1 / n) / Real.sqrt n + L / (n * Real.sqrt n) := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  field_simp
  ring

end GppFixedWindowCurvature
