import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field

/-!
# The second derivative of a log-partition function is a variance

Source: Codex's twistor theta-mixture note
(`work/codex/2026-10-16_twistor_theta_mixture_fisher_variance_obstruction.md`, PR11 comment 6222904247):
`−m'(u) = E_u[−q'] − Var_u(q)`, and Grok S49's check ("the log-partition second derivative; `(cq)' = c(q² + q')`").

Setting: a finite family `i ∈ ι` with weights `a i`, exponents `φ i` with `φ i' = q i`, and the partition
function `F x = Σ a_i exp (φ_i x)`. The "mean" `m = F'/F = Σ c_i q_i` has tilted weights
`c_i = a_i exp (φ_i)/F`. Then
* `hasDerivAt_m`: `m' = Σ c_i q_i' + Σ c_i q_i² − (Σ c_i q_i)²`;
* `m_deriv_eq_var`: when `Σ c_i = 1` the last two terms are the variance `Σ c_i (q_i − m)²`,
  i.e. **`m' = E[q'] + Var(q)`** (so `−m' = E[−q'] − Var(q)`).

For Codex's mixture `f(u) = ∫ cosh(t√u) dν`, `q_t = t·tanh(t√u)/(2√u)` is `(log cosh(t√u))'`, so the
identity applies with `exp (φ_t) = cosh(t√u)`; that substitution (and the integral over `ν`) is **not**
formalized here.

**Scope.** Exact finite calculus. It says nothing about the sign of `−m'`, the true `ξ` margin, or any
zero of `ξ`. No RH claim.
-/

namespace GppLogPartitionVariance

open Finset

variable {ι : Type*} [Fintype ι]

/-- The partition function `F x = Σ a_i exp (φ_i x)`. -/
noncomputable def F (a : ι → ℝ) (φ : ι → ℝ → ℝ) (x : ℝ) : ℝ := ∑ i, a i * Real.exp (φ i x)

/-- Its derivative `Σ a_i exp (φ_i x) q_i x`. -/
noncomputable def dF (a : ι → ℝ) (φ q : ι → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ i, a i * Real.exp (φ i x) * q i x

/-- The mean `m = F'/F`. -/
noncomputable def m (a : ι → ℝ) (φ q : ι → ℝ → ℝ) (x : ℝ) : ℝ := dF a φ q x / F a φ x

/-- Tilted weights `c_i = a_i exp (φ_i x) / F x`. -/
noncomputable def c (a : ι → ℝ) (φ : ι → ℝ → ℝ) (x : ℝ) (i : ι) : ℝ :=
  a i * Real.exp (φ i x) / F a φ x

theorem hasDerivAt_F (a : ι → ℝ) (φ q : ι → ℝ → ℝ) (hφ : ∀ i x, HasDerivAt (φ i) (q i x) x) (x : ℝ) :
    HasDerivAt (F a φ) (dF a φ q x) x := by
  unfold F dF
  refine HasDerivAt.fun_sum fun i _ => ?_
  have := ((hφ i x).exp).const_mul (a i)
  refine this.congr_deriv ?_
  ring

theorem hasDerivAt_dF (a : ι → ℝ) (φ q q' : ι → ℝ → ℝ) (hφ : ∀ i x, HasDerivAt (φ i) (q i x) x)
    (x : ℝ) (hq : ∀ i, HasDerivAt (q i) (q' i x) x) :
    HasDerivAt (dF a φ q)
      (∑ i, (a i * Real.exp (φ i x) * q i x * q i x + a i * Real.exp (φ i x) * q' i x)) x := by
  unfold dF
  refine HasDerivAt.fun_sum fun i _ => ?_
  have h1 := ((hφ i x).exp).const_mul (a i)
  have h2 := h1.mul (hq i)
  refine h2.congr_deriv ?_
  ring

/-- `m' = Σ c_i q_i' + Σ c_i q_i² − (Σ c_i q_i)²` at any point where `F ≠ 0`. -/
theorem hasDerivAt_m (a : ι → ℝ) (φ q q' : ι → ℝ → ℝ) (hφ : ∀ i x, HasDerivAt (φ i) (q i x) x)
    (x : ℝ) (hq : ∀ i, HasDerivAt (q i) (q' i x) x) (hF : F a φ x ≠ 0) :
    HasDerivAt (m a φ q)
      (∑ i, c a φ x i * q' i x + ∑ i, c a φ x i * q i x ^ 2 - (∑ i, c a φ x i * q i x) ^ 2) x := by
  have h := HasDerivAt.div (hasDerivAt_dF a φ q q' hφ x hq) (hasDerivAt_F a φ q hφ x) hF
  have e1 : dF a φ q x = F a φ x * ∑ i, c a φ x i * q i x := by
    unfold dF c
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  have e2 : ∑ i, (a i * Real.exp (φ i x) * q i x * q i x + a i * Real.exp (φ i x) * q' i x) =
      F a φ x * (∑ i, c a φ x i * q i x ^ 2 + ∑ i, c a φ x i * q' i x) := by
    unfold c
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  show HasDerivAt (dF a φ q / F a φ) _ x
  refine h.congr_deriv ?_
  rw [e2, e1]
  field_simp
  ring

/-- The tilted weights sum to `1`. -/
theorem sum_c (a : ι → ℝ) (φ : ι → ℝ → ℝ) (x : ℝ) (hF : F a φ x ≠ 0) : ∑ i, c a φ x i = 1 := by
  unfold c
  rw [← Finset.sum_div]
  exact div_self hF

/-- The variance identity: `Σ c_i q_i² − (Σ c_i q_i)² = Σ c_i (q_i − Σ c_j q_j)²` when `Σ c_i = 1`. -/
theorem var_eq (w q : ι → ℝ) (hw : ∑ i, w i = 1) :
    ∑ i, w i * q i ^ 2 - (∑ i, w i * q i) ^ 2 = ∑ i, w i * (q i - ∑ j, w j * q j) ^ 2 := by
  set μ := ∑ j, w j * q j with hμ
  have key : ∀ i, w i * (q i - μ) ^ 2 = w i * q i ^ 2 - 2 * μ * (w i * q i) + μ ^ 2 * w i :=
    fun i => by ring
  simp only [key, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [← hμ, hw]
  ring

/-- **`m' = E[q'] + Var(q)`** at any point where `F ≠ 0` (hence `−m' = E[−q'] − Var(q)`). -/
theorem m_deriv_eq_var (a : ι → ℝ) (φ q q' : ι → ℝ → ℝ) (hφ : ∀ i x, HasDerivAt (φ i) (q i x) x)
    (x : ℝ) (hq : ∀ i, HasDerivAt (q i) (q' i x) x) (hF : F a φ x ≠ 0) :
    HasDerivAt (m a φ q)
      (∑ i, c a φ x i * q' i x + ∑ i, c a φ x i * (q i x - m a φ q x) ^ 2) x := by
  have h := hasDerivAt_m a φ q q' hφ x hq hF
  have hm : m a φ q x = ∑ i, c a φ x i * q i x := by
    unfold m dF c
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  rw [hm, ← var_eq _ _ (sum_c a φ x hF)]
  refine h.congr_deriv ?_
  ring

end GppLogPartitionVariance
