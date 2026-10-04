import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Feasible-set geometry for the odd semilocal Weil form: finite cores

Discovery: GPPDiscovery `discovery/odd_weil/` (2026-10-04, Claude chat seat).

Two finite statements used in that thread, proved here for arbitrary real matrices:

* `eq_zero_of_psd_add_smul`: if two vectors are null for `Q` and `P` takes opposite signs on
  them, then `Q + t • P` is positive semidefinite only at `t = 0`. In the thread,
  `A(c Λ) = Q + (1 - c) P_prime` (zero side plus a multiple of the prime form), and the
  numerics supply the two vectors; this lemma is the logic that then forces `c = 1`
  (`scaling_forced`).
* `not_psd_of_blind_certificate`: a family of vectors whose total quadratic weight vanishes on
  every coefficient direction `W n` but is negative on `W0` rules out every coefficient vector:
  `W0 - ∑ n, b n • W n` is never positive semidefinite. This is weak duality for the feasible
  set `{b | W0 - ∑ b n • W n ⪰ 0}` ("prime-blind certificate").

Nothing here asserts positivity of any Weil form, and no zeta-specific input is used.
-/

namespace GppVerify.OddWeil

open Matrix

variable {m : Type*} [Fintype m]

/-- The quadratic form `x ↦ xᵀ M x`. -/
def qf (M : Matrix m m ℝ) (x : m → ℝ) : ℝ := x ⬝ᵥ (M *ᵥ x)

/-- Positive semidefiniteness as a statement about the quadratic form only. -/
def PSDq (M : Matrix m m ℝ) : Prop := ∀ x : m → ℝ, 0 ≤ qf M x

lemma qf_add (A B : Matrix m m ℝ) (x : m → ℝ) : qf (A + B) x = qf A x + qf B x := by
  simp [qf, Matrix.add_mulVec, dotProduct_add]

lemma qf_sub (A B : Matrix m m ℝ) (x : m → ℝ) : qf (A - B) x = qf A x - qf B x := by
  simp [qf, Matrix.sub_mulVec, dotProduct_sub]

lemma qf_smul (t : ℝ) (A : Matrix m m ℝ) (x : m → ℝ) : qf (t • A) x = t * qf A x := by
  have h : (t • A) *ᵥ x = t • (A *ᵥ x) := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  simp [qf, h, dotProduct_smul, smul_eq_mul]

/-- `A ↦ qf A x` as a linear map, so finite sums pass through it. -/
def qfLin (x : m → ℝ) : Matrix m m ℝ →ₗ[ℝ] ℝ where
  toFun A := qf A x
  map_add' A B := qf_add A B x
  map_smul' t A := by simp [qf_smul]

lemma qf_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix m m ℝ) (x : m → ℝ) :
    qf (∑ i ∈ s, A i) x = ∑ i ∈ s, qf (A i) x :=
  map_sum (qfLin x) A s

/-- **Isolation along a line.** If `u` and `v` are null for `Q` and `P` is negative on `u` and
positive on `v`, the only `t` with `Q + t • P` positive semidefinite is `t = 0`. -/
theorem eq_zero_of_psd_add_smul (Q P : Matrix m m ℝ) (u v : m → ℝ)
    (hu : qf Q u = 0) (hv : qf Q v = 0) (hPu : qf P u < 0) (hPv : 0 < qf P v)
    (t : ℝ) (ht : PSDq (Q + t • P)) : t = 0 := by
  have h1 : 0 ≤ t * qf P u := by
    have := ht u
    rwa [qf_add, qf_smul, hu, zero_add] at this
  have h2 : 0 ≤ t * qf P v := by
    have := ht v
    rwa [qf_add, qf_smul, hv, zero_add] at this
  have hle : t ≤ 0 := by
    by_contra h
    push_neg at h
    have : t * qf P u < 0 := mul_neg_of_pos_of_neg h hPu
    linarith
  have hge : 0 ≤ t := by
    by_contra h
    push_neg at h
    have : t * qf P v < 0 := mul_neg_of_neg_of_pos h hPv
    linarith
  linarith

/-- **Prime-strength form.** With `A(c) = Q + (1 - c) • P`, the same hypotheses force `c = 1`. -/
theorem scaling_forced (Q P : Matrix m m ℝ) (u v : m → ℝ)
    (hu : qf Q u = 0) (hv : qf Q v = 0) (hPu : qf P u < 0) (hPv : 0 < qf P v)
    (c : ℝ) (hc : PSDq (Q + (1 - c) • P)) : c = 1 := by
  have := eq_zero_of_psd_add_smul Q P u v hu hv hPu hPv (1 - c) hc
  linarith

/-- **Prime-blind certificate (weak duality).** If vectors `z i` have total weight zero on every
coefficient direction `W n` and negative total weight on `W0`, then no coefficient vector `b`
makes `W0 - ∑ n, b n • W n` positive semidefinite. -/
theorem not_psd_of_blind_certificate {ι κ : Type*} [Fintype ι] [Fintype κ]
    (W0 : Matrix m m ℝ) (W : κ → Matrix m m ℝ) (z : ι → m → ℝ)
    (hblind : ∀ n, ∑ i, qf (W n) (z i) = 0)
    (hneg : ∑ i, qf W0 (z i) < 0) (b : κ → ℝ) :
    ¬ PSDq (W0 - ∑ n, b n • W n) := by
  intro hpsd
  have hpt : ∀ i, qf (W0 - ∑ n, b n • W n) (z i) = qf W0 (z i) - ∑ n, b n * qf (W n) (z i) := by
    intro i
    rw [qf_sub, qf_sum]
    simp only [qf_smul]
  have hzero : ∑ i, ∑ n, b n * qf (W n) (z i) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hblind, mul_zero, Finset.sum_const_zero]
  have htot : ∑ i, qf (W0 - ∑ n, b n • W n) (z i) = ∑ i, qf W0 (z i) := by
    simp_rw [hpt, Finset.sum_sub_distrib, hzero, sub_zero]
  have hnn : 0 ≤ ∑ i, qf (W0 - ∑ n, b n • W n) (z i) :=
    Finset.sum_nonneg (fun i _ => hpsd (z i))
  linarith

end GppVerify.OddWeil
