import GppVerify.RiemannHypothesis.PrimeHankelFiniteGramStrict
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Infinite lifting for strict prime-gas Gram positivity

A strictly positive finite truncation of a summable nonnegative series forces the
full infinite sum to be strictly positive.  This is the order-theoretic bridge
needed to pass from finite prime witnesses to the full von-Mangoldt moment form.
-/

namespace GppPrimeHankelInfiniteLift

open Polynomial BigOperators
open GppPrimeHankelRootEscape

/-- A positive finite witness inside a summable nonnegative series forces the
whole `tsum` to be strictly positive. -/
theorem tsum_pos_of_finite_sum_pos
    {ι : Type*} (f : ι → ℝ) (S : Finset ι)
    (hf : Summable f)
    (hnonneg : ∀ i, 0 ≤ f i)
    (hS : 0 < ∑ i ∈ S, f i) :
    0 < ∑' i, f i := by
  exact lt_of_lt_of_le hS
    (sum_le_tsum S (fun i _ => hnonneg i) hf)

/-- Convenient form for weighted squares: positivity of one finite truncation
lifts to positivity of the full summable weighted-square series. -/
theorem weighted_sq_tsum_pos
    {ι : Type*} (w q : ι → ℝ) (S : Finset ι)
    (hsum : Summable (fun i => w i * (q i) ^ 2))
    (hw : ∀ i, 0 ≤ w i)
    (hS : 0 < ∑ i ∈ S, w i * (q i) ^ 2) :
    0 < ∑' i, w i * (q i) ^ 2 := by
  apply tsum_pos_of_finite_sum_pos (fun i => w i * (q i) ^ 2) S hsum
  · intro i
    exact mul_nonneg (hw i) (sq_nonneg (q i))
  · exact hS

/-- Finite strict positivity directly on an indexed support map.  It is enough
that the finite set contributes more than `N` distinct support values. -/
theorem finite_weighted_eval_comp_sq_sum_pos
    {ι : Type*} (p : ℝ[X]) (S : Finset ι) (x w : ι → ℝ) (N : ℕ)
    (hp : p ≠ 0)
    (hdeg : p.natDegree ≤ N)
    (hcard : N < (S.image x).card)
    (hw : ∀ i ∈ S, 0 < w i) :
    0 < ∑ i ∈ S, w i * (p.eval (x i)) ^ 2 := by
  classical
  rcases exists_eval_ne_zero_of_card_gt_degree_bound p (S.image x) N hp hdeg hcard with
    ⟨y, hy, hpy⟩
  rcases Finset.mem_image.mp hy with ⟨i, hi, rfl⟩
  apply Finset.sum_pos'
  · intro j hj
    exact mul_nonneg (hw j hj).le (sq_nonneg (p.eval (x j)))
  · refine ⟨i, hi, ?_⟩
    exact mul_pos (hw i hi) (sq_pos_of_ne_zero hpy)

/-- All-order strict positivity of a summable weighted polynomial Gram series.
A finite set with more than `N` distinct support values supplies the witness;
nonnegativity and summability lift it to the full infinite sum. -/
theorem weighted_polynomial_tsum_pos
    {ι : Type*} (p : ℝ[X]) (x w : ι → ℝ) (S : Finset ι) (N : ℕ)
    (hp : p ≠ 0)
    (hdeg : p.natDegree ≤ N)
    (hcard : N < (S.image x).card)
    (hw : ∀ i, 0 ≤ w i)
    (hwS : ∀ i ∈ S, 0 < w i)
    (hsum : Summable (fun i => w i * (p.eval (x i)) ^ 2)) :
    0 < ∑' i, w i * (p.eval (x i)) ^ 2 := by
  apply weighted_sq_tsum_pos w (fun i => p.eval (x i)) S hsum hw
  exact finite_weighted_eval_comp_sq_sum_pos p S x w N hp hdeg hcard hwS

end GppPrimeHankelInfiniteLift

#print axioms GppPrimeHankelInfiniteLift.tsum_pos_of_finite_sum_pos
#print axioms GppPrimeHankelInfiniteLift.weighted_sq_tsum_pos
#print axioms GppPrimeHankelInfiniteLift.finite_weighted_eval_comp_sq_sum_pos
#print axioms GppPrimeHankelInfiniteLift.weighted_polynomial_tsum_pos
