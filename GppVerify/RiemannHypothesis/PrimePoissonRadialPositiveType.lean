import GppVerify.RiemannHypothesis.PrimePoissonRadialBridge
import Mathlib.Tactic

/-!
# Positive type for arbitrary-radial prime Poisson response

The previously formalized theorem `KrClosed_minus_one_positiveType` proves positivity for
`K_r-1` at every `0 <= r < 1`.  This file transports that theorem through the two operations
needed by the radial prime response:

* input scaling `t |-> (log p) t`;
* multiplication by the nonnegative scalar `log p`.

Thus `WpA p a` is positive type for every real `p>1` and `a>0`.
-/

namespace GppPrimePoissonRadialPositiveType

open Complex Real
open GppCutkoskyWeil
open GppPrimePoissonRadial
open GppHaarPositivityWeil

/-- Positive type is preserved under real input scaling. -/
theorem positiveType_comp_mul {f : ℝ → ℝ}
    (hf : PositiveType f) (c : ℝ) :
    PositiveType (fun t => f (c * t)) := by
  intro n x z
  have h := hf n (fun i => c * x i) z
  simpa [mul_sub] using h

/-- Positive type is preserved under multiplication by a nonnegative real scalar. -/
theorem positiveType_nonneg_mul {f : ℝ → ℝ}
    (hf : PositiveType f) {c : ℝ} (hc : 0 ≤ c) :
    PositiveType (fun t => c * f t) := by
  intro n x z
  have h := hf n x z
  let S : ℂ := ∑ i : Fin n, ∑ j : Fin n,
    (starRingEnd ℂ (z i)) * z j * (f (x i - x j) : ℂ)
  have hS : 0 ≤ S.re := by
    simpa [S] using h
  have heq :
      (∑ i : Fin n, ∑ j : Fin n,
        (starRingEnd ℂ (z i)) * z j * ((c * f (x i - x j) : ℝ) : ℂ)) =
      (c : ℂ) * S := by
    dsimp [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    push_cast
    ring
  rw [heq]
  simpa [Complex.mul_re] using mul_nonneg hc hS

/-- The arbitrary-radial local prime response is positive type for every `p>1`, `a>0`. -/
theorem WpA_positiveType {p a : ℝ} (hp : 1 < p) (ha : 0 < a) :
    PositiveType (WpA p a) := by
  have hp0 : (0 : ℝ) < p := lt_trans one_pos hp
  let r : ℝ := p ^ (-a)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact Real.rpow_nonneg hp0.le _
  have hr1 : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp (neg_lt_zero.mpr ha)
  have hbase : PositiveType (fun θ => KrClosed r θ - 1) :=
    KrClosed_minus_one_positiveType hr0 hr1
  have hscaled : PositiveType (fun t => KrClosed r (Real.log p * t) - 1) :=
    positiveType_comp_mul hbase (Real.log p)
  have hlog : 0 ≤ Real.log p := (Real.log_pos hp).le
  have hweighted :
      PositiveType (fun t => Real.log p * (KrClosed r (Real.log p * t) - 1)) :=
    positiveType_nonneg_mul hscaled hlog
  simpa [WpA, r, mul_comm] using hweighted

end GppPrimePoissonRadialPositiveType

#print axioms GppPrimePoissonRadialPositiveType.positiveType_comp_mul
#print axioms GppPrimePoissonRadialPositiveType.positiveType_nonneg_mul
#print axioms GppPrimePoissonRadialPositiveType.WpA_positiveType
