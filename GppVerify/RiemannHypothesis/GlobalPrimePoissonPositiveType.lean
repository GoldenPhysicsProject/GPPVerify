import GppVerify.RiemannHypothesis.VonMangoldtPrimePowerPoissonFiber
import GppVerify.RiemannHypothesis.PrimePoissonRadialPositiveType
import GppVerify.RiemannHypothesis.ConvolutionSquarePositive
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

/-!
# Positive type of the global prime-Poisson response

On the honest half-plane `a > 1`, the global response

  `t ↦ ∑' p : Nat.Primes, WpA p a t`

is absolutely convergent pointwise and each local prime kernel is positive type.
This file proves that the pointwise `tsum` is itself positive type by commuting the
finite Gram form with the absolutely convergent prime series.
-/

namespace GppGlobalPrimePoissonPositiveType

open Real
open GppHaarPositivityWeil
open GppPrimePoissonRadial
open GppPrimePoissonRadialPositiveType
open GppVonMangoldtPrimePowerPoissonFiber

/-- A pointwise summable family of real positive-type kernels has positive-type `tsum`. -/
theorem positiveType_tsum {ι : Type*} {F : ι → ℝ → ℝ}
    (hF : ∀ i, PositiveType (F i))
    (hs : ∀ t, Summable (fun i => F i t)) :
    PositiveType (fun t => ∑' i, F i t) := by
  intro n x c
  rw [Complex.re_sum]
  simp_rw [Complex.re_sum, GppHaarPositivityWeil.mul_ofReal_re]
  simp_rw [← tsum_mul_left]
  have hswap :
      (∑ i : Fin n, ∑ j : Fin n,
        ∑' k : ι,
          ((starRingEnd ℂ (c i)) * c j).re * F k (x i - x j)) =
      ∑' k : ι, ∑ i : Fin n, ∑ j : Fin n,
        ((starRingEnd ℂ (c i)) * c j).re * F k (x i - x j) := by
    calc
      (∑ i : Fin n, ∑ j : Fin n,
          ∑' k : ι,
            ((starRingEnd ℂ (c i)) * c j).re * F k (x i - x j)) =
        ∑ i : Fin n, ∑' k : ι, ∑ j : Fin n,
          ((starRingEnd ℂ (c i)) * c j).re * F k (x i - x j) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hj : ∀ j ∈ (Finset.univ : Finset (Fin n)),
              Summable (fun k : ι =>
                ((starRingEnd ℂ (c i)) * c j).re * F k (x i - x j)) := by
            intro j hj
            exact (hs (x i - x j)).mul_left _
          simpa using (Summable.tsum_finsetSum hj).symm
      _ = ∑' k : ι, ∑ i : Fin n, ∑ j : Fin n,
          ((starRingEnd ℂ (c i)) * c j).re * F k (x i - x j) := by
          have hi : ∀ i ∈ (Finset.univ : Finset (Fin n)),
              Summable (fun k : ι => ∑ j : Fin n,
                ((starRingEnd ℂ (c i)) * c j).re * F k (x i - x j)) := by
            intro i hi
            exact summable_sum fun j hj =>
              (hs (x i - x j)).mul_left _
          simpa using (Summable.tsum_finsetSum hi).symm
  rw [hswap]
  apply tsum_nonneg
  intro k
  have hk := hF k n x c
  rw [Complex.re_sum] at hk
  simp_rw [Complex.re_sum, GppHaarPositivityWeil.mul_ofReal_re] at hk
  exact hk

/-- The infinite prime-Poisson response is positive type for every `a > 1`. -/
theorem global_WpA_positiveType {a : ℝ} (ha : 1 < a) :
    PositiveType (fun t => ∑' p : Nat.Primes, WpA ((p : ℕ) : ℝ) a t) := by
  apply positiveType_tsum
  · intro p
    have hp : (1 : ℝ) < (p : ℕ) := by
      exact_mod_cast p.prop.one_lt
    exact WpA_positiveType hp (lt_trans zero_lt_one ha)
  · intro t
    exact summable_WpA ha t

/-- Therefore the real logarithmic derivative response is positive type on `a > 1`. -/
theorem neg_zeta_logDeriv_response_positiveType {a : ℝ} (ha : 1 < a) :
    PositiveType (fun t =>
      2 * (-(Complex.deriv Complex.riemannZeta
        ((a : ℂ) + (t : ℂ) * Complex.I) /
        Complex.riemannZeta ((a : ℂ) + (t : ℂ) * Complex.I))).re) := by
  have h := global_WpA_positiveType ha
  intro n x c
  simpa [two_mul_neg_zeta_logDeriv_re_eq_tsum_WpA ha] using h n x c

end GppGlobalPrimePoissonPositiveType

#print axioms GppGlobalPrimePoissonPositiveType.positiveType_tsum
#print axioms GppGlobalPrimePoissonPositiveType.global_WpA_positiveType
#print axioms GppGlobalPrimePoissonPositiveType.neg_zeta_logDeriv_response_positiveType
