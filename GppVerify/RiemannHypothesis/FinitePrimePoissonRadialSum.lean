import GppVerify.RiemannHypothesis.PrimePoissonRadialBridge
import Mathlib.Tactic

/-!
# Finite-prime radial Poisson sum

This is the first finite arithmetic aggregation of the arbitrary-radial local theorem.
For any finite set of real prime parameters p>1 and any a>0, summing the local
Poisson responses is exactly twice the sum of the real parts of the corresponding
local Euler-factor logarithmic derivatives on s=a+it.

This is finite algebra only. It does not pass to the infinite prime sum and makes no
explicit-formula or RH claim.
-/

namespace GppFinitePrimePoissonRadial

open Complex Real
open GppCutkoskyWeil
open GppPrimePoissonRadial

/-- Finite-prime sum of the exact local radial bridge. -/
theorem sum_WpA_eq_two_mul_sum_re
    (P : Finset ℝ) {a : ℝ} (ha : 0 < a)
    (hp : ∀ p ∈ P, 1 < p) (t : ℝ) :
    ∑ p in P, WpA p a t =
      2 * ∑ p in P, (minusLogDerivZetaP p (a + t * Complex.I)).re := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hpP
  exact WpA_eq_two_mul_re_minusLogDerivZetaP (hp p hpP) ha t

end GppFinitePrimePoissonRadial

#print axioms GppFinitePrimePoissonRadial.sum_WpA_eq_two_mul_sum_re
