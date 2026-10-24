import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# The centred kernel is a rank-two correction

Source: Codex, GPP-bridge PR #11 comment 6380730175 (suggestion 2; recipients corrected in
6380734644), on Turbo's Wave 295 decomposition `K^c(m, n) = K₁(m, n) − u(m) − u(n) + C`.
Daniel Toupin / Golden Physics Project, with AI assistance from Codex (statement) and Claude Code
(formalization).

For a finite real vector `r`, write `S = ∑ r_m` and `U = ∑ u(m) r_m`.

* `centred_quadratic_form`: `rᵀ K^c r = rᵀ K₁ r − 2 S U + C S²`.
* `centred_quadratic_form_of_neutral`: on the neutral subspace `S = 0` the centred and
  uncentred forms coincide, `rᵀ K^c r = rᵀ K₁ r`. So centring adds no sign mechanism there; the
  whole difference sits in the two scalar moments `S` and `U`.

**Scope.** Finite index set, no symmetry or positivity assumption, and no positivity claim. For
`r_n = Λ(n) − 1`, `S = ψ(X) − ⌊X⌋` is RH-sensitive; nothing here bounds it. No claim about RH.
-/

open Finset

namespace GppRankTwoCentring

variable {ι : Type*} [Fintype ι]

/-- The centred kernel `K^c(m, n) = K₁(m, n) − u(m) − u(n) + C`. -/
def centred (K₁ : ι → ι → ℝ) (u : ι → ℝ) (C : ℝ) (m n : ι) : ℝ := K₁ m n - u m - u n + C

/-- The quadratic form `rᵀ K r`. -/
def qform (K : ι → ι → ℝ) (r : ι → ℝ) : ℝ := ∑ m, ∑ n, r m * r n * K m n

/-- **Rank-two centring identity.** `rᵀ K^c r = rᵀ K₁ r − 2 S U + C S²`. -/
theorem centred_quadratic_form (K₁ : ι → ι → ℝ) (u r : ι → ℝ) (C : ℝ) :
    qform (centred K₁ u C) r =
      qform K₁ r - 2 * (∑ m, r m) * (∑ m, u m * r m) + C * (∑ m, r m) ^ 2 := by
  have h1 : ∑ m, ∑ n, r m * r n * u m = (∑ m, r m) * ∑ m, u m * r m := by
    rw [mul_comm, sum_mul_sum]
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => by ring
  have h2 : ∑ m, ∑ n, r m * r n * u n = (∑ m, r m) * ∑ m, u m * r m := by
    rw [sum_mul_sum]
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => by ring
  have h3 : ∑ m, ∑ n, r m * r n * C = C * (∑ m, r m) ^ 2 := by
    rw [sq, sum_mul_sum, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun n _ => by ring
  have hexp : qform (centred K₁ u C) r =
      qform K₁ r - ∑ m, ∑ n, r m * r n * u m - ∑ m, ∑ n, r m * r n * u n
        + ∑ m, ∑ n, r m * r n * C := by
    simp only [qform, centred, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  rw [hexp, h1, h2, h3]
  ring

/-- **Neutral subspace.** If `∑ r_m = 0`, then `rᵀ K^c r = rᵀ K₁ r`. -/
theorem centred_quadratic_form_of_neutral (K₁ : ι → ι → ℝ) (u r : ι → ℝ) (C : ℝ)
    (hS : ∑ m, r m = 0) : qform (centred K₁ u C) r = qform K₁ r := by
  rw [centred_quadratic_form, hS]
  ring

end GppRankTwoCentring
