import Mathlib

/-!
# Prime-local arithmetic Osterwalder--Schrader positivity

For a real scale `p ≥ 1`, the arithmetic prime-power weights

  log p * exp (-(m/2) log p)

are nonnegative.  Each prime-power transfer mode is rank one on positive
Euclidean logarithmic times.  Therefore every finite truncation of the
prime-local reflected kernel is a positive Gram form.

This is the finite algebraic core of the positive measure

  μ_p = Σ_{m≥1} (log p) p^{-m/2} δ_{m log p}.

It does not prove positivity of the completed prime--Archimedean explicit
formula, where the prime sector occurs with the opposite sign.
-/

namespace GppArithmeticPrimeLocalOS

open scoped BigOperators

/-- Positive coefficient carried by the `m`-th prime-power mode. -/
noncomputable def modeWeight (p : ℝ) (m : ℕ) : ℝ :=
  Real.log p * Real.exp (-((m : ℝ) / 2) * Real.log p)

/-- Euclidean transfer amplitude of the `m`-th mode at logarithmic time `t`. -/
noncomputable def modeValue (p : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-(m : ℝ) * Real.log p * t)

/-- Prime-power weights are nonnegative for `p ≥ 1`. -/
theorem modeWeight_nonneg {p : ℝ} (hp : 1 ≤ p) (m : ℕ) :
    0 ≤ modeWeight p m := by
  unfold modeWeight
  exact mul_nonneg (Real.log_nonneg hp) (Real.exp_pos _).le

/-- A single weighted transfer mode is a nonnegative rank-one Gram form. -/
theorem singleMode_os_nonneg
    {p : ℝ} (hp : 1 ≤ p) (m : ℕ)
    {N : ℕ} (c t : Fin N → ℝ) :
    0 ≤ modeWeight p m *
      (∑ i : Fin N, c i * modeValue p m (t i)) ^ 2 := by
  exact mul_nonneg (modeWeight_nonneg hp m) (sq_nonneg _)

/-- Every finite prime-power truncation is reflection positive. -/
theorem truncatedPrime_os_nonneg
    {p : ℝ} (hp : 1 ≤ p) (M N : ℕ)
    (c t : Fin N → ℝ) :
    0 ≤ ∑ m ∈ Finset.range M,
      modeWeight p (m + 1) *
        (∑ i : Fin N, c i * modeValue p (m + 1) (t i)) ^ 2 := by
  exact Finset.sum_nonneg fun m hm => singleMode_os_nonneg hp (m + 1) c t

/-- The same statement with arbitrary nonnegative local weights.  This is the
abstract finite OS lemma used when replacing the prime weights by any positive
local arithmetic measure. -/
theorem finitePositiveMeasure_os_nonneg
    {M N : ℕ} (w : Fin M → ℝ) (hw : ∀ m, 0 ≤ w m)
    (v : Fin M → Fin N → ℝ) (c : Fin N → ℝ) :
    0 ≤ ∑ m : Fin M, w m * (∑ i : Fin N, c i * v m i) ^ 2 := by
  exact Finset.sum_nonneg fun m hm => mul_nonneg (hw m) (sq_nonneg _)

end GppArithmeticPrimeLocalOS

#print axioms GppArithmeticPrimeLocalOS.modeWeight_nonneg
#print axioms GppArithmeticPrimeLocalOS.singleMode_os_nonneg
#print axioms GppArithmeticPrimeLocalOS.truncatedPrime_os_nonneg
#print axioms GppArithmeticPrimeLocalOS.finitePositiveMeasure_os_nonneg
