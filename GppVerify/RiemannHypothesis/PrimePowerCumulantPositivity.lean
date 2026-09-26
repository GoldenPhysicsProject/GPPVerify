import Mathlib

/-!
# Strict positivity of prime-power cumulant terms

This file isolates the elementary strict-sign kernel behind the zeta-Gibbs
cumulant hierarchy. Convergence of the global prime-power sum is a separate
analytic layer and is only available on the honest Gibbs half-plane `β > 1`.
-/

namespace GppPrimePowerCumulantPositivity

/-- The `(p,k)` Euler-mode contribution to the `r`th logarithmic cumulant.
Here `k=0` denotes the first prime power `p^1`. -/
noncomputable def primePowerCumulantTerm
    (r : ℕ) (p : Nat.Primes) (k : ℕ) (β : ℝ) : ℝ :=
  (((k + 1 : ℕ) : ℝ) ^ (r - 1)) *
    (Real.log (p : ℕ) ^ r) *
    Real.exp (-((k + 1 : ℕ) : ℝ) * Real.log (p : ℕ) * β)

/-- Every prime-power cumulant term is strictly positive for positive order.
The sign is independent of `β`; the restriction `β > 1` enters only when the
infinite sum is formed. -/
theorem primePowerCumulantTerm_pos
    {r : ℕ} (hr : 1 ≤ r) (p : Nat.Primes) (k : ℕ) (β : ℝ) :
    0 < primePowerCumulantTerm r p k β := by
  have hp1_nat : 1 < (p : ℕ) := p.prop.one_lt
  have hp1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast hp1_nat
  have hlog : 0 < Real.log ((p : ℕ) : ℝ) := Real.log_pos hp1
  have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hexp : 0 < Real.exp (-((k + 1 : ℕ) : ℝ) * Real.log (p : ℕ) * β) :=
    Real.exp_pos _
  unfold primePowerCumulantTerm
  have hpowk : 0 < (((k + 1 : ℕ) : ℝ) ^ (r - 1)) := pow_pos hk _
  have hpowlog : 0 < (Real.log (p : ℕ) ^ r) := pow_pos hlog _
  exact mul_pos (mul_pos hpowk hpowlog) hexp

/-- In particular the cubic term controlling `g'(β)=-κ₃(β)` is strictly
positive at every prime-power mode. -/
theorem cubic_primePowerCumulantTerm_pos
    (p : Nat.Primes) (k : ℕ) (β : ℝ) :
    0 < primePowerCumulantTerm 3 p k β := by
  exact primePowerCumulantTerm_pos (by norm_num) p k β

end GppPrimePowerCumulantPositivity

#print axioms GppPrimePowerCumulantPositivity.primePowerCumulantTerm_pos
#print axioms GppPrimePowerCumulantPositivity.cubic_primePowerCumulantTerm_pos
