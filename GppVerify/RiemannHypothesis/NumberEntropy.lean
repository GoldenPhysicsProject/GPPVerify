import GppVerify.RiemannHypothesis.GlobalVonMangoldtBridge
import GppVerify.RiemannHypothesis.PrimeGasPartition
import Mathlib.Tactic

/-!
# Number entropy

This file isolates the canonical thermodynamics of the zeta / prime-gas system in the
half-plane where the Dirichlet series is an honest convergent partition sum.

For real inverse temperature `β > 1`, positive integers are microstates with energy
`log n`, and the partition function is `ζ(β)`. We first formalize normalization of the
integer Gibbs weights (as complex numbers; positivity is a separate real-valued corollary),
then identify the internal-energy response with the global von Mangoldt L-series.

The canonical entropy is

  S(s) = log ζ(s) + s U(s),   U(s) = -ζ'(s)/ζ(s).

On the real thermodynamic axis `s = β > 1`, this is the standard Gibbs entropy formula.
No claim is made here that its complex analytic continuation is itself a probability entropy.
-/

namespace GppNumberEntropy

open Complex LSeries

/-- Integer Gibbs weight, indexed from `n = 0` so the physical integer microstate is `n+1`. -/
noncomputable def integerGibbsWeight (β : ℝ) (n : ℕ) : ℂ :=
  (1 / (((n + 1 : ℕ) : ℂ) ^ (β : ℂ))) / riemannZeta (β : ℂ)

/-- The zeta Dirichlet series is the integer partition sum for real `β > 1`. -/
theorem integer_partition_sum_eq_zeta {β : ℝ} (hβ : 1 < β) :
    (∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) ^ (β : ℂ))) = riemannZeta (β : ℂ) := by
  have hs : 1 < ((β : ℂ).re) := by simpa using hβ
  exact (zeta_eq_tsum_one_div_nat_add_one_cpow hs).symm

/-- The integer Gibbs weights are normalized in the thermodynamic domain `β > 1`. -/
theorem integerGibbsWeight_tsum_eq_one {β : ℝ} (hβ : 1 < β) :
    (∑' n : ℕ, integerGibbsWeight β n) = 1 := by
  have hs : 1 < ((β : ℂ).re) := by simpa using hβ
  have hz : riemannZeta (β : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  rw [show (∑' n : ℕ, integerGibbsWeight β n) =
      (∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) ^ (β : ℂ))) / riemannZeta (β : ℂ) by
        simp only [integerGibbsWeight, tsum_div_const]]
  rw [integer_partition_sum_eq_zeta hβ]
  exact div_self hz

/-- Global zeta internal-energy / response function. -/
noncomputable def internalEnergy (s : ℂ) : ℂ :=
  -(deriv riemannZeta s / riemannZeta s)

/-- Canonical number entropy, analytically continued as a complex response function. -/
noncomputable def numberEntropy (s : ℂ) : ℂ :=
  Complex.log (riemannZeta s) + s * internalEnergy s

/-- Canonical entropy identity `S = log Z + β U`. -/
theorem numberEntropy_eq_logZ_add_sU (s : ℂ) :
    numberEntropy s = Complex.log (riemannZeta s) + s * internalEnergy s := rfl

/-- In `Re s > 1`, the internal energy is exactly the global von Mangoldt L-series. -/
theorem internalEnergy_eq_vonMangoldt {s : ℂ} (hs : 1 < s.re) :
    internalEnergy s = L GppGlobalVonMangoldt.vonMangoldtComplex s := by
  unfold internalEnergy
  exact GppGlobalVonMangoldt.neg_zeta_logDeriv_eq_vonMangoldtLSeries hs

/-- Hence number entropy decomposes into partition entropy plus the prime-power energy response. -/
theorem numberEntropy_eq_logZ_add_vonMangoldt {s : ℂ} (hs : 1 < s.re) :
    numberEntropy s = Complex.log (riemannZeta s) +
      s * L GppGlobalVonMangoldt.vonMangoldtComplex s := by
  rw [numberEntropy_eq_logZ_add_sU, internalEnergy_eq_vonMangoldt hs]

end GppNumberEntropy

#print axioms GppNumberEntropy.integer_partition_sum_eq_zeta
#print axioms GppNumberEntropy.integerGibbsWeight_tsum_eq_one
#print axioms GppNumberEntropy.internalEnergy_eq_vonMangoldt
#print axioms GppNumberEntropy.numberEntropy_eq_logZ_add_vonMangoldt
