import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.BigOperators.Field

/-!
# The centered divisor coordinate: the principal-series line is the fixed centre of Hodge duality

Source: Codex, GPPDiscovery2 `research/2026-09-28_centered_divisor_principal_series_geometry.md`.

For `d ∣ N` put `ℓ_N(d) = log d − ½ log N` (`centered`).

* `centered_eq_sum`: `ℓ_N(d) = Σ_{p ∣ N} (v_p(d) − K_p/2) log p`, with `K_p = v_p(N)`: every local
  valuation coordinate is reflected about its midpoint `K_p/2`;
* `centered_complement`: divisor complementation `d ↦ N/d` acts on the centered coordinate by
  `ℓ ↦ −ℓ`;
* `character_complement`: for the centered scaling character `χ_t(d) = e^{−i t ℓ_N(d)}`,
  `χ_t(N/d) = χ_{−t}(d) = conj χ_t(d)`, the unitary reflection law of the one-dimensional principal
  series.

Together with `GppSelfDualDivisor` (the overlap `⟨v_d, v_{dp}⟩ = p^{-1/2}`), the half shift is the
midpoint of the local valuation reflection, the half-density of normalized subgroup inclusion, and the
Mellin–Plancherel unitary line of the scaling representation.

## Checks and scope

All claims check. **Not formalized:** the finite Fourier statement `𝓕 v_d = v_{N/d}` that motivates
the complementation (the note takes it from the preceding self-dual divisor note), and the global
statement (spectral quantization: why the continuous `t` becomes the Riemann ordinates), which is the
note's open target. No RH claim.
-/

open Real

namespace GppCenteredDivisor

/-- The centered logarithmic divisor coordinate. -/
noncomputable def centered (N d : ℕ) : ℝ := Real.log d - Real.log N / 2

/-- **Divisor complementation negates the centered coordinate.** -/
theorem centered_complement (N d : ℕ) (hd : 0 < d) (hdN : d ∣ N) (hN : 0 < N) :
    centered N (N / d) = -centered N d := by
  unfold centered
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have : ((N / d : ℕ) : ℝ) = N / d := Nat.cast_div hdN hd'
  rw [this, Real.log_div hN' hd']
  ring

/-- **Valuation form.** For `d ∣ N`, `ℓ_N(d) = Σ_{p ∣ N} (v_p(d) − v_p(N)/2) log p`. -/
theorem centered_eq_sum (N d : ℕ) (hd : 0 < d) (hdN : d ∣ N) (hN : 0 < N) :
    centered N d = ∑ p ∈ N.primeFactors,
      ((d.factorization p : ℝ) - (N.factorization p : ℝ) / 2) * Real.log p := by
  have hsub : d.primeFactors ⊆ N.primeFactors := Nat.primeFactors_mono hdN hN.ne'
  have key : ∀ n : ℕ, n ≠ 0 → n.primeFactors ⊆ N.primeFactors →
      Real.log n = ∑ p ∈ N.primeFactors, (n.factorization p : ℝ) * Real.log p := by
    intro n hn hs
    rw [Real.log_nat_eq_sum_factorization]
    refine Finsupp.sum_of_support_subset _ ?_ _ (fun p _ => by simp)
    rw [Nat.support_factorization]
    exact hs
  have h1 := key d hd.ne' hsub
  have h2 := key N hN.ne' subset_rfl
  unfold centered
  rw [h1, h2, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- The centered scaling character `χ_t(d) = e^{−i t ℓ_N(d)}`. -/
noncomputable def chi (N : ℕ) (t : ℝ) (d : ℕ) : ℂ :=
  Complex.exp (-(Complex.I * ((t * centered N d : ℝ) : ℂ)))

/-- **`χ_t(N/d) = conj χ_t(d) = χ_{−t}(d)`.** -/
theorem character_complement (N d : ℕ) (t : ℝ) (hd : 0 < d) (hdN : d ∣ N) (hN : 0 < N) :
    chi N t (N / d) = chi N (-t) d ∧ chi N t (N / d) = (starRingEnd ℂ) (chi N t d) := by
  have hc := centered_complement N d hd hdN hN
  constructor
  · unfold chi
    rw [hc]
    congr 1
    push_cast
    ring
  · unfold chi
    rw [hc, ← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]

end GppCenteredDivisor
