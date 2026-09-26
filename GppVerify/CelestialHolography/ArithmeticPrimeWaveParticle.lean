import GppVerify.RiemannHypothesis.WeilSupportLadder
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Arithmetic prime wave-particle dictionary: finite exact layer

The Weil prime side is supported on the discrete arithmetic locations

  x = ± log n,

with von Mangoldt weight `Lambda(n)/sqrt(n)`, and `Lambda(n)` vanishes unless `n` is a
prime power. Pairing this discrete source with the real principal-series wave

  x |-> cos(tau x)

therefore gives an exact finite superposition of oscillatory responses. This file records
that layer only; it takes no infinite limit and makes no claim about zeta-zero support or RH.
-/

namespace GppArithmeticPrimeWaveParticle

open Finset ArithmeticFunction

/-- The real principal-series wave in logarithmic scale. -/
noncomputable def principalWave (tau x : ℝ) : ℝ := Real.cos (tau * x)

/-- The arithmetic particle weight at the integer location `n`. -/
noncomputable def particleWeight (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt n

/-- The symmetric response of the particle at `± log n` to a principal wave. -/
noncomputable def particleWaveResponse (n : ℕ) (tau : ℝ) : ℝ :=
  particleWeight n *
    (principalWave tau (Real.log n) + principalWave tau (-(Real.log n)))

/-- A single symmetric arithmetic particle contributes twice the cosine wave at `log n`. -/
theorem particleWaveResponse_eq (n : ℕ) (tau : ℝ) :
    particleWaveResponse n tau =
      2 * particleWeight n * Real.cos (tau * Real.log n) := by
  unfold particleWaveResponse principalWave
  rw [show tau * (-Real.log n) = -(tau * Real.log n) by ring, Real.cos_neg]
  ring

/-- Non-prime-powers carry no arithmetic particle weight. -/
theorem particleWeight_eq_zero_of_not_primePow {n : ℕ} (hn : ¬ IsPrimePow n) :
    particleWeight n = 0 := by
  unfold particleWeight
  have hLambda : ArithmeticFunction.vonMangoldt n = 0 := by
    by_contra hne
    exact hn (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hne)
  rw [hLambda, zero_div]

/-- Consequently a non-prime-power has zero response to every principal wave. -/
theorem particleWaveResponse_eq_zero_of_not_primePow {n : ℕ} (hn : ¬ IsPrimePow n)
    (tau : ℝ) :
    particleWaveResponse n tau = 0 := by
  rw [particleWaveResponse_eq, particleWeight_eq_zero_of_not_primePow hn]
  ring

/-- Finite prime/prime-power source paired with a principal wave. -/
noncomputable def finitePrimeWaveResponse (N : ℕ) (tau : ℝ) : ℝ :=
  ∑ n ∈ range (N + 1), particleWaveResponse n tau

/-- Exact finite wave-particle dictionary: the symmetric discrete prime-power source is the
finite cosine superposition with von Mangoldt weights. -/
theorem finitePrimeWaveResponse_eq (N : ℕ) (tau : ℝ) :
    finitePrimeWaveResponse N tau =
      2 * ∑ n ∈ range (N + 1), particleWeight n * Real.cos (tau * Real.log n) := by
  unfold finitePrimeWaveResponse
  simp_rw [particleWaveResponse_eq]
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  ring

/-- The finite response is even in spectral time/frequency. -/
theorem finitePrimeWaveResponse_neg (N : ℕ) (tau : ℝ) :
    finitePrimeWaveResponse N (-tau) = finitePrimeWaveResponse N tau := by
  rw [finitePrimeWaveResponse_eq, finitePrimeWaveResponse_eq]
  apply congrArg (fun x : ℝ => 2 * x)
  apply sum_congr rfl
  intro n hn
  rw [show (-tau) * Real.log n = -(tau * Real.log n) by ring, Real.cos_neg]

/-- The response at zero frequency is twice the total finite arithmetic particle weight. -/
theorem finitePrimeWaveResponse_zero (N : ℕ) :
    finitePrimeWaveResponse N 0 =
      2 * ∑ n ∈ range (N + 1), particleWeight n := by
  rw [finitePrimeWaveResponse_eq]
  simp

end GppArithmeticPrimeWaveParticle

#print axioms GppArithmeticPrimeWaveParticle.particleWaveResponse_eq
#print axioms GppArithmeticPrimeWaveParticle.particleWeight_eq_zero_of_not_primePow
#print axioms GppArithmeticPrimeWaveParticle.finitePrimeWaveResponse_eq
#print axioms GppArithmeticPrimeWaveParticle.finitePrimeWaveResponse_neg
