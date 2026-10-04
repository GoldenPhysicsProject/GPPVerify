import GppVerify.RiemannHypothesis.WeilPositivityCriterion
import GppVerify.RiemannHypothesis.OrientationCriticalRealStructureBridge

/-!
# Arrow-dictionary audit lemmas

These are finite algebraic checks for the Oct. 3, 2026 RH roadmap.

They formalize two points that are easy to blur in prose:

1. reversal symmetry of an off-critical pair only makes the *average* centered
   real part vanish; it does not make either point fixed;
2. conjugating a linear evolution by an invertible linear gauge preserves
   every eigencharacter.

Neither statement proves RH.  Together they force the hard step to remain
positivity of the arithmetic pairing rather than half-density normalization.
-/

namespace GppArrowDictionaryAudit

open Complex
open GppWeilCriterion

/-- A zeta-involution orbit always has zero *average* centered real part.
    This is unconditional and therefore cannot by itself force RH. -/
theorem orbit_centered_real_sum_zero (rho : ℂ) :
    (rho.re - (1 : ℝ) / 2) +
      ((zetaInvolution rho).re - (1 : ℝ) / 2) = 0 := by
  simp [zetaInvolution]
  ring

/-- If a point is not fixed by the zeta involution, the two-point Weil block
    already has an explicit negative direction. -/
open Classical in
theorem off_fixed_pair_has_negative_direction
    {rho : ℂ} (hne : zetaInvolution rho ≠ rho) :
    ∃ c : ℂ → ℂ,
      (pairedForm zetaInvolution {rho, zetaInvolution rho} c).re = -2 := by
  let sigma := zetaInvolution rho
  have hrs : rho ≠ sigma := by
    intro h
    exact hne h.symm
  let c : ℂ → ℂ := fun s =>
    if s = rho then 1 else if s = sigma then -1 else 0
  have hc1 : c rho = 1 := by
    simp [c]
  have hc2 : c sigma = -1 := by
    simp [c, sigma, hne]
  have his : zetaInvolution sigma = rho := by
    simpa [sigma] using zetaInvolution_involutive rho
  have hval : pairedForm zetaInvolution {rho, sigma} c = -2 := by
    simp only [pairedForm]
    rw [Finset.sum_pair hrs, show zetaInvolution rho = sigma from rfl, his]
    exact GppYakaboylu.swap_test_vector_value hc1 hc2
  refine ⟨c, ?_⟩
  rw [show ({rho, zetaInvolution rho} : Finset ℂ) = {rho, sigma} by rfl, hval]
  norm_num

section Gauge

variable {E : Type*} [AddCommMonoid E] [Module ℂ E]

/-- Conjugating a linear evolution by an invertible linear gauge does not
    change its eigencharacter: it only transports the eigenvector. -/
theorem linear_gauge_preserves_eigencharacter
    (M : E ≃ₗ[ℂ] E)
    (V : ℝ → E →ₗ[ℂ] E)
    (chi : ℝ → ℂ)
    (v : E)
    (hEig : ∀ t : ℝ, V t v = chi t • v) :
    ∀ t : ℝ,
      (M.toLinearMap.comp ((V t).comp M.symm.toLinearMap)) (M v)
        = chi t • M v := by
  intro t
  simp [hEig]

end Gauge

end GppArrowDictionaryAudit
