import GppVerify.QuantumGravity.GlobalEisensteinCoefficient
import GppVerify.RiemannHypothesis.CompletedZetaReality
import Mathlib.Tactic

/-!
# Arithmetic Eisenstein scattering is unitary on the principal axis

The spherical global Eisenstein coefficient already formalized in
`GlobalEisensteinCoefficient` is

  phi(Delta) = Lambda(2-Delta) / Lambda(Delta),

where `Lambda` is Mathlib's completed Riemann zeta function.  On the celestial /
arithmetic principal axis `Re Delta = 1`, the shadow argument is exactly complex
conjugation:

  2-Delta = conj Delta.

Completed-zeta reality therefore turns the automorphic scattering coefficient into

  phi(Delta) = conj(Lambda(Delta)) / Lambda(Delta).

Consequently it has norm one wherever the denominator is nonzero.  This is a
genuine automorphic principal-series scattering/unitarity statement, not merely an
analogy with CFT.  It does not constrain zeros off the principal axis and is not an
RH proof.
-/

namespace GppArithmeticEisensteinUnitarity

open GppEisenstein

/-- On the principal axis, celestial shadow is exactly Hermitian conjugation of the
spectral parameter. -/
theorem two_sub_eq_star_of_re_one {Delta : ℂ} (hDelta : Delta.re = 1) :
    2 - Delta = (starRingEnd ℂ) Delta := by
  apply Complex.ext
  · norm_num [hDelta]
  · simp

/-- The global Eisenstein scattering coefficient is a pure completed-zeta phase on
the principal axis. -/
theorem eisensteinCoeff_eq_star_div_of_re_one
    {Delta : ℂ} (hDelta : Delta.re = 1) :
    eisensteinCoeff Delta =
      (starRingEnd ℂ) (completedRiemannZeta Delta) / completedRiemannZeta Delta := by
  have hpos : 0 < Delta.re := by rw [hDelta]; norm_num
  rw [eisensteinCoeff_eq_shadow_ratio,
    two_sub_eq_star_of_re_one hDelta,
    GppCompletedZetaReality.completedRiemannZeta_conj hpos]

/-- **Principal-series scattering unitarity.**  Away from a zero of the completed
zeta denominator, the global spherical Eisenstein coefficient has unit norm on
`Re Delta = 1`. -/
theorem norm_eisensteinCoeff_eq_one_of_re_one
    {Delta : ℂ} (hDelta : Delta.re = 1)
    (hLambda : completedRiemannZeta Delta ≠ 0) :
    ‖eisensteinCoeff Delta‖ = 1 := by
  rw [eisensteinCoeff_eq_star_div_of_re_one hDelta, norm_div]
  simp [hLambda]

/-- Explicit principal-axis parameterization induced from
`s = 1/2 + i tau` by `Delta = 2s`. -/
noncomputable def principalDelta (tau : ℝ) : ℂ :=
  1 + (2 * tau : ℂ) * Complex.I

@[simp] theorem principalDelta_re (tau : ℝ) :
    (principalDelta tau).re = 1 := by
  simp [principalDelta]

/-- Parameterized principal-series scattering unitarity. -/
theorem norm_eisensteinCoeff_principalDelta
    (tau : ℝ)
    (hLambda : completedRiemannZeta (principalDelta tau) ≠ 0) :
    ‖eisensteinCoeff (principalDelta tau)‖ = 1 := by
  exact norm_eisensteinCoeff_eq_one_of_re_one (principalDelta_re tau) hLambda

/-- The reflected coefficient and original coefficient multiply to one on the
principal axis, using the already formalized global Weyl/reflection law. -/
theorem eisensteinCoeff_reflection_principal
    {Delta : ℂ} (hDelta : Delta.re = 1)
    (hLambda : completedRiemannZeta Delta ≠ 0) :
    eisensteinCoeff (2 - Delta) * eisensteinCoeff Delta = 1 := by
  have hshadow : completedRiemannZeta (2 - Delta) ≠ 0 := by
    rw [two_sub_eq_star_of_re_one hDelta]
    have hpos : 0 < Delta.re := by rw [hDelta]; norm_num
    rw [GppCompletedZetaReality.completedRiemannZeta_conj hpos]
    exact (map_ne_zero (starRingEnd ℂ)).2 hLambda
  exact eisensteinCoeff_reflection hLambda hshadow

end GppArithmeticEisensteinUnitarity

#print axioms GppArithmeticEisensteinUnitarity.eisensteinCoeff_eq_star_div_of_re_one
#print axioms GppArithmeticEisensteinUnitarity.norm_eisensteinCoeff_eq_one_of_re_one
#print axioms GppArithmeticEisensteinUnitarity.norm_eisensteinCoeff_principalDelta
#print axioms GppArithmeticEisensteinUnitarity.eisensteinCoeff_reflection_principal
