import Mathlib.Tactic
import GppVerify.CelestialHolography.EinsteinNullRaySL2Geometry
import GppVerify.CelestialHolography.LegendreCrossingSturmConnection

/-!
# Sturm solution ratios and the Schwarzian projective connection

For a second-order normal-form equation

    psi'' + U psi = 0,

take two independent solutions with nonzero Wronskian `W` and form their projective ratio
`tau = psi1/psi2`.  Standard ODE calculus gives

    tau'   = W / psi2^2,
    tau''  = -2 W psi2' / psi2^3,
    tau''' = -2 W psi2'' / psi2^3 + 6 W (psi2')^2 / psi2^4.

The Schwarzian derivative is

    {tau,s} = tau'''/tau' - (3/2)(tau''/tau')^2,

and the cancellations imply

    {tau,s} = -2 psi2''/psi2 = 2 U.

This is the exact local bridge between a rank-two Sturm system and its projective
connection.  The file formalizes the rational jet identity, avoiding any hidden ODE or
differentiability axiom.  To use it geometrically one supplies the standard calculus facts
that the displayed jets are derivatives of an actual solution ratio.

This bridge is important for the googly program because both the null-ray Einstein/NSF
bundle and the Legendre/Gauss--Manin four-point system are rank-two Sturm systems.  Equality
of their Schwarzian/projective connections is therefore a precise local target for the
missing global intertwiner.
-/

namespace GppSturmSchwarzianProjectiveBridge

open GppLegendreCrossingSturmConnection

/-- First derivative of a projective solution ratio, expressed through Wronskian and the
chosen denominator solution. -/
def ratioJet1 (W y : ℝ) : ℝ := W / y^2

/-- Second derivative jet of the same ratio. -/
def ratioJet2 (W y yp : ℝ) : ℝ := -2 * W * yp / y^3

/-- Third derivative jet of the same ratio. -/
def ratioJet3 (W y yp ypp : ℝ) : ℝ :=
  -2 * W * ypp / y^3 + 6 * W * yp^2 / y^4

/-- Algebraic Schwarzian built from three derivative jets. -/
def schwarzianFromJets (t1 t2 t3 : ℝ) : ℝ :=
  t3 / t1 - ((3 : ℝ) / 2) * (t2 / t1)^2

/-- Core cancellation: the Schwarzian of the ratio jets depends only on `y''/y`; the
Wronskian and first derivative cancel completely. -/
theorem ratioJets_schwarzian_eq
    (W y yp ypp : ℝ) (hW : W ≠ 0) (hy : y ≠ 0) :
    schwarzianFromJets
      (ratioJet1 W y)
      (ratioJet2 W y yp)
      (ratioJet3 W y yp ypp)
      = -2 * ypp / y := by
  unfold schwarzianFromJets ratioJet1 ratioJet2 ratioJet3
  field_simp [hW, hy]
  ring

/-- If the denominator solution obeys `y''+U y=0`, the projective Schwarzian is exactly
`2U`. -/
theorem ratioJets_schwarzian_eq_two_potential
    (W y yp ypp U : ℝ) (hW : W ≠ 0) (hy : y ≠ 0)
    (hODE : ypp + U*y = 0) :
    schwarzianFromJets
      (ratioJet1 W y)
      (ratioJet2 W y yp)
      (ratioJet3 W y yp ypp)
      = 2 * U := by
  rw [ratioJets_schwarzian_eq W y yp ypp hW hy]
  have hypp : ypp = -U*y := by linarith
  rw [hypp]
  field_simp [hy]
  ring

/-- Legendre specialization: any genuine denominator period satisfying the normal-form
Legendre equation has projective Schwarzian `2 U_Leg(z)` on its nonsingular domain.  Lean
formalizes the jet implication; that actual period functions satisfy the ODE is classical
external input. -/
theorem legendre_ratioJets_schwarzian
    (z W y yp ypp : ℝ) (hW : W ≠ 0) (hy : y ≠ 0)
    (hODE : ypp + legendrePotential z * y = 0) :
    schwarzianFromJets
      (ratioJet1 W y)
      (ratioJet2 W y yp)
      (ratioJet3 W y yp ypp)
      = 2 * legendrePotential z := by
  exact ratioJets_schwarzian_eq_two_potential
    W y yp ypp (legendrePotential z) hW hy hODE

end GppSturmSchwarzianProjectiveBridge
