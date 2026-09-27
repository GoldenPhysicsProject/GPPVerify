import Mathlib.Tactic
import GppVerify.CelestialHolography.NSFSchwarzianEinsteinBridge
import GppVerify.CelestialHolography.SturmSchwarzianProjectiveBridge

/-!
# Local criterion for the NSF/Legendre projective-connection bridge

The null-surface Einstein scale and the Legendre four-point period system now both have an
exact finite-jet Schwarzian description:

    S_NSF = 2 P_rr,
    S_Leg = 2 U_Leg(z).

Therefore their local projective connections agree if and only if their normal-form Sturm
potentials agree (after whatever coordinate pullback is supplied by the global geometry).

This is a useful reduction of the global googly problem.  Instead of trying to identify
solution bases directly, it is enough locally to identify the projective potential.  A
change of solution basis acts by Mobius transformation on the ratio and leaves the
Schwarzian unchanged, so the criterion is basis-independent at the projective level.

Lean proves the coefficient/jet equivalence below.  The global map from a sky/NSF ray patch
to the four-point/Legendre base, and the transformation law including coordinate Schwarzian
for a non-Mobius reparametrization, remain open geometry.
-/

namespace GppNSFLegendreProjectiveCriterion

open GppNullSurfaceEinsteinBundleBridge
open GppSturmSchwarzianProjectiveBridge
open GppNSFSchwarzianEinsteinBridge
open GppLegendreCrossingSturmConnection

/-- Abstract local fact: two normal-form projective Schwarzians `2U1` and `2U2` agree iff
the underlying potentials agree. -/
theorem two_potential_schwarzians_eq_iff
    (U1 U2 : ℝ) : 2 * U1 = 2 * U2 ↔ U1 = U2 := by
  constructor <;> intro h <;> linarith

/-- Full jet specialization.  Under the NSF Einstein equation and a Legendre normal-form
ODE jet, equality of the two projective Schwarzians is equivalent to
`P_rr = U_Leg(z)`. -/
theorem nsf_legendre_schwarzian_eq_iff_potential_eq
    (z Wn Omega OmegaD OmegaDD RrrNSF RicrrStd PrrStd
       Wl y yp ypp : ℝ)
    (hWn : Wn ≠ 0) (hOmega : Omega ≠ 0)
    (hP : FourDimNullSchoutenRelation PrrStd RicrrStd)
    (hR : NSFCurvatureSignBridge RrrNSF RicrrStd)
    (hNSF : NSFEinsteinBundleEquation OmegaDD RrrNSF Omega)
    (hWl : Wl ≠ 0) (hy : y ≠ 0)
    (hLeg : ypp + legendrePotential z * y = 0) :
    schwarzianFromJets
        (ratioJet1 Wn Omega)
        (ratioJet2 Wn Omega OmegaD)
        (ratioJet3 Wn Omega OmegaD OmegaDD)
      =
    schwarzianFromJets
        (ratioJet1 Wl y)
        (ratioJet2 Wl y yp)
        (ratioJet3 Wl y yp ypp)
      ↔ PrrStd = legendrePotential z := by
  rw [nsf_scale_ratio_schwarzian_eq_two_schouten
        Wn Omega OmegaD OmegaDD RrrNSF RicrrStd PrrStd
        hWn hOmega hP hR hNSF]
  rw [legendre_ratioJets_schwarzian z Wl y yp ypp hWl hy hLeg]
  exact two_potential_schwarzians_eq_iff PrrStd (legendrePotential z)

end GppNSFLegendreProjectiveCriterion
