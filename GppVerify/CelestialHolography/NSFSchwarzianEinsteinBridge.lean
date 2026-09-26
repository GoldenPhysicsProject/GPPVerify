import Mathlib.Tactic
import GppVerify.CelestialHolography.NullSurfaceEinsteinBundleBridge
import GppVerify.CelestialHolography.SturmSchwarzianProjectiveBridge

/-!
# NSF Einstein scale determines the null-ray projective Schwarzian

`NullSurfaceEinsteinBundleBridge` proves, at the coefficient level, that the NSF vacuum
scale equation is the null almost-Einstein equation

    Omega'' + P_rr Omega = 0

once the explicit curvature-sign convention is imposed.

`SturmSchwarzianProjectiveBridge` proves that for any normal-form equation

    y'' + U y = 0,

the projective ratio of two independent solutions has Schwarzian `2U`.

Combining them gives the exact local projective-curvature statement needed by the googly
program:

    {tau,r} = 2 P_rr.

Here `tau` is represented by its Wronskian-derived derivative jets.  The remaining analytic
step is to identify these jets with derivatives of the actual NSF projective/physical affine
parameter globally along each ray and then glue the ray data over the sky bundle.
-/

namespace GppNSFSchwarzianEinsteinBridge

open GppNullSurfaceEinsteinBundleBridge
open GppSturmSchwarzianProjectiveBridge

/-- Main local bridge: an NSF Einstein-scale jet has projective Schwarzian `2 P_rr`. -/
theorem nsf_scale_ratio_schwarzian_eq_two_schouten
    (W Omega OmegaD OmegaDD RrrNSF RicrrStd PrrStd : ℝ)
    (hW : W ≠ 0) (hOmega : Omega ≠ 0)
    (hP : FourDimNullSchoutenRelation PrrStd RicrrStd)
    (hR : NSFCurvatureSignBridge RrrNSF RicrrStd)
    (hNSF : NSFEinsteinBundleEquation OmegaDD RrrNSF Omega) :
    schwarzianFromJets
      (ratioJet1 W Omega)
      (ratioJet2 W Omega OmegaD)
      (ratioJet3 W Omega OmegaD OmegaDD)
      = 2 * PrrStd := by
  have hAE : NullAlmostEinsteinEquation OmegaDD PrrStd Omega :=
    (nsf_equation_iff_null_almostEinstein
      OmegaDD RrrNSF RicrrStd PrrStd Omega hP hR).mp hNSF
  exact ratioJets_schwarzian_eq_two_potential
    W Omega OmegaD OmegaDD PrrStd hW hOmega hAE

/-- Equivalent NSF-curvature form: because `P_rr = -Rrr_NSF/2`, the same Schwarzian is
`-Rrr_NSF`. -/
theorem nsf_scale_ratio_schwarzian_eq_neg_nsfRicci
    (W Omega OmegaD OmegaDD RrrNSF RicrrStd PrrStd : ℝ)
    (hW : W ≠ 0) (hOmega : Omega ≠ 0)
    (hP : FourDimNullSchoutenRelation PrrStd RicrrStd)
    (hR : NSFCurvatureSignBridge RrrNSF RicrrStd)
    (hNSF : NSFEinsteinBundleEquation OmegaDD RrrNSF Omega) :
    schwarzianFromJets
      (ratioJet1 W Omega)
      (ratioJet2 W Omega OmegaD)
      (ratioJet3 W Omega OmegaD OmegaDD)
      = - RrrNSF := by
  rw [nsf_scale_ratio_schwarzian_eq_two_schouten
    W Omega OmegaD OmegaDD RrrNSF RicrrStd PrrStd hW hOmega hP hR hNSF]
  have hU := projective_potential_identification RrrNSF RicrrStd PrrStd hP hR
  linarith

end GppNSFSchwarzianEinsteinBridge
