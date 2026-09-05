import Mathlib.Tactic
import GppVerify.CelestialHolography.EinsteinNullRaySL2Geometry
import GppVerify.CelestialHolography.SkyProjectiveEinsteinCriterion

/-!
# Null-surface Einstein-bundle equation versus the null-ray almost-Einstein equation

In the four-dimensional null-surface formulation (NSF), the reconstructed contravariant
physical metric is written

  g^ab = Omega^2 h^ab,

so covariantly `g_ab = Omega^(-2) h_ab`.  The scalar `Omega` is therefore precisely a
conformal scale relative to the conformal representative `h`.

The NSF coordinate

  r = eth ethbar Z

is affine along the null geodesics of `h`, and the trace-free vacuum Einstein equation
reduces to the linear second-order equation

  2 Omega'' = Rrr_NSF[h] Omega.

In standard four-dimensional conformal geometry, the almost-Einstein scale equation
contracted twice with an `h`-affine null tangent is

  Omega'' + Prr_std[h] Omega = 0,

and because the metric term drops out on a null vector,

  Prr_std = (1/2) Ricrr_std.

Hence the two equations are identical when the NSF curvature convention is related to
the standard convention by

  Rrr_NSF = - Ricrr_std.

The sign is kept explicit here because the cited NSF literature and the GPP conformal-
geometry convention need not use the same Riemann-tensor sign.

This module formalizes only this scalar coefficient identity.  The deeper NSF facts are
external geometry: `Z` determines the conformal structure, its metricity equations glue
the ray/angular data into one spacetime metric, and together those equations plus the
second-order scale equation are equivalent to the vacuum Einstein equations.
-/

namespace GppNullSurfaceEinsteinBundleBridge

/-- Algebraic NSF Einstein-bundle equation along an `h`-affine null coordinate. -/
def NSFEinsteinBundleEquation (OmegaDD RrrNSF Omega : ℝ) : Prop :=
  2 * OmegaDD = RrrNSF * Omega

/-- Standard null contraction of the almost-Einstein scale equation. -/
def NullAlmostEinsteinEquation (OmegaDD PrrStd Omega : ℝ) : Prop :=
  OmegaDD + PrrStd * Omega = 0

/-- In four dimensions the null Schouten contraction is half the null Ricci contraction. -/
def FourDimNullSchoutenRelation (PrrStd RicrrStd : ℝ) : Prop :=
  PrrStd = RicrrStd / 2

/-- Explicit curvature-convention bridge between the NSF and standard Ricci signs. -/
def NSFCurvatureSignBridge (RrrNSF RicrrStd : ℝ) : Prop :=
  RrrNSF = - RicrrStd

/-- Main coefficient theorem: with `Prr = Ricrr/2` and opposite NSF/standard curvature
sign, the NSF second-order scale equation is exactly the null almost-Einstein equation. -/
theorem nsf_equation_iff_null_almostEinstein
    (OmegaDD RrrNSF RicrrStd PrrStd Omega : ℝ)
    (hP : FourDimNullSchoutenRelation PrrStd RicrrStd)
    (hR : NSFCurvatureSignBridge RrrNSF RicrrStd) :
    NSFEinsteinBundleEquation OmegaDD RrrNSF Omega ↔
      NullAlmostEinsteinEquation OmegaDD PrrStd Omega := by
  unfold FourDimNullSchoutenRelation at hP
  unfold NSFCurvatureSignBridge at hR
  unfold NSFEinsteinBundleEquation NullAlmostEinsteinEquation
  rw [hP, hR]
  constructor <;> intro h
  · linarith
  · linarith

/-- Solved form of the NSF equation. -/
theorem nsf_equation_solved
    (OmegaDD RrrNSF Omega : ℝ) :
    NSFEinsteinBundleEquation OmegaDD RrrNSF Omega ↔
      OmegaDD = (RrrNSF / 2) * Omega := by
  unfold NSFEinsteinBundleEquation
  constructor <;> intro h
  · linarith
  · linarith

/-- Solved form of the standard null almost-Einstein equation. -/
theorem null_almostEinstein_solved
    (OmegaDD PrrStd Omega : ℝ) :
    NullAlmostEinsteinEquation OmegaDD PrrStd Omega ↔
      OmegaDD = - PrrStd * Omega := by
  unfold NullAlmostEinsteinEquation
  constructor <;> intro h <;> linarith

/-- Under the four-dimensional Schouten and sign conventions, both solved forms have the
same right-hand side. -/
theorem nsf_and_standard_potentials_match
    (RrrNSF RicrrStd PrrStd : ℝ)
    (hP : FourDimNullSchoutenRelation PrrStd RicrrStd)
    (hR : NSFCurvatureSignBridge RrrNSF RicrrStd) :
    RrrNSF / 2 = - PrrStd := by
  unfold FourDimNullSchoutenRelation at hP
  unfold NSFCurvatureSignBridge at hR
  rw [hP, hR]
  ring

/-- Convention-safe formulation: the NSF potential `-Rrr_NSF/2` is exactly the standard
Schouten potential when the curvature signs are opposite. -/
theorem projective_potential_identification
    (RrrNSF RicrrStd PrrStd : ℝ)
    (hP : FourDimNullSchoutenRelation PrrStd RicrrStd)
    (hR : NSFCurvatureSignBridge RrrNSF RicrrStd) :
    - RrrNSF / 2 = PrrStd := by
  have h := nsf_and_standard_potentials_match RrrNSF RicrrStd PrrStd hP hR
  linarith

end GppNullSurfaceEinsteinBundleBridge
