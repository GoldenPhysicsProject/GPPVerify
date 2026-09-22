import Mathlib.Tactic
import GppVerify.CelestialHolography.NSFSchwarzianEinsteinBridge
import GppVerify.CelestialHolography.SturmSchwarzianProjectiveBridge
import GppVerify.CelestialHolography.SchwarzianChainRuleJets

/-!
# Curved-coordinate criterion for the NSF/Legendre projective bridge

The earlier local criterion compared the NSF null-ray projective connection directly with
the Legendre one in the same coordinate.  A genuine curved/global identification need not
use the same coordinate.  If the four-point coordinate is `z=f(r)`, the Schwarzian chain
rule gives the correct pullback:

    P_rr(r) = f'(r)^2 U_Leg(f(r)) + 1/2 {f,r}.

This file proves the exact finite-jet equivalence behind that statement.

It is deliberately a *criterion*, not a construction of `f`.  The remaining geometric
problem is to derive a canonical map from the sky/NSF ray data to the appropriate
four-point/crossing moduli (if such a map exists at all), and then prove that its derivative
jets satisfy the displayed equation.  Failure to construct such a map is a genuine
obstruction to the Legendre/Gauss--Manin route and must not be hidden by choosing `f` by
hand.
-/

namespace GppNSFLegendreCoordinatePullbackCriterion

open GppNullSurfaceEinsteinBundleBridge
open GppSturmSchwarzianProjectiveBridge
open GppNSFSchwarzianEinsteinBridge
open GppSchwarzianChainRuleJets
open GppLegendreCrossingSturmConnection

/-- Main curved-coordinate projective criterion.  The `f` jets stand for a proposed local
coordinate map `z=f(r)`.  The `g` jets are the Legendre projective-ratio jets in the `z`
coordinate. -/
theorem nsf_eq_pulledBack_legendre_iff
    (z
      Wn Omega OmegaD OmegaDD RrrNSF RicrrStd PrrStd
      Wl y yp ypp
      f1 f2 f3 : ℝ)
    (hWn : Wn ≠ 0) (hOmega : Omega ≠ 0)
    (hP : FourDimNullSchoutenRelation PrrStd RicrrStd)
    (hR : NSFCurvatureSignBridge RrrNSF RicrrStd)
    (hNSF : NSFEinsteinBundleEquation OmegaDD RrrNSF Omega)
    (hWl : Wl ≠ 0) (hy : y ≠ 0)
    (hLeg : ypp + legendrePotential z * y = 0)
    (hf1 : f1 ≠ 0) :
    schwarzianFromJets
        (ratioJet1 Wn Omega)
        (ratioJet2 Wn Omega OmegaD)
        (ratioJet3 Wn Omega OmegaD OmegaDD)
      =
    schwarzianFromJets
        (composeJet1 f1 (ratioJet1 Wl y))
        (composeJet2 f1 f2 (ratioJet1 Wl y) (ratioJet2 Wl y yp))
        (composeJet3 f1 f2 f3
          (ratioJet1 Wl y) (ratioJet2 Wl y yp) (ratioJet3 Wl y yp ypp))
      ↔
    PrrStd =
      f1^2 * legendrePotential z
        + (1/2 : ℝ) * schwarzianFromJets f1 f2 f3 := by
  have hg1 : ratioJet1 Wl y ≠ 0 := by
    unfold ratioJet1
    exact div_ne_zero hWl (pow_ne_zero 2 hy)
  have hLegS :
      schwarzianFromJets
          (ratioJet1 Wl y)
          (ratioJet2 Wl y yp)
          (ratioJet3 Wl y yp ypp)
        = 2 * legendrePotential z :=
    legendre_ratioJets_schwarzian z Wl y yp ypp hWl hy hLeg
  rw [nsf_scale_ratio_schwarzian_eq_two_schouten
        Wn Omega OmegaD OmegaDD RrrNSF RicrrStd PrrStd
        hWn hOmega hP hR hNSF]
  rw [pulledBack_potential_from_chain_rule
        f1 f2 f3
        (ratioJet1 Wl y) (ratioJet2 Wl y yp) (ratioJet3 Wl y yp ypp)
        (legendrePotential z) hf1 hg1 hLegS]
  constructor <;> intro h <;> linarith

/-- Möbius specialization.  If the proposed coordinate map has zero Schwarzian, only the
weight-two factor remains. -/
theorem nsf_eq_mobiusPulledBack_legendre_iff
    (z
      Wn Omega OmegaD OmegaDD RrrNSF RicrrStd PrrStd
      Wl y yp ypp
      f1 f2 f3 : ℝ)
    (hWn : Wn ≠ 0) (hOmega : Omega ≠ 0)
    (hP : FourDimNullSchoutenRelation PrrStd RicrrStd)
    (hR : NSFCurvatureSignBridge RrrNSF RicrrStd)
    (hNSF : NSFEinsteinBundleEquation OmegaDD RrrNSF Omega)
    (hWl : Wl ≠ 0) (hy : y ≠ 0)
    (hLeg : ypp + legendrePotential z * y = 0)
    (hf1 : f1 ≠ 0)
    (hMobius : schwarzianFromJets f1 f2 f3 = 0) :
    schwarzianFromJets
        (ratioJet1 Wn Omega)
        (ratioJet2 Wn Omega OmegaD)
        (ratioJet3 Wn Omega OmegaD OmegaDD)
      =
    schwarzianFromJets
        (composeJet1 f1 (ratioJet1 Wl y))
        (composeJet2 f1 f2 (ratioJet1 Wl y) (ratioJet2 Wl y yp))
        (composeJet3 f1 f2 f3
          (ratioJet1 Wl y) (ratioJet2 Wl y yp) (ratioJet3 Wl y yp ypp))
      ↔
    PrrStd = f1^2 * legendrePotential z := by
  rw [nsf_eq_pulledBack_legendre_iff
        z Wn Omega OmegaD OmegaDD RrrNSF RicrrStd PrrStd
        Wl y yp ypp f1 f2 f3
        hWn hOmega hP hR hNSF hWl hy hLeg hf1,
      hMobius]
  ring_nf

end GppNSFLegendreCoordinatePullbackCriterion
