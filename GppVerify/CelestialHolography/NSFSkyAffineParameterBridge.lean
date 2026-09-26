import Mathlib.Tactic

/-!
# NSF physical affine parameter equals the raywise projective solution ratio

In the null-surface formulation, `r` is affine for the conformal metric `h` and `s` is an
affine parameter for the physical metric `g = Omega^(-2) h`.  The 2023 NSF equations state

  dr/ds = Omega^2,

hence, wherever `Omega != 0`,

  ds/dr = Omega^(-2).

Independently, for the second-order equation

  Omega'' + q Omega = 0,

reduction of order says that a second solution can be written locally as

  OmegaHat = Omega * tau,

with

  tau' = C * Omega^(-2).

Thus after an affine/projective normalization `C=1`, the projective ratio
`tau = OmegaHat/Omega` has exactly the same derivative with respect to `r` as the physical
Einstein affine parameter `s`.  They therefore differ only by an additive constant on a
connected ray patch; a general change of solution basis enlarges this to the usual Mobius
freedom of the projective parameter.

This file formalizes only the reciprocal/rate algebra.  Differentiation, ODE existence,
connectedness, and the conclusion that equal derivatives imply equality up to a constant
are external calculus facts.
-/

namespace GppNSFSkyAffineParameterBridge

/-- Algebraic NSF relation `dr/ds = Omega^2`. -/
def NSFParameterRate (drds Omega : ℝ) : Prop :=
  drds = Omega^2

/-- Algebraic reciprocal physical-affine rate `ds/dr = Omega^{-2}`. -/
def PhysicalAffineReciprocalRate (dsdr Omega : ℝ) : Prop :=
  dsdr = 1 / Omega^2

/-- Algebraic projective/reduction-of-order rate for normalized Wronskian `C=1`. -/
def ProjectiveRatioRate (taudot Omega : ℝ) : Prop :=
  taudot = 1 / Omega^2

/-- The reciprocal of the NSF affine-rate relation is exactly the physical affine rate. -/
theorem nsf_rate_reciprocal
    (drds dsdr Omega : ℝ)
    (hOmega : Omega ≠ 0)
    (hNSF : NSFParameterRate drds Omega)
    (hrecip : dsdr * drds = 1) :
    PhysicalAffineReciprocalRate dsdr Omega := by
  unfold NSFParameterRate at hNSF
  unfold PhysicalAffineReciprocalRate
  rw [hNSF] at hrecip
  field_simp [hOmega]
  nlinarith

/-- Once the physical affine rate and the normalized projective-ratio rate are both written
with respect to the conformal affine coordinate `r`, they are identical. -/
theorem physical_affine_rate_eq_projective_ratio_rate
    (dsdr taudot Omega : ℝ)
    (hs : PhysicalAffineReciprocalRate dsdr Omega)
    (htau : ProjectiveRatioRate taudot Omega) :
    dsdr = taudot := by
  unfold PhysicalAffineReciprocalRate at hs
  unfold ProjectiveRatioRate at htau
  rw [hs, htau]

/-- Direct package from the NSF rate plus reciprocal relation to the projective rate. -/
theorem nsf_physical_rate_matches_projective_rate
    (drds dsdr taudot Omega : ℝ)
    (hOmega : Omega ≠ 0)
    (hNSF : NSFParameterRate drds Omega)
    (hrecip : dsdr * drds = 1)
    (htau : ProjectiveRatioRate taudot Omega) :
    dsdr = taudot := by
  have hs := nsf_rate_reciprocal drds dsdr Omega hOmega hNSF hrecip
  exact physical_affine_rate_eq_projective_ratio_rate dsdr taudot Omega hs htau

/-- With an arbitrary nonzero Wronskian normalization `C`, the solution-ratio rate differs
from the physical affine rate only by that constant projective scale. -/
def ProjectiveRatioRateScaled (taudot C Omega : ℝ) : Prop :=
  taudot = C / Omega^2

/-- Scaled projective rate is `C` times the normalized physical affine rate. -/
theorem scaled_projective_rate_eq_constant_times_physical
    (dsdr taudot C Omega : ℝ)
    (hs : PhysicalAffineReciprocalRate dsdr Omega)
    (htau : ProjectiveRatioRateScaled taudot C Omega) :
    taudot = C * dsdr := by
  unfold PhysicalAffineReciprocalRate at hs
  unfold ProjectiveRatioRateScaled at htau
  rw [hs, htau]
  ring

end GppNSFSkyAffineParameterBridge
