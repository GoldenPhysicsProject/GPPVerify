import GppVerify.CelestialHolography.ArithmeticSplitSignature
import Mathlib

/-!
# Arithmetic principal-series selection criterion

The centered Mellin mode attached to a spectral parameter `s` evolves in logarithmic
scale as

  exp(t * (s - 1/2)).

If such a mode is an actual nonzero state of a norm-preserving arithmetic evolution,
its norm cannot grow or decay.  Already at unit logarithmic time this forces

  exp(Re(s)-1/2) = 1,

hence `Re(s)=1/2` by injectivity of the real exponential.  This is the exact
Hilbert--Polya/OS branch-selection mechanism needed once the arithmetic construction
identifies zeta zeros with genuine spectral modes of the reconstructed scale flow.

Separately, the split-signature formulation shows that any nonreal split-null spectral
point lies on the same principal branch.  Neither theorem identifies zeta zeros with
such modes or proves their split-nullity; those are the remaining arithmetic inputs.
-/

namespace GppArithmeticPrincipalSeriesSelection

open GppArithmeticSplitSignature

/-- Real growth exponent of the centered arithmetic Mellin mode. -/
def centeredGrowthExponent (s : ℂ) : ℝ := s.re - (1 : ℝ) / 2

/-- Norm-growth factor at logarithmic time `t`. -/
noncomputable def centeredNormGrowth (s : ℂ) (t : ℝ) : ℝ :=
  Real.exp (t * centeredGrowthExponent s)

/-- Unit norm at one nonzero time already forces the principal-series line. -/
theorem principal_of_unit_growth_one {s : ℂ}
    (hunit : centeredNormGrowth s 1 = 1) :
    s.re = (1 : ℝ) / 2 := by
  unfold centeredNormGrowth centeredGrowthExponent at hunit
  have hzero : s.re - (1 : ℝ) / 2 = 0 := by
    have h := (Real.exp_eq_exp).mp
      (show Real.exp (s.re - (1 : ℝ) / 2) = Real.exp 0 by simpa using hunit)
    exact h
  linarith

/-- More generally, norm preservation at any nonzero logarithmic time forces the
principal-series line. -/
theorem principal_of_unit_growth {s : ℂ} {t : ℝ} (ht : t ≠ 0)
    (hunit : centeredNormGrowth s t = 1) :
    s.re = (1 : ℝ) / 2 := by
  unfold centeredNormGrowth centeredGrowthExponent at hunit
  have hzero : t * (s.re - (1 : ℝ) / 2) = 0 := by
    have h := (Real.exp_eq_exp).mp
      (show Real.exp (t * (s.re - (1 : ℝ) / 2)) = Real.exp 0 by simpa using hunit)
    exact h
  rcases mul_eq_zero.mp hzero with ht0 | hs0
  · exact False.elim (ht ht0)
  · linarith

/-- Split-signature branch selection: a nonreal arithmetic null point cannot lie on
the real-axis null branch, so it lies on the critical/principal branch. -/
theorem principal_of_nonreal_splitNull {s : ℂ}
    (hnull : splitFormA s = 0) (him : s.im ≠ 0) :
    s.re = (1 : ℝ) / 2 := by
  rw [splitFormA_eq_zero_iff] at hnull
  exact hnull.resolve_right him

/-- Equivalent centered-coordinate statement. -/
theorem sigmaA_eq_zero_of_nonreal_splitNull {s : ℂ}
    (hnull : splitFormA s = 0) (him : s.im ≠ 0) :
    sigmaA s = 0 := by
  unfold sigmaA
  rw [principal_of_nonreal_splitNull hnull him]
  ring

end GppArithmeticPrincipalSeriesSelection

#print axioms GppArithmeticPrincipalSeriesSelection.principal_of_unit_growth_one
#print axioms GppArithmeticPrincipalSeriesSelection.principal_of_unit_growth
#print axioms GppArithmeticPrincipalSeriesSelection.principal_of_nonreal_splitNull
