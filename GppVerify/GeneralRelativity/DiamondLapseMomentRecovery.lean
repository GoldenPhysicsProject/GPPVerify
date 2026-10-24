import Mathlib.Tactic

/-!
# Recovering local scalar curvature constraints from diamond moment data

In n=3, the normalized CKV lapse N_l=(l²-r²)/(2l)
averages a radial polynomial source F(r)=a+b*r² on B_l as
  <F>_{N_l} = a + (3/7)b*l².

Indeed (integral_B N_l) = l*V/5 and
(int_B N_l*r²)/(int_B N_l) = 3*l²/7.

Two distinct radii therefore determine the constant and quadratic
Taylor coefficients of F. This is a finite polynomial instance of
local constraint recovery from the vanishing smeared Hamiltonian
residual, NOT a proof of inversion for arbitrary continuous fields
or of the Einstein equations in full tensor form.

The physical source F should be delta(R_hat)-16pi G delta(rho),
not a zeta/RH spectral surrogate.
-/

namespace GppDiamondLapseMomentRecovery

/-- The unit CKV-lapse-weighted normalized average of a quadratic
radial constraint residual in three spatial dimensions. -/
noncomputable def weightedRadialAverage
    (a b R : ℝ) : ℝ := a + (3 / 7 : ℝ) * b * R^2

/-- Under the Euclidean moment identities,
(int N)/(Vol) = R/5 and (int N*r²)/(Vol)=3R³/35. -/
noncomputable def lapseMass (R V : ℝ) : ℝ := R*V/5

noncomputable def quadraticMoment (R V : ℝ) : ℝ :=
  3*R^3*V/35

/-- Exact reconstruction of normalized quadratic moment from the
geometry of the 3-ball. -/
theorem quadratic_lapse_moment_ratio
    (R V : ℝ) (hR : R ≠ 0) (hV : V ≠ 0) :
    quadraticMoment R V / lapseMass R V =
      3*R^2/7 := by
  unfold quadraticMoment lapseMass
  field_simp
  ring

/-- A vanishing normalized lapse integral at two radii with
different squared radii eliminates both low-order coefficients. -/
theorem two_radii_determine_quadratic_constraint
    (a b R₁ R₂ : ℝ)
    (h₁ : weightedRadialAverage a b R₁ = 0)
    (h₂ : weightedRadialAverage a b R₂ = 0)
    (hDistinct : R₁^2 ≠ R₂^2) :
    a = 0 ∧ b = 0 := by
  have hDiff : b * (R₁^2 - R₂^2) = 0 := by
    unfold weightedRadialAverage at h₁ h₂
    nlinarith
  have hb : b = 0 :=
    (mul_eq_zero.mp hDiff).resolve_right (sub_ne_zero.mpr hDistinct)
  constructor
  · rw [hb] at h₁
    simpa [weightedRadialAverage] using h₁
  · exact hb

/-- A single radius is insufficient: a nonzero constant and
quadratic coefficient can cancel in the same weighted integral. -/
theorem one_radius_not_enough :
    ∃ a b : ℝ,
      a ≠ 0 ∧ b ≠ 0 ∧ weightedRadialAverage a b 1 = 0 := by
  refine ⟨-(3/7), 1, by norm_num, by norm_num, ?_⟩
  norm_num [weightedRadialAverage]

/-- Vanishing smeared residual at arbitrarily small radii kills
the constant Taylor coefficient, even without knowing the
quadratic coefficient. -/
theorem small_radius_constant_coefficient
    (a b : ℝ)
    (hAll : ∀ R : ℝ, 0 < R → weightedRadialAverage a b R = 0) :
    a = 0 := by
  have h₁ := hAll 1 (by norm_num)
  have h₂ := hAll 2 (by norm_num)
  exact (two_radii_determine_quadratic_constraint
    a b 1 2 h₁ h₂ (by norm_num)).1

end GppDiamondLapseMomentRecovery

#print axioms GppDiamondLapseMomentRecovery.quadratic_lapse_moment_ratio
#print axioms GppDiamondLapseMomentRecovery.two_radii_determine_quadratic_constraint
#print axioms GppDiamondLapseMomentRecovery.one_radius_not_enough
