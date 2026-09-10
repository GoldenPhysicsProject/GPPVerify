import Mathlib.Tactic

/-!
# A scale compensator converts conformal geometry into a Weyl-invariant physical metric

If the primordial geometry is only conformal, a representative metric transforms as

    g -> Omega^2 g,

while a weight-minus-one scale field transforms as

    phi -> phi/Omega.

The combination

    g_phys = phi^2 g

is exactly Weyl invariant.  Likewise the physical tetrad/clock one-form is schematically
`phi e`, since `e -> Omega e`.

This provides a precise reconciliation of two facts established elsewhere in the project:

* ordinary masslessness does NOT imply a degenerate conformal/Lorentz metric;
* nevertheless a zero scale field can make the *dimensionful Weyl-invariant metric* vanish.

Thus the pre-mass boundary can carry null/conformal/incidence structure while having no
nonzero physical proper-time ruler.  Once `phi != 0`, fixing its Weyl gauge produces an
ordinary dimensionful metric and, through Yukawa coupling, Compton clocks.

Only scalar component/weight algebra is formalized here; tensorial Lorentzian signature,
Einstein equations and cosmological dynamics are separate.
-/

namespace GppWeylInvariantPhysicalMetric

/-- Constant-Weyl transformation of a representative metric component. -/
def rescaledMetricComponent (Omega g : ℝ) : ℝ := Omega^2 * g

/-- Weight-minus-one compensator. -/
def rescaledScaleField (Omega phi : ℝ) : ℝ := phi / Omega

/-- Weyl-invariant dimensionful metric component. -/
def physicalMetricComponent (phi g : ℝ) : ℝ := phi^2 * g

/-- The scale-dressed metric is exactly Weyl invariant. -/
theorem physical_metric_Weyl_invariant
    (Omega phi g : ℝ) (hO : Omega ≠ 0) :
    physicalMetricComponent (rescaledScaleField Omega phi)
      (rescaledMetricComponent Omega g) =
    physicalMetricComponent phi g := by
  simp [physicalMetricComponent, rescaledScaleField, rescaledMetricComponent]
  field_simp [hO]
  ring

/-- At the scale-symmetric point the physical metric component vanishes for every conformal
    representative. -/
theorem zero_scale_field_zero_physical_metric (g : ℝ) :
    physicalMetricComponent 0 g = 0 := by
  simp [physicalMetricComponent]

/-- Reversing the sign of the scale field leaves the physical metric unchanged. -/
theorem scale_branch_sign_metric_blind (phi g : ℝ) :
    physicalMetricComponent (-phi) g = physicalMetricComponent phi g := by
  simp [physicalMetricComponent]

/-- A nonzero scale field and nonzero conformal metric component give a nonzero physical
    metric component. -/
theorem nonzero_scale_turns_on_physical_metric
    (phi g : ℝ) (hphi : phi ≠ 0) (hg : g ≠ 0) :
    physicalMetricComponent phi g ≠ 0 := by
  exact mul_ne_zero (pow_ne_zero 2 hphi) hg

/-- A Weyl-weight-one tetrad component and a weight-minus-one scale field combine to a
    Weyl-invariant physical tetrad component. -/
def physicalTetradComponent (phi e : ℝ) : ℝ := phi*e

def rescaledTetradComponent (Omega e : ℝ) : ℝ := Omega*e

/-- Exact scale cancellation in the physical tetrad. -/
theorem physical_tetrad_Weyl_invariant
    (Omega phi e : ℝ) (hO : Omega ≠ 0) :
    physicalTetradComponent (rescaledScaleField Omega phi)
      (rescaledTetradComponent Omega e) =
    physicalTetradComponent phi e := by
  simp [physicalTetradComponent, rescaledScaleField, rescaledTetradComponent]
  field_simp [hO]
  ring

/-- The same scale-field sign is invisible to the metric but visible to the oriented physical
    tetrad. -/
theorem sign_flip_even_metric_odd_tetrad (phi g e : ℝ) :
    physicalMetricComponent (-phi) g = physicalMetricComponent phi g ∧
    physicalTetradComponent (-phi) e = -physicalTetradComponent phi e := by
  constructor
  · exact scale_branch_sign_metric_blind phi g
  · simp [physicalTetradComponent]

end GppWeylInvariantPhysicalMetric
