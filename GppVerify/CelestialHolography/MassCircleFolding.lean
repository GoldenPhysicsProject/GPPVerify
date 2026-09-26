import Mathlib.Tactic

/-!
# Fixed-mass transverse circle folding

Finite algebra accompanying Daniel Toupin,
"Which Way Is Forward?", v17.

For m != 0 and u^2+v^2=m^2, the explicit SO(2)-type matrix

  (1/m) [[u,v],[-v,u]]

takes (u,v) to (m,0).  This is the elementary transitivity statement behind
the paper's fixed-mass quotient: the transverse angle is gauge/orbit data while
the radius m survives.

This file proves only the coordinate algebra.  It does not formalize quotient
manifolds or Lie-group actions.
-/

namespace GppMassCircleFolding

noncomputable section

/-- First component of the explicit gauge-fixing rotation. -/
def rotX (u v m : ℝ) : ℝ :=
  (u / m) * u + (v / m) * v

/-- Second component of the explicit gauge-fixing rotation. -/
def rotY (u v m : ℝ) : ℝ :=
  -(v / m) * u + (u / m) * v

/-- The normalized coefficients have unit Euclidean norm on the mass circle. -/
theorem normalized_coefficients_unit
    (u v m : ℝ) (hm : m ≠ 0)
    (hcircle : u^2 + v^2 = m^2) :
    (u / m)^2 + (v / m)^2 = 1 := by
  field_simp [hm]
  nlinarith

/-- The explicit rotation sends a point on the mass circle to the positive-axis representative. -/
theorem mass_circle_gauge_fix_x
    (u v m : ℝ) (hm : m ≠ 0)
    (hcircle : u^2 + v^2 = m^2) :
    rotX u v m = m := by
  unfold rotX
  field_simp [hm]
  nlinarith

/-- The orthogonal component vanishes under the same gauge-fixing rotation. -/
theorem mass_circle_gauge_fix_y
    (u v m : ℝ) (hm : m ≠ 0) :
    rotY u v m = 0 := by
  unfold rotY
  field_simp [hm]
  ring

/-- Coordinate package of the fixed-mass orbit representative. -/
theorem mass_circle_gauge_fix
    (u v m : ℝ) (hm : m ≠ 0)
    (hcircle : u^2 + v^2 = m^2) :
    (rotX u v m, rotY u v m) = (m, 0) := by
  apply Prod.ext
  · exact mass_circle_gauge_fix_x u v m hm hcircle
  · exact mass_circle_gauge_fix_y u v m hm

end

end GppMassCircleFolding
