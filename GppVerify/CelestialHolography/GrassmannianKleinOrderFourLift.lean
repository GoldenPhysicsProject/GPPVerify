import Mathlib.Tactic
import GppVerify.CelestialHolography.GrassmannianGooglyDecomposition

/-!
# Global Klein-quadric order-four lift of Grassmannian epsilon-duality

The big-cell map

  tau(A) = A epsilon / det(A)

looks rational because a graph plane `[I|A]` is renormalized after applying it.  In
Plucker coordinates the same operation is induced projectively by a linear map on the
six-dimensional Klein carrier:

  T(p01,p02,p03,p12,p13,p23)
    = (p23,-p03,p02,-p13,p12,p01).

This file proves, by coordinate algebra only, that:

* `T` preserves the Klein quadratic form;
* `T^2` is the central conformal inversion on the four middle Plucker coordinates;
* `T^4 = id`;
* on the invertible big cell, `chartPlucker (tau A)` is exactly the projective
  normalization `(det A)^(-1) • T(chartPlucker A)`.

Thus the denominator in the chart formula is a projective normalization rather than a
singularity of the induced Klein-quadric transformation.  This module does NOT identify
`T^2` with four-orientation reversal.  In four spacetime dimensions total inversion has
positive determinant; chirality exchange and orientation reversal require additional
Pin/Hodge data handled in the neighboring modules.
-/

namespace GppGrassmannianKleinOrderFourLift

open GppGrassmannianGooglyDecomposition

/-- The global linear Klein representative of the big-cell epsilon-duality. -/
def kleinQuarterLift (p : P6) : P6 :=
  ⟨p.p23, -p.p03, p.p02, -p.p13, p.p12, p.p01⟩

/-- The square of the quarter lift: signs on the four middle Plucker coordinates. -/
def kleinCentralInversion (p : P6) : P6 :=
  ⟨p.p01, -p.p02, -p.p03, -p.p12, -p.p13, p.p23⟩

/-- Componentwise scaling on the Klein carrier. -/
def scaleP6Global (r : ℝ) (p : P6) : P6 :=
  ⟨r*p.p01, r*p.p02, r*p.p03, r*p.p12, r*p.p13, r*p.p23⟩

/-- Two applications give the central conformal inversion. -/
theorem kleinQuarterLift_sq (p : P6) :
    kleinQuarterLift (kleinQuarterLift p) = kleinCentralInversion p := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  rfl

/-- Four applications close exactly on the six-dimensional Klein carrier. -/
theorem kleinQuarterLift_four (p : P6) :
    kleinQuarterLift (kleinQuarterLift (kleinQuarterLift (kleinQuarterLift p))) = p := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  simp [kleinQuarterLift]

/-- The Klein quadratic form is invariant under the global order-four map. -/
theorem kleinQ_kleinQuarterLift (p : P6) :
    kleinQ (kleinQuarterLift p) = kleinQ p := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  simp [kleinQ, kleinQuarterLift]
  ring

/-- The central inversion also preserves the Klein quadratic form. -/
theorem kleinQ_kleinCentralInversion (p : P6) :
    kleinQ (kleinCentralInversion p) = kleinQ p := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  simp [kleinQ, kleinCentralInversion]

/-- The rational big-cell map is exactly the affine/projective chart of the global
linear Klein transformation. -/
theorem chartPlucker_tau_is_projective_kleinQuarterLift
    (A : M2) (hD : det2 A ≠ 0) :
    chartPlucker (tau A) =
      scaleP6Global (1 / det2 A) (kleinQuarterLift (chartPlucker A)) := by
  rcases A with ⟨a,b,c,d⟩
  simp only [det2] at hD
  simp only [tau, det2, chartPlucker, scaleP6Global, kleinQuarterLift]
  apply P6.ext
  · field_simp [hD]
  · field_simp [hD]
  · field_simp [hD]
  · field_simp [hD]
  · field_simp [hD]
  · field_simp [hD]
    ring

/-- On graph-plane Plucker coordinates, the square of the global lift is precisely the
chart image of `A -> -A`. -/
theorem kleinQuarterLift_sq_chart (A : M2) :
    kleinQuarterLift (kleinQuarterLift (chartPlucker A)) =
      chartPlucker (-A.1, -A.2.1, -A.2.2.1, -A.2.2.2) := by
  rcases A with ⟨a,b,c,d⟩
  apply P6.ext <;> simp [kleinQuarterLift, chartPlucker, det2] <;> ring

/-- The induced projective action has order dividing two after two quarter-lifts because
`T^2` is an ordinary central conformal inversion, while the linear lift itself has
four-step closure. -/
theorem order_four_package (p : P6) :
    kleinQuarterLift (kleinQuarterLift p) = kleinCentralInversion p ∧
    kleinQuarterLift (kleinQuarterLift (kleinQuarterLift (kleinQuarterLift p))) = p ∧
    kleinQ (kleinQuarterLift p) = kleinQ p := by
  exact ⟨kleinQuarterLift_sq p, kleinQuarterLift_four p, kleinQ_kleinQuarterLift p⟩

end GppGrassmannianKleinOrderFourLift
