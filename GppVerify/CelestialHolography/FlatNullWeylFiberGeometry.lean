import Mathlib.Tactic
import GppVerify.CelestialHolography.FlatInfinityCelestialFactorization

/-!
# Flat-null Weyl and unipotent fibre geometry

At flat infinity each chiral Clifford kernel is two-dimensional.  Projectivizing either
kernel gives one `RP^1` factor of the split celestial torus.  In an affine chart a
nonzero spinor is represented by `(1,u)`.

The lower unipotent subgroup acts transitively on this affine chart,

  n(a) : (1,u) |-> (1,u+a),

while the rank-one Weyl element

  w(x,y)=(-y,x)

satisfies `w^2=-id` on spinors and is therefore an involution projectively.  On the
affine coordinate it acts by the usual inversion

  u |-> -1/u.

Standard Knapp--Stein theory constructs the principal-series Weyl intertwiner by
integrating the Weyl action over the appropriate unipotent orbit.  Brown--Gowdy--Spence's
normalized celestial light transform is an integral over precisely this `RP^1` chiral
factor.  Those analytic integral statements are external; this file proves the exact
finite-dimensional projective/unipotent geometry on which they act.
-/

namespace GppFlatNullWeylFiberGeometry

open GppFlatInfinityCelestialFactorization

/-- Rank-one Weyl action on a real two-spinor. -/
def weylSpinor (x : Spinor2) : Spinor2 := (-x.2,x.1)

/-- Lower-unipotent translation action in the affine chart. -/
def unipotentSpinor (a : ℝ) (x : Spinor2) : Spinor2 :=
  (x.1, x.2 + a*x.1)

/-- Standard affine representative of a projective spinor. -/
def affineSpinor (u : ℝ) : Spinor2 := (1,u)

/-- Scalar multiplication on two-spinors. -/
def scaleSpinor (a : ℝ) (x : Spinor2) : Spinor2 := (a*x.1,a*x.2)

/-- The unipotent orbit of the base point `(1,0)` is the whole affine chart. -/
theorem unipotent_orbit_base (u : ℝ) :
    unipotentSpinor u (1,0) = affineSpinor u := by
  simp [unipotentSpinor, affineSpinor]

/-- Unipotent parameters add, as expected for the additive group of the affine line. -/
theorem unipotent_add (a b : ℝ) (x : Spinor2) :
    unipotentSpinor a (unipotentSpinor b x) = unipotentSpinor (a+b) x := by
  rcases x with ⟨x0,x1⟩
  simp [unipotentSpinor]
  ring

/-- The Weyl element squares to the central sign `-1`. -/
theorem weylSpinor_sq (x : Spinor2) :
    weylSpinor (weylSpinor x) = scaleSpinor (-1) x := by
  rcases x with ⟨x0,x1⟩
  rfl

/-- Hence the Weyl action is order two after projectivization, where nonzero scalar
multiples represent the same point. -/
theorem weylSpinor_fourth_power (x : Spinor2) :
    weylSpinor (weylSpinor (weylSpinor (weylSpinor x))) = x := by
  rcases x with ⟨x0,x1⟩
  rfl

/-- Weyl exchanges the two coordinate chart base directions. -/
theorem weyl_exchanges_chart_poles :
    weylSpinor (1,0) = (0,1) ∧ weylSpinor (0,1) = (-1,0) := by
  exact ⟨rfl,rfl⟩

/-- On a nonzero affine coordinate the Weyl-transformed spinor is projectively the
affine representative with coordinate `-1/u`. -/
theorem weyl_affine_is_projective_inversion
    (u : ℝ) (hu : u ≠ 0) :
    scaleSpinor (-1/u) (weylSpinor (affineSpinor u)) = affineSpinor (-1/u) := by
  apply Prod.ext
  · simp [scaleSpinor, weylSpinor, affineSpinor]
    field_simp [hu]
  · simp [scaleSpinor, weylSpinor, affineSpinor]

/-- Every ordinary flat-infinity kernel point in the affine spinor chart is obtained by
embedding this unipotent orbit. -/
theorem ordinary_kernel_affine_orbit (u : ℝ) :
    ordinaryKernelSpinor (unipotentSpinor u (1,0)) =
      ordinaryKernelSpinor (affineSpinor u) := by
  rw [unipotent_orbit_base]

/-- Likewise for the dual chiral kernel. -/
theorem dual_kernel_affine_orbit (u : ℝ) :
    dualKernelSpinor (unipotentSpinor u (1,0)) =
      dualKernelSpinor (affineSpinor u) := by
  rw [unipotent_orbit_base]

/-- The affine ordinary-kernel orbit remains in the exact flat Clifford kernel. -/
theorem ordinary_affine_orbit_in_flat_kernel (u : ℝ) :
    GppKleinSpinorIncidence.cPlus
      GppKleinNullInfinityBoundary.infinityPoint
      (ordinaryKernelSpinor (affineSpinor u)) = (0,0,0,0) := by
  exact ordinaryKernelSpinor_mem_kernel (affineSpinor u)

/-- The affine dual-kernel orbit remains in the opposite exact flat Clifford kernel. -/
theorem dual_affine_orbit_in_flat_kernel (u : ℝ) :
    GppKleinSpinorIncidence.cMinus
      GppKleinNullInfinityBoundary.infinityPoint
      (dualKernelSpinor (affineSpinor u)) = (0,0,0,0) := by
  exact dualKernelSpinor_mem_kernel (affineSpinor u)

end GppFlatNullWeylFiberGeometry
