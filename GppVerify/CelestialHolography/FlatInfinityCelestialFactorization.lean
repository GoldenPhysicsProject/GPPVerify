import Mathlib.Tactic
import GppVerify.CelestialHolography.FlatInfinityChiralComplex
import GppVerify.CelestialHolography.GrassmannianGooglyDecomposition

/-!
# Celestial spinor factorization from the flat-infinity chiral complex

At the standard flat infinity point, the two chiral Clifford kernels are two-dimensional:

  ker cPlus(I)  = {(0,0,lambda0,lambda1)},
  ker cMinus(I) = {(lambdatilde0,lambdatilde1,0,0)}.

Projectively, each nonzero two-dimensional kernel gives an `RP^1`.  Their product is the
standard split-signature celestial cut `RP^1 x RP^1`.

The familiar spinor-helicity null momentum is the rank-one outer product

  p_{alpha alphadot} = lambda_alpha lambdatilde_alphadot.

This file formalizes the coordinate content of that statement: the two kernel spinors
produce a `2x2` matrix with identically vanishing determinant.  No projective-space type
is introduced, so the `RP^1 x RP^1` statement remains the standard geometric interpretation
of the proved two-dimensional homogeneous factors.
-/

namespace GppFlatInfinityCelestialFactorization

open GppTwistorAnnihilatorIncidence
open GppGrassmannianGooglyDecomposition
open GppKleinSpinorIncidence
open GppKleinNullInfinityBoundary

abbrev Spinor2 := ℝ × ℝ

/-- Ordinary-twistor kernel embedding at flat infinity. -/
def ordinaryKernelSpinor (λ : Spinor2) : V4 := (0,0,λ.1,λ.2)

/-- Dual-twistor kernel embedding at flat infinity. -/
def dualKernelSpinor (λt : Spinor2) : V4 := (λt.1,λt.2,0,0)

/-- Every ordinary kernel spinor is annihilated by the flat infinity Clifford map. -/
theorem ordinaryKernelSpinor_mem_kernel (λ : Spinor2) :
    cPlus infinityPoint (ordinaryKernelSpinor λ) = (0,0,0,0) := by
  rcases λ with ⟨l0,l1⟩
  simp [ordinaryKernelSpinor, cPlus, infinityPoint]

/-- Every dual kernel spinor is annihilated by the opposite map. -/
theorem dualKernelSpinor_mem_kernel (λt : Spinor2) :
    cMinus infinityPoint (dualKernelSpinor λt) = (0,0,0,0) := by
  rcases λt with ⟨t0,t1⟩
  simp [dualKernelSpinor, cMinus, infinityPoint]

/-- Conversely every vector in the ordinary kernel has this two-spinor form. -/
theorem ordinary_kernel_parameterized (z : V4)
    (h : cPlus infinityPoint z = (0,0,0,0)) :
    z = ordinaryKernelSpinor (z.2.2.1,z.2.2.2) := by
  have hk := (infinity_cPlus_kernel z).mp h
  rcases z with ⟨z0,z1,z2,z3⟩
  simp at hk
  rcases hk with ⟨rfl,rfl⟩
  rfl

/-- And every vector in the dual kernel has the complementary two-spinor form. -/
theorem dual_kernel_parameterized (α : V4)
    (h : cMinus infinityPoint α = (0,0,0,0)) :
    α = dualKernelSpinor (α.1,α.2.1) := by
  have hk := (infinity_cMinus_kernel α).mp h
  rcases α with ⟨a0,a1,a2,a3⟩
  simp at hk
  rcases hk with ⟨rfl,rfl⟩
  rfl

/-- Rank-one spinor-helicity momentum matrix `lambda tensor lambdatilde`. -/
def nullMomentum (λ λt : Spinor2) : M2 :=
  (λ.1*λt.1, λ.1*λt.2, λ.2*λt.1, λ.2*λt.2)

/-- The spinor outer product is exactly null: its `2x2` determinant vanishes identically. -/
theorem nullMomentum_det_zero (λ λt : Spinor2) :
    det2 (nullMomentum λ λt) = 0 := by
  rcases λ with ⟨l0,l1⟩
  rcases λt with ⟨t0,t1⟩
  simp [nullMomentum, det2]
  ring

/-- Scaling the first celestial spinor scales the null momentum linearly. -/
def scale2 (r : ℝ) (λ : Spinor2) : Spinor2 := (r*λ.1,r*λ.2)

/-- Coordinate scaling on the `2x2` momentum matrix. -/
def scaleM2 (r : ℝ) (A : M2) : M2 :=
  (r*A.1,r*A.2.1,r*A.2.2.1,r*A.2.2.2)

/-- Independent rescalings of the two spinors act only through their product on momentum. -/
theorem nullMomentum_biscaling (r s : ℝ) (λ λt : Spinor2) :
    nullMomentum (scale2 r λ) (scale2 s λt) =
      scaleM2 (r*s) (nullMomentum λ λt) := by
  rcases λ with ⟨l0,l1⟩
  rcases λt with ⟨t0,t1⟩
  apply Prod.ext
  · simp [nullMomentum, scale2, scaleM2]
    ring
  · apply Prod.ext
    · simp [nullMomentum, scale2, scaleM2]
      ring
    · apply Prod.ext
      · simp [nullMomentum, scale2, scaleM2]
        ring
      · simp [nullMomentum, scale2, scaleM2]
        ring

/-- Opposite rescalings leave the momentum representative itself unchanged when the
scale is nonzero: the usual real split little-group action. -/
theorem nullMomentum_littleGroup_invariant
    (r : ℝ) (hr : r ≠ 0) (λ λt : Spinor2) :
    nullMomentum (scale2 r λ) (scale2 (1/r) λt) = nullMomentum λ λt := by
  rw [nullMomentum_biscaling]
  have hs : r * (1/r) = 1 := by field_simp [hr]
  rw [hs]
  rcases nullMomentum λ λt with ⟨a,b,c,d⟩
  simp [scaleM2]

end GppFlatInfinityCelestialFactorization
