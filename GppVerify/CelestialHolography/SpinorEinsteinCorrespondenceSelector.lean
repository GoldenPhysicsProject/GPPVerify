import Mathlib.Tactic
import GppVerify.CelestialHolography.FlatInfinityCelestialFactorization
import GppVerify.CelestialHolography.NullConeEinsteinSelector

/-!
# Spinor/correspondence-space form of the null-cone Einstein selector

In split signature every null tangent vector is a rank-one `2x2` matrix

  X = lambda tensor lambdatilde.

The converse is as important as the familiar forward statement: every real `2x2` matrix
with zero determinant admits such a factorization.  This file proves that converse in the
coordinate carrier already used by GPPVerify.

Consequently, for a general quadratic tensor polynomial `T(X,X)`, vanishing on every
spinor outer product is equivalent to vanishing on the entire split null cone.  By the
null-cone rigidity theorem in `NullConeEinsteinSelector`, this is equivalent to `T` being
a scalar multiple of the determinant metric, i.e. pure trace.

Geometric interpretation (external to the finite algebra): LeBrun's Einstein-bundle
pullback on correspondence space is cut out by a second-order spinorial operator obtained
by contracting the conformal-Einstein Hessian/Schouten tensor with the projective spinor
coordinates.  A further contraction with the complementary spinor gives precisely the
null-direction equation formalized abstractly here.  No differential operator or
holomorphic bundle is hidden in this module.
-/

namespace GppSpinorEinsteinCorrespondenceSelector

open GppGrassmannianGooglyDecomposition
open GppFlatInfinityCelestialFactorization
open GppNullConeEinsteinSelector

/-- Every determinant-zero real `2x2` matrix factors as a split spinor outer product. -/
theorem det_zero_factors_as_spinors
    (a b c d : ℝ) (hdet : det2 (a,b,c,d) = 0) :
    ∃ lambda lambdatilde : Spinor2,
      nullMomentum lambda lambdatilde = (a,b,c,d) := by
  by_cases ha : a = 0
  · subst a
    have hbc : b*c = 0 := by
      simp [det2] at hdet
      linarith
    rcases mul_eq_zero.mp hbc with hb | hc
    · subst b
      refine ⟨(0,1),(c,d), ?_⟩
      apply Prod.ext
      · simp [nullMomentum]
      · apply Prod.ext
        · simp [nullMomentum]
        · apply Prod.ext <;> simp [nullMomentum]
    · subst c
      by_cases hb : b = 0
      · subst b
        refine ⟨(0,1),(0,d), ?_⟩
        apply Prod.ext
        · simp [nullMomentum]
        · apply Prod.ext
          · simp [nullMomentum]
          · apply Prod.ext <;> simp [nullMomentum]
      · refine ⟨(1,d/b),(0,b), ?_⟩
        apply Prod.ext
        · simp [nullMomentum]
        · apply Prod.ext
          · simp [nullMomentum]
          · apply Prod.ext
            · simp [nullMomentum]
            · simp [nullMomentum]
              field_simp [hb]
  · have had : a*d = b*c := by
      simp [det2] at hdet
      linarith
    refine ⟨(a,c),(1,b/a), ?_⟩
    apply Prod.ext
    · simp [nullMomentum]
    · apply Prod.ext
      · simp [nullMomentum]
        field_simp [ha]
      · apply Prod.ext
        · simp [nullMomentum]
        · simp [nullMomentum]
          field_simp [ha]
          nlinarith [had]

/-- Exact iff: the split null cone is precisely the image of the two-spinor outer-product
map. -/
theorem det_zero_iff_spinor_factorization (A : M2) :
    det2 A = 0 ↔ ∃ lambda lambdatilde : Spinor2,
      nullMomentum lambda lambdatilde = A := by
  rcases A with ⟨a,b,c,d⟩
  constructor
  · exact det_zero_factors_as_spinors a b c d
  · rintro ⟨lambda,lambdatilde,rfl⟩
    exact nullMomentum_det_zero lambda lambdatilde

/-- If a quadratic tensor polynomial vanishes on every pair of split spinors, it vanishes
on every null tangent direction. -/
theorem spinor_vanishing_implies_null_cone_vanishing
    (A B C D E F G H I J : ℝ)
    (hspin : ∀ lambda lambdatilde : Spinor2,
      let X := nullMomentum lambda lambdatilde
      quad4 A B C D E F G H I J X.1 X.2.1 X.2.2.1 X.2.2.2 = 0) :
    ∀ a b c d : ℝ,
      det2 (a,b,c,d) = 0 -> quad4 A B C D E F G H I J a b c d = 0 := by
  intro a b c d hdet
  obtain ⟨lambda,lambdatilde,hfac⟩ := det_zero_factors_as_spinors a b c d hdet
  have hs := hspin lambda lambdatilde
  change quad4 A B C D E F G H I J
    (nullMomentum lambda lambdatilde).1
    (nullMomentum lambda lambdatilde).2.1
    (nullMomentum lambda lambdatilde).2.2.1
    (nullMomentum lambda lambdatilde).2.2.2 = 0 at hs
  rw [hfac] at hs
  exact hs

/-- Main correspondence-space selector theorem: vanishing of the quadratic scale tensor
on every spinor pair forces it to be pure trace, represented by a scalar multiple of the
split determinant metric. -/
theorem spinor_vanishing_implies_pure_trace
    (A B C D E F G H I J : ℝ)
    (hspin : ∀ lambda lambdatilde : Spinor2,
      let X := nullMomentum lambda lambdatilde
      quad4 A B C D E F G H I J X.1 X.2.1 X.2.2.1 X.2.2.2 = 0) :
    ∃ mu : ℝ, ∀ a b c d : ℝ,
      quad4 A B C D E F G H I J a b c d = mu * det2 (a,b,c,d) := by
  apply vanishing_on_rankOne_implies_det_multiple
  exact spinor_vanishing_implies_null_cone_vanishing
    A B C D E F G H I J hspin

/-- Converse: every pure-trace quadratic tensor vanishes on all spinor-factorized null
directions. -/
theorem pure_trace_vanishes_on_spinors
    (mu : ℝ) (lambda lambdatilde : Spinor2) :
    let X := nullMomentum lambda lambdatilde
    mu * det2 X = 0 := by
  dsimp
  rw [nullMomentum_det_zero]
  ring

/-- Hence the correspondence-space spinor condition and the pure-trace condition are
exactly equivalent at the finite quadratic level. -/
theorem spinor_vanishing_iff_pure_trace
    (A B C D E F G H I J : ℝ) :
    (∀ lambda lambdatilde : Spinor2,
      let X := nullMomentum lambda lambdatilde
      quad4 A B C D E F G H I J X.1 X.2.1 X.2.2.1 X.2.2.2 = 0) ↔
    (∃ mu : ℝ, ∀ a b c d : ℝ,
      quad4 A B C D E F G H I J a b c d = mu * det2 (a,b,c,d)) := by
  constructor
  · exact spinor_vanishing_implies_pure_trace A B C D E F G H I J
  · rintro ⟨mu,hmu⟩ lambda lambdatilde
    let X := nullMomentum lambda lambdatilde
    change quad4 A B C D E F G H I J X.1 X.2.1 X.2.2.1 X.2.2.2 = 0
    rw [hmu X.1 X.2.1 X.2.2.1 X.2.2.2]
    change mu * det2 (nullMomentum lambda lambdatilde) = 0
    rw [nullMomentum_det_zero]
    ring

end GppSpinorEinsteinCorrespondenceSelector
