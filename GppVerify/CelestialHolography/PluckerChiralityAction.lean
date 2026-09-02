import Mathlib.Tactic
import GppVerify.CelestialHolography.GrassmannianGooglyDecomposition

/-!
# Hodge action on Plucker SD/ASD coordinates

Important correction for the googly programme:

Applying the Hodge star to a bivector does NOT exchange the self-dual and
anti-self-dual eigenspaces.  In Euclidean signature it acts as +1 on the SD
coordinates and -1 on the ASD coordinates.  What exchanges the sector labels
is reversal of the spacetime orientation, which changes the Hodge operator
itself from `star` to `-star`.

This file proves the coordinate statement exactly for the Plucker basis used by
`GrassmannianGooglyDecomposition.lean`.
-/

namespace GppPluckerChiralityAction

open GppGrassmannianGooglyDecomposition

/-- Self-dual coordinate 1. -/
def s1 (p : P6) : ℝ := (p.p01 + p.p23) / 2
/-- Self-dual coordinate 2. -/
def s2 (p : P6) : ℝ := (p.p02 - p.p13) / 2
/-- Self-dual coordinate 3. -/
def s3 (p : P6) : ℝ := (p.p03 + p.p12) / 2

/-- Anti-self-dual coordinate 1. -/
def a1 (p : P6) : ℝ := (p.p01 - p.p23) / 2
/-- Anti-self-dual coordinate 2. -/
def a2 (p : P6) : ℝ := (p.p02 + p.p13) / 2
/-- Anti-self-dual coordinate 3. -/
def a3 (p : P6) : ℝ := (p.p03 - p.p12) / 2

/-- Hodge star fixes all three self-dual coordinates. -/
theorem pluckerStar_fixes_sd (p : P6) :
    s1 (pluckerStar p) = s1 p ∧
    s2 (pluckerStar p) = s2 p ∧
    s3 (pluckerStar p) = s3 p := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  simp [s1,s2,s3,pluckerStar]
  constructor
  · ring
  · constructor <;> ring

/-- Hodge star negates all three anti-self-dual coordinates. -/
theorem pluckerStar_negates_asd (p : P6) :
    a1 (pluckerStar p) = -a1 p ∧
    a2 (pluckerStar p) = -a2 p ∧
    a3 (pluckerStar p) = -a3 p := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  simp [a1,a2,a3,pluckerStar]
  constructor
  · ring
  · constructor <;> ring

/-- Orientation reversal swaps the eigenspace labels abstractly: if `F` is
+1-self-dual for `star`, it is -1-anti-self-dual for `-star`. -/
theorem orientation_reversal_relabels_sd_as_asd
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (star : V →ₗ[ℝ] V) (F : V) (hF : star F = F) :
    (-star) F = (-1 : ℝ) • F := by
  simp [hF]

/-- Conversely an ASD vector for `star` becomes SD for the reversed orientation. -/
theorem orientation_reversal_relabels_asd_as_sd
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (star : V →ₗ[ℝ] V) (F : V) (hF : star F = (-1 : ℝ) • F) :
    (-star) F = F := by
  simp [hF]

end GppPluckerChiralityAction
