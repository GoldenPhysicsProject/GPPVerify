import Mathlib.Tactic
import GppVerify.CelestialHolography.KleinSpinorIncidence

/-!
# Null versus non-null Klein chiral bridge

`KleinSpinorIncidence` proves the epsilon Clifford identities

  cMinus(p) (cPlus(p) z)   = (-Q_Klein(p)) z,
  cPlus(p)  (cMinus(p) α)  = (-Q_Klein(p)) α.

This file extracts the resulting dichotomy.

* If `Q_Klein(p) != 0`, the same bivector gives mutually inverse maps between the two
  chiral twistor modules after one scalar normalization.
* If `Q_Klein(p) = 0`, the bridge degenerates to a nilpotent incidence operator.

This is exactly the algebraic shape obeyed by the standard infinity twistor: in common
twistor conventions its contraction with its epsilon-dual is proportional to the
cosmological constant.  We therefore define the convention-neutral bridge parameter

  lambdaK(p) = -Q_Klein(p)

and prove all statements in terms of `lambdaK`.  Identifying `lambdaK` with a physical
cosmological constant is external geometric input, not assumed by the algebra.
-/

namespace GppKleinSpinorInfinityBridge

open GppGrassmannianGooglyDecomposition
open GppTwistorAnnihilatorIncidence
open GppKleinSpinorIncidence

/-- Convention-neutral scalar controlling the square of the chiral bridge. -/
def lambdaK (p : P6) : ℝ := -kleinQ p

/-- The epsilon Clifford square is exactly the bridge parameter. -/
theorem cMinus_cPlus_eq_lambdaK (p : P6) (z : V4) :
    cMinus p (cPlus p z) = scale4 (lambdaK p) z := by
  exact cMinus_cPlus p z

/-- Same statement on the opposite chirality. -/
theorem cPlus_cMinus_eq_lambdaK (p : P6) (α : V4) :
    cPlus p (cMinus p α) = scale4 (lambdaK p) α := by
  exact cPlus_cMinus p α

/-- Scalar multiplication composes multiplicatively. -/
theorem scale4_scale (λ μ : ℝ) (x : V4) :
    scale4 λ (scale4 μ x) = scale4 (λ*μ) x := by
  rcases x with ⟨x0,x1,x2,x3⟩
  apply Prod.ext
  · simp [scale4]
    ring
  · apply Prod.ext
    · simp [scale4]
      ring
    · apply Prod.ext
      · simp [scale4]
        ring
      · simp [scale4]
        ring

/-- Unit scalar acts trivially. -/
theorem scale4_one (x : V4) : scale4 1 x = x := by
  rcases x with ⟨x0,x1,x2,x3⟩
  simp [scale4]

/-- `cPlus` respects scalar multiplication. -/
theorem cPlus_scale (p : P6) (λ : ℝ) (z : V4) :
    cPlus p (scale4 λ z) = scale4 λ (cPlus p z) := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  rcases z with ⟨z0,z1,z2,z3⟩
  apply Prod.ext
  · simp [cPlus, scale4]
    ring
  · apply Prod.ext
    · simp [cPlus, scale4]
      ring
    · apply Prod.ext
      · simp [cPlus, scale4]
        ring
      · simp [cPlus, scale4]
        ring

/-- `cMinus` respects scalar multiplication. -/
theorem cMinus_scale (p : P6) (λ : ℝ) (α : V4) :
    cMinus p (scale4 λ α) = scale4 λ (cMinus p α) := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  rcases α with ⟨a0,a1,a2,a3⟩
  apply Prod.ext
  · simp [cMinus, scale4]
    ring
  · apply Prod.ext
    · simp [cMinus, scale4]
      ring
    · apply Prod.ext
      · simp [cMinus, scale4]
        ring
      · simp [cMinus, scale4]
        ring

/-- For a non-null Klein bivector, normalized `cMinus` is a left inverse of `cPlus`. -/
theorem normalized_cMinus_leftInverse_cPlus
    (p : P6) (h : lambdaK p ≠ 0) (z : V4) :
    scale4 (1 / lambdaK p) (cMinus p (cPlus p z)) = z := by
  rw [cMinus_cPlus_eq_lambdaK, scale4_scale]
  have hs : (1 / lambdaK p) * lambdaK p = 1 := by
    field_simp [h]
  rw [hs]
  exact scale4_one z

/-- For a non-null Klein bivector, normalized `cMinus` is also a right inverse of
`cPlus`; hence no independent metric identification `V* ≅ V` is needed. -/
theorem cPlus_normalized_cMinus_rightInverse
    (p : P6) (h : lambdaK p ≠ 0) (α : V4) :
    cPlus p (scale4 (1 / lambdaK p) (cMinus p α)) = α := by
  rw [cPlus_scale, cPlus_cMinus_eq_lambdaK, scale4_scale]
  have hs : (1 / lambdaK p) * lambdaK p = 1 := by
    field_simp [h]
  rw [hs]
  exact scale4_one α

/-- Non-null `cPlus` is injective. -/
theorem cPlus_injective_of_nonnull
    (p : P6) (h : lambdaK p ≠ 0) : Function.Injective (cPlus p) := by
  intro z₁ z₂ hz
  have hz' := congrArg (fun α => scale4 (1 / lambdaK p) (cMinus p α)) hz
  rw [normalized_cMinus_leftInverse_cPlus p h z₁,
      normalized_cMinus_leftInverse_cPlus p h z₂] at hz'
  exact hz'

/-- Non-null `cPlus` is surjective. -/
theorem cPlus_surjective_of_nonnull
    (p : P6) (h : lambdaK p ≠ 0) : Function.Surjective (cPlus p) := by
  intro α
  refine ⟨scale4 (1 / lambdaK p) (cMinus p α), ?_⟩
  exact cPlus_normalized_cMinus_rightInverse p h α

/-- Therefore the epsilon Clifford bridge is a bijection between the two chiral twistor
modules whenever the Klein norm is nonzero. -/
theorem cPlus_bijective_of_nonnull
    (p : P6) (h : lambdaK p ≠ 0) : Function.Bijective (cPlus p) :=
  ⟨cPlus_injective_of_nonnull p h, cPlus_surjective_of_nonnull p h⟩

/-- The same non-null condition makes `cMinus` a bijection in the reverse direction. -/
theorem normalized_cPlus_leftInverse_cMinus
    (p : P6) (h : lambdaK p ≠ 0) (α : V4) :
    scale4 (1 / lambdaK p) (cPlus p (cMinus p α)) = α := by
  rw [cPlus_cMinus_eq_lambdaK, scale4_scale]
  have hs : (1 / lambdaK p) * lambdaK p = 1 := by
    field_simp [h]
  rw [hs]
  exact scale4_one α

/-- At zero bridge parameter, both chiral compositions vanish identically. -/
theorem zero_parameter_is_nilpotent
    (p : P6) (h : lambdaK p = 0) (z α : V4) :
    cMinus p (cPlus p z) = (0,0,0,0) ∧
    cPlus p (cMinus p α) = (0,0,0,0) := by
  constructor
  · rw [cMinus_cPlus_eq_lambdaK, h]
    rcases z with ⟨z0,z1,z2,z3⟩
    simp [scale4]
  · rw [cPlus_cMinus_eq_lambdaK, h]
    rcases α with ⟨a0,a1,a2,a3⟩
    simp [scale4]

/-- Every actual spacetime point on the graph chart lies on the degenerate/null side of
the dichotomy. -/
theorem graph_spacetime_parameter_zero (A : M2) :
    lambdaK (chartPlucker A) = 0 := by
  simp [lambdaK, chartPlucker_klein_null]

/-- If an external geometric normalization identifies `lambdaK(p)` with a nonzero scalar
`Λ`, then the bridge square is exactly `Λ` and is invertible.  This is the abstract algebraic
form of the nonzero-cosmological-constant infinity-twistor relation. -/
theorem nonzero_parameter_bridge
    (p : P6) (Λ : ℝ) (hΛ : lambdaK p = Λ) (hne : Λ ≠ 0) (z : V4) :
    cMinus p (cPlus p z) = scale4 Λ z ∧
    scale4 (1 / Λ) (cMinus p (cPlus p z)) = z := by
  constructor
  · rw [cMinus_cPlus_eq_lambdaK, hΛ]
  · rw [cMinus_cPlus_eq_lambdaK, hΛ, scale4_scale]
    have hs : (1 / Λ) * Λ = 1 := by field_simp [hne]
    rw [hs]
    exact scale4_one z

end GppKleinSpinorInfinityBridge
