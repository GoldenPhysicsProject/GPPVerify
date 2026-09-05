import Mathlib.Tactic
import GppVerify.CelestialHolography.KleinNullInfinityBoundary

/-!
# Exact chiral complex at flat infinity

At nonzero Klein norm, a bivector gives an invertible Clifford bridge between the two
four-dimensional chiral twistor modules.  At the flat infinity point the norm vanishes,
so the two maps instead form a two-periodic complex

  V --cPlus(I)--> V* --cMinus(I)--> V --cPlus(I)--> V*.

For the standard infinity point `I=e2∧e3` the complex is exact at the vector-space level:

  im cPlus(I)  = ker cMinus(I),
  im cMinus(I) = ker cPlus(I).

Thus the flat limit does not identify ordinary and dual twistors pointwise.  It organizes
them into complementary kernel/image incidence data on the same null Klein geometry.

This is the precise finite-dimensional algebra behind the phrase "both halves are here".
It does not yet identify a field-level cohomology quotient or a nonlinear Einstein googly map.
-/

namespace GppFlatInfinityChiralComplex

open GppTwistorAnnihilatorIncidence
open GppKleinSpinorIncidence
open GppKleinNullInfinityBoundary

/-- First differential followed by the second is zero at flat infinity. -/
theorem cMinus_after_cPlus_zero (z : V4) :
    cMinus infinityPoint (cPlus infinityPoint z) = (0,0,0,0) := by
  rw [GppKleinSpinorIncidence.cMinus_cPlus,
      GppKleinNullInfinityBoundary.infinityPoint_is_null]
  rcases z with ⟨z0,z1,z2,z3⟩
  simp [scale4]

/-- The reverse composition also vanishes. -/
theorem cPlus_after_cMinus_zero (α : V4) :
    cPlus infinityPoint (cMinus infinityPoint α) = (0,0,0,0) := by
  rw [GppKleinSpinorIncidence.cPlus_cMinus,
      GppKleinNullInfinityBoundary.infinityPoint_is_null]
  rcases α with ⟨a0,a1,a2,a3⟩
  simp [scale4]

/-- Explicit image characterization of `cPlus(I)`: precisely the first two dual-twistor
coordinate directions. -/
theorem cPlus_image_iff (α : V4) :
    (∃ z : V4, cPlus infinityPoint z = α) ↔ α.2.2.1 = 0 ∧ α.2.2.2 = 0 := by
  constructor
  · rintro ⟨z,hz⟩
    have hk : cMinus infinityPoint α = (0,0,0,0) := by
      rw [← hz]
      exact cMinus_after_cPlus_zero z
    exact (infinity_cMinus_kernel α).mp hk
  · intro h
    rcases α with ⟨a0,a1,a2,a3⟩
    simp at h
    rcases h with ⟨rfl,rfl⟩
    refine ⟨(a1,-a0,0,0), ?_⟩
    simp [cPlus, infinityPoint]

/-- Explicit image characterization of `cMinus(I)`: precisely the last two ordinary
 twistor coordinate directions. -/
theorem cMinus_image_iff (z : V4) :
    (∃ α : V4, cMinus infinityPoint α = z) ↔ z.1 = 0 ∧ z.2.1 = 0 := by
  constructor
  · rintro ⟨α,hα⟩
    have hk : cPlus infinityPoint z = (0,0,0,0) := by
      rw [← hα]
      exact cPlus_after_cMinus_zero α
    exact (infinity_cPlus_kernel z).mp hk
  · intro h
    rcases z with ⟨z0,z1,z2,z3⟩
    simp at h
    rcases h with ⟨rfl,rfl⟩
    refine ⟨(0,0,z3,-z2), ?_⟩
    simp [cMinus, infinityPoint]

/-- Exactness at the dual-twistor term: image of `cPlus` equals kernel of `cMinus`. -/
theorem im_cPlus_eq_ker_cMinus (α : V4) :
    (∃ z : V4, cPlus infinityPoint z = α) ↔
      cMinus infinityPoint α = (0,0,0,0) := by
  rw [cPlus_image_iff, infinity_cMinus_kernel]

/-- Exactness at the ordinary-twistor term: image of `cMinus` equals kernel of `cPlus`. -/
theorem im_cMinus_eq_ker_cPlus (z : V4) :
    (∃ α : V4, cMinus infinityPoint α = z) ↔
      cPlus infinityPoint z = (0,0,0,0) := by
  rw [cMinus_image_iff, infinity_cPlus_kernel]

/-- The infinity complex contains nonzero kernel directions on the ordinary-twistor side. -/
theorem ordinary_kernel_nontrivial :
    cPlus infinityPoint (0,0,1,0) = (0,0,0,0) ∧
    (0,0,1,0 : V4) ≠ (0,0,0,0) := by
  constructor
  · simp [cPlus, infinityPoint]
  · norm_num

/-- And nonzero kernel directions on the dual-twistor side. -/
theorem dual_kernel_nontrivial :
    cMinus infinityPoint (1,0,0,0) = (0,0,0,0) ∧
    (1,0,0,0 : V4) ≠ (0,0,0,0) := by
  constructor
  · simp [cMinus, infinityPoint]
  · norm_num

/-- Therefore neither flat-infinity chiral map is injective; the flat limit is genuinely
incidence/exact-complex geometry, not a hidden isomorphism. -/
theorem flat_infinity_maps_not_injective :
    ¬ Function.Injective (cPlus infinityPoint) ∧
    ¬ Function.Injective (cMinus infinityPoint) := by
  constructor
  · intro hinj
    have h := hinj ordinary_kernel_nontrivial.1
    exact ordinary_kernel_nontrivial.2 h
  · intro hinj
    have h := hinj dual_kernel_nontrivial.1
    exact dual_kernel_nontrivial.2 h

end GppFlatInfinityChiralComplex
