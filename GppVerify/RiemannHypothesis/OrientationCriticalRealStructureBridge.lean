import Mathlib.Tactic
import GppVerify.StandardModel.OrientationComplexStructureDoubleCover
import GppVerify.RiemannHypothesis.L2Constraint
import GppVerify.RiemannHypothesis.CayleyShadowAdjointBridge

/-!
# Orientation real structure and the centered critical-line reflection

This file separates two operations that are easy to conflate:

* the linear centered shadow `nu -> -nu`;
* the anti-linear fixed-locus reflection `nu -> -conj(nu)`.

The four-lift diagonal reversal `D` is complex-linear for the ambient C^4 structure,
but anticommutes with the microscopic complex structure `Iq`.  Thus, on the underlying
real vector space equipped with `Iq` as multiplication by i, `D` is a real structure.

The critical-line reflection has the same algebra: it is an anti-linear involution whose
fixed locus is Re(nu)=0, i.e. Re(s)=1/2 for nu=s-1/2.
-/

namespace GppOrientationCriticalRealStructureBridge

open Complex
open GppFourOrientationGaugeProjection
open GppOrientationComplexStructureDoubleCover

/-- The relative grading on the D-fixed carrier is exactly diag(+1,-1). -/
theorem chi_on_physicalLift (a b : ℂ) :
    chi (physicalLift a b) = physicalLift a (-b) := by
  simp [chi, physicalLift]

/-- `D` is conjugate-linear relative to the complex structure `Iq`. -/
theorem diagReverse_is_Iq_antilinear (v : Orientation4) :
    diagReverse (Iq v) = - Iq (diagReverse v) :=
  diag_anticommutes_Iq v

/-- The same diagonal reversal is an involution. -/
theorem diagReverse_sq (v : Orientation4) :
    diagReverse (diagReverse v) = v :=
  (flip_involutions v).1

/-- Every vector decomposes into a D-fixed real part plus Iq times another D-fixed part.
    This is the concrete real-form decomposition relative to `Iq`. -/
theorem Iq_real_form_decomposition (v : Orientation4) :
    ∃ x y : Orientation4,
      diagReverse x = x ∧
      diagReverse y = y ∧
      v = x + Iq y := by
  rcases v with ⟨a,b,c,d⟩
  let x : Orientation4 :=
    ((a+d)/2, (b+c)/2, (b+c)/2, (a+d)/2)
  let y : Orientation4 :=
    (-Complex.I*(a-d)/2, -Complex.I*(b-c)/2,
     -Complex.I*(b-c)/2, -Complex.I*(a-d)/2)
  refine ⟨x, y, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · simp only [x, y, Iq, Prod.mk_add_mk, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

/-- Centered linear shadow. -/
def centeredShadow (nu : ℂ) : ℂ := -nu

/-- Centered anti-linear critical-line reflection. -/
def criticalRealStructure (nu : ℂ) : ℂ := -(starRingEnd ℂ nu)

/-- The anti-linear reflection is an involution. -/
theorem criticalRealStructure_sq (nu : ℂ) :
    criticalRealStructure (criticalRealStructure nu) = nu := by
  simp [criticalRealStructure]

/-- It is exactly shadow composed with complex conjugation. -/
theorem criticalRealStructure_eq_shadow_conj (nu : ℂ) :
    criticalRealStructure nu = centeredShadow ((starRingEnd ℂ) nu) := by
  rfl

/-- Its fixed locus is the centered critical line. -/
theorem criticalRealStructure_fixed_iff (nu : ℂ) :
    criticalRealStructure nu = nu ↔ nu.re = 0 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp [criticalRealStructure] at hre
    linarith
  · intro hre
    apply Complex.ext
    · simp [criticalRealStructure, hre]
    · simp [criticalRealStructure]

/-- The two centered half operations, linear shadow and coefficient conjugation,
    coincide exactly on the critical real form.  This is the scalar arithmetic analogue
    of the v21 finite theorem that the two half flips coincide on the D-fixed real form. -/
theorem centered_shadow_eq_conj_iff_critical_real_form (nu : ℂ) :
    centeredShadow nu = (starRingEnd ℂ) nu ↔ nu.re = 0 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp [centeredShadow] at hre
    linarith
  · intro hre
    apply Complex.ext
    · simp [centeredShadow, hre]
    · simp [centeredShadow]

/-- In the original s-coordinate the fixed-locus reflection is s -> 1-conj(s). -/
theorem centered_reflection_from_s (s : ℂ) :
    criticalRealStructure (s - (1/2 : ℂ)) =
      (1 - (starRingEnd ℂ) s) - (1/2 : ℂ) := by
  simp only [criticalRealStructure, map_sub, map_div₀, map_one, map_ofNat]
  ring

/-- Consequently its fixed locus is exactly Re(s)=1/2. -/
theorem s_fixed_iff_critical (s : ℂ) :
    (1 - (starRingEnd ℂ) s = s) ↔ s.re = (1/2 : ℝ) := by
  constructor
  · intro h
    have hs : (starRingEnd ℂ) s = 1 - s := by
      calc
        (starRingEnd ℂ) s = 1 - (1 - (starRingEnd ℂ) s) := by ring
        _ = 1 - s := by rw [h]
    exact GppL2.conj_eq_shadow_iff_critical s hs
  · intro hcrit
    have hs : (starRingEnd ℂ) s = 1 - s :=
      GppCayleyShadowAdjointBridge.conj_eq_shadow_of_critical s hcrit
    calc
      1 - (starRingEnd ℂ) s = 1 - (1 - s) := by rw [hs]
      _ = s := by ring

/-- On the critical line the anti-linear reflection fixes the point, while bare shadow
    reverses the spectral coordinate. -/
theorem critical_line_actions (t : ℝ) :
    criticalRealStructure (Complex.I * (t : ℂ)) = Complex.I * (t : ℂ) ∧
    centeredShadow (Complex.I * (t : ℂ)) = -(Complex.I * (t : ℂ)) := by
  constructor
  · simp [criticalRealStructure]
  · rfl

end GppOrientationCriticalRealStructureBridge

#print axioms GppOrientationCriticalRealStructureBridge.chi_on_physicalLift
#print axioms GppOrientationCriticalRealStructureBridge.Iq_real_form_decomposition
#print axioms GppOrientationCriticalRealStructureBridge.criticalRealStructure_fixed_iff
#print axioms GppOrientationCriticalRealStructureBridge.centered_shadow_eq_conj_iff_critical_real_form
#print axioms GppOrientationCriticalRealStructureBridge.s_fixed_iff_critical
