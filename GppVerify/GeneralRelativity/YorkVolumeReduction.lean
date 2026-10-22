import Mathlib.Tactic
import GppVerify.GeneralRelativity.YorkVolumeSymplectic
import GppVerify.QuantumGravity.FubiniStudyYorkBridge

/-!
# York symplectic reduction: necessity of the fixed-volume tangent space

A new exact linearized theorem, suitable for the main claim of
"The Volume Constraint in Entanglement Equilibrium".

Suppose a real symplectic/presymplectic form `omega` and a York vector
field `y` satisfy the moment-map identity
  omega y x = c * dV x, c != 0.
If the York vector is to become null when the 2-form is restricted to
the *admissible* variation space W (a necessary condition for the
form to descend to the quotient W/<y>), then every x in W must satisfy
dV x = 0. Conversely, fixed-volume tangents make y null.

This establishes necessity and sufficiency of the *first-order
constraint* for this particular York-flow symplectic reduction. It
does NOT establish the physical premise that York flow MUST be
quotiented in arbitrary causal-diamond entanglement equilibrium.

No local/global symplectic quotient geometry is assumed implicitly.
The input York moment-map identity and the necessity of treating
York flow as gauge/vertical must be justified in the physical model.
-/

namespace GppYorkReduction

section Linearized
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (omega : E → E → ℝ) (y : E)
  (dV : E →ₗ[ℝ] ℝ) (c : ℝ)
  (hc : c ≠ 0) (hYork : ∀ x, omega y x = c * dV x)

/-- Horizontal/characteristic York condition is precisely the
linearized fixed-volume condition. -/
theorem york_horizontal_iff_fixed_volume (x : E) :
    omega y x = 0 ↔ dV x = 0 := by
  constructor
  · intro h
    rw [hYork x] at h
    exact (mul_eq_zero.mp h).resolve_left hc
  · intro h
    rw [hYork x, h]
    ring

/-- If the York direction annihilates the induced two-form on a
chosen admissible tangent subspace, that space lies in ker(dV). -/
theorem reduction_domain_forces_fixed_volume
    (W : Submodule ℝ E)
    (hnull : ∀ x ∈ W, omega y x = 0) :
    W ≤ LinearMap.ker dV := by
  intro x hx
  change dV x = 0
  exact (york_horizontal_iff_fixed_volume
     omega y dV c hc hYork x).mp (hnull x hx)

/-- Converse and exact uniqueness of the maximal York-reducible
linearized variation space: the full kernel of the volume functional. -/
theorem york_reduction_iff_volume_level
    (W : Submodule ℝ E) :
    (∀ x ∈ W, omega y x = 0) ↔
    W ≤ LinearMap.ker dV := by
  constructor
  · exact reduction_domain_forces_fixed_volume omega y dV c hc hYork W
  · intro hW x hx
    apply (york_horizontal_iff_fixed_volume
       omega y dV c hc hYork x).mpr
    have hmem : x ∈ LinearMap.ker dV := hW hx
    exact (LinearMap.mem_ker).mp hmem

/-- If dV is nonzero on some admitted perturbation, the York
generator CANNOT be in the presymplectic kernel on the entire
unconstrained tangent space. It is not a phase-only gauge direction. -/
theorem nontrivial_volume_excludes_global_york_null
    (x : E) (hvol : dV x ≠ 0) :
    omega y x ≠ 0 := by
  rw [hYork x]
  exact mul_ne_zero hc hvol

/-- In particular, treating York flow as an everywhere-degenerate
direction is inconsistent when nonzero volume variations exist. -/
theorem no_unconstrained_york_reduction
    (x : E) (hvol : dV x ≠ 0) :
    ¬ (∀ z : E, omega y z = 0) := by
  intro hall
  exact (nontrivial_volume_excludes_global_york_null
     omega y dV c hc hYork x hvol) (hall x)

end Linearized

end GppYorkReduction

#print axioms GppYorkReduction.york_horizontal_iff_fixed_volume
#print axioms GppYorkReduction.reduction_domain_forces_fixed_volume
#print axioms GppYorkReduction.york_reduction_iff_volume_level
#print axioms GppYorkReduction.no_unconstrained_york_reduction
