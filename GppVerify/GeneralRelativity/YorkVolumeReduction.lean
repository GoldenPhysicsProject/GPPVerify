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

/-- Horizontal/characteristic York condition is precisely the
linearized fixed-volume condition. -/
theorem york_horizontal_iff_fixed_volume
    (hc : c ≠ 0) (hYork : ∀ z, omega y z = c * dV z) (x : E) :
    omega y x = 0 ↔ dV x = 0 := by
  constructor
  · intro h
    rw [hYork x] at h
    exact (mul_eq_zero.mp h).resolve_left hc
  · intro h
    simp [hYork x, h]

/-- If the York direction annihilates the induced two-form on a
chosen admissible tangent subspace, that space lies in ker(dV). -/
theorem reduction_domain_forces_fixed_volume
    (hc : c ≠ 0) (hYork : ∀ z, omega y z = c * dV z)
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
    (hc : c ≠ 0) (hYork : ∀ z, omega y z = c * dV z)
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
    (hc : c ≠ 0) (hYork : ∀ z, omega y z = c * dV z)
    (x : E) (hvol : dV x ≠ 0) :
    omega y x ≠ 0 := by
  rw [hYork x]
  exact mul_ne_zero hc hvol

/-- In particular, treating York flow as an everywhere-degenerate
direction is inconsistent when nonzero volume variations exist. -/
theorem no_unconstrained_york_reduction
    (hc : c ≠ 0) (hYork : ∀ z, omega y z = c * dV z)
    (x : E) (hvol : dV x ≠ 0) :
    ¬ (∀ z : E, omega y z = 0) := by
  intro hall
  exact (nontrivial_volume_excludes_global_york_null
     omega y dV c hc hYork x hvol) (hall x)


/-- A bilinear antisymmetric form is independent of representatives
shifted along the York direction when both variations have fixed
volume. This is the pointwise algebra behind descent to W / span(y),
with the geometric quotient and boundary terms still separate. -/
theorem york_form_representative_invariant
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hskew : ∀ x z, B x z = -(B z x))
    (hMoment : ∀ z, B y z = c * dV z)
    (x z : E) (hx : dV x = 0) (hz : dV z = 0)
    (hy : dV y = 0) (a b : ℝ) :
    B (x + a • y) (z + b • y) = B x z := by
  have hyx : B y x = 0 := by
    rw [hMoment x, hx]
    ring
  have hyz : B y z = 0 := by
    rw [hMoment z, hz]
    ring
  have hyy : B y y = 0 := by
    rw [hMoment y, hy]
    ring
  have hxy : B x y = 0 := by
    rw [hskew x y, hyx]
    ring
  calc
    B (x + a • y) (z + b • y) =
        B x z + b * B x y + a * B y z + a * b * B y y := by
          simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
          ring
    _ = B x z := by rw [hxy, hyz, hyy]; ring


/-- The York Hamiltonian flow preserves its own moment map: since an
antisymmetric form annihilates (y,y), dV(y)=0 follows automatically.
No independent tangency assumption on y is needed. -/
theorem york_generator_preserves_volume
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hskew : ∀ x z, B x z = -(B z x))
    (hc : c ≠ 0)
    (hMoment : ∀ z, B y z = c * dV z) :
    dV y = 0 := by
  have hzero : B y y = 0 := by
    have h := hskew y y
    linarith
  have hcy : c * dV y = 0 := by
    rw [← hMoment y]
    exact hzero
  exact (mul_eq_zero.mp hcy).resolve_left hc

/-- Representative independence for York quotient follows from the
moment-map relation and antisymmetry without postulating dV(y)=0. -/
theorem york_quotient_pairing_well_defined
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hskew : ∀ x z, B x z = -(B z x))
    (hc : c ≠ 0)
    (hMoment : ∀ z, B y z = c * dV z)
    (x z : E) (hx : dV x = 0) (hz : dV z = 0)
    (a b : ℝ) :
    B (x + a • y) (z + b • y) = B x z := by
  have hy := york_generator_preserves_volume
    omega y dV c B hskew hc hMoment
  exact york_form_representative_invariant
    omega y dV c B hskew hMoment x z hx hz hy a b

end Linearized


section ConcreteADM
variable {N M : ℕ}

/-- No external York moment-map hypothesis: the finite ADM momentum
trace formula was already proved in YorkVolumeSymplectic. A York-null
admissible metric perturbation must have zero proper-volume variation. -/
theorem adm_york_null_forces_fixed_volume
    (c : ℝ) (hc : c ≠ 0) (weight : Fin N → ℝ)
    (invMetric dh : Fin N → Fin M → Fin M → ℝ)
    (hnull : GppYorkVolume.canonicalMomentumPair
      (GppYorkVolume.yorkMomentum c weight invMetric) dh = 0) :
    GppYorkVolume.volumeTangent weight invMetric dh = 0 := by
  have h : (2 * c) * GppYorkVolume.volumeTangent weight invMetric dh = 0 := by
    rw [← GppYorkVolume.york_pairing_is_volume_variation]
    exact hnull
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (by norm_num) hc)

/-- Converse: fixed proper volume suffices to make the ADM York
momentum shift invisible to the linearized canonical pairing. -/
theorem adm_fixed_volume_implies_york_null
    (c : ℝ) (weight : Fin N → ℝ)
    (invMetric dh : Fin N → Fin M → Fin M → ℝ)
    (hvol : GppYorkVolume.volumeTangent weight invMetric dh = 0) :
    GppYorkVolume.canonicalMomentumPair
       (GppYorkVolume.yorkMomentum c weight invMetric) dh = 0 := by
  rw [GppYorkVolume.york_pairing_is_volume_variation, hvol]
  ring

end ConcreteADM

end GppYorkReduction

#print axioms GppYorkReduction.york_horizontal_iff_fixed_volume
#print axioms GppYorkReduction.reduction_domain_forces_fixed_volume
#print axioms GppYorkReduction.york_reduction_iff_volume_level
#print axioms GppYorkReduction.no_unconstrained_york_reduction

#print axioms GppYorkReduction.adm_york_null_forces_fixed_volume
#print axioms GppYorkReduction.adm_fixed_volume_implies_york_null

#print axioms GppYorkReduction.york_form_representative_invariant

#print axioms GppYorkReduction.york_generator_preserves_volume
#print axioms GppYorkReduction.york_quotient_pairing_well_defined
