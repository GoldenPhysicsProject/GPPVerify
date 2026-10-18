import GppVerify.GeneralRelativity.YorkVolumeSymplectic
import GppVerify.CelestialHolography.FubiniStudyOrientation
import Mathlib.Tactic

/-!
# Fubini--Study phase quotient and York-volume orthogonality

The projective-state phase quotient and the York-volume hyperplane
must not be conflated. Both are formalized, together with the exact
conditional bridge made available by a boundary/bulk identification
of symplectic forms.

Sources:
* Belin--Lewkowycz--Sarosi, JHEP 03 (2019) 044, volume from York symplectic pairing.
* Jacobson--Visser, SciPost Phys. 7 (2019) 079, causal-diamond volume work.
* Existing GPPVerify CP^1 antipodal Fubini--Study orientation modules.

The equality of boundary Fubini--Study and bulk gravitational symplectic
forms is a *named hypothesis* (true in particular holographic settings),
not proved for arbitrary QFTs, gravity backgrounds or causal diamonds.

No `sorry`, custom `axiom`, or trivial `True` placeholders.
-/

namespace GppFSYorkBridge

open scoped BigOperators

section RayQuotient
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Horizontal projection determined by a normalized complex line
and an explicit complex-linear amplitude functional. -/
def horizontal (L : E →ₗ[ℂ] ℂ) (psi x : E) : E :=
  x - (L x) • psi

theorem horizontal_amplitude_zero
    (L : E →ₗ[ℂ] ℂ) (psi x : E) (hpsi : L psi = 1) :
    L (horizontal L psi x) = 0 := by
  simp [horizontal, map_sub, map_smul, hpsi]

/-- The overall complex-line direction is removed by projectivization. -/
theorem horizontal_scalar_ray_zero
    (L : E →ₗ[ℂ] ℂ) (psi : E) (z : ℂ)
    (hpsi : L psi = 1) :
    horizontal L psi (z • psi) = 0 := by
  simp [horizontal, map_smul, hpsi]

/-- Adding a multiple of the same ray does not change the horizontal tangent. -/
theorem horizontal_shift_invariant
    (L : E →ₗ[ℂ] ℂ) (psi x : E) (z : ℂ)
    (hpsi : L psi = 1) :
    horizontal L psi (x + z • psi) = horizontal L psi x := by
  calc
    horizontal L psi (x + z • psi) =
        (x + z • psi) - (L x + z) • psi := by
          simp [horizontal, map_add, map_smul, hpsi]
    _ = horizontal L psi x := by
          rw [add_smul]
          unfold horizontal
          abel

end RayQuotient

section FSOrientation

/-- The antipodal involution on CP^1 preserves the unsigned FS measure
and reverses the oriented two-form: both Jacobian factors are essential. -/
theorem antipodal_even_measure_odd_symplectic (r : ℝ) (hr : 0 < r) :
    (GppFubiniStudy.fsDensity r⁻¹ * (1 / r ^ 2) =
       GppFubiniStudy.fsDensity r) ∧
    (GppFubiniStudy.fsDensity r⁻¹ * (-(1 / r ^ 2)) =
       -GppFubiniStudy.fsDensity r) := by
  exact ⟨GppFSOrientation.antipodal_unsigned_measure_invariant r hr,
         GppFSOrientation.antipodal_oriented_form_anti_invariant r hr⟩

end FSOrientation

section SymplecticBridge
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Kähler compatibility and York Hamiltonian volume law imply the
precise FS tangent-hyperplane characterization. Scalar normalization
and the boundary-bulk symplectic identification are explicit. -/
theorem volume_hyperplane_eq_fs_orthogonal
    (g omega : E → E → ℝ) (J : E → E)
    (y : E) (dV : E → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hKahler : ∀ x z, omega x z = g (J x) z)
    (hYork : ∀ z, omega y z = c * dV z)
    (delta : E) :
    dV delta = 0 ↔ g (J y) delta = 0 := by
  constructor
  · intro hv
    calc
      g (J y) delta = omega y delta := (hKahler y delta).symm
      _ = c * dV delta := hYork delta
      _ = 0 := by rw [hv]; ring
  · intro hg
    have hs : c * dV delta = 0 := by
      calc
        c * dV delta = omega y delta := (hYork delta).symm
        _ = g (J y) delta := hKahler y delta
        _ = 0 := hg
    exact (mul_eq_zero.mp hs).resolve_left hc

/-- For variations satisfying the gravitational first law dS = k dV
with k nonzero, FS orthogonality and entropy stationarity coincide. -/
theorem fs_orthogonality_eq_entropy_stationarity
    (g omega : E → E → ℝ) (J : E → E)
    (y : E) (dV dS : E → ℝ) (c k : ℝ)
    (hc : c ≠ 0) (hk : k ≠ 0)
    (hKahler : ∀ x z, omega x z = g (J x) z)
    (hYork : ∀ z, omega y z = c * dV z)
    (hEntropy : ∀ z, dS z = k * dV z)
    (delta : E) :
    dS delta = 0 ↔ g (J y) delta = 0 := by
  have hvol := volume_hyperplane_eq_fs_orthogonal
     g omega J y dV c hc hKahler hYork delta
  constructor
  · intro hs
    have hkv : k * dV delta = 0 := by rw [← hEntropy delta]; exact hs
    apply hvol.mp
    exact (mul_eq_zero.mp hkv).resolve_left hk
  · intro hg
    have hv := hvol.mpr hg
    rw [hEntropy delta, hv]
    ring

end SymplecticBridge

section NoGo

/-- Normalization of a quantum-state tangent cannot *by itself* imply
vanishing of an independently variable spatial-volume response. -/
theorem normalized_state_tangent_with_nonzero_volume :
    ∃ (dp : Fin 2 → ℝ) (dV : ℝ),
      (∑ i, dp i) = 0 ∧ dV ≠ 0 := by
  refine ⟨(fun i => if i = 0 then 1 else -1), 1, ?_, by norm_num⟩
  simp [Fin.sum_univ_two]

end NoGo

end GppFSYorkBridge

#print axioms GppFSYorkBridge.horizontal_amplitude_zero
#print axioms GppFSYorkBridge.horizontal_scalar_ray_zero
#print axioms GppFSYorkBridge.horizontal_shift_invariant
#print axioms GppFSYorkBridge.volume_hyperplane_eq_fs_orthogonal
#print axioms GppFSYorkBridge.fs_orthogonality_eq_entropy_stationarity
#print axioms GppFSYorkBridge.normalized_state_tangent_with_nonzero_volume
