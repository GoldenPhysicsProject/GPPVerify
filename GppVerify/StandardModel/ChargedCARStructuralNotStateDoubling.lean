import Mathlib.Tactic
import Mathlib.Data.Matrix.Notation
import GppVerify.StandardModel.ChargedCAROrientationFock
import GppVerify.StandardModel.ChargedCARComplexOrientationNoGo

/-!
# Standard charged CAR realizes relative orientation structurally, not as four particle species

Two results now have to be kept together.

1. Standard positive-energy charged-CAR quantization really does contain two complex
   orientations `I` and `J` with relative product `q=-IJ`; the local charged field contains
   opposite microscopic frequency signs while the Fock Hamiltonian is positive.

2. The standard theory does NOT contain an additional four-dimensional `(++,+-,-+,--)`
   particle label.  The original complex structure `I` is scalar multiplication by `i`, so
   a nonzero complex-linear deck operation reversing `I` is impossible.  The simultaneous
   `(I,J)->(-I,-J)` relation is naturally anti-linear/conjugate.

This file also records that ordinary gauge-invariant/global charge-preserving operators can
distinguish the particle and antiparticle charge sectors.  What is unobservable is therefore
not the RELATIVE charge `q`; what lacks an independent state label in standard CAR is the
absolute sign choice of the two complex structures themselves.
-/

namespace GppChargedCARStructuralNotStateDoubling

open GppChargedCAROrientationFock
open GppChargedCARComplexOrientationNoGo

/-- Projectors onto the one-particle and one-antiparticle Fock basis states. -/
def Pparticle : M4C := !![0,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,0]
def Pantiparticle : M4C := !![0,0,0,0; 0,0,0,0; 0,0,1,0; 0,0,0,0]

/-- Both charge-sector projectors commute with the global charge operator and are therefore
    compatible with U(1) charge superselection/gauge invariance at this finite-mode level. -/
theorem charge_projectors_commute_Q :
    commutator Q Pparticle = 0 ∧ commutator Q Pantiparticle = 0 := by
  rw [Q_explicit]
  constructor <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [commutator, Pparticle, Pantiparticle,
        Matrix.mul_apply, Fin.sum_univ_succ]

/-- They are nevertheless distinct observables/operators.  Gauge invariance does not identify
    particle with antiparticle. -/
theorem particle_antiparticle_projectors_distinct : Pparticle ≠ Pantiparticle := by
  intro h
  have h11 := congrArg (fun M : M4C => M 1 1) h
  norm_num [Pparticle, Pantiparticle] at h11

/-- The local charged field still contains both opposite Heisenberg frequency signs. -/
theorem local_field_has_both_frequency_orientations (eps : ℝ) :
    commutator (H eps) ap = (-(eps : ℂ)) • ap ∧
    commutator (H eps) aaDag = (eps : ℂ) • aaDag := by
  exact ⟨particle_annihilator_frequency eps, antiparticle_creator_frequency eps⟩

/-- But a nonzero complex-linear deck flip of the actual scalar complex orientation does not
    exist. -/
theorem no_nonzero_internal_absolute_orientation_flip
    (D : M2) (hrev : D * phaseI = -(phaseI * D)) : D = 0 :=
  complex_linear_orientation_reversal_forces_zero D hrev

/-- Capstone: the standard charged-CAR structure simultaneously supports opposite local
    frequency components and distinct physical charge sectors, while forbidding the proposed
    absolute-orientation reversal as a nontrivial complex-linear internal gauge operation. -/
theorem standard_CAR_orientation_capstone (eps : ℝ) :
    commutator (H eps) ap = (-(eps : ℂ)) • ap ∧
    commutator (H eps) aaDag = (eps : ℂ) • aaDag ∧
    commutator Q Pparticle = 0 ∧
    commutator Q Pantiparticle = 0 ∧
    Pparticle ≠ Pantiparticle := by
  rcases charge_projectors_commute_Q with ⟨hp,ha⟩
  exact ⟨particle_annihilator_frequency eps, antiparticle_creator_frequency eps,
    hp, ha, particle_antiparticle_projectors_distinct⟩

end GppChargedCARStructuralNotStateDoubling
