import Mathlib.Tactic
import GppVerify.StandardModel.FourOrientationGaugeProjection
import GppVerify.StandardModel.ChargedCAROrientationFock

/-!
# Bridge from the diagonal four-lift quotient to the charged CAR one-particle sector

The diagonal-even four-lift states have the exact form

  physicalLift a b = (a,b,b,a),

so they carry only two complex amplitudes. The charged two-mode CAR model has
one-particle subspace

  a |p> + b |a> = (0,a,b,0)

inside the Fock basis |0>,|p>,|a>,|pa>.

This file exhibits the explicit linear identification between those two
two-dimensional spaces and checks that the orientation grading chi becomes the
standard Fock charge grading Q, while either microscopic half flip becomes
particle/antiparticle exchange.

This is an exact finite intertwiner. It does not prove that the orientation
labels are the microscopic origin of electric charge; that remains a physical
representation/dynamics question.
-/

namespace GppOrientationCARBridge

open Matrix

open GppFourOrientationGaugeProjection
open GppChargedCAROrientationFock

/-- Charged-CAR one-particle vector with particle amplitude a and antiparticle amplitude b. -/
def oneParticleVec (a b : ℂ) : Fin 4 → ℂ :=
  ![0, a, b, 0]

/-- Coefficient map from the diagonal-even orientation representative to the
one-particle CAR sector. We state it on its two independent amplitudes. -/
def bridge (a b : ℂ) : Fin 4 → ℂ := oneParticleVec a b

/-- The orientation matter basis goes to the CAR particle basis vector. -/
theorem bridge_matter_basis :
    bridge 1 0 = ![0,1,0,0] := by
  rfl

/-- The orientation antimatter basis goes to the CAR antiparticle basis vector. -/
theorem bridge_antimatter_basis :
    bridge 0 1 = ![0,0,1,0] := by
  rfl

/-- On the diagonal-even quotient, chi acts by (a,b) -> (a,-b). -/
theorem chi_on_physicalLift (a b : ℂ) :
    chi (physicalLift a b) = physicalLift a (-b) := by
  simp [chi, physicalLift]

/-- The standard CAR charge matrix acts on the one-particle sector by the same grading. -/
theorem Q_on_oneParticleVec (a b : ℂ) :
    Q *ᵥ oneParticleVec a b = oneParticleVec a (-b) := by
  rw [Q_explicit]
  funext i
  fin_cases i <;>
    norm_num [oneParticleVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Capstone intertwiner: orientation chi becomes the standard particle/antiparticle
charge grading on the CAR one-particle sector. -/
theorem bridge_intertwines_chi_with_Q (a b : ℂ) :
    Q *ᵥ bridge a b = bridge a (-b) := by
  exact Q_on_oneParticleVec a b

/-- Either orientation half flip exchanges the two physical amplitudes. -/
theorem halfFlip_on_physicalLift (a b : ℂ) :
    chargeFlip (physicalLift a b) = physicalLift b a ∧
    temporalFlip (physicalLift a b) = physicalLift b a := by
  constructor <;> rfl

/-- Particle-antiparticle exchange on the CAR one-particle subspace. -/
def exchangeOneParticle (a b : ℂ) : Fin 4 → ℂ :=
  oneParticleVec b a

/-- The bridge sends either orientation half flip to particle/antiparticle exchange. -/
theorem bridge_halfFlip_is_exchange (a b : ℂ) :
    bridge b a = exchangeOneParticle a b := by
  rfl

/-- The positive CAR Hamiltonian gives the same positive excitation energy to both
orientation sectors after the bridge. -/
theorem H_on_oneParticleVec (eps : ℝ) (a b : ℂ) :
    H eps *ᵥ oneParticleVec a b =
      oneParticleVec ((eps : ℂ) * a) ((eps : ℂ) * b) := by
  rw [H_explicit]
  funext i
  fin_cases i <;>
    norm_num [oneParticleVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- Hence the matter and antimatter basis vectors are degenerate in positive energy. -/
theorem equal_particle_antiparticle_energy (eps : ℝ) :
    H eps *ᵥ bridge 1 0 = (eps : ℂ) • bridge 1 0 ∧
    H eps *ᵥ bridge 0 1 = (eps : ℂ) • bridge 0 1 := by
  constructor
  · rw [bridge, H_on_oneParticleVec]
    funext i
    fin_cases i <;> norm_num [bridge, oneParticleVec]
  · rw [bridge, H_on_oneParticleVec]
    funext i
    fin_cases i <;> norm_num [bridge, oneParticleVec]

end GppOrientationCARBridge
