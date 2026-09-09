import Mathlib.Tactic
import Mathlib.Data.Matrix.Notation

/-!
# Charged CAR positive-energy quantization: the finite two-mode orientation core

This module is a finite exact model of the standard charged-fermion construction reviewed by
Derezinski--Gerard, `Positive energy quantization of linear dynamics` (2009), Sec. 7.2.
For a nondegenerate charged fermionic dynamics with one-particle generator `b`, the standard
construction sets

    q = sgn b,
    j = i q,
    h = |b|,

so that `b = q h`, the new one-particle complex structure is `j`, and the Fock Hamiltonian
is the positive second quantization of `h`.  Negative-frequency one-particle modes are
quantized with creation/annihilation interchanged.

Here we realize one particle mode and one antiparticle mode explicitly on the four-state
fermionic Fock basis

    |0>, |p>, |a>, |pa>.

The matrices `ap` and `aa` satisfy the two-mode CAR.  The physical operators are

    Q = Np - Na,
    H = eps (Np + Na).

Thus particle and antiparticle have opposite charge but equal positive excitation energy.
The charged field core

    psi = ap + aa^dagger

contains BOTH microscopic frequency orientations: the particle annihilator has commutator
`[H,ap] = -eps ap`, whereas the antiparticle creator has
`[H,aa^dagger] = +eps aa^dagger`.  At the same time both terms have the same field charge,
`[Q,psi] = -psi`.

This is the precise standard-QFT statement closest to the project's intuition that opposite
microscopic temporal/frequency orientations are simultaneously present locally without
implying negative physical energy or a reversed thermodynamic arrow.  It does NOT say that
a one-particle charge eigenstate is a 50/50 superposition of two additional hidden species.
-/

namespace GppChargedCAROrientationFock

abbrev M4C := Matrix (Fin 4) (Fin 4) ℂ

/-- Particle annihilation operator in basis `|0>,|p>,|a>,|pa>`. -/
def ap : M4C :=
  !![0,1,0,0;
     0,0,0,0;
     0,0,0,1;
     0,0,0,0]

/-- Particle creation operator. -/
def apDag : M4C :=
  !![0,0,0,0;
     1,0,0,0;
     0,0,0,0;
     0,0,1,0]

/-- Antiparticle annihilation operator.  The minus sign is the Jordan--Wigner/CAR sign. -/
def aa : M4C :=
  !![0,0,1,0;
     0,0,0,-1;
     0,0,0,0;
     0,0,0,0]

/-- Antiparticle creation operator. -/
def aaDag : M4C :=
  !![0,0,0,0;
     0,0,0,0;
     1,0,0,0;
     0,-1,0,0]

def antiComm (A B : M4C) : M4C := A * B + B * A
def commutator (A B : M4C) : M4C := A * B - B * A

/-- Canonical anticommutator for the particle mode. -/
theorem ap_car_self : antiComm ap apDag = (1 : M4C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [antiComm, ap, apDag, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

/-- Canonical anticommutator for the antiparticle mode. -/
theorem aa_car_self : antiComm aa aaDag = (1 : M4C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [antiComm, aa, aaDag, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

/-- Distinct annihilation modes anticommute. -/
theorem ap_aa_anticommute : antiComm ap aa = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [antiComm, ap, aa, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Particle annihilation also anticommutes with antiparticle creation. -/
theorem ap_aaDag_anticommute : antiComm ap aaDag = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [antiComm, ap, aaDag, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Occupation-number operators. -/
def Np : M4C := apDag * ap
def Na : M4C := aaDag * aa

/-- Physical electric-charge grading in units of the elementary charge. -/
def Q : M4C := Np - Na

/-- Positive Fock Hamiltonian for common one-particle energy `eps`. -/
def H (eps : ℝ) : M4C := (eps : ℂ) • (Np + Na)

/-- Number operators have the expected diagonal form. -/
theorem number_operators_explicit :
    Np = !![0,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,1] ∧
    Na = !![0,0,0,0; 0,0,0,0; 0,0,1,0; 0,0,0,1] := by
  constructor <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Np, Na, ap, apDag, aa, aaDag, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Charge is `0,+1,-1,0` on vacuum, particle, antiparticle and pair states. -/
theorem Q_explicit :
    Q = !![0,0,0,0; 0,1,0,0; 0,0,-1,0; 0,0,0,0] := by
  rcases number_operators_explicit with ⟨hp,ha⟩
  rw [Q, hp, ha]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- The physical Hamiltonian is nonnegative on the basis and gives equal positive energy
    `eps` to particle and antiparticle. -/
theorem H_explicit (eps : ℝ) :
    H eps = !![0,0,0,0;
               0,(eps:ℂ),0,0;
               0,0,(eps:ℂ),0;
               0,0,0,(2*eps:ℂ)] := by
  rcases number_operators_explicit with ⟨hp,ha⟩
  rw [H, hp, ha]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num <;> ring

/-- Standard charged Dirac field core: positive-frequency particle annihilation plus
    negative-frequency antiparticle creation. -/
def psi : M4C := ap + aaDag

/-- Particle annihilation carries the `-eps` Heisenberg frequency. -/
theorem particle_annihilator_frequency (eps : ℝ) :
    commutator (H eps) ap = (-(eps : ℂ)) • ap := by
  rw [H_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [commutator, ap, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- Antiparticle creation carries the opposite `+eps` Heisenberg frequency. -/
theorem antiparticle_creator_frequency (eps : ℝ) :
    commutator (H eps) aaDag = (eps : ℂ) • aaDag := by
  rw [H_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [commutator, aaDag, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- Despite the opposite frequency signs, both pieces of the charged field have the same
    physical field charge. -/
theorem particle_annihilator_charge : commutator Q ap = (-1 : ℂ) • ap := by
  rw [Q_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [commutator, ap, Matrix.mul_apply, Fin.sum_univ_succ]

 theorem antiparticle_creator_charge : commutator Q aaDag = (-1 : ℂ) • aaDag := by
  rw [Q_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [commutator, aaDag, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Therefore the local charged field is a sum of opposite microscopic frequencies while
    transforming with one definite U(1) charge. -/
theorem psi_opposite_frequencies_same_charge (eps : ℝ) :
    commutator (H eps) ap = (-(eps : ℂ)) • ap ∧
    commutator (H eps) aaDag = (eps : ℂ) • aaDag ∧
    commutator Q psi = (-1 : ℂ) • psi := by
  refine ⟨particle_annihilator_frequency eps, antiparticle_creator_frequency eps, ?_⟩
  rw [psi, commutator]
  rw [show Q * (ap + aaDag) - (ap + aaDag) * Q =
      (Q*ap-ap*Q) + (Q*aaDag-aaDag*Q) by noncomm_ring]
  rw [particle_annihilator_charge, antiparticle_creator_charge]
  module

end GppChargedCAROrientationFock
