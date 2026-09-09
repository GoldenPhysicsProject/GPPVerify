import Mathlib.Tactic
import Mathlib.Data.Matrix.Notation
import GppVerify.StandardModel.ChargedKahlerRelativeOrientation

/-!
# Charged Kahler dynamics: signed frequency becomes charge, energy stays positive

In the charged Klein-Gordon construction of Gerard-Jaekel, the energy complex structure is
introduced from the real first-order dynamical generator `L` by

    i = j L / |L|.

Since `j^2=-1`, the charged-Kahler charge operator

    q = - i j

is therefore precisely the sign of the dynamical generator:

    q = L / |L|.

Equivalently,

    L = q h,     h = |L| >= 0.

This is the rigorous standard mechanism by which the two signs of the underlying relativistic
frequency generator become particle/antiparticle charge sectors while the physical
one-particle Hamiltonian is positive on BOTH sectors.

The finite standard-form model below takes `h=eps I`, `q=diag(1,-1)`, hence
`L=diag(eps,-eps)`, and proves

    i = j q,
    q = - i j,
    L = q h,

with equal positive Hamiltonian eigenvalue `eps` for the two q sectors.  This sharply
separates a microscopic signed-frequency generator from the thermodynamic arrow.

Prior-art content is standard charged-Kahler/Klein-Gordon theory.  The project's extra
hypothesis, still open, is whether the individual complex orientations themselves admit a
physical diagonal double-cover redundancy whose product alone descends.
-/

namespace GppChargedKahlerDynamicalSign

open GppChargedKahlerRelativeOrientation

/-- Positive one-particle Hamiltonian. -/
def hPos (eps : ℝ) : M2C :=
  !![(eps:ℂ),0;
     0,(eps:ℂ)]

/-- Underlying signed first-order frequency generator `L = Q h`. -/
def signedL (eps : ℝ) : M2C := chargeQ * hPos eps

/-- Explicit signed spectrum `(+eps,-eps)`. -/
theorem signedL_explicit (eps : ℝ) :
    signedL eps = !![(eps:ℂ),0;0,-(eps:ℂ)] := by
  rw [chargeQ_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [signedL, hPos, Matrix.mul_apply, Fin.sum_univ_two]

/-- The positive Hamiltonian is the same on both charge sectors. -/
theorem positive_hamiltonian_both_sectors (eps : ℝ) :
    hPos eps *ᵥ plusState = (eps:ℂ) • plusState ∧
    hPos eps *ᵥ minusState = (eps:ℂ) • minusState := by
  exact ⟨Hamiltonian_plus eps, Hamiltonian_minus eps⟩

/-- The underlying first-order generator retains opposite frequency signs. -/
theorem signed_frequency_sectors (eps : ℝ) :
    signedL eps *ᵥ plusState = (eps:ℂ) • plusState ∧
    signedL eps *ᵥ minusState = -(eps:ℂ) • minusState := by
  rw [signedL_explicit]
  constructor <;>
    ext i <;> fin_cases i <;>
      norm_num [plusState, minusState, Matrix.mulVec, Fin.sum_univ_two]

/-- Energy complex structure equals charge complex structure times dynamical sign:
`i = j q`. -/
theorem energyComplex_eq_chargeComplex_mul_sign :
    dynI = gaugeJ * chargeQ :=
  dynI_eq_gaugeJ_mul_chargeQ

/-- Conversely the dynamical sign/physical charge is the relative product `-i j`. -/
theorem dynamicalSign_eq_relative_complex_orientation :
    chargeQ = -(dynI * gaugeJ) := by
  rfl

/-- Polar form of the dynamics: signed generator = sign times positive magnitude. -/
theorem signedL_eq_charge_times_positive (eps : ℝ) :
    signedL eps = chargeQ * hPos eps := by
  rfl

/-- The sign operator commutes with the positive Hamiltonian. -/
theorem charge_commutes_hPos (eps : ℝ) :
    chargeQ * hPos eps = hPos eps * chargeQ := by
  rw [chargeQ_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hPos, Matrix.mul_apply, Fin.sum_univ_two]

/-- Squaring the signed generator forgets the frequency/charge orientation. -/
theorem signedL_sq (eps : ℝ) :
    signedL eps * signedL eps =
      !![((eps:ℂ)^2),0;0,((eps:ℂ)^2)] := by
  rw [signedL_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end GppChargedKahlerDynamicalSign
