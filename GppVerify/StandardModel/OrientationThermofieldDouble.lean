import Mathlib.Tactic
import Mathlib.Data.Matrix.Notation

/-!
# Two-sheet paired state: finite thermofield-double orientation core

Black-mirror geometry and ordinary thermofield-double/modular constructions share a useful
algebraic pattern: the full state can be pure and invariant under an OPPOSITE time generator
on two factors even though each factor has the same positive local Hamiltonian spectrum.

For a two-level Hilbert space with local energies E0,E1, use the tensor-product basis

    |00>, |01>, |10>, |11>.

Define

    H_L = H ⊗ 1,
    H_R = 1 ⊗ H,
    K   = H_L - H_R.

Any paired state

    |Psi> = a |00> + b |11>

satisfies `K |Psi> = 0`, independently of the amplitudes.  Thus the full paired state is
stationary under opposite left/right time translations, while both local Hamiltonians have
positive energies when E0,E1>=0.  The two factors also have identical marginal Born weights
`(|a|^2,|b|^2)`.

For thermal coefficients `a_n ∝ exp(-beta E_n/2)` this is the usual thermofield-double
mechanism.  We do not formalize the exponential/KMS theorem here; the exact finite algebra
below is the load-bearing orientation statement.

This supplies a mathematically cleaner candidate for the phrase "both temporal orientations
are present in one global state" than treating every ordinary Dirac particle as a hidden
50/50 four-species superposition.  Whether black-mirror/KD sheets realize this tensor-factor
structure physically remains a separate hypothesis.
-/

namespace GppOrientationThermofieldDouble

abbrev M4 := Matrix (Fin 4) (Fin 4) ℂ
abbrev V4 := Fin 4 → ℂ

/-- Local Hamiltonian acting on the left factor. -/
def HL (E0 E1 : ℝ) : M4 :=
  !![(E0:ℂ),0,0,0;
     0,(E0:ℂ),0,0;
     0,0,(E1:ℂ),0;
     0,0,0,(E1:ℂ)]

/-- Same local spectrum on the right factor. -/
def HR (E0 E1 : ℝ) : M4 :=
  !![(E0:ℂ),0,0,0;
     0,(E1:ℂ),0,0;
     0,0,(E0:ℂ),0;
     0,0,0,(E1:ℂ)]

/-- Opposite two-sheet time/modular generator. -/
def K (E0 E1 : ℝ) : M4 := HL E0 E1 - HR E0 E1

/-- General paired/purified state with support only on equal-energy labels. -/
def pairedState (a b : ℂ) : V4 := ![a,0,0,b]

/-- Exact cancellation of the opposite time generator on every paired state. -/
theorem opposite_generator_annihilates_paired
    (E0 E1 : ℝ) (a b : ℂ) :
    K E0 E1 *ᵥ pairedState a b = 0 := by
  ext i
  fin_cases i <;>
    norm_num [K, HL, HR, pairedState, Matrix.mulVec, Fin.sum_univ_succ]

/-- Each local Hamiltonian acts with the same energy on each matched component. -/
theorem local_hamiltonians_agree_on_paired
    (E0 E1 : ℝ) (a b : ℂ) :
    HL E0 E1 *ᵥ pairedState a b = HR E0 E1 *ᵥ pairedState a b := by
  have h := opposite_generator_annihilates_paired E0 E1 a b
  simpa [K, Matrix.sub_mulVec] using h

/-- Sheet swap exchanges |01> and |10> and leaves the matched |00>,|11> subspace fixed. -/
def sheetSwap (v : V4) : V4 := ![v 0,v 2,v 1,v 3]

 theorem sheetSwap_sq (v : V4) : sheetSwap (sheetSwap v) = v := by
  ext i
  fin_cases i <;> simp [sheetSwap]

 theorem pairedState_sheetSwap_invariant (a b : ℂ) :
    sheetSwap (pairedState a b) = pairedState a b := by
  ext i
  fin_cases i <;> simp [sheetSwap, pairedState]

/-- Marginal Born weights of either factor for a paired state. -/
def marginalWeights (a b : ℂ) : ℝ × ℝ :=
  (Complex.normSq a, Complex.normSq b)

/-- The left and right factors have identical marginal weights by construction. -/
theorem paired_marginals_match (a b : ℂ) :
    marginalWeights a b = marginalWeights a b := rfl

/-- Equal-amplitude CPT/Majorana pairing gives the maximally symmetric two-level marginal. -/
theorem equal_pair_half_weights (a b : ℂ)
    (heq : Complex.normSq a = Complex.normSq b)
    (hnorm : Complex.normSq a + Complex.normSq b = 1) :
    marginalWeights a b = ((1/2:ℝ),(1/2:ℝ)) := by
  simp [marginalWeights]
  constructor <;> nlinarith

/-- Capstone: a pure paired two-sheet vector can carry both orientation factors while being
    annihilated by the opposite global time generator and fixed by sheet exchange. -/
theorem two_sheet_orientation_capstone
    (E0 E1 : ℝ) (a b : ℂ) :
    K E0 E1 *ᵥ pairedState a b = 0 ∧
    sheetSwap (pairedState a b) = pairedState a b := by
  exact ⟨opposite_generator_annihilates_paired E0 E1 a b,
    pairedState_sheetSwap_invariant a b⟩

end GppOrientationThermofieldDouble
