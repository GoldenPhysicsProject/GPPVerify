import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import GppVerify.StandardModel.ContactDiracCliffordReduction

/-!
# Uniqueness of the contact-symmetric chirality-mixing mass operator

Let the two contact/twistor halves be graded by

    K = sigma3,

and exchanged by

    E = sigma1.

Consider an arbitrary complex `2x2` operator

    M = [[a,b],[c,d]].

Two natural structural conditions characterize a rest mass coupling:

1. it is chirality-odd, `{M,K}=0`, so it couples opposite chiral halves rather than acting
   separately inside them;
2. it treats the two contact halves symmetrically, `E M E = M`.

The first condition forces `a=d=0`.  The second then forces `b=c`.  Consequently

    M = mu E

for a unique complex scalar `mu`.

Thus the matrix form of the two-state Dirac rest mass is not an arbitrary choice once the
contact doublet, chirality grading, and exchange symmetry are fixed: the only allowed
chirality-mixing symmetric coupling is a scalar multiple of canonical factor exchange.
Physics must still determine the scalar magnitude/phase `mu`; the geometry fixes the
operator direction.
-/

namespace GppUniqueContactMassCoupling

open GppContactDiracCliffordReduction
open GppContactCliffordWeylBridge

/-- General explicit `2x2` operator. -/
def general2 (a b c d : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![a,b;
     c,d]

/-- Chirality-odd condition. -/
def ChiralityOdd (M : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  M * chiralityReduced + chiralityReduced * M = 0

/-- Symmetry under exchange of the two contact halves. -/
def ExchangeSymmetric (M : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  gamma0Reduced * M * gamma0Reduced = M

/-- Anticommuting with chirality forces the diagonal entries to vanish. -/
theorem chiralityOdd_general_iff (a b c d : ℂ) :
    ChiralityOdd (general2 a b c d) ↔ a = 0 ∧ d = 0 := by
  constructor
  · intro h
    unfold ChiralityOdd at h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
    have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) h
    constructor
    · simpa [general2, chiralityReduced, chiralityMatrix,
        Matrix.mul_apply, Fin.sum_univ_two] using h00
    · simpa [general2, chiralityReduced, chiralityMatrix,
        Matrix.mul_apply, Fin.sum_univ_two] using h11
  · rintro ⟨rfl,rfl⟩
    unfold ChiralityOdd
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [general2, chiralityReduced, chiralityMatrix,
        Matrix.mul_apply, Fin.sum_univ_two]

/-- For a purely off-diagonal operator, exchange symmetry forces the two couplings equal. -/
theorem exchangeSymmetric_offdiag_iff (b c : ℂ) :
    ExchangeSymmetric (general2 0 b c 0) ↔ b = c := by
  constructor
  · intro h
    unfold ExchangeSymmetric at h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
    simpa [general2, gamma0Reduced, exchangeMatrix,
      Matrix.mul_apply, Fin.sum_univ_two] using h01
  · intro hbc
    subst c
    unfold ExchangeSymmetric
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [general2, gamma0Reduced, exchangeMatrix,
        Matrix.mul_apply, Fin.sum_univ_two]

/-- Scalar multiple of canonical exchange in coordinates. -/
theorem scalar_exchange_eq_general (mu : ℂ) :
    mu • exchangeMatrix = general2 0 mu mu 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exchangeMatrix, general2]

/-- Main uniqueness theorem: chirality-odd plus exchange-symmetric forces `M=mu E`. -/
theorem unique_chiralityMixing_exchangeSymmetric
    (a b c d : ℂ)
    (hOdd : ChiralityOdd (general2 a b c d))
    (hEx : ExchangeSymmetric (general2 a b c d)) :
    ∃! mu : ℂ, general2 a b c d = mu • exchangeMatrix := by
  have had := (chiralityOdd_general_iff a b c d).1 hOdd
  rcases had with ⟨ha,hd⟩
  subst a
  subst d
  have hbc := (exchangeSymmetric_offdiag_iff b c).1 hEx
  subst c
  refine ⟨b, ?_, ?_⟩
  · rw [scalar_exchange_eq_general]
  · intro mu hmu
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hmu
    simpa [general2, exchangeMatrix] using h01

/-- Conversely every scalar multiple of exchange has both defining structural properties. -/
theorem scalar_exchange_has_mass_symmetries (mu : ℂ) :
    ChiralityOdd (mu • exchangeMatrix) ∧
    ExchangeSymmetric (mu • exchangeMatrix) := by
  constructor
  · rw [scalar_exchange_eq_general]
    exact (chiralityOdd_general_iff 0 mu mu 0).2 ⟨rfl,rfl⟩
  · rw [scalar_exchange_eq_general]
    exact (exchangeSymmetric_offdiag_iff mu mu).2 rfl

end GppUniqueContactMassCoupling
