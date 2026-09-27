import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import GppVerify.QuantumInformation.TransposeNotCompletelyPositive
import GppVerify.StandardModel.UniversalNotFidelity
import GppVerify.CelestialHolography.CelestialShadowHelicity

/-!
# The Half-Flip Proposition: Antimatter as the Unitary Shadow of CPT
# Lean 4 | GPPVerify
# Author: Daniel Toupin | Golden Physics Project

Source: half_flip_proposition_v11.tex

## What is formalized here

Lemma 2.1 (antiunitary conjugation is unitary composed with transpose, on
Hermitian inputs): for A = U∘K antiunitary (U unitary, K entrywise complex
conjugation) and ρ a Hermitian density operator, A ρ A⁻¹ = U ρ̄ Uᴴ, where ρ̄
is the entrywise conjugate of ρ; since ρ is Hermitian, ρ̄ = ρᵀ, so this
equals U ρᵀ Uᴴ. The whole content reduces to the one fact that a Hermitian
matrix's entrywise conjugate is its transpose, proved below
(`hermitian_map_star_eq_transpose`), from which the displayed identity
(`antiunitary_conj_eq_unitary_transpose`) follows immediately.

A new operational theorem separates two statements that are often conflated.
The transpose/antiunitary action cannot be enacted on an unknown qubit state by
itself as a completely positive quantum channel.  But if both the state and the
measurement frame are transposed, every Born trace pairing is unchanged.  Thus
there is no contradiction between the no-enactment theorem and the statement
that a globally conjugated description of the entire experiment is operationally
indistinguishable.

Proposition 4.1(a) (Wigner time reversal is the universal spin inverter):
on ℂ², T(ψ₁,ψ₂) = (conj ψ₂, -conj ψ₁) is exactly i·σy·K. Proved: ⟨ψ,Tψ⟩ = 0
identically (`wignerT_orthogonal`), and T² = -1 (`wignerT_wignerT`).

Proposition 2.2 (No-Enactment), for `d = 2`, is imported from the actual
Choi-matrix / complete-positivity development and exposed below as a substantive
theorem rather than the former `True` placeholder.

Proposition 4.1(c) is now formalized algebraically without a Bloch-sphere parametrization.
The exact Pauli identity
`Σᵢ σᵢ A σᵢ = 2 Tr(A) I - A` gives the equal-Pauli channel
`E(ρ) = (2I-ρ)/3` for every trace-one qubit state.  If `ρ²=ρ`, then the overlap
with the orthogonal projector `I-ρ` is exactly `2/3`.
-/

namespace GppHalfFlip

open scoped ComplexConjugate

/-- A Hermitian matrix's entrywise complex conjugate equals its transpose:
    the algebraic fact underlying Lemma 2.1. -/
theorem hermitian_map_star_eq_transpose {d : Type*} [Fintype d] [DecidableEq d]
    (ρ : Matrix d d ℂ) (hρ : ρ.IsHermitian) :
    ρ.map (starRingEnd ℂ) = ρ.transpose := by
  ext i j
  have h : Matrix.conjTranspose ρ j i = ρ j i := by rw [hρ]
  simp only [Matrix.conjTranspose_apply, RCLike.star_def] at h
  simpa only [Matrix.map_apply, Matrix.transpose_apply] using h

/-- Lemma 2.1: antiunitary conjugation of a Hermitian density operator is
    unitary conjugation of its transpose. -/
theorem antiunitary_conj_eq_unitary_transpose {d : Type*} [Fintype d] [DecidableEq d]
    (U ρ : Matrix d d ℂ) (hρ : ρ.IsHermitian) :
    U * ρ.map (starRingEnd ℂ) * Matrix.conjTranspose U
      = U * ρ.transpose * Matrix.conjTranspose U := by
  rw [hermitian_map_star_eq_transpose ρ hρ]

/-- **Paired-frame observational invariance for a qubit.**  Transposing only the
state is the non-CP operation appearing in `no_enactment`.  Transposing both the
state and the observable leaves the trace pairing exactly unchanged.  This is
the finite-dimensional algebraic core of the distinction between trying to enact
an antiunitary on a subsystem and conjugating the description of the entire
experiment. -/
theorem paired_transpose_trace_invariant
    (rho observable : GppUniversalNot.QMat) :
    GppUniversalNot.tr2 (rho.transpose * observable.transpose) =
      GppUniversalNot.tr2 (rho * observable) := by
  simp [GppUniversalNot.tr2, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_two]
  ring

/-- Wigner time reversal T = i σ_y K on ℂ², in components:
    T(ψ₁,ψ₂) = (conj ψ₂, -conj ψ₁). -/
def wignerT (ψ1 ψ2 : ℂ) : ℂ × ℂ := (conj ψ2, -conj ψ1)

/-- Proposition 4.1(a), part 1: ⟨ψ,Tψ⟩ = 0 identically -- T maps every
    state to one orthogonal to it. -/
theorem wignerT_orthogonal (ψ1 ψ2 : ℂ) :
    conj ψ1 * (wignerT ψ1 ψ2).1 + conj ψ2 * (wignerT ψ1 ψ2).2 = 0 := by
  simp only [wignerT]
  ring

/-- Proposition 4.1(a), part 2: T² = -1. -/
theorem wignerT_wignerT (ψ1 ψ2 : ℂ) :
    wignerT (wignerT ψ1 ψ2).1 (wignerT ψ1 ψ2).2 = (-ψ1, -ψ2) := by
  simp only [wignerT, map_neg, ← RCLike.star_def, star_star]

/-- Celestial shadow reverses the spin/helicity representation label exactly.
    This is the clean observable label exchange already certified independently
    in the celestial-shadow development. -/
theorem shadow_reverses_celestial_spin
    (w : GppCelestialShadowHelicity.Weights) :
    GppCelestialShadowHelicity.Weights.spin
        (GppCelestialShadowHelicity.Weights.shadow w) =
      -GppCelestialShadowHelicity.Weights.spin w :=
  GppCelestialShadowHelicity.Weights.spin_shadow w

/-- **Proposition 2.2 (No-Enactment), d = 2.**  The transpose map on
`M₂(ℂ)` is not completely positive.  This is the operational obstruction behind
trying to enact an antiunitary/transpose operation as a quantum channel.
`GppVerify/QuantumInformation/ChoiMatrix.lean` builds the Choi-matrix /
complete-positivity framework (forward direction of Choi's theorem), and
`GppVerify/QuantumInformation/TransposeNotCompletelyPositive.lean` proves
Choi(transpose) = SWAP and concludes non-complete-positivity. What remains open
is the *general* `d`-dimensional statement (antisymmetric subspace of dimension
`d(d-1)/2`) and the converse of Choi's theorem (not needed here). Verified
numerically for d = 2..5 in the companion script. -/
theorem no_enactment :
    ¬ GppChoiMatrix.CompletelyPositive GppHalfFlipMatrix.transposeMap :=
  GppHalfFlipMatrix.transposeMap_not_completelyPositive

/-- Proposition 4.1(c), exact finite-dimensional form.  For a normalized pure qubit
projector `ρ`, the equal mixture of the three Pauli conjugations has fidelity exactly
`2/3` with the orthogonal projector `I-ρ`. -/
theorem universal_not_fidelity
    (rho : GppUniversalNot.QMat)
    (htr : GppUniversalNot.tr2 rho = 1)
    (hpure : rho * rho = rho) :
    GppUniversalNot.tr2 ((1 - rho) * GppUniversalNot.universalNot rho) = (2 : ℂ) / 3 :=
  GppUniversalNot.universalNot_orthogonal_fidelity rho htr hpure

end GppHalfFlip

#print axioms GppHalfFlip.paired_transpose_trace_invariant
#print axioms GppHalfFlip.shadow_reverses_celestial_spin
#print axioms GppHalfFlip.no_enactment
#print axioms GppHalfFlip.universal_not_fidelity
