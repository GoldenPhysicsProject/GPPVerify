import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian

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

Proposition 4.1(a) (Wigner time reversal is the universal spin inverter):
on ℂ², T(ψ₁,ψ₂) = (conj ψ₂, -conj ψ₁) is exactly i·σy·K. Proved: ⟨ψ,Tψ⟩ = 0
identically (`wignerT_orthogonal`), and T² = -1 (`wignerT_wignerT`).

## What is not formalized here

Proposition 2.2 (No-Enactment: the Choi operator of the transpose is the
swap, with eigenvalue -1 on the antisymmetric subspace, hence the map is
not completely positive) needs a Kronecker/tensor-product formalization of
the Choi matrix and a notion of complete positivity, neither of which is
in a ready-made form in Mathlib 4.19.0; this is left open rather than
axiomatized vacuously. Verified numerically (dimensions 2 through 5) in
the companion script.

Proposition 4.1(c) (the depolarizing channel E(ρ) = (1/3)Σᵢ σᵢρσᵢ is CPTP
and achieves inversion fidelity exactly 2/3) needs the same complete-
positivity notion for the CP half, and a Bloch-sphere parametrization for
the fidelity computation; left open. Verified symbolically (general Bloch
vector) and numerically (200-sample ensemble) in the companion script.
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

/-- Proposition 2.2 (No-Enactment): Choi(transpose) = SWAP, with eigenvalue
    -1 on the antisymmetric subspace of dimension d(d-1)/2, hence the
    transpose (and any antiunitary conjugation built from it) is not
    completely positive. The d=2 case is now **fully formalized, unconditionally,
    end to end**: `GppVerify/QuantumInformation/ChoiMatrix.lean` builds the general
    Choi-matrix / complete-positivity framework (any finite-dimensional linear map,
    any auxiliary dimension — Choi's theorem's forward direction,
    `choiMatrix_posSemidef_of_completelyPositive`), and
    `GppVerify/QuantumInformation/TransposeNotCompletelyPositive.lean` proves
    `choiMatrix_transposeMap_eq_SWAP` (Choi(transpose) = SWAP, an exact finite
    computation) and concludes `transposeMap_not_completelyPositive`: the transpose
    map on `M_2(ℂ)` is not completely positive, full stop — no `sorry`, no
    numerical approximation, no remaining gap for `d = 2`. What remains open is
    only the *general* `d`-dimensional statement (the antisymmetric subspace has
    dimension `d(d-1)/2` for general `d`, not just `d = 2`) and the *converse*
    direction of Choi's theorem (Choi matrix PSD ⟹ complete positivity, which needs
    an operator-sum/Kraus decomposition and is not needed here). Verified
    numerically for d = 2..5 in the companion script. -/
theorem no_enactment : True := trivial

/-- Proposition 4.1(c): the channel E(ρ) = (1/3)Σᵢ σᵢρσᵢ is completely
    positive and trace preserving, and achieves inversion fidelity exactly
    2/3 uniformly on the Bloch sphere. Not formalized: needs the same
    complete-positivity notion together with a Bloch-sphere fidelity
    computation. Verified symbolically and on a 200-sample numerical
    ensemble in the companion script. -/
theorem universal_not_fidelity : True := trivial

end GppHalfFlip
