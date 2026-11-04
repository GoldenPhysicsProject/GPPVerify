import Mathlib.Tactic

/-!
# *Which Way Is Forward?*: a half flip is not the spin-deck element — the anti-linear case

Source: Daniel Toupin, *Which Way Is Forward?* (v26), Proposition
`prop:halfnotdeck` ("A half flip is not the spin-deck element"): there is no
invertible linear **or anti-linear** map `U` from the four-lift carrier to a
spinor carrier satisfying `U R_t = δ U`, where `δ = -I` is the spin-cover deck
transformation. The linear case is on main as
`GppWhichWayV26.half_flip_not_deck` (in `WhichWayForwardV26Gaps`); this module
adds the anti-linear case, which that file's scope note left open.

An anti-linear map is written `v ↦ M *ᵥ star v` for a matrix `M` over `ℂ`;
it is invertible iff `M` is a unit. Since `R_t` has real entries, conjugation
passes through it, so the anti-linear identity collapses to the same matrix
equation as the linear case, `M * R_t = -M`, and invertibility of `M` reduces
it to `R_t = -1` — false, since `R_t` has `0` in the `(0, 0)` entry (it fixes
the nonzero vector `(1, 1, 0, 0)` and swaps the first two lifts).

Scope: the four-lift carrier with the label basis `++, +-, -+, --`, exactly
the paper's finite statement. The identification of `δ` with the scalar `-I`
on the spinor carrier is the paper's input, as in the linear case.
-/

namespace GppWhichWayForwardDeck

open Matrix

/-- The temporal half flip `|q,t⟩ ↦ |q,−t⟩` on the basis `++, +−, −+, −−`.
The same matrix as `GppWhichWayV26.Rt` on main. -/
def Rt : Matrix (Fin 4) (Fin 4) ℂ := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

/-- Conjugation passes through matrix-vector multiplication. -/
theorem star_mulVec (A : Matrix (Fin 4) (Fin 4) ℂ) (v : Fin 4 → ℂ) :
    star (A *ᵥ v) = (A.map star) *ᵥ star v := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Pi.star_apply, Matrix.map_apply, star_sum, star_mul]
  apply Finset.sum_congr rfl
  intro x _
  exact mul_comm _ _

/-- `R_t` has real entries, so entrywise conjugation fixes it. -/
theorem map_star_Rt : Rt.map star = Rt := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rt, Matrix.map_apply]

/-- Two matrices that agree under `*ᵥ` on every vector are equal. -/
theorem matrix_ext_of_mulVec {A B : Matrix (Fin 4) (Fin 4) ℂ}
    (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq] using h1

/-- **A half flip is not the spin-deck element (anti-linear case).** There is
no anti-linear map `v ↦ M *ᵥ star v`, with `M` invertible, satisfying
`U R_t = -U` as operators. -/
theorem half_flip_not_deck_antilinear :
    ¬ ∃ M : Matrix (Fin 4) (Fin 4) ℂ, IsUnit M ∧
      ∀ v : Fin 4 → ℂ, M *ᵥ star (Rt *ᵥ v) = -(M *ᵥ star v) := by
  rintro ⟨M, hM, h⟩
  have hmat : M * Rt = -M := by
    apply matrix_ext_of_mulVec
    intro w
    have hw := h (star w)
    rw [star_mulVec, map_star_Rt] at hw
    simp only [star_star] at hw
    rw [← Matrix.mulVec_mulVec]
    rw [Matrix.neg_mulVec]
    exact hw
  have hR : Rt = -1 := by
    have h2 := congrArg (fun X => M⁻¹ * X) hmat
    simp only [← Matrix.mul_assoc, Matrix.mul_neg] at h2
    rwa [Matrix.nonsing_inv_mul M ((Matrix.isUnit_iff_isUnit_det M).mp hM),
      Matrix.one_mul] at h2
  have h3 := congrFun (congrFun hR 0) 0
  simp [Rt] at h3

end GppWhichWayForwardDeck
