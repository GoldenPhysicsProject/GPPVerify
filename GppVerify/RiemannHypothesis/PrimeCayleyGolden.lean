import GppVerify.RiemannHypothesis.PrimeCayleyChannel

/-!
# Prime Cayley channel: the τ-anticommutation, the golden point `p = 5`, and Cayley inversion

Source: Codex, `codex.formalization_queue` rows of 2026-10-02 ("Prime mass/TFD/Householder
equivalence", "Operator Cayley functional calculus identities"). Most of both rows is already in
`PrimeCayleyChannel` (GPPVerify #219): `μ_p = 2/√(p−1)`, the entries `q`, `b`, `S(μ)² = I`,
`μ_p = 1 ⟺ p = 5`, and `C = tanh(L/4)`. This file adds the rest.

* `channel_anticomm`: with `τ = [[0, −1], [1, 0]]`, `S(μ) τ = −τ S(μ)`.
* `cayley_five`: `c_5 = (√5 − 1)/(√5 + 1) = φ^{-2}`, with `φ = (1 + √5)/2`.
* `channel_five_golden_eigen`: `S_5 (φ, 1) = (φ, 1)`. This is the golden `+1` eigenline.
* `cayley_inv` and `cayley_diag_inv`: `A = (1 − C)/(1 + C)` when `C = (1 − A)/(1 + A)`, for a
  scalar and for a finite diagonal operator (entrywise, `A_i > 0`). That is the finite-diagonal
  case the queue row asks for first. The general self-adjoint functional calculus is not
  formalized.

Checked by hand; no corrections. As recorded with #219, `p = 5` is singled out by the
normalization `μ = 2/√(p−1)`, not by arithmetic.

## Scope

`2 × 2` real algebra and scalar/diagonal Cayley inversion. No RH content.
-/

open Matrix GppPrimeCayley

namespace GppPrimeCayleyGolden

/-- The rotation `τ = [[0, −1], [1, 0]]`. -/
def tau : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- **`S(μ)` anticommutes with `τ`.** -/
theorem channel_anticomm (μ : ℝ) : channel μ * tau = -(tau * channel μ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [channel, dirac, tau, Matrix.mul_apply, Fin.sum_univ_two]

/-- The golden ratio `φ = (1 + √5)/2`. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

lemma sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

/-- **`c_5 = φ^{-2}`.** -/
theorem cayley_five : (Real.sqrt 5 - 1) / (Real.sqrt 5 + 1) = (phi ^ 2)⁻¹ := by
  have hs : 0 < Real.sqrt 5 := by positivity
  have h1 : Real.sqrt 5 + 1 ≠ 0 := by positivity
  have h2 : phi ≠ 0 := by unfold phi; positivity
  rw [inv_eq_one_div, div_eq_div_iff h1 (pow_ne_zero 2 h2), phi]
  nlinarith [sqrt5_sq]

/-- **The golden `+1` eigenline.** `S_5 (φ, 1) = (φ, 1)`. -/
theorem channel_five_golden_eigen : channel 1 *ᵥ ![phi, 1] = ![phi, 1] := by
  have hs : 0 < Real.sqrt 5 := by positivity
  have h4 : Real.sqrt (1 + 4) = Real.sqrt 5 := by norm_num
  ext i; fin_cases i <;>
    simp [channel, dirac, Matrix.mulVec, dotProduct, Fin.sum_univ_two, phi] <;> rw [h4] <;>
    field_simp <;> nlinarith [sqrt5_sq]

/-- **Scalar Cayley inversion.** If `C = (1 − A)/(1 + A)` with `A > 0`, then `A = (1 − C)/(1 + C)`. -/
theorem cayley_inv (A : ℝ) (hA : 0 < A) :
    (1 - (1 - A) / (1 + A)) / (1 + (1 - A) / (1 + A)) = A := by
  have h : 1 + A ≠ 0 := by linarith
  field_simp
  ring

/-- **Finite diagonal Cayley inversion** (entrywise on a positive diagonal). -/
theorem cayley_diag_inv {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    (fun i => (1 - (1 - a i) / (1 + a i)) / (1 + (1 - a i) / (1 + a i))) = a := by
  funext i; exact cayley_inv (a i) (ha i)

end GppPrimeCayleyGolden
