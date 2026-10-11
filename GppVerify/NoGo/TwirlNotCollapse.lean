import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Gauge invariance of a state does not give collapse onto singlets

Source: Codex, 2026-10-11 (GPP-bridge
`work/codex/2026-10-11_arithmetic_prime_bulk_boundary_qft_mass_gap.md`, §E "Chapter 11
Haar/collapse missing step"). This is a **correction to *On the Nature of Nature*, Chapter 11
(§§11.5–11.6)**, which derives measurement collapse and Born's rule from Haar averaging over
the gauge group.

There are two different Haar averages:
* the state twirl `T(ρ) = ∫ U(g) ρ U(g)* dg`, and
* the singlet projector `P = ∫ U(g) dg`.

Gauge invariance `T(ρ) = ρ` does **not** imply `ρ = PρP`. Here is the exact `U(1)`
counterexample on `ℂ²`. Let `U_θ = diag(1, e^{iθ})` and let `ρ = |e₂⟩⟨e₂|`, a charged pure
state.

* `twirl_rho`: `ρ` is invariant under every `U_θ`, so its twirl is `ρ`.
* `singletProj_eq`: the normalised Haar integral `(1/2π)∫₀^{2π} U_θ dθ` is `diag(1, 0)`.
* `collapse_fails`: `PρP = 0 ≠ ρ`.

So collapse cannot be derived as singlet projection from gauge invariance alone. Codex's
constructive replacement, Born probabilities from the GNS representation of a positive state
(`ω(P) = ‖π(P)Ω‖²`), is a separate, standard theorem and is not formalized here.
-/

namespace GppNoGo.TwirlNotCollapse

open Complex Matrix Real

/-- The `U(1)` representation `diag(1, e^{iθ})` on `ℂ²`. -/
noncomputable def U (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, exp (θ * I)]

/-- The charged pure state `|e₂⟩⟨e₂|`. -/
def rho : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]

/-- The normalised Haar average `(1/2π) ∫₀^{2π} U_θ dθ`, taken entrywise. -/
noncomputable def singletProj : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => (1 / (2 * π) : ℂ) * ∫ θ in (0 : ℝ)..2 * π, U θ i j

/-- `ρ` is invariant under every gauge transformation. -/
theorem twirl_rho (θ : ℝ) : U θ * rho * (U θ)ᴴ = rho := by
  have h : exp (θ * I) * (starRingEnd ℂ) (exp (θ * I)) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U, rho, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, h]

lemma integral_exp_I : ∫ θ in (0 : ℝ)..2 * π, exp (θ * I) = 0 := by
  have h := integral_exp_mul_complex (a := 0) (b := 2 * π) (c := I) I_ne_zero
  simp only [mul_comm I] at h
  rw [h]
  have h2 : exp (((2 * π : ℝ) : ℂ) * I) = 1 := by
    push_cast; exact Complex.exp_two_pi_mul_I
  rw [h2]; simp

/-- **The Haar average of `U` is the singlet projector `diag(1, 0)`.** -/
theorem singletProj_eq : singletProj = !![1, 0; 0, 0] := by
  have hπ : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  ext i j
  fin_cases i <;> fin_cases j
  · simp [singletProj, U]; field_simp
  · simp [singletProj, U]
  · simp [singletProj, U]
  · simp [singletProj, U, integral_exp_I]

/-- **No collapse from gauge invariance.** `ρ` is gauge invariant, yet `PρP = 0 ≠ ρ`. -/
theorem collapse_fails :
    (∀ θ : ℝ, U θ * rho * (U θ)ᴴ = rho) ∧
      singletProj * rho * singletProj = 0 ∧ singletProj * rho * singletProj ≠ rho := by
  have h0 : singletProj * rho * singletProj = 0 := by
    rw [singletProj_eq]
    ext i j; fin_cases i <;> fin_cases j <;> simp [rho, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨twirl_rho, h0, ?_⟩
  rw [h0]
  intro h
  have := congrFun (congrFun h 1) 1
  simp [rho] at this

end GppNoGo.TwirlNotCollapse
