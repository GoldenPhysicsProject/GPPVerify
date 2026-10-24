import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# One spectral atom: the Toeplitz and Hankel pieces complete to rank-one squares

Source: Codex, GPP-bridge PR #11 comment 6382027722. Turbo's Wave 310 confirmed (PR #11
6382194036) that this is the mechanism behind the Wave 308 γ₁ D/C near-cancellation, with
`|m| = 2A₁` in both channels and `α = 1.7γ₁`. Daniel Toupin / Golden Physics Project, with AI
assistance from Codex (statement), Turbo (identification) and Claude Code (formalization).

**Hypotheses** (labelled, as Codex asks): one real spectral atom at frequency `ω` with real
weight `m`, and a common phase `α`, so `D_ij = m cos(ω(i − j))` and `C_ij = m cos(ω(i + j) + 2α)`
on indices `i, j ∈ Fin K`. For a real vector `v` put `a = ∑ v_j cos(ωj + α)` and
`b = ∑ v_j sin(ωj + α)`, so that `W = e^{iα} ∑ v_j e^{iωj} = a + ib`.

* `toeplitz_form`: `vᵀ D v = m (a² + b²) = m |W|²`.
* `hankel_form`: `vᵀ C v = m (a² − b²) = m Re(W²)`.
* `add_form`, `sub_form`: `vᵀ (D + C) v = 2m a²` and `vᵀ (D − C) v = 2m b²`.
* `add_form_nonneg`, `sub_form_nonneg`: both are `≥ 0` when `m ≥ 0`, for every `v` and every `K`,
  although `D` and `C` separately have norm of order `K` and `C` is indefinite.

**Scope.** Finite-dimensional algebra only. It does not identify the Wave 305/306/308 blocks with
`D` and `C` (that block identification is Turbo's), says nothing about the remaining
continuous or other-atomic spectrum, and gives no uniform positivity. No claim about RH.
-/

open Finset Real

namespace GppAtomSquare

variable {K : ℕ}

/-- The cosine coordinate `a = ∑ v_j cos(ωj + α)`. -/
noncomputable def cosCoord (ω α : ℝ) (v : Fin K → ℝ) : ℝ := ∑ j, v j * cos (ω * j + α)

/-- The sine coordinate `b = ∑ v_j sin(ωj + α)`. -/
noncomputable def sinCoord (ω α : ℝ) (v : Fin K → ℝ) : ℝ := ∑ j, v j * sin (ω * j + α)

/-- The Toeplitz quadratic form `∑ v_i v_j m cos(ω(i − j))`. -/
noncomputable def toeplitzForm (m ω : ℝ) (v : Fin K → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * v j * (m * cos (ω * ((i : ℝ) - j)))

/-- The Hankel quadratic form `∑ v_i v_j m cos(ω(i + j) + 2α)`. -/
noncomputable def hankelForm (m ω α : ℝ) (v : Fin K → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * v j * (m * cos (ω * ((i : ℝ) + j) + 2 * α))

lemma sq_coord (f : ℝ → ℝ) (ω α : ℝ) (v : Fin K → ℝ) :
    (∑ j, v j * f (ω * j + α)) ^ 2 =
      ∑ i, ∑ j, v i * v j * (f (ω * i + α) * f (ω * j + α)) := by
  rw [sq, sum_mul_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

/-- **Toeplitz piece.** `vᵀ D v = m (a² + b²)`. -/
theorem toeplitz_form (m ω α : ℝ) (v : Fin K → ℝ) :
    toeplitzForm m ω v = m * (cosCoord ω α v ^ 2 + sinCoord ω α v ^ 2) := by
  rw [cosCoord, sinCoord, sq_coord cos, sq_coord sin, ← sum_add_distrib, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  have h : ω * ((i : ℝ) - j) = (ω * i + α) - (ω * j + α) := by ring
  rw [h, cos_sub]
  ring

/-- **Hankel piece.** `vᵀ C v = m (a² − b²)`. -/
theorem hankel_form (m ω α : ℝ) (v : Fin K → ℝ) :
    hankelForm m ω α v = m * (cosCoord ω α v ^ 2 - sinCoord ω α v ^ 2) := by
  rw [cosCoord, sinCoord, sq_coord cos, sq_coord sin, ← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  have h : ω * ((i : ℝ) + j) + 2 * α = (ω * i + α) + (ω * j + α) := by ring
  rw [h, cos_add]
  ring

/-- **`D + C` is a rank-one square.** `vᵀ (D + C) v = 2m a²`. -/
theorem add_form (m ω α : ℝ) (v : Fin K → ℝ) :
    toeplitzForm m ω v + hankelForm m ω α v = 2 * m * cosCoord ω α v ^ 2 := by
  rw [toeplitz_form m ω α, hankel_form]; ring

/-- **`D − C` is a rank-one square.** `vᵀ (D − C) v = 2m b²`. -/
theorem sub_form (m ω α : ℝ) (v : Fin K → ℝ) :
    toeplitzForm m ω v - hankelForm m ω α v = 2 * m * sinCoord ω α v ^ 2 := by
  rw [toeplitz_form m ω α, hankel_form]; ring

theorem add_form_nonneg {m : ℝ} (hm : 0 ≤ m) (ω α : ℝ) (v : Fin K → ℝ) :
    0 ≤ toeplitzForm m ω v + hankelForm m ω α v := by
  rw [add_form]; positivity

theorem sub_form_nonneg {m : ℝ} (hm : 0 ≤ m) (ω α : ℝ) (v : Fin K → ℝ) :
    0 ≤ toeplitzForm m ω v - hankelForm m ω α v := by
  rw [sub_form]; positivity

end GppAtomSquare
