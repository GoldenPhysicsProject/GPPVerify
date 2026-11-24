import GppVerify.RiemannHypothesis.NymanBeurlingBoundStates

/-!
# The Beurling span is a module over the dilation semigroup

The Beurling function `ρ_θ(x) = {1/(x/θ)} - θ{1/x}` is `(U_{1/θ} - θ)` applied to the single
fractional-part profile `χ(x) = {1/x}`, where `(U_a f)(x) = f(a x)`.  This module proves the
exact composition law

  `ρ_η(θ⁻¹ x) = ρ_{θη}(x) - η ρ_θ(x)`,

so dilating a Beurling function by `x ↦ θ⁻¹ x` stays inside the span of Beurling functions
with parameters in `(0, 1]`.  The span `N` is therefore invariant under the dilation semigroup
`{U_{1/θ} : 0 < θ ≤ 1}`, which is the Lax–Phillips structure behind the bound-state picture:
the orthogonal complement `N^⊥` carries the adjoint semigroup, and the zero-states
`x^{ρ-1}` are its eigenvectors with eigenvalue `θ^{ρ̄}`-type scaling.

* `beurling_dilate`: the composition law.
* `beurlingSpan`: the linear span of `{ρ_θ : 0 < θ ≤ 1}` in `ℝ → ℂ`.
* `dilate_mem_beurlingSpan`: invariance of the span under `f ↦ f(θ⁻¹ ·)`.
* `mellin_beurling_dilate_consistent`: the Mellin symbol of the composition law, with the
  factor `-ζ(s)/s` cancelled, is the identity
  `θ^s (η^s - η) = ((θη)^s - θη) - η (θ^s - θ)`.
-/

open Complex Set GppNymanBeurling

namespace GppBeurlingDilation

/-- **Composition law.** Dilating `ρ_η` by `x ↦ θ⁻¹ x` gives `ρ_{θη} - η ρ_θ`. -/
theorem beurling_dilate (θ η : ℝ) (x : ℝ) :
    beurling η (θ⁻¹ * x) = beurling (θ * η) x - (η : ℂ) * beurling θ x := by
  unfold beurling
  have h : η⁻¹ * (θ⁻¹ * x) = (θ * η)⁻¹ * x := by
    rw [mul_inv, ← mul_assoc, mul_comm η⁻¹ θ⁻¹]
  rw [h]
  push_cast
  ring

/-- The linear span of the Beurling functions `ρ_θ`, `0 < θ ≤ 1`, inside `ℝ → ℂ`. -/
def beurlingSpan : Submodule ℂ (ℝ → ℂ) :=
  Submodule.span ℂ {f | ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ f = beurling θ}

theorem beurling_mem_span {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ 1) : beurling θ ∈ beurlingSpan :=
  Submodule.subset_span ⟨θ, h0, h1, rfl⟩

/-- **Dilation invariance.** For `0 < θ ≤ 1`, `f ↦ f(θ⁻¹ ·)` maps the Beurling span into
itself. -/
theorem dilate_mem_beurlingSpan {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ 1) {f : ℝ → ℂ}
    (hf : f ∈ beurlingSpan) : (fun x => f (θ⁻¹ * x)) ∈ beurlingSpan := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨η, hη0, hη1, rfl⟩ := hg
    have : (fun x => beurling η (θ⁻¹ * x)) = beurling (θ * η) - (η : ℂ) • beurling θ := by
      funext x
      simp [beurling_dilate]
    rw [this]
    exact Submodule.sub_mem _ (beurling_mem_span (mul_pos h0 hη0)
      (mul_le_one₀ h1 hη0.le hη1)) (Submodule.smul_mem _ _ (beurling_mem_span h0 h1))
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul c a _ ha => exact Submodule.smul_mem _ c ha

/-- **Mellin symbol of the composition law.** Dilation multiplies the symbol by `θ^s`, and the
composition law `ρ_η(θ⁻¹ ·) = ρ_{θη} - η ρ_θ` holds at the level of the symbols
`η^s - η` (after the common factor `-ζ(s)/s`). -/
theorem mellin_beurling_dilate_consistent (θ η : ℝ) (hθ : 0 < θ) (hη : 0 < η) (s : ℂ) :
    (θ : ℂ) ^ s * ((η : ℂ) ^ s - η) =
      (((θ * η : ℝ) : ℂ) ^ s - ((θ * η : ℝ) : ℂ)) - η * ((θ : ℂ) ^ s - θ) := by
  push_cast
  rw [Complex.mul_cpow_ofReal_nonneg hθ.le hη.le]
  ring

end GppBeurlingDilation

#print axioms GppBeurlingDilation.beurling_dilate
#print axioms GppBeurlingDilation.dilate_mem_beurlingSpan
#print axioms GppBeurlingDilation.mellin_beurling_dilate_consistent
