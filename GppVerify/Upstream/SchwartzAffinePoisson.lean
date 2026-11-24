/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Poisson summation over a shifted lattice

Mathlib-only, in Mathlib's naming, for upstreaming.

* `SchwartzMap.affineComp φ N hN ρ`: the Schwartz function `x ↦ φ (ρ + N x)`.
* `SchwartzMap.fourier_affineComp`: its Fourier transform is
  `|N|⁻¹ · 𝐞(ρ k / N) · 𝓕 φ (k / N)`.
* `SchwartzMap.summable_int`: a Schwartz function is summable over `ℤ`.
* `SchwartzMap.tsum_affineComp_eq_tsum_fourier`: for `N > 0` an integer and `ρ ∈ ℝ`,
  `∑_m φ(ρ + N m) = ∑_k N⁻¹ 𝐞(ρ k / N) 𝓕 φ (k / N)`, both sides summable.
-/

open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace SchwartzMap

noncomputable section

/-- The Schwartz function `x ↦ φ(ρ + N x)`. -/
def affineComp (φ : 𝓢(ℝ, ℂ)) (N : ℝ) (hN : N ≠ 0) (ρ : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℂ (g := fun x : ℝ => ρ + N * x)
    (by fun_prop) (by
      refine ⟨1, (1 + |ρ|) / |N|, fun x => ?_⟩
      have hN' : 0 < |N| := abs_pos.2 hN
      rw [pow_one, Real.norm_eq_abs, Real.norm_eq_abs, div_mul_eq_mul_div, le_div_iff₀ hN']
      have h1 : |N| * |x| = |N * x| := (abs_mul _ _).symm
      have h2 : |N * x| ≤ |ρ + N * x| + |ρ| := by
        have := abs_sub (ρ + N * x) ρ
        simpa using this
      have h3 : 0 ≤ |ρ| := abs_nonneg _
      have h4 : 0 ≤ |ρ + N * x| := abs_nonneg _
      rw [mul_comm, h1]
      nlinarith) φ

theorem affineComp_apply (φ : 𝓢(ℝ, ℂ)) (N : ℝ) (hN : N ≠ 0) (ρ x : ℝ) :
    affineComp φ N hN ρ x = φ (ρ + N * x) := rfl

open Real in
theorem fourier_affineComp (φ : 𝓢(ℝ, ℂ)) (N : ℝ) (hN : N ≠ 0) (ρ k : ℝ) :
    𝓕 (affineComp φ N hN ρ) k =
      ((|N|⁻¹ : ℝ) : ℂ) * (𝐞 (ρ * k / N) : ℂ) * 𝓕 φ (k / N) := by
  have e1 : ∀ (ψ : 𝓢(ℝ, ℂ)) (w : ℝ), 𝓕 ψ w = ∫ v : ℝ, (𝐞 (-(v * w)) : ℂ) * ψ v := by
    intro ψ w
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
    simp [Circle.smul_def]
  rw [e1, e1]
  set G : ℝ → ℂ := fun t => (𝐞 (-((t - ρ) * (k / N))) : ℂ) * φ t with hG
  have h1 : ∀ x : ℝ, (𝐞 (-(x * k)) : ℂ) * affineComp φ N hN ρ x = G (ρ + N * x) := by
    intro x
    rw [affineComp_apply, hG]
    simp only
    congr 3
    field_simp
    ring_nf
  simp_rw [h1]
  have h2 := Measure.integral_comp_mul_left (fun t => G (ρ + t)) N
  rw [h2, integral_add_left_eq_self G ρ]
  have h3 : ∀ t : ℝ, G t = (𝐞 (ρ * k / N) : ℂ) * ((𝐞 (-(t * (k / N))) : ℂ) * φ t) := by
    intro t
    rw [hG]
    simp only
    have : -((t - ρ) * (k / N)) = ρ * k / N + -(t * (k / N)) := by ring
    rw [this, Real.fourierChar.map_add_eq_mul]
    push_cast
    ring
  simp_rw [h3, integral_const_mul]
  rw [Complex.real_smul, abs_inv]
  push_cast
  ring

theorem summable_int (φ : 𝓢(ℝ, ℂ)) : Summable (fun n : ℤ => φ n) :=
  summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    ((φ.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)

open Real in
/-- **Poisson summation over a shifted lattice `ρ + Nℤ`.** -/
theorem tsum_affineComp_eq_tsum_fourier (φ : 𝓢(ℝ, ℂ)) (N : ℕ) (hN : N ≠ 0) (ρ : ℝ) :
    Summable (fun m : ℤ => φ (ρ + N * m)) ∧
    Summable (fun k : ℤ => (((N : ℝ)⁻¹ : ℝ) : ℂ) * (𝐞 (ρ * k / N) : ℂ) * 𝓕 φ ((k : ℝ) / N)) ∧
    ∑' m : ℤ, φ (ρ + N * m) =
      ∑' k : ℤ, (((N : ℝ)⁻¹ : ℝ) : ℂ) * (𝐞 (ρ * k / N) : ℂ) * 𝓕 φ ((k : ℝ) / N) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  set F := affineComp φ N hN' ρ with hF
  have hFk : ∀ k : ℤ, 𝓕 F k = (((N : ℝ)⁻¹ : ℝ) : ℂ) * (𝐞 (ρ * k / N) : ℂ) * 𝓕 φ ((k : ℝ) / N) := by
    intro k
    rw [hF, fourier_affineComp, abs_of_nonneg (Nat.cast_nonneg N)]
  have h1 : Summable (fun m : ℤ => φ (ρ + N * m)) := summable_int F
  have h2 : Summable (fun k : ℤ => 𝓕 F k) := summable_int (𝓕 F)
  refine ⟨h1, by simpa [hFk] using h2, ?_⟩
  have := SchwartzMap.tsum_eq_tsum_fourier F 0
  simp only [zero_add, hFk, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at this
  exact this

end

end SchwartzMap
