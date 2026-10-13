import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# A Haar square is of positive type but need not be reflection positive

Source: Codex, GPP-bridge PR #11 comment 6139438663 and
`work/codex/2026-10-13_haar_lc_affine_modular_os_criterion.md`, testing Daniel Toupin's proposal
that Haar measure on a locally compact group is the missing structural principle.

On the group `ℤ` with counting (Haar) measure, every finitely supported autocorrelation
`C(n) = Σ_k u(k) u(k+n)` is **of positive type**: `Σᵢⱼ vᵢ vⱼ C(pᵢ − pⱼ) ≥ 0` for any points and
weights (`autocorr_posType`). For `u = δ₀ + c δ₁`, `C = (1+c²)δ₀ + c(δ₁ + δ₋₁)` (`C_zero`, `C_one`,
`C_two`). Yet its **reflected** (OS/Hankel) form `[C(tᵢ + tⱼ)]` at times `t = (0, 1)` takes the value
`−c²(1+c²) < 0` (`hankel_witness`). The bilateral transform factors as
`F(z) = (1 + c e^{z})(1 + c e^{−z})` (`transform_factor`). It is `|1 + c e^{iτ}|² ≥ 0` on the
imaginary axis, but for `c > 0` it vanishes at `z₀ = −log c + iπ`, which lies off the axis when
`c ≠ 1` (`transform_zero_off_axis`).

So the missing arithmetic law cannot be "any Haar square". It has to be **reflected** positivity
of the actual signed prime–Archimedean `W`. That is RH-strength and is not assumed here. Codex's
smooth two-Gaussian version (determinant `≈ −4`) and the adelic affine group
`𝔸 ⋊ 𝔸^×` (left Haar `|a|⁻¹ db d^×a`, modular `Δ = |a|⁻¹`) are not formalized. **No RH claim.**
-/

namespace GppNoGo.HaarSquareNotReflection

open Finset

/-- The autocorrelation `C(n) = Σ_{k ∈ S} u(k) u(k+n)` of a sequence supported in `S`. -/
def autocorr (S : Finset ℤ) (u : ℤ → ℝ) (n : ℤ) : ℝ := ∑ k ∈ S, u k * u (k + n)

/-- **Haar squares are of positive type** on `ℤ`. -/
theorem autocorr_posType (S : Finset ℤ) (u : ℤ → ℝ) (hu : ∀ k ∉ S, u k = 0) {N : ℕ}
    (p : Fin N → ℤ) (v : Fin N → ℝ) :
    0 ≤ ∑ i, ∑ j, v i * v j * autocorr S u (p i - p j) := by
  set T : Finset ℤ := univ.biUnion (fun i => S.map (Equiv.addRight (p i)).toEmbedding)
  have hshift : ∀ i j, autocorr S u (p i - p j) = ∑ m ∈ T, u (m - p i) * u (m - p j) := by
    intro i j
    have hsub : S.map (Equiv.addRight (p i)).toEmbedding ⊆ T :=
      subset_biUnion_of_mem (fun i => S.map (Equiv.addRight (p i)).toEmbedding) (mem_univ i)
    rw [autocorr, ← sum_subset hsub]
    · rw [sum_map]
      refine sum_congr rfl (fun k _ => ?_)
      simp only [Equiv.coe_toEmbedding, Equiv.coe_addRight]
      congr 2 <;> ring
    · intro m _ hm
      have : m - p i ∉ S := by
        intro h
        apply hm
        rw [mem_map]
        exact ⟨m - p i, h, by simp⟩
      rw [hu _ this, zero_mul]
  simp_rw [hshift, mul_sum]
  have hswap : ∑ i, ∑ j, ∑ m ∈ T, v i * v j * (u (m - p i) * u (m - p j))
      = ∑ m ∈ T, ∑ i, ∑ j, v i * v j * (u (m - p i) * u (m - p j)) := by
    calc ∑ i, ∑ j, ∑ m ∈ T, v i * v j * (u (m - p i) * u (m - p j))
        = ∑ i, ∑ m ∈ T, ∑ j, v i * v j * (u (m - p i) * u (m - p j)) :=
          sum_congr rfl (fun i _ => sum_comm)
      _ = _ := sum_comm
  rw [hswap]
  refine sum_nonneg (fun m _ => ?_)
  have hsq : ∑ i, ∑ j, v i * v j * (u (m - p i) * u (m - p j))
      = (∑ i, v i * u (m - p i)) ^ 2 := by
    rw [sq, sum_mul_sum]
    refine sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => ?_))
    ring
  rw [hsq]
  positivity

/-- `u = δ₀ + c δ₁`. -/
def u (c : ℝ) (k : ℤ) : ℝ := if k = 0 then 1 else if k = 1 then c else 0

/-- Its autocorrelation. -/
def C (c : ℝ) : ℤ → ℝ := autocorr {0, 1} (u c)

theorem u_support (c : ℝ) : ∀ k ∉ ({0, 1} : Finset ℤ), u c k = 0 := by
  intro k hk
  simp only [mem_insert, mem_singleton, not_or] at hk
  simp [u, hk.1, hk.2]

theorem C_zero (c : ℝ) : C c 0 = 1 + c ^ 2 := by
  simp [C, autocorr, u]
  ring

theorem C_one (c : ℝ) : C c 1 = c := by
  simp [C, autocorr, u]

theorem C_two (c : ℝ) : C c 2 = 0 := by
  simp [C, autocorr, u]

/-- `C` is of positive type (it is a Haar square). -/
theorem C_posType (c : ℝ) {N : ℕ} (p : Fin N → ℤ) (v : Fin N → ℝ) :
    0 ≤ ∑ i, ∑ j, v i * v j * C c (p i - p j) :=
  autocorr_posType _ _ (u_support c) p v

/-- **The reflected (Hankel) form is negative**: at times `t = (0, 1)` and weights
`(c, −(1+c²))`, `Σ vᵢ vⱼ C(tᵢ + tⱼ) = −c²(1+c²)`. -/
theorem hankel_witness (c : ℝ) :
    c * c * C c 0 + 2 * (c * (-(1 + c ^ 2))) * C c 1 + (-(1 + c ^ 2)) * (-(1 + c ^ 2)) * C c 2
      = -(c ^ 2 * (1 + c ^ 2)) := by
  rw [C_zero, C_one, C_two]
  ring

theorem hankel_neg {c : ℝ} (hc : c ≠ 0) :
    c * c * C c 0 + 2 * (c * (-(1 + c ^ 2))) * C c 1 + (-(1 + c ^ 2)) * (-(1 + c ^ 2)) * C c 2
      < 0 := by
  rw [hankel_witness]
  have : 0 < c ^ 2 := by positivity
  nlinarith

/-- The bilateral transform factors: `F(z) = (1 + c e^{z})(1 + c e^{−z})`. -/
theorem transform_factor (c : ℝ) (z : ℂ) :
    (1 + c ^ 2 : ℂ) + c * (Complex.exp z + Complex.exp (-z))
      = (1 + c * Complex.exp z) * (1 + c * Complex.exp (-z)) := by
  have h : Complex.exp z * Complex.exp (-z) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  linear_combination (-(c : ℂ) ^ 2) * h

/-- **Off-axis zero**: for `c > 0`, `1 + c e^{z₀} = 0` at `z₀ = −log c + iπ`, with
`Re z₀ = −log c ≠ 0` when `c ≠ 1`. -/
theorem transform_zero_off_axis {c : ℝ} (hc : 0 < c) :
    1 + (c : ℂ) * Complex.exp (-(Real.log c : ℂ) + Real.pi * Complex.I) = 0 := by
  rw [Complex.exp_add, Complex.exp_pi_mul_I, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
    Real.exp_neg, Real.exp_log hc]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  push_cast
  field_simp
  ring

theorem off_axis {c : ℝ} (hc : 0 < c) (hc1 : c ≠ 1) :
    (-(Real.log c : ℂ) + Real.pi * Complex.I).re ≠ 0 := by
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, neg_ne_zero]
  intro h
  exact hc1 (Real.eq_one_of_pos_of_log_eq_zero hc h)

end GppNoGo.HaarSquareNotReflection
