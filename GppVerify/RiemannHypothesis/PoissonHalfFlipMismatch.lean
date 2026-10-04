import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Fourier leakage, the spectral-angle bound, and the Poisson support transfer

Source: Codex, GPPDiscovery2 `research/2026-10-03_poisson_half_flip_ccm_step2_bridge.md`,
§§4, 5 (pointwise part), 6, 13 (support part).

* `unitary_mismatch`: for an isometry `U` and `f = Σ a_j f_j` with `f_j` orthonormal and
  `⟨f_i, U f_j⟩ = δ_ij χ_j` (the compressed-operator eigenvector condition), the half-flip mismatch is the
  leakage budget `‖U f − f‖² = 2 Σ |a_j|² (1 − Re χ_j)` (note §4);
* `spectral_angle`: if `A` is symmetric, `A ξ = ε₀ ξ`, `⟨v, A v⟩ ≥ ε₁ ‖v‖²` for `v ⊥ ξ`, and `k` is a unit
  vector with Rayleigh quotient `μ`, then `1 − |⟨ξ, k⟩|² ≤ (μ − ε₀)/(ε₁ − ε₀)` (note §6);
* `strip_kernel_bound`: for `u ∈ [1/λ, λ]` and `|Im z| ≤ η`, `|u^{-iz}| ≤ λ^η` (the pointwise half of note §5);
* `emap_support`: if `f` is supported in `[-λ, λ]` then `Σ_{n≥1} f(n x) = 0` for `x > λ` (the upper half
  of note §13).

## Checks and scope

All four statements check. **Not formalized:** the Poisson identity `𝓔𝓕 = 𝓘𝓔` itself, the
Fourier-fixedness of the Connes–Consani seed, the integral form of the strip estimate (the
Cauchy–Schwarz step with `√(2 log λ)`), the identification of the Weil operator and its simple ground
state, and the quantitative sufficient condition for Step 2 (this note's conditional claim). The note's
open estimate `μ − ε₀ ≲ 𝒬(( 𝓕 − I) h)` is **not** proved and nothing here supports it. No RH claim.
-/

open scoped InnerProductSpace ComplexConjugate

namespace GppPoissonMismatch

section Mismatch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Gram expansion of `⟨Σ a_i f_i, T Σ a_j f_j⟩` for a linear map `T`. -/
theorem inner_expand {ι : Type*} (s : Finset ι) (a : ι → ℂ) (f : ι → E) (T : E →ₗ[ℂ] E) :
    ⟪∑ i ∈ s, a i • f i, T (∑ j ∈ s, a j • f j)⟫_ℂ =
      ∑ i ∈ s, ∑ j ∈ s, conj (a i) * a j * ⟪f i, T (f j)⟫_ℂ := by
  rw [map_sum, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, inner_smul_left, inner_smul_right]
  ring

/-- Diagonal Gram sums collapse to `Σ |a_j|² c_j`. -/
theorem gram_diag {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℂ) (c : ι → ℂ) :
    ∑ i ∈ s, ∑ j ∈ s, conj (a i) * a j * (if i = j then c j else 0) =
      ∑ j ∈ s, ((‖a j‖ ^ 2 : ℝ) : ℂ) * c j := by
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq s i]
  simp only [hi, if_true]
  rw [Complex.conj_mul']
  push_cast; ring

/-- **The half-flip mismatch is the leakage budget.** -/
theorem unitary_mismatch {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℂ) (f : ι → E)
    (χ : ι → ℂ) (U : E →ₗᵢ[ℂ] E)
    (hon : ∀ i ∈ s, ∀ j ∈ s, ⟪f i, f j⟫_ℂ = if i = j then 1 else 0)
    (hU : ∀ i ∈ s, ∀ j ∈ s, ⟪f i, U (f j)⟫_ℂ = if i = j then χ j else 0) :
    ‖U (∑ i ∈ s, a i • f i) - ∑ i ∈ s, a i • f i‖ ^ 2 =
      2 * ∑ j ∈ s, ‖a j‖ ^ 2 * (1 - (χ j).re) := by
  set g : E := ∑ i ∈ s, a i • f i with hg
  have h1 : ‖U g‖ = ‖g‖ := U.norm_map g
  have hgg : ⟪g, g⟫_ℂ = ((∑ j ∈ s, ‖a j‖ ^ 2 : ℝ) : ℂ) := by
    have := inner_expand s a f (LinearMap.id)
    simp only [LinearMap.id_apply] at this
    have h2 := gram_diag s a (fun _ => 1)
    simp only [mul_one] at h2
    rw [hg, this, Complex.ofReal_sum]
    refine Eq.trans ?_ (h2.trans (by simp))
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    rw [hon i hi j hj]
  have hgU : ⟪g, U g⟫_ℂ = ∑ j ∈ s, ((‖a j‖ ^ 2 : ℝ) : ℂ) * χ j := by
    have := inner_expand s a f U.toLinearMap
    simp only [LinearIsometry.coe_toLinearMap] at this
    rw [hg, this, ← gram_diag s a χ]
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    rw [hU i hi j hj]
  have hn : ‖g‖ ^ 2 = ∑ j ∈ s, ‖a j‖ ^ 2 := by
    have h' : ((‖g‖ ^ 2 : ℝ) : ℂ) = ((∑ j ∈ s, ‖a j‖ ^ 2 : ℝ) : ℂ) := by
      rw [← hgg, inner_self_eq_norm_sq_to_K]; norm_cast
    exact Complex.ofReal_injective h'
  have hre : (⟪g, U g⟫_ℂ).re = ∑ j ∈ s, ‖a j‖ ^ 2 * (χ j).re := by
    rw [hgU, Complex.re_sum]
    exact Finset.sum_congr rfl fun j _ => Complex.re_ofReal_mul _ _
  have hsym : RCLike.re ⟪U g, g⟫_ℂ = (⟪g, U g⟫_ℂ).re := by
    rw [← inner_conj_symm (𝕜 := ℂ) g (U g)]; exact Complex.conj_re _
  rw [norm_sub_sq (𝕜 := ℂ) (U g) g, hsym, hre, h1, hn, Finset.mul_sum, Finset.mul_sum]
  have e : ∀ j ∈ s, (2 : ℝ) * (‖a j‖ ^ 2 * (1 - (χ j).re)) =
      ‖a j‖ ^ 2 - 2 * (‖a j‖ ^ 2 * (χ j).re) + ‖a j‖ ^ 2 := fun j _ => by ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- **Spectral-angle bound** (note §6). -/
theorem spectral_angle (A : E →ₗ[ℂ] E) (hA : ∀ x y, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ)
    (ξ k : E) (ε₀ ε₁ : ℝ) (hξ : ‖ξ‖ = 1) (hk : ‖k‖ = 1) (hAξ : A ξ = (ε₀ : ℂ) • ξ)
    (hgap : ∀ v, ⟪ξ, v⟫_ℂ = 0 → ε₁ * ‖v‖ ^ 2 ≤ (⟪v, A v⟫_ℂ).re) :
    (ε₁ - ε₀) * (1 - ‖⟪ξ, k⟫_ℂ‖ ^ 2) ≤ (⟪k, A k⟫_ℂ).re - ε₀ := by
  set c : ℂ := ⟪ξ, k⟫_ℂ with hc
  set w : E := k - c • ξ with hw
  have hxx : ⟪ξ, ξ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hξ]; simp
  have hxw : ⟪ξ, w⟫_ℂ = 0 := by
    rw [hw, inner_sub_right, inner_smul_right, hxx, ← hc]; ring
  have hwx : ⟪w, ξ⟫_ℂ = 0 := by
    rw [← inner_conj_symm, hxw]; simp
  have hkw : k = c • ξ + w := by rw [hw]; abel
  have hAw : ⟪ξ, A w⟫_ℂ = 0 := by
    rw [← hA, hAξ, inner_smul_left, hxw, mul_zero]
  have hwA : ⟪w, A ξ⟫_ℂ = 0 := by
    rw [hAξ, inner_smul_right, hwx, mul_zero]
  have hwA' : ⟪w, (ε₀ : ℂ) • ξ⟫_ℂ = 0 := by rw [inner_smul_right, hwx, mul_zero]
  have e1 : ⟪k, A k⟫_ℂ = conj c * c * (ε₀ : ℂ) + ⟪w, A w⟫_ℂ := by
    conv_lhs => rw [hkw]
    rw [map_add, map_smul, hAξ, inner_add_left, inner_add_right, inner_add_right, inner_smul_left,
      inner_smul_left, inner_smul_right, inner_smul_right, inner_smul_right, hxx, hwA', hAw]
    ring
  have e2 : ⟪k, k⟫_ℂ = conj c * c + ⟪w, w⟫_ℂ := by
    conv_lhs => rw [hkw]
    rw [inner_add_left, inner_add_right, inner_add_right, inner_smul_left, inner_smul_left,
      inner_smul_right, inner_smul_right, hxx, hxw, hwx]
    ring
  have hkk : ‖c‖ ^ 2 + ‖w‖ ^ 2 = 1 := by
    have h := e2
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) k, inner_self_eq_norm_sq_to_K (𝕜 := ℂ) w,
      Complex.conj_mul', hk] at h
    have h' : ((‖c‖ ^ 2 + ‖w‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      push_cast; simpa using h.symm
    exact Complex.ofReal_injective h'
  have hw0 := hgap w hxw
  have hre := congrArg Complex.re e1
  have hre' : (⟪k, A k⟫_ℂ).re = ‖c‖ ^ 2 * ε₀ + (⟪w, A w⟫_ℂ).re := by
    rw [hre, Complex.add_re, Complex.conj_mul']
    have : ((‖c‖ : ℂ) ^ 2 * (ε₀ : ℂ)).re = ‖c‖ ^ 2 * ε₀ := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]; exact Complex.ofReal_re _
    rw [this]
  rw [hre']
  have : ‖c‖ ^ 2 = 1 - ‖w‖ ^ 2 := by linarith
  rw [this]
  nlinarith

end Mismatch

/-- **Pointwise strip bound** (note §5): `|u^{-iz}| ≤ λ^η` for `u ∈ [1/λ, λ]`, `|Im z| ≤ η`. -/
theorem strip_kernel_bound (L η u : ℝ) (hL : 1 ≤ L) (hu : u ∈ Set.Icc L⁻¹ L) (z : ℂ)
    (hz : |z.im| ≤ η) :
    ‖(u : ℂ) ^ (-(Complex.I * z))‖ ≤ L ^ η := by
  have hL0 : 0 < L := by linarith
  have hu0 : 0 < u := lt_of_lt_of_le (inv_pos.mpr hL0) hu.1
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0]
  have hre : (-(Complex.I * z)).re = z.im := by simp
  rw [hre]
  rcases le_total 0 z.im with h | h
  · calc u ^ z.im ≤ L ^ z.im := Real.rpow_le_rpow hu0.le hu.2 h
      _ ≤ L ^ η := Real.rpow_le_rpow_of_exponent_le hL (by rw [abs_of_nonneg h] at hz; exact hz)
  · calc u ^ z.im ≤ (L⁻¹) ^ z.im := Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hL0) hu.1 h
      _ = L ^ (-z.im) := by rw [Real.inv_rpow hL0.le, ← Real.rpow_neg hL0.le]
      _ ≤ L ^ η := Real.rpow_le_rpow_of_exponent_le hL (by rw [abs_of_nonpos h] at hz; exact hz)

/-- **Support transfer** (note §13, upper half): if `f` vanishes outside `[-λ, λ]`, then the E-map sum
`Σ_{n ≥ 1} f(n x)` vanishes for `x > λ`. -/
theorem emap_support (L x : ℝ) (f : ℝ → ℂ) (hf : ∀ y, L < |y| → f y = 0) (hx : L < x) :
    ∑' n : ℕ, f (((n : ℝ) + 1) * x) = 0 := by
  have : ∀ n : ℕ, f (((n : ℝ) + 1) * x) = 0 := by
    intro n
    apply hf
    rcases lt_or_ge L 0 with hL | hL
    · exact lt_of_lt_of_le hL (abs_nonneg _)
    · have hx0 : 0 < x := lt_of_le_of_lt hL hx
      have h1 : x ≤ ((n : ℝ) + 1) * x := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      rw [abs_of_pos (by positivity)]
      linarith
  simp [this]

end GppPoissonMismatch
