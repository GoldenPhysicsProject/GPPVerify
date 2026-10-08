import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The abstract growth lemma: a bounded exponential sum has no growing exponent

The unification target of the RH map (`CLAUDE_RH_MAP.md` §3, item 10b): routes R1 (translation orbit),
R3 (cutoff length) and R15 (Gaussian orbit) all reduce to a statement of the form "a finite sum
`Σ c_k e^{λ_k s}` with `c_k ≠ 0` stays bounded on `s ≥ 0`, hence no exponent has positive real part".

`bounded_exp_sum_re_nonpos`: for distinct complex exponents `λ_k`, nonzero complex coefficients `c_k`, if
`‖Σ_k c_k e^{λ_k s}‖ ≤ M` for all real `s ≥ 0`, then `Re λ_k ≤ 0` for every `k`.

The proof needs no mean-value or Cesàro argument. Sampling the sum at `s, s+t, …, s+(n−1)t` gives
`Σ_k (c_k e^{λ_k s}) z_k^j` with nodes `z_k = e^{λ_k t}`, which are distinct for small `t`; the Vandermonde
matrix is therefore invertible, so each term `c_k e^{λ_k s}` is a fixed linear image of the bounded sample
vector, hence bounded; and `|c_k| e^{Re λ_k s}` bounded forces `Re λ_k ≤ 0`.

## Scope

A finite-sum lemma. The *infinite* sums over zeros in the RH criteria need an additional approximation step
(which is where Landau's lemma and the positivity of the coefficients enter), and nothing here locates a zero
of zeta. A one-sided bound with real exponents and a negative coefficient is **not** enough (`−e^s ≤ 0`), which
is why the lemma bounds the norm. No RH claim.
-/

open Complex Matrix Real

namespace GppExpSumGrowth

variable {n : ℕ}

/-- Nodes `e^{λ_k t}` are distinct for small `t > 0` when the exponents are. -/
theorem exists_small_t (l : Fin n → ℂ) (hl : Function.Injective l) :
    ∃ t : ℝ, 0 < t ∧ Function.Injective (fun k => Complex.exp (l k * t)) := by
  set B : ℝ := ∑ k, |(l k).im| + 1 with hB
  have hBpos : 0 < B := by
    have : 0 ≤ ∑ k, |(l k).im| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hpi := Real.pi_pos
  obtain ⟨t0, ht0def⟩ : ∃ t0 : ℝ, t0 = Real.pi / (2 * B) := ⟨_, rfl⟩
  have ht : 0 < t0 := by rw [ht0def]; positivity
  refine ⟨t0, ht, ?_⟩
  intro j k hjk
  simp only at hjk
  rw [Complex.exp_eq_exp_iff_exists_int] at hjk
  obtain ⟨m, hm⟩ := hjk
  have him := congrArg Complex.im hm
  simp at him
  have hjle : |(l j).im| ≤ ∑ k, |(l k).im| :=
    Finset.single_le_sum (f := fun k => |(l k).im|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have hkle : |(l k).im| ≤ ∑ k, |(l k).im| :=
    Finset.single_le_sum (f := fun k => |(l k).im|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
  have hdiff : |(l j).im - (l k).im| ≤ 2 * B := by
    have := abs_sub (l j).im (l k).im
    linarith
  have h1 : ((l j).im - (l k).im) * t0 = m * (2 * Real.pi) := by linarith [him]
  have h2 : |((l j).im - (l k).im) * t0| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos ht]
    calc |(l j).im - (l k).im| * t0 ≤ (2 * B) * t0 := mul_le_mul_of_nonneg_right hdiff ht.le
      _ = Real.pi := by rw [ht0def]; field_simp
  rw [h1, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at h2
  have hmabs : |(m : ℝ)| ≤ 1 / 2 := by nlinarith [abs_nonneg (m : ℝ)]
  have hm0 : m = 0 := by
    have : |(m : ℝ)| < 1 := by linarith
    have h3 : |m| < 1 := by exact_mod_cast this
    have := abs_lt.mp h3
    omega
  subst hm0
  apply hl
  have ht' : (t0 : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have : l j * (t0 : ℂ) = l k * (t0 : ℂ) := by simpa using hm
  exact mul_right_cancel₀ ht' this

/-- **A bounded exponential sum has no exponent with positive real part.** -/
theorem bounded_exp_sum_re_nonpos (c l : Fin n → ℂ) (hc : ∀ k, c k ≠ 0)
    (hl : Function.Injective l) (M : ℝ)
    (hM : ∀ s : ℝ, 0 ≤ s → ‖∑ k, c k * Complex.exp (l k * s)‖ ≤ M) : ∀ k, (l k).re ≤ 0 := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 le_rfl)
  obtain ⟨t, ht, hz⟩ := exists_small_t l hl
  set z : Fin n → ℂ := fun k => Complex.exp (l k * t) with hzdef
  have hdet : (Matrix.vandermonde z).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hz
  set A : Matrix (Fin n) (Fin n) ℂ := (Matrix.vandermonde z).transpose with hA
  have hAdet : IsUnit A.det := by
    rw [hA, Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr hdet
  -- the continuous linear map `v ↦ A⁻¹ v`
  let L : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := Matrix.mulVecLin A⁻¹
  let Lc : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap L
  obtain ⟨C, hCpos, hC⟩ := Lc.bound
  -- sample vector and the coefficient vector
  have hsample : ∀ s : ℝ, 0 ≤ s →
      (fun j : Fin n => ∑ k, c k * Complex.exp (l k * ((s + j * t : ℝ) : ℂ))) =
        A *ᵥ (fun k => c k * Complex.exp (l k * s)) := by
    intro s hs
    funext j
    simp only [Matrix.mulVec, dotProduct, hA, Matrix.transpose_apply, Matrix.vandermonde_apply, hzdef]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : Complex.exp (l k * ((s + j * t : ℝ) : ℂ)) =
        Complex.exp (l k * s) * (Complex.exp (l k * t)) ^ (j : ℕ) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; push_cast; ring
    rw [e]; ring
  intro k
  by_contra hpos
  push Not at hpos
  have hbound : ∀ s : ℝ, 0 ≤ s → ‖c k‖ * Real.exp ((l k).re * s) ≤ C * M := by
    intro s hs
    have hF : ‖(fun j : Fin n => ∑ k, c k * Complex.exp (l k * ((s + j * t : ℝ) : ℂ)))‖ ≤ M := by
      refine (pi_norm_le_iff_of_nonneg hM0).mpr fun j => ?_
      have := hM (s + j * t) (by positivity)
      simpa using this
    set b : Fin n → ℂ := fun k => c k * Complex.exp (l k * s) with hb
    have hbA : b = A⁻¹ *ᵥ (fun j : Fin n => ∑ k, c k * Complex.exp (l k * ((s + j * t : ℝ) : ℂ))) := by
      rw [hsample s hs, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAdet, Matrix.one_mulVec]
    have hLb : Lc (fun j : Fin n => ∑ k, c k * Complex.exp (l k * ((s + j * t : ℝ) : ℂ))) = b := by
      rw [hbA]; rfl
    have h1 : ‖b‖ ≤ C * M := by
      rw [← hLb]
      exact (hC _).trans (mul_le_mul_of_nonneg_left hF hCpos.le)
    have h2 : ‖b k‖ ≤ ‖b‖ := norm_le_pi_norm b k
    have h3 : ‖b k‖ = ‖c k‖ * Real.exp ((l k).re * s) := by
      simp [hb, norm_mul, Complex.norm_exp]
    linarith
  -- contradiction with `Re l_k > 0`
  have hck : 0 < ‖c k‖ := norm_pos_iff.mpr (hc k)
  set r := (l k).re
  have hpos' : 0 < ‖c k‖ * r := mul_pos hck hpos
  obtain ⟨s, hs⟩ : ∃ s : ℝ, C * M < ‖c k‖ * r * s := by
    refine ⟨(C * M + 1) / (‖c k‖ * r), ?_⟩
    rw [mul_div_cancel₀ _ hpos'.ne']; linarith
  have hs0 : 0 ≤ s := by
    by_contra hneg; push Not at hneg
    have : ‖c k‖ * r * s < 0 := mul_neg_of_pos_of_neg hpos' hneg
    have : 0 ≤ C * M := mul_nonneg hCpos.le hM0
    linarith
  have := hbound s hs0
  have hexp : r * s + 1 ≤ Real.exp (r * s) := by linarith [Real.add_one_le_exp (r * s)]
  nlinarith [mul_le_mul_of_nonneg_left hexp hck.le]

end GppExpSumGrowth
