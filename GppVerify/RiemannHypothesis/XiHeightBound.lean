import GppVerify.RiemannHypothesis.ThetaHalfWave
import GppVerify.RiemannHypothesis.LogDerivativeZeroFree
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# No zero of `ξ` at height at most `3` in the closed strip

With `ξ(s) = (1 + s(s-1) Λ₀(s)) / 2` (`GppLogDerivZeroFree.xi`) and Riemann's split
`Λ₀(s) = I(s) + I(1-s)`, `I(s) = ∫₁^∞ ψ(x) x^{s/2-1} dx` (`GppThetaSplit`), this file proves

* `norm_I_le`: for `Re s ≤ 2`, `‖I(s)‖ ≤ ψ(1)/π`;
* `psi_one_le`: `ψ(1) ≤ 1/19`;
* `xi_ne_zero_of_abs_im_le`: for `0 ≤ Re s ≤ 1` and `|Im s| ≤ 3`, `ξ(s) ≠ 0`,
  because `‖2ξ(s) - 1‖ = ‖s(s-1) Λ₀(s)‖ ≤ 10 · 2ψ(1)/π < 1`;
* `three_lt_abs_im_of_zeta_zero`: every zero `ρ` of `ζ` with `0 < Re ρ < 1` has `3 < |Im ρ|`.
* `lam_admissible`: for centred coordinates `r = γ + iδ` with `|δ| ≤ 3/4` and `3 < |γ|`, the quartet
  parameter `λ = r²` satisfies `|Im λ| < Re λ` (the hypothesis of `GppQuartetTwoRate`);
* `zeta_zero_admissible`: every zero of `ζ` with `0 < Re ρ < 1` is such a quartet, with
  `|δ| < 1/2`; the same bound `|δ| ≤ 3/4` covers the quarter-shifted product.

The inputs are the theta continuation (`GppThetaSplit`) and the decay of `ψ` (`GppThetaHalfWave`).
The zeros of the quarter-shifted product `ξ(s + 1/4) ξ(s - 1/4)` are the shifts by `∓1/4` of the
zeros of `ξ`, so they have the same imaginary parts and the same height bound `3`.
-/

open Real Complex MeasureTheory Set GppRiemannPhi GppThetaSplit GppThetaHalfWave GppLogDerivZeroFree

namespace GppXiHeight

lemma psi_nonneg (x : ℝ) : 0 ≤ psi x := tsum_nonneg fun _ => (Real.exp_pos _).le

/-- `ψ(x) ≤ ψ(1) e^{-π(x-1)}` for `x ≥ 1`. -/
lemma psi_le {x : ℝ} (hx : 1 ≤ x) : psi x ≤ psi 1 * rexp (-π * (x - 1)) := by
  have h := series_bound (c := fun _ => 1) (k := 0) (fun _ => by simp) hx
  have h1 : psi x ≤ |psi x| := le_abs_self _
  have h2 : ∑' n : ℕ, (π ^ 0 * (((n : ℝ) + 1) ^ (2 * 0) * g n 1)) = psi 1 := by
    simp [psi]
  simp only [one_mul] at h
  rw [h2] at h
  exact h1.trans (by simpa [psi] using h)

/-- `ψ(1) ≤ 1/19`. -/
lemma psi_one_le : psi 1 ≤ 1 / 19 := by
  set r : ℝ := rexp (-3) with hr
  have he : (2.7182818283 : ℝ) < rexp 1 := Real.exp_one_gt_d9
  have h3 : rexp 3 = rexp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h20 : (20 : ℝ) < rexp 3 := by
    rw [h3]
    have : (2.7182818283 : ℝ) ^ 3 < rexp 1 ^ 3 := by
      apply pow_lt_pow_left₀ he (by norm_num) (by norm_num)
    linarith [show (20 : ℝ) < 2.7182818283 ^ 3 by norm_num]
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r ≤ 1 / 20 := by
    rw [hr, Real.exp_neg]
    rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  have hgn : ∀ n : ℕ, g n 1 ≤ r * r ^ n := by
    intro n
    unfold g
    have : rexp (-π * ((n : ℝ) + 1) ^ 2 * 1) ≤ rexp (-3 * ((n + 1 : ℕ) : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      have h2 : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
      push_cast
      nlinarith [Real.pi_gt_three, mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ π - 3 by linarith [Real.pi_gt_three])]
    refine this.trans ?_
    have e : rexp (-3 * ((n + 1 : ℕ) : ℝ)) = r ^ (n + 1) := by
      rw [hr, ← Real.exp_nat_mul]; congr 1; ring
    rw [e]; ring_nf; exact le_refl _
  have hgeo : Summable fun n : ℕ => r * r ^ n :=
    (summable_geometric_of_lt_one hr0.le (by linarith)).mul_left r
  have hsg : Summable fun n : ℕ => g n 1 :=
    Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) hgn hgeo
  calc psi 1 = ∑' n : ℕ, g n 1 := rfl
    _ ≤ ∑' n : ℕ, r * r ^ n := Summable.tsum_le_tsum hgn hsg hgeo
    _ = r * (1 - r)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0.le (by linarith)]
    _ ≤ 1 / 19 := by
      have h1r : 0 < 1 - r := by linarith
      rw [← div_eq_mul_inv, div_le_iff₀ h1r]
      linarith

/-- `‖I(s)‖ ≤ ψ(1)/π` for `Re s ≤ 2`. -/
lemma norm_I_le {s : ℂ} (hs : s.re ≤ 2) : ‖I s‖ ≤ psi 1 / π := by
  have hπ : 0 < π := pi_pos
  have hint : IntegrableOn (fun x : ℝ => psi 1 * rexp π * rexp (-π * x)) (Ioi 1) :=
    (integrableOn_exp_mul_Ioi (by linarith) 1).const_mul _
  have hpt : ∀ x ∈ Ioi (1 : ℝ),
      ‖(x : ℂ) ^ (s / 2 - 1) * (psi x : ℂ)‖ ≤ psi 1 * rexp π * rexp (-π * x) := by
    intro x hx
    have hx1 : (1 : ℝ) < x := hx
    have hx0 : 0 < x := by linarith
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real,
      Real.norm_of_nonneg (psi_nonneg x)]
    have hre : (s / 2 - 1).re ≤ 0 := by
      simp only [Complex.sub_re, Complex.one_re]
      have : (s / 2).re = s.re / 2 := by simp
      rw [this]; linarith
    have hle : x ^ (s / 2 - 1).re ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1.le hre
    calc x ^ (s / 2 - 1).re * psi x ≤ 1 * psi x :=
          mul_le_mul_of_nonneg_right hle (psi_nonneg x)
      _ = psi x := one_mul _
      _ ≤ psi 1 * rexp (-π * (x - 1)) := psi_le hx1.le
      _ = psi 1 * rexp π * rexp (-π * x) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  calc ‖I s‖ ≤ ∫ x in Ioi (1 : ℝ), psi 1 * rexp π * rexp (-π * x) :=
        norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioi).2
          (Filter.Eventually.of_forall hpt))
    _ = psi 1 / π := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 1]
        have : rexp π * (-rexp (-π * 1) / -π) = 1 / π := by
          rw [neg_div_neg_eq, mul_one, ← mul_div_assoc, ← Real.exp_add]
          simp
        rw [mul_assoc, this]; ring

/-- `‖Λ₀(s)‖ ≤ 2ψ(1)/π` for `-1 ≤ Re s ≤ 2`. -/
lemma norm_completedRiemannZeta₀_le {s : ℂ} (h0 : -1 ≤ s.re) (h1 : s.re ≤ 2) :
    ‖completedRiemannZeta₀ s‖ ≤ 2 * (psi 1 / π) := by
  rw [completedRiemannZeta₀_eq_split]
  have a := norm_I_le (s := s) h1
  have b := norm_I_le (s := 1 - s) (by simp; linarith)
  linarith [norm_add_le (I s) (I (1 - s))]

/-- `‖s (s-1)‖ ≤ 10` on `0 ≤ Re s ≤ 1`, `|Im s| ≤ 3`. -/
lemma norm_mul_sub_one_le {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) (him : |s.im| ≤ 3) :
    ‖s * (s - 1)‖ ≤ 10 := by
  have him2 : s.im ^ 2 ≤ 9 := by nlinarith [abs_nonneg s.im, sq_abs s.im]
  have a : ‖s‖ ^ 2 ≤ 10 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith
  have b : ‖s - 1‖ ^ 2 ≤ 10 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; nlinarith
  rw [norm_mul]
  have hprod : (‖s‖ * ‖s - 1‖) ^ 2 ≤ 100 := by
    rw [mul_pow]; nlinarith [norm_nonneg s, norm_nonneg (s - 1)]
  nlinarith [norm_nonneg s, norm_nonneg (s - 1), mul_nonneg (norm_nonneg s) (norm_nonneg (s - 1))]

/-- **Height bound.** `ξ(s) ≠ 0` for `0 ≤ Re s ≤ 1`, `|Im s| ≤ 3`. -/
theorem xi_ne_zero_of_abs_im_le {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) (him : |s.im| ≤ 3) :
    xi s ≠ 0 := by
  intro hx
  have hL := norm_completedRiemannZeta₀_le (s := s) (by linarith) (by linarith)
  have hP := norm_mul_sub_one_le h0 h1 him
  have hψ := psi_one_le
  have hπ := Real.pi_gt_three
  have e : s * (s - 1) * completedRiemannZeta₀ s = -1 := by
    unfold xi at hx
    have : 1 + s * (s - 1) * completedRiemannZeta₀ s = 0 := by
      rcases div_eq_zero_iff.mp hx with h | h
      · exact h
      · norm_num at h
    linear_combination this
  have hn : ‖s * (s - 1) * completedRiemannZeta₀ s‖ = 1 := by rw [e]; simp
  rw [norm_mul] at hn
  have hbound : ‖s * (s - 1)‖ * ‖completedRiemannZeta₀ s‖ ≤ 10 * (2 * (psi 1 / π)) :=
    mul_le_mul hP hL (norm_nonneg _) (by norm_num)
  have hpsi0 := psi_nonneg 1
  have : psi 1 / π ≤ 1 / 19 / 3 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  nlinarith

/-- Every zero of `ζ` with `0 < Re ρ < 1` has `3 < |Im ρ|`. -/
theorem three_lt_abs_im_of_zeta_zero {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) : 3 < |ρ.im| := by
  by_contra hle
  replace hle := not_lt.mp hle
  have hρ0 : ρ ≠ 0 := fun h => by simp [h] at h0
  have hρ1 : ρ ≠ 1 := fun h => by simp [h] at h1
  have hg : Gammaℝ ρ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos h0
  exact xi_ne_zero_of_abs_im_le h0.le h1.le hle (xi_eq_zero_of_zeta_zero hz hρ0 hρ1 hg)

/-- **Admissibility of a quartet.** With centred coordinates `r = γ + iδ` of a zero (`δ` the real
displacement from the line `Re = 1/2`, `γ` the height) and `λ = r²`, the condition
`|Im λ| < Re λ` (that is `|arg λ| < π/4`) holds whenever `|δ| ≤ 3/4` and `3 < |γ|`. -/
theorem lam_admissible {γ δ : ℝ} (hδ : |δ| ≤ 3 / 4) (hγ : 3 < |γ|) :
    |(((γ : ℂ) + δ * Complex.I) ^ 2).im| < (((γ : ℂ) + δ * Complex.I) ^ 2).re := by
  have e1 : (((γ : ℂ) + δ * Complex.I) ^ 2).im = 2 * γ * δ := by
    simp [pow_two]; ring
  have e2 : (((γ : ℂ) + δ * Complex.I) ^ 2).re = γ ^ 2 - δ ^ 2 := by
    simp [pow_two]
  rw [e1, e2]
  have hδ2 : δ ^ 2 ≤ 9 / 16 := by nlinarith [abs_nonneg δ, sq_abs δ]
  have hγ2 : 9 < γ ^ 2 := by nlinarith [abs_nonneg γ, sq_abs γ]
  have hg : |γ| * |δ| ≤ |γ| * (3 / 4) := mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
  have hab : |2 * γ * δ| = 2 * (|γ| * |δ|) := by
    rw [abs_mul, abs_mul, abs_two]; ring
  rw [hab]
  have hγ3 : 3 < |γ| := hγ
  have hsq : γ ^ 2 = |γ| ^ 2 := (sq_abs γ).symm
  nlinarith [abs_nonneg γ, abs_nonneg δ]

/-- Every zero `ρ` of `ζ` with `0 < Re ρ < 1` is an admissible quartet: its centred coordinates
`γ = Im ρ`, `δ = Re ρ - 1/2` satisfy `|Im λ| < Re λ` for `λ = (γ + iδ)²`, and `3 < |γ|`. -/
theorem zeta_zero_admissible {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    3 < |ρ.im| ∧
      |(((ρ.im : ℂ) + (ρ.re - 1 / 2 : ℝ) * Complex.I) ^ 2).im| <
        (((ρ.im : ℂ) + (ρ.re - 1 / 2 : ℝ) * Complex.I) ^ 2).re := by
  have hh := three_lt_abs_im_of_zeta_zero hz h0 h1
  refine ⟨hh, lam_admissible ?_ hh⟩
  rw [abs_le]; constructor <;> linarith

#print axioms lam_admissible
#print axioms zeta_zero_admissible

#print axioms psi_le
#print axioms psi_one_le
#print axioms norm_I_le
#print axioms xi_ne_zero_of_abs_im_le
#print axioms three_lt_abs_im_of_zeta_zero

end GppXiHeight
