import GppVerify.QuantumGravity.SinhWeierstrassProduct
import GppVerify.QuantumGravity.StefanBoltzmannFamily
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ZetaValues

/-!
# The cumulant law: `log P(λ) = -Σ_{k≥1}(-1)^{k+1}ζ(2k)λ^{2k}/k`

From `blackbody_law_qg_dtoupin_v1.tex`, Test T5 of `verify_blackbody_capstone.py`
("cumulants are even zeta values"), for `|λ| < 1`. Derived from the Weierstrass product
(`SinhWeierstrassProduct.tendsto_prod_one_add_sq_div`) by taking logarithms and expanding
each factor's `log(1+x)` as its Taylor series, then swapping the resulting double sum.
-/

namespace GppCumulantLaw

open Real Filter Topology GppStefanBoltzmann Finset

/-- `Σ_j 1/(j+1)²` is summable (the Basel series shifted by one index). -/
theorem summable_inv_sq_shift : Summable (fun j : ℕ => 1 / ((j:ℝ) + 1) ^ 2) := by
  have hf : Summable (fun n : ℕ => 1 / (n:ℝ) ^ 2) := hasSum_zeta_two.summable
  have hshift' : Summable (fun j : ℕ => 1 / (((j + 1 : ℕ):ℝ)) ^ 2) :=
    (summable_nat_add_iff 1).mpr hf
  convert hshift' using 2 with j
  push_cast
  ring

/-! ## Step A: `log` of the Weierstrass product is a sum of `log`s -/

theorem hasSum_log_one_add_sq_div {lam : ℝ} (hlam : lam ≠ 0) :
    HasSum (fun j : ℕ => Real.log (1 + lam ^ 2 / ((j:ℝ) + 1) ^ 2))
      (Real.log (Real.sinh (Real.pi * lam) / (Real.pi * lam))) := by
  have hpi : Real.pi * lam ≠ 0 := mul_ne_zero Real.pi_ne_zero hlam
  have hT := (GppSinhWeierstrass.tendsto_prod_one_add_sq_div lam).div_const (Real.pi * lam)
  have hcongr : ∀ n : ℕ, (Real.pi * lam *
      ∏ j ∈ range n, ((1:ℝ) + lam ^ 2 / ((j:ℝ) + 1) ^ 2)) / (Real.pi * lam)
      = ∏ j ∈ range n, ((1:ℝ) + lam ^ 2 / ((j:ℝ) + 1) ^ 2) := by
    intro n
    rw [mul_comm (Real.pi * lam), mul_div_assoc, div_self hpi, mul_one]
  simp_rw [hcongr] at hT
  have hlogcont : Tendsto (fun n : ℕ => Real.log (∏ j ∈ range n, ((1:ℝ) + lam ^ 2 / ((j:ℝ) + 1) ^ 2)))
      atTop (𝓝 (Real.log (Real.sinh (Real.pi * lam) / (Real.pi * lam)))) := by
    have hpos : (0:ℝ) < Real.sinh (Real.pi * lam) / (Real.pi * lam) := by
      rcases hlam.lt_or_gt with h | h
      · have h1 : Real.pi * lam < 0 := by nlinarith [Real.pi_pos]
        have h2 : Real.sinh (Real.pi * lam) < 0 := Real.sinh_neg_iff.mpr h1
        exact div_pos_of_neg_of_neg h2 h1
      · have h1 : (0:ℝ) < Real.pi * lam := by positivity
        have h2 : (0:ℝ) < Real.sinh (Real.pi * lam) := Real.sinh_pos_iff.mpr h1
        exact div_pos h2 h1
    exact (Real.continuousAt_log hpos.ne').tendsto.comp hT
  have hterm_pos : ∀ j : ℕ, (0:ℝ) < 1 + lam ^ 2 / ((j:ℝ) + 1) ^ 2 := by
    intro j; positivity
  have hlogsum : ∀ n : ℕ, Real.log (∏ j ∈ range n, ((1:ℝ) + lam ^ 2 / ((j:ℝ) + 1) ^ 2))
      = ∑ j ∈ range n, Real.log (1 + lam ^ 2 / ((j:ℝ) + 1) ^ 2) := by
    intro n
    exact Real.log_prod (fun j _ => (hterm_pos j).ne')
  simp_rw [hlogsum] at hlogcont
  have hsummable : Summable (fun j : ℕ => Real.log (1 + lam ^ 2 / ((j:ℝ) + 1) ^ 2)) := by
    apply Summable.of_nonneg_of_le
      (fun j : ℕ => Real.log_nonneg
        (by rw [le_add_iff_nonneg_right]; positivity : (1:ℝ) ≤ 1 + lam^2/((j:ℝ)+1)^2))
      (fun j : ℕ => Real.log_le_sub_one_of_pos (hterm_pos j))
    simpa [Pi.div_def] using summable_inv_sq_shift.mul_left (lam^2)
  exact (hsummable.hasSum_iff_tendsto_nat).mpr hlogcont

/-! ## Step B: the Taylor series of each factor's `log(1+x)` -/

/-- The `k`-summand of the cumulant series contributed by loop index `j`:
    `(-1)^k·(λ²/(j+1)²)^{k+1}/(k+1)` (`k` zero-indexed, representing the paper's `k+1 ≥ 1`). -/
noncomputable def term (lam : ℝ) (j k : ℕ) : ℝ :=
  (-1) ^ k * (lam ^ 2 / ((j:ℝ) + 1) ^ 2) ^ (k + 1) / (k + 1)

theorem hasSum_term {lam : ℝ} (hlam : |lam| < 1) (j : ℕ) :
    HasSum (fun k : ℕ => term lam j k) (Real.log (1 + lam ^ 2 / ((j:ℝ) + 1) ^ 2)) := by
  have hx : |(-(lam ^ 2 / ((j:ℝ) + 1) ^ 2))| < 1 := by
    rw [abs_neg, abs_of_nonneg (by positivity)]
    have hj1 : (1:ℝ) ≤ ((j:ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) j]
    have hlam2 : lam ^ 2 < 1 := by
      have := abs_lt.mp hlam
      nlinarith [this.1, this.2]
    calc lam ^ 2 / ((j:ℝ) + 1) ^ 2 ≤ lam ^ 2 / 1 := by
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hj1
      _ = lam ^ 2 := by ring
      _ < 1 := hlam2
  have h := hasSum_pow_div_log_of_abs_lt_one hx
  have hrw1 : (1:ℝ) - (-(lam ^ 2 / ((j:ℝ) + 1) ^ 2)) = 1 + lam ^ 2 / ((j:ℝ) + 1) ^ 2 := by ring
  rw [hrw1] at h
  have h2 := h.neg
  rw [neg_neg] at h2
  have hterm_eq : ∀ n : ℕ, -((-(lam ^ 2 / ((j:ℝ) + 1) ^ 2)) ^ (n + 1) / (n + 1)) = term lam j n := by
    intro n
    unfold term
    rw [neg_pow, pow_succ']
    field_simp
  simp_rw [hterm_eq] at h2
  exact h2

/-! ## Steps C+D: joint summability and the double-sum swap -/

set_option maxHeartbeats 1000000 in
theorem summable_uncurry_term {lam : ℝ} (hlam : |lam| < 1) :
    Summable (Function.uncurry (term lam)) := by
  have hlam2 : lam ^ 2 < 1 := by nlinarith [(abs_lt.mp hlam).1, (abs_lt.mp hlam).2]
  have hgeom : Summable (fun k : ℕ => (lam ^ 2) ^ (k + 1)) := by
    have hg : Summable (fun n : ℕ => (lam ^ 2) ^ n) :=
      summable_geometric_of_lt_one (sq_nonneg lam) hlam2
    have heq : ∀ k : ℕ, (lam ^ 2) ^ (k + 1) = lam ^ 2 * (lam ^ 2) ^ k := fun k => pow_succ' (lam ^ 2) k
    simp_rw [heq]
    exact hg.mul_left (lam ^ 2)
  have hM : Summable (Function.uncurry
      (fun j k : ℕ => (1 / ((j:ℝ) + 1) ^ 2) * (lam ^ 2) ^ (k + 1))) :=
    summable_inv_sq_shift.mul_of_nonneg hgeom (fun j => by positivity) (fun k => by positivity)
  have hle : ∀ p : ℕ × ℕ, |Function.uncurry (term lam) p| ≤
      Function.uncurry (fun j k : ℕ => (1 / ((j:ℝ) + 1) ^ 2) * (lam ^ 2) ^ (k + 1)) p := by
    rintro ⟨j, k⟩
    simp only [Function.uncurry, term]
    have hj1 : (1:ℝ) ≤ ((j:ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) j]
    have hjk : ((j:ℝ) + 1) ^ 2 ≤ (((j:ℝ) + 1) ^ 2) ^ (k + 1) :=
      le_self_pow₀ hj1 (Nat.succ_ne_zero k)
    have hnum : (0:ℝ) ≤ (lam ^ 2 / ((j:ℝ) + 1) ^ 2) ^ (k + 1) := by positivity
    rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg hnum, abs_of_pos (by positivity : (0:ℝ) < ((k:ℝ) + 1))]
    rw [div_pow, div_le_iff₀ (by positivity : (0:ℝ) < ((k:ℝ) + 1))]
    calc (lam ^ 2) ^ (k + 1) / (((j:ℝ) + 1) ^ 2) ^ (k + 1)
        ≤ (lam ^ 2) ^ (k + 1) / ((j:ℝ) + 1) ^ 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) hjk
      _ ≤ (lam ^ 2) ^ (k + 1) / ((j:ℝ) + 1) ^ 2 * ((k:ℝ) + 1) := by
          nlinarith [div_nonneg (pow_nonneg (sq_nonneg lam) (k+1)) (sq_nonneg ((j:ℝ)+1))]
      _ = 1 / ((j:ℝ) + 1) ^ 2 * (lam ^ 2) ^ (k + 1) * ((k:ℝ) + 1) := by ring
  exact Summable.of_abs (Summable.of_nonneg_of_le (fun p => abs_nonneg _) hle hM)

/-- **The cumulant law** (`blackbody_law_qg_dtoupin_v1.tex`, Test T5): for `|λ| < 1`,
    `log P(λ) = -Σ_{k≥1}(-1)^{k+1}ζ(2k)λ^{2k}/k`, presented (equivalently, negated) as
    `-log P(λ) = Σ_{k≥0} (-1)^k ζ(2(k+1)) λ^{2(k+1)}/(k+1)`, `k` zero-indexed. -/
theorem cumulant_law {lam : ℝ} (hlam : |lam| < 1) (hlam0 : lam ≠ 0) :
    HasSum (fun k : ℕ => (-1) ^ k * (∑' j : ℕ, 1 / ((j:ℝ) + 1) ^ (2 * (k + 1))) *
        lam ^ (2 * (k + 1)) / (k + 1))
      (- Real.log (GppStefanBoltzmann.P lam)) := by
  have hSuncurry := summable_uncurry_term hlam
  have hSj : ∀ j : ℕ, Summable (fun k : ℕ => term lam j k) := fun j => (hasSum_term hlam j).summable
  have hSk : ∀ k : ℕ, Summable (fun j : ℕ => term lam j k) :=
    fun k => (hSuncurry.prod_symm).prod_factor k
  have hswap : ∑' k, ∑' j, term lam j k = ∑' j, ∑' k, term lam j k :=
    hSuncurry.tsum_comm
  have hinner : ∀ j : ℕ, ∑' k, term lam j k = Real.log (1 + lam ^ 2 / ((j:ℝ) + 1) ^ 2) :=
    fun j => (hasSum_term hlam j).tsum_eq
  have houter : ∑' j : ℕ, Real.log (1 + lam ^ 2 / ((j:ℝ) + 1) ^ 2)
      = Real.log (Real.sinh (Real.pi * lam) / (Real.pi * lam)) :=
    (hasSum_log_one_add_sq_div hlam0).tsum_eq
  simp_rw [hinner] at hswap
  rw [houter] at hswap
  have hPlog : Real.log (Real.sinh (Real.pi * lam) / (Real.pi * lam))
      = - Real.log (GppStefanBoltzmann.P lam) := by
    unfold GppStefanBoltzmann.P
    rw [← Real.log_inv, inv_div]
  rw [hPlog] at hswap
  have hkterm : ∀ k : ℕ, ∑' j : ℕ, term lam j k
      = (-1) ^ k * (∑' j : ℕ, 1 / ((j:ℝ) + 1) ^ (2 * (k + 1))) * lam ^ (2 * (k + 1)) / (k + 1) := by
    intro k
    have hcongr : ∀ j : ℕ, term lam j k
        = ((-1) ^ k * lam ^ (2 * (k+1)) / (k+1)) * (1 / ((j:ℝ) + 1) ^ (2 * (k + 1))) := by
      intro j
      unfold term
      rw [div_pow, ← pow_mul lam 2 (k+1), ← pow_mul ((j:ℝ)+1) 2 (k+1)]
      ring
    simp_rw [hcongr]
    rw [tsum_mul_left]
    ring
  have hSouter : Summable (fun k : ℕ => ∑' j : ℕ, term lam j k) := hSuncurry.prod_symm.prod
  have hSouter' : Summable (fun k : ℕ => (-1) ^ k *
      (∑' j : ℕ, 1 / ((j:ℝ) + 1) ^ (2 * (k + 1))) * lam ^ (2 * (k + 1)) / (k + 1)) :=
    hSouter.congr hkterm
  simp_rw [hkterm] at hswap
  exact hswap ▸ hSouter'.hasSum

end GppCumulantLaw
