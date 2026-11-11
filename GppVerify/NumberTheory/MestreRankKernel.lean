import GppVerify.Upstream.BoseIntegral
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.Algebra.IsPrimePow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

/-!
# Kernel-proved Mestre rank bounds for 11a1 and 37a1 (conditional on GRH(E))

This module removes the trusted Arb boxes of `MestreRankCertificates`. Every numerical input is
proved here in the kernel.

## Test function

The test function is `f = 1_{[-1/2, 1/2]}`, so `F = f ∗ f̃ = tri = max (1 - |x|) 0` (Fejér).
This is a different test function from the `cos((j+1/2)πx/L)` Galerkin basis used in
`MestreRankCertificates`. Every term of the explicit formula is then elementary:

* **Prime-power sum.** Since `log 3 > 1` (`e < 3`), only `n = 2` lies in the support. Here
  `a_2 = -2` for both curves, decided by counting points of the Mathlib `WeierstrassCurve`
  reduced over `ZMod 2`.
* **Archimedean term.** Mestre's x-space form `-2γF(0) + 2∫_{(0,∞)} (F(0)-F(x))/(eˣ-1) dx`. It
  splits as `∫_{(0,1]} x/(eˣ-1)`, bounded by `7/9` via the Bernoulli bound
  `x/(eˣ-1) ≤ 1 - x/2 + x²/12`, plus the closed form
  `∫_{(1,∞)} 1/(eˣ-1) = -log(1-e⁻¹)` (`GppVerify.Upstream.BoseIntegral`).
* **Constants.** `γ > 1/2`, `log 2`, `π`, `e` come from Mathlib. `log 11`, `log 37`, `log π` and
  `-log(1-e⁻¹)` are bounded through Taylor bounds for `exp`.
* **`F̂(0) = ∫ F = 1`.** Proved exactly.

The result is `weilRHS ≤ log N - 1.76`. That gives `0.64 < 1` for 11a1 and `1.86 < 2` for 37a1.
The interval-arithmetic values are 0.4656 and 1.678.

## Named hypotheses (the only ones)

1. `hEF`, the explicit formula. The sum of `F̂(γ)` over the zeros of `L(E, s)` equals
   `weilRHS E N tri`. Behind it sit modularity/analytic continuation, the functional equation
   with conductor `N`, and Weil's explicit formula. None of these is in Mathlib.
2. `hGRH`, GRH(E). Off-centre zeros contribute `≥ 0`, so `r · F̂(0) ≤ zeroSum`.

For `r = 1` on 37a1 only, `hodd` adds the sign `w = -1` of the same functional equation.

Nothing here concerns BSD itself, which remains open.
-/

namespace GppMestreRankKernel

open Real MeasureTheory Set

/-! ### Arithmetic data -/

/-- Number of affine points of the reduction of `W` modulo `p`. -/
noncomputable def affinePointCount (W : WeierstrassCurve ℤ) (p : ℕ) : ℕ :=
  Nat.card {P : ZMod p × ZMod p // (W.map (Int.castRingHom (ZMod p))).toAffine.Equation P.1 P.2}

/-- `a_p = p + 1 - #W(𝔽_p)`, where `#W(𝔽_p)` counts the point at infinity too. -/
noncomputable def traceOfFrobenius (W : WeierstrassCurve ℤ) (p : ℕ) : ℤ :=
  (p : ℤ) - affinePointCount W p

/-- `s_k = α^k + β^k`, where `α + β = a` and `αβ = p`. -/
def frobPowerSum (a : ℤ) (p : ℕ) : ℕ → ℤ
  | 0 => 2
  | 1 => a
  | k + 2 => a * frobPowerSum a p (k + 1) - p * frobPowerSum a p k

/-- Coefficient of `n^{-s}` in `-L'/L(E, s)`, for conductor `N`. At `n = p^k` it is
`(α^k + β^k) log p` when `p ∤ N` and `a_p^k log p` when `p ∣ N`; it vanishes when `n` is not a
prime power. -/
noncomputable def dirichletLogCoeff (W : WeierstrassCurve ℤ) (N n : ℕ) : ℝ :=
  if IsPrimePow n then
    (((if n.minFac ∣ N then traceOfFrobenius W n.minFac ^ n.factorization n.minFac
      else frobPowerSum (traceOfFrobenius W n.minFac) n.minFac (n.factorization n.minFac)) : ℤ)
      : ℝ) * log n.minFac
  else 0

/-! ### The Fejér test function and the explicit-formula side -/

/-- `F = f ∗ f̃` with `f = 1_{[-1/2, 1/2]}`, the triangle `max (1 - |x|) 0`. -/
noncomputable def tri (x : ℝ) : ℝ := max (1 - |x|) 0

/-- The explicit-formula side of the Weil pairing of `L(E, s)` (centred at `s = 1`) against `F`:
the conductor/Γ-shift term, the archimedean term in Mestre's `x`-space form, and the
prime-power sum. -/
noncomputable def weilRHS (W : WeierstrassCurve ℤ) (N : ℕ) (F : ℝ → ℝ) : ℝ :=
  F 0 * (log N - 2 * log (2 * π)) +
    (-2 * eulerMascheroniConstant * F 0 + 2 * ∫ x in Ioi 0, (F 0 - F x) / (exp x - 1)) -
    2 * ∑' n : ℕ, dirichletLogCoeff W N n / n * F (log n)

/-- Cremona 11a1: `y² + y = x³ - x² - 10x - 20`. -/
def W11a1 : WeierstrassCurve ℤ := ⟨0, -1, 1, -10, -20⟩

/-- Cremona 37a1: `y² + y = x³ - x`. -/
def W37a1 : WeierstrassCurve ℤ := ⟨0, 0, 1, -1, 0⟩

/-! ### `a_2` by point counting -/

theorem traceOfFrobenius_11a1_two : traceOfFrobenius W11a1 2 = -2 := by
  have h : ∀ P : ZMod 2 × ZMod 2,
      (W11a1.map (Int.castRingHom (ZMod 2))).toAffine.Equation P.1 P.2 ↔
        P.2 ^ 2 + ((0 : ℤ) : ZMod 2) * P.1 * P.2 + ((1 : ℤ) : ZMod 2) * P.2 =
          P.1 ^ 3 + ((-1 : ℤ) : ZMod 2) * P.1 ^ 2 + ((-10 : ℤ) : ZMod 2) * P.1 +
            ((-20 : ℤ) : ZMod 2) := fun P => by
    rw [WeierstrassCurve.Affine.equation_iff]; rfl
  unfold traceOfFrobenius affinePointCount
  rw [Nat.card_congr (Equiv.subtypeEquivRight h), Nat.card_eq_fintype_card]
  decide

theorem traceOfFrobenius_37a1_two : traceOfFrobenius W37a1 2 = -2 := by
  have h : ∀ P : ZMod 2 × ZMod 2,
      (W37a1.map (Int.castRingHom (ZMod 2))).toAffine.Equation P.1 P.2 ↔
        P.2 ^ 2 + ((0 : ℤ) : ZMod 2) * P.1 * P.2 + ((1 : ℤ) : ZMod 2) * P.2 =
          P.1 ^ 3 + ((0 : ℤ) : ZMod 2) * P.1 ^ 2 + ((-1 : ℤ) : ZMod 2) * P.1 +
            ((0 : ℤ) : ZMod 2) := fun P => by
    rw [WeierstrassCurve.Affine.equation_iff]; rfl
  unfold traceOfFrobenius affinePointCount
  rw [Nat.card_congr (Equiv.subtypeEquivRight h), Nat.card_eq_fintype_card]
  decide

/-! ### The prime-power sum collapses to `n = 2` -/

theorem tri_zero : tri 0 = 1 := by norm_num [tri]

theorem tri_of_one_le {x : ℝ} (hx : 1 ≤ |x|) : tri x = 0 := by
  unfold tri; exact max_eq_right (by linarith)

theorem tri_of_mem_Icc {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : tri x = 1 - x := by
  unfold tri; rw [abs_of_nonneg h0]; exact max_eq_left (by linarith)

theorem one_lt_log_three : 1 < log 3 := by
  rw [lt_log_iff_exp_lt (by norm_num)]
  have := exp_one_lt_d9; norm_num at this ⊢; linarith

theorem dirichletLogCoeff_two (W : WeierstrassCurve ℤ) {N : ℕ} (hN : ¬ 2 ∣ N) :
    dirichletLogCoeff W N 2 = traceOfFrobenius W 2 * log 2 := by
  unfold dirichletLogCoeff
  rw [if_pos Nat.prime_two.isPrimePow, Nat.prime_two.minFac_eq, if_neg hN,
    Nat.prime_two.factorization_self]
  rfl

theorem tsum_dirichletLogCoeff_tri (W : WeierstrassCurve ℤ) {N : ℕ} (hN : ¬ 2 ∣ N) :
    ∑' n : ℕ, dirichletLogCoeff W N n / n * tri (log n) =
      traceOfFrobenius W 2 * log 2 / 2 * (1 - log 2) := by
  rw [tsum_eq_single 2]
  · rw [Nat.cast_ofNat, dirichletLogCoeff_two W hN, tri_of_mem_Icc (log_nonneg (by norm_num))
      (log_two_lt_d9.le.trans (by norm_num))]
  · intro n hn
    rcases Nat.lt_or_ge n 3 with h | h
    · have hn' : n = 0 ∨ n = 1 := by omega
      have : ¬ IsPrimePow n := by
        rcases hn' with rfl | rfl
        · exact not_isPrimePow_zero
        · exact not_isPrimePow_one
      simp [dirichletLogCoeff, this]
    · have h3 : (3 : ℝ) ≤ n := by exact_mod_cast h
      have hl : 1 ≤ |log n| := by
        rw [abs_of_nonneg (log_nonneg (by linarith))]
        exact one_lt_log_three.le.trans (log_le_log (by norm_num) h3)
      rw [tri_of_one_le hl, mul_zero]

/-! ### The archimedean integral -/

theorem continuousOn_div_exp_sub_one :
    ContinuousOn (fun x : ℝ => x / (exp x - 1)) (Ioc 0 1) :=
  continuousOn_id.div (continuous_exp.sub continuous_const).continuousOn
    (fun _ hx => (sub_pos.2 (one_lt_exp_iff.2 hx.1)).ne')

theorem integrableOn_div_exp_sub_one :
    IntegrableOn (fun x : ℝ => x / (exp x - 1)) (Ioc 0 1) := by
  refine Integrable.mono' (integrableOn_const (C := (1 : ℝ)) measure_Ioc_lt_top.ne)
    (continuousOn_div_exp_sub_one.aestronglyMeasurable measurableSet_Ioc) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (div_exp_sub_one_nonneg hx.1.le)]
  have hd : 0 < exp x - 1 := sub_pos.2 (one_lt_exp_iff.2 hx.1)
  rw [div_le_one hd]
  linarith [add_one_le_exp x]

theorem integral_div_exp_sub_one_le :
    ∫ x in Ioc (0 : ℝ) 1, x / (exp x - 1) ≤ 7 / 9 := by
  have hpoly : IntegrableOn (fun x : ℝ => 1 - x / 2 + x ^ 2 / 12) (Ioc 0 1) :=
    (by fun_prop : Continuous fun x : ℝ => 1 - x / 2 + x ^ 2 / 12).integrableOn_Ioc
  calc ∫ x in Ioc (0 : ℝ) 1, x / (exp x - 1)
      ≤ ∫ x in Ioc (0 : ℝ) 1, (1 - x / 2 + x ^ 2 / 12) :=
        setIntegral_mono_on integrableOn_div_exp_sub_one hpoly measurableSet_Ioc
          fun x hx => div_exp_sub_one_le hx.1
    _ = 7 / 9 := by
        rw [← intervalIntegral.integral_of_le zero_le_one,
          intervalIntegral.integral_eq_sub_of_hasDerivAt
            (f := fun x : ℝ => x - x ^ 2 / 4 + x ^ 3 / 36)
            (fun x _ => by
              have := (((hasDerivAt_id' x).sub ((hasDerivAt_pow 2 x).div_const 4)).add
                ((hasDerivAt_pow 3 x).div_const 36))
              convert this using 1
              · funext y; simp only [Pi.add_apply, Pi.sub_apply]
              · norm_num; ring)
            ((by fun_prop : Continuous fun x : ℝ => 1 - x / 2 + x ^ 2 / 12).intervalIntegrable
              _ _)]
        norm_num

theorem integral_tri_arch :
    ∫ x in Ioi (0 : ℝ), (tri 0 - tri x) / (exp x - 1) =
      (∫ x in Ioc (0 : ℝ) 1, x / (exp x - 1)) - log (1 - exp (-1)) := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have h1 : EqOn (fun x => (tri 0 - tri x) / (exp x - 1)) (fun x => x / (exp x - 1))
      (Ioc 0 1) := fun x hx => by
    simp only [tri_zero, tri_of_mem_Icc hx.1.le hx.2, sub_sub_cancel]
  have h2 : EqOn (fun x => (tri 0 - tri x) / (exp x - 1)) (fun x => 1 / (exp x - 1))
      (Ioi 1) := fun x hx => by
    have : 1 ≤ |x| := by rw [abs_of_pos (zero_lt_one.trans hx)]; exact hx.le
    simp only [tri_zero, tri_of_one_le this, sub_zero]
  rw [hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (integrableOn_div_exp_sub_one.congr_fun h1.symm measurableSet_Ioc)
      ((integrableOn_Ioi_one_div_exp_sub_one zero_lt_one).congr_fun h2.symm measurableSet_Ioi),
    setIntegral_congr_fun measurableSet_Ioc h1, setIntegral_congr_fun measurableSet_Ioi h2,
    integral_Ioi_one_div_exp_sub_one zero_lt_one]
  ring

/-! ### Elementary constants -/

theorem exp_ge_sum6 {x : ℝ} (hx : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 ≤ exp x :=
  quintic_le_exp_of_nonneg hx

theorem log_eleven_le : log 11 ≤ 2.4 := by
  rw [log_le_iff_le_exp (by norm_num)]
  have he := exp_one_gt_d9
  have hs := exp_ge_sum6 (x := 0.4) (by norm_num)
  have hsplit : exp 2.4 = exp 1 * exp 1 * exp 0.4 := by
    rw [← exp_add, ← exp_add]; norm_num
  rw [hsplit]
  have hE : (2.7182818283 : ℝ) ≤ exp 1 := he.le
  have hp : 0 ≤ exp 1 := (exp_pos 1).le
  nlinarith [mul_le_mul hE hE (by norm_num) hp, exp_pos 0.4,
    mul_le_mul (mul_le_mul hE hE (by norm_num) hp) hs (by norm_num) (by positivity)]

theorem log_thirtyseven_le : log 37 ≤ 3.62 := by
  rw [log_le_iff_le_exp (by norm_num)]
  have hE : (2.7182818283 : ℝ) ≤ exp 1 := exp_one_gt_d9.le
  have hs := exp_ge_sum6 (x := 0.62) (by norm_num)
  have hsplit : exp 3.62 = exp 1 * exp 1 * exp 1 * exp 0.62 := by
    rw [← exp_add, ← exp_add, ← exp_add]; norm_num
  rw [hsplit]
  have hp : 0 ≤ exp 1 := (exp_pos 1).le
  have h2 := mul_le_mul hE hE (by norm_num) hp
  have h3 := mul_le_mul h2 hE (by norm_num) (by positivity)
  nlinarith [mul_le_mul h3 hs (by norm_num) (by positivity)]

theorem log_pi_ge : 1.14 ≤ log π := by
  rw [le_log_iff_exp_le pi_pos]
  have hb := Real.exp_bound' (x := 0.14) (by norm_num) (by norm_num) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  have hsplit : exp 1.14 = exp 1 * exp 0.14 := by rw [← exp_add]; norm_num
  rw [hsplit]
  have hE := exp_one_lt_d9
  have := pi_gt_d6
  nlinarith [mul_le_mul hE.le hb (exp_pos _).le (by norm_num), exp_pos 0.14]

theorem neg_log_one_sub_exp_neg_one_le : -log (1 - exp (-1)) ≤ 0.46 := by
  have hpos : 0 < 1 - exp (-1) := sub_pos.2 (exp_lt_one_iff.2 (by norm_num))
  rw [neg_le, le_log_iff_exp_le hpos, exp_neg, exp_neg]
  have hs := exp_ge_sum6 (x := 0.46) (by norm_num)
  have h1 : (exp 0.46)⁻¹ ≤ (1.584 : ℝ)⁻¹ :=
    (inv_le_inv₀ (exp_pos _) (by norm_num)).2 (by norm_num at hs ⊢; linarith)
  have h2 : (exp 1)⁻¹ ≤ (2.7182818283 : ℝ)⁻¹ :=
    (inv_le_inv₀ (exp_pos _) (by norm_num)).2 exp_one_gt_d9.le
  norm_num at h1 h2 ⊢
  linarith

/-! ### `F̂(0) = ∫ F = 1` -/

theorem continuous_tri : Continuous tri := by unfold tri; fun_prop

theorem integral_tri : ∫ x, tri x = 1 := by
  have hout : ∀ x, x ∉ Ioc (-1 : ℝ) 1 → tri x = 0 := fun x hx => by
    apply tri_of_one_le
    rcases not_and_or.1 hx with h | h
    · rw [abs_of_neg (by linarith [not_lt.1 h])]; linarith [not_lt.1 h]
    · rw [abs_of_pos (by linarith [not_le.1 h])]; linarith [not_le.1 h]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout,
    ← intervalIntegral.integral_of_le (by norm_num),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (continuous_tri.intervalIntegrable _ _) (continuous_tri.intervalIntegrable _ _)]
  have hl : EqOn tri (fun x => 1 + x) (uIcc (-1) 0) := fun x hx => by
    rw [uIcc_of_le (by norm_num)] at hx
    unfold tri; rw [abs_of_nonpos hx.2, max_eq_left (by linarith [hx.1])]; ring
  have hr : EqOn tri (fun x => 1 - x) (uIcc 0 1) := fun x hx => by
    rw [uIcc_of_le (by norm_num)] at hx
    exact tri_of_mem_Icc hx.1 hx.2
  rw [intervalIntegral.integral_congr hl, intervalIntegral.integral_congr hr,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => x + x ^ 2 / 2)
      (fun x _ => by
        convert (hasDerivAt_id' x).add ((hasDerivAt_pow 2 x).div_const 2) using 1
        · rfl
        · norm_num)
      ((by fun_prop : Continuous fun x : ℝ => 1 + x).intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => x - x ^ 2 / 2)
      (fun x _ => by
        convert (hasDerivAt_id' x).sub ((hasDerivAt_pow 2 x).div_const 2) using 1
        · rfl
        · norm_num)
      ((by fun_prop : Continuous fun x : ℝ => 1 - x).intervalIntegrable _ _)]
  norm_num

/-! ### The explicit-formula side for `F = tri` -/

theorem weilRHS_tri (W : WeierstrassCurve ℤ) {N : ℕ} (hN : ¬ 2 ∣ N) :
    weilRHS W N tri = log N - 2 * (log 2 + log π) - 2 * eulerMascheroniConstant +
      2 * ((∫ x in Ioc (0 : ℝ) 1, x / (exp x - 1)) - log (1 - exp (-1))) -
      traceOfFrobenius W 2 * log 2 * (1 - log 2) := by
  unfold weilRHS
  rw [integral_tri_arch, tsum_dirichletLogCoeff_tri W hN, tri_zero,
    log_mul two_ne_zero pi_ne_zero]
  ring

/-- Upper bound on the explicit-formula side, valid for any curve with `a_2 = -2`. -/
theorem weilRHS_tri_le (W : WeierstrassCurve ℤ) {N : ℕ} (hN : ¬ 2 ∣ N)
    (ha : traceOfFrobenius W 2 = -2) :
    weilRHS W N tri ≤ log N - 1.76 := by
  rw [weilRHS_tri W hN, ha]
  have hI := integral_div_exp_sub_one_le
  have hL := neg_log_one_sub_exp_neg_one_le
  have hγ := one_half_lt_eulerMascheroniConstant
  have hπ := log_pi_ge
  have h2l := log_two_gt_d9
  have h2u := log_two_lt_d9
  have hprod : log 2 * (1 - log 2) ≤ 0.6931471808 * (1 - 0.6931471803) :=
    mul_le_mul h2u.le (by linarith) (by linarith) (by norm_num)
  push_cast
  norm_num at hI hL hγ hπ h2l h2u hprod ⊢
  linarith

/-! ### Rank certificates: only the explicit formula and GRH(E) are hypotheses -/

/-- **11a1.** Assume the explicit formula `zeroSum = weilRHS` for `F = tri`, where `zeroSum` is
the sum of `F̂` over the zeros of `L(11a1, s)`. Assume also GRH(E): every off-centre term is
`≥ 0`, so a central zero of order `r` gives `r · F̂(0) ≤ zeroSum`. Then `r = 0`. -/
theorem analyticRank_eq_zero_11a1 (r : ℕ) (zeroSum : ℝ)
    (hEF : zeroSum = weilRHS W11a1 11 tri) (hGRH : (r : ℝ) * ∫ x, tri x ≤ zeroSum) :
    r = 0 := by
  have hB := weilRHS_tri_le W11a1 (N := 11) (by norm_num) traceOfFrobenius_11a1_two
  have hl := log_eleven_le
  rw [integral_tri, mul_one] at hGRH
  have : (r : ℝ) < 1 := by norm_num at hB hl; linarith
  exact_mod_cast Nat.lt_one_iff.1 (by exact_mod_cast this)

/-- **37a1.** Under the same two hypotheses, `r ≤ 1`. -/
theorem analyticRank_le_one_37a1 (r : ℕ) (zeroSum : ℝ)
    (hEF : zeroSum = weilRHS W37a1 37 tri) (hGRH : (r : ℝ) * ∫ x, tri x ≤ zeroSum) :
    r ≤ 1 := by
  have hB := weilRHS_tri_le W37a1 (N := 37) (by norm_num) traceOfFrobenius_37a1_two
  have hl := log_thirtyseven_le
  rw [integral_tri, mul_one] at hGRH
  have : (r : ℝ) < 2 := by norm_num at hB hl; linarith
  have : r < 2 := by exact_mod_cast this
  omega

/-- **37a1, with the sign of the functional equation.** The root number `w = -1` makes the
order of vanishing odd. That is the functional-equation input to the explicit formula. With it,
`r = 1`. -/
theorem analyticRank_eq_one_37a1 (r : ℕ) (zeroSum : ℝ)
    (hEF : zeroSum = weilRHS W37a1 37 tri) (hGRH : (r : ℝ) * ∫ x, tri x ≤ zeroSum)
    (hodd : Odd r) : r = 1 := by
  have := analyticRank_le_one_37a1 r zeroSum hEF hGRH
  rcases hodd with ⟨k, rfl⟩
  omega

end GppMestreRankKernel
