import GppVerify.RiemannHypothesis.BoxInitialInterval
import GppVerify.RiemannHypothesis.FirstPrimeNegativeBound

/-!
# Numerics for the first interval: the point `a = 2 log(5/4)`

Here `e^{−a/2} = 4/5`, so `cosh(a/2) = 41/40`, `sinh(a/2) = 9/40` and `curv a = 5/4 − (4/5)^5/(1 − (4/5)^4)` are
rational, and `Gcl a` is the sum of the positive series of `GclSeries.lean` at `u = 4/5`.

This file establishes the facts about `a` (`aPt`), the rigorous bounds
(`17733/10000 < Gcl a < 17735/10000` from the positive series; `∫₀^a Gcl > 1022/1000` from a 16-term partial sum,
integrated termwise — every term is positive, so no tail estimate), the constant `C∞ ≥ −5.3726`, and the assembly:

**`box_pos_first_interval`**: `0 < 16 (cosh(L/2) − 1) + archBox L + primeBox L` for every `0 < L ≤ log 2`.

The argument runs with the rational constant `C = −5.3726 ≤ C∞` (`Vm C ≤ Vm C∞`, so only a *lower* bound of
`C∞` is needed, from the in-tree upper bounds on `γ` and `log π`).  The tests are exact rational/series
inequalities; the margins are `vslope < −0.025` (needs `Gcl a < 1.7735`, true value `1.77335…`) and
`Vm C a > 0.045` against the required `≈ 0.0007/(4·0.69)`.

**Scope.** This certifies positivity of the (explicit-formula-defined) box form on the *prime-free* interval
`(0, log 2]` only; it is the first link of GPT's `10⁷` certificate, not the certificate.  The continuation past
the first prime power (`WnModel_pos_on_gap` at `q = 2, 3, …` with event values) is not done here, and nothing
here is the Weil criterion: ARP, RH, OB-6, UB are OPEN.

No `sorry`, no axiom.
-/

open Real Set MeasureTheory Filter Topology
open GppBoxCurvature GppGclSeries GppEventParabola GppPlastic GppBoxArchimedean GppBoxInitial

noncomputable section

namespace GppBoxNumerics

/-- The first-interval test point `a = 2 log(5/4)` (`e^{−a/2} = 4/5`). -/
def aPt : ℝ := 2 * Real.log (5 / 4)

theorem exp_half : Real.exp (aPt / 2) = 5 / 4 := by
  rw [aPt, show 2 * Real.log (5 / 4) / 2 = Real.log (5 / 4) by ring, Real.exp_log (by norm_num)]

theorem exp_neg_half : Real.exp (-aPt / 2) = 4 / 5 := by
  rw [show -aPt / 2 = -(aPt / 2) by ring, Real.exp_neg, exp_half]; norm_num

theorem aPt_pos : 0 < aPt := by
  unfold aPt
  have := Real.log_pos (show (1 : ℝ) < 5 / 4 by norm_num)
  linarith

theorem aPt_lt_log_two : aPt < Real.log 2 := by
  have h : aPt = Real.log (25 / 16) := by
    rw [aPt, show (25 / 16 : ℝ) = (5 / 4) ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [h]
  exact Real.log_lt_log (by norm_num) (by norm_num)

theorem aPt_le : aPt ≤ 4464 / 10000 := by
  have h : Real.log (5 / 4) ≤ 2232 / 10000 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 2232 / 10000 by norm_num) 5
    refine le_trans ?_ this
    norm_num [Finset.sum_range_succ, Nat.factorial]
  unfold aPt; linarith

theorem cosh_half : Real.cosh (aPt / 2) = 41 / 40 := by
  rw [Real.cosh_eq, exp_half, show -(aPt / 2) = -aPt / 2 by ring, exp_neg_half]; norm_num

theorem sinh_half : Real.sinh (aPt / 2) = 9 / 40 := by
  rw [Real.sinh_eq, exp_half, show -(aPt / 2) = -aPt / 2 by ring, exp_neg_half]; norm_num

theorem curv_aPt : curv aPt = 5 / 4 - (4 / 5) ^ 5 / (1 - (4 / 5) ^ 4) := by
  unfold curv kappaGamma
  have e1 : Real.exp (-5 * aPt / 2) = (4 / 5) ^ 5 := by
    rw [show -5 * aPt / 2 = (5 : ℕ) * (-aPt / 2) by push_cast; ring, Real.exp_nat_mul, exp_neg_half]
  have e2 : Real.exp (-2 * aPt) = (4 / 5) ^ 4 := by
    rw [show -2 * aPt = (4 : ℕ) * (-aPt / 2) by push_cast; ring, Real.exp_nat_mul, exp_neg_half]
  rw [exp_half, e1, e2]

theorem curv_aPt_gt : (69 : ℝ) / 100 < curv aPt := by
  rw [curv_aPt]; norm_num

theorem tStar_lt_aPt : tStar < aPt := by
  by_contra h
  push Not at h
  rcases h.lt_or_eq with h | h
  · have := curv_neg_of_lt aPt_pos h
    linarith [curv_aPt_gt]
  · have := curv_tStar
    rw [← h] at this
    linarith [curv_aPt_gt]

/-! ### `Gcl` at `a` -/

/-- Rational term of the series at `u = 4/5`. -/
def gq (k : ℕ) : ℚ := (1 + (-1) ^ k) * (4 / 5) ^ (2 * k + 1) / (2 * k + 1)

theorem gq_cast (k : ℕ) : ((gq k : ℚ) : ℝ) = gterm (4 / 5) k := by
  unfold gq gterm; push_cast; ring

theorem gq_partial_gt : (17733 / 10000 : ℚ) < ∑ k ∈ Finset.range 24, gq k := by decide +kernel

theorem gq_partial_lt : (∑ k ∈ Finset.range 24, gq k) + 2 * (4 / 5) ^ 49 / (1 - (4 / 5) ^ 2) <
    (17735 / 10000 : ℚ) := by decide +kernel

theorem Gcl_aPt_gt : (17733 / 10000 : ℝ) < Gcl aPt := by
  have h := Gcl_ge_partial aPt_pos 24
  rw [exp_neg_half] at h
  have hq : ((17733 / 10000 : ℚ) : ℝ) < ((∑ k ∈ Finset.range 24, gq k : ℚ) : ℝ) := by
    exact_mod_cast gq_partial_gt
  push_cast [gq_cast] at hq
  linarith

theorem Gcl_aPt_lt : Gcl aPt < 17735 / 10000 := by
  have h := Gcl_le_partial_add_tail aPt_pos 24
  rw [exp_neg_half] at h
  have hq : (((∑ k ∈ Finset.range 24, gq k) + 2 * (4 / 5) ^ 49 / (1 - (4 / 5) ^ 2) : ℚ) : ℝ) <
      ((17735 / 10000 : ℚ) : ℝ) := by exact_mod_cast gq_partial_lt
  push_cast [gq_cast] at hq
  norm_num at h ⊢
  linarith

/-! ### A lower bound for `∫₀^a Gcl` -/

theorem partial_reindex (u : ℝ) (P : ℕ) :
    ∑ k ∈ Finset.range (2 * P), gterm u k =
      ∑ j ∈ Finset.range P, 2 * u ^ (4 * j + 1) / (4 * j + 1) := by
  induction P with
  | zero => simp
  | succ P ih =>
    rw [show 2 * (P + 1) = 2 * P + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    have h1 : gterm u (2 * P) = 2 * u ^ (4 * P + 1) / (4 * P + 1) := by
      unfold gterm
      rw [pow_mul]; norm_num
      ring_nf
    have h2 : gterm u (2 * P + 1) = 0 := by
      unfold gterm
      rw [pow_succ, pow_mul]; norm_num
    rw [h1, h2]; ring

theorem Gcl_ge_series {s : ℝ} (hs : 0 < s) (P : ℕ) :
    ∑ j ∈ Finset.range P, 2 * Real.exp (-s / 2) ^ (4 * j + 1) / (4 * j + 1) ≤ Gcl s := by
  have := Gcl_ge_partial hs (2 * P)
  rwa [partial_reindex] at this

theorem integral_exp_neg_mul {c : ℝ} (hc : 0 < c) (a : ℝ) :
    ∫ s in (0 : ℝ)..a, Real.exp (-c * s) = (1 - Real.exp (-c * a)) / c := by
  have hd : ∀ x ∈ uIcc 0 a, HasDerivAt (fun s : ℝ => -Real.exp (-c * s) / c) (Real.exp (-c * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun s : ℝ => -c * s) (-c) x := by
      simpa using (hasDerivAt_id x).const_mul (-c)
    have h2 := (h1.exp).neg.div_const c
    refine h2.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)]
  simp
  field_simp
  ring

/-- Rational lower bound for `∫₀^a Gcl`: `Σ_{j<16} 4 (1 − (4/5)^{4j+1}) / (4j+1)²`. -/
def ILowQ : ℚ := ∑ j ∈ Finset.range 16, 4 * (1 - (4 / 5) ^ (4 * j + 1)) / (4 * j + 1) ^ 2

theorem ILowQ_gt : (1022 / 1000 : ℚ) < ILowQ := by unfold ILowQ; decide +kernel

theorem integral_term (j : ℕ) :
    ∫ s in (0 : ℝ)..aPt, 2 * Real.exp (-s / 2) ^ (4 * j + 1) / (4 * j + 1) =
      4 * (1 - (4 / 5 : ℝ) ^ (4 * j + 1)) / (4 * j + 1) ^ 2 := by
  have hc : (0 : ℝ) < (4 * j + 1) / 2 := by positivity
  have e : ∀ s : ℝ, 2 * Real.exp (-s / 2) ^ (4 * j + 1) / (4 * j + 1) =
      2 / (4 * j + 1) * Real.exp (-((4 * j + 1) / 2) * s) := by
    intro s
    rw [← Real.exp_nat_mul]
    push_cast
    rw [show ((4 * (j : ℝ) + 1) * (-s / 2)) = -((4 * j + 1) / 2) * s by ring]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, integral_exp_neg_mul hc]
  have e2 : Real.exp (-((4 * (j : ℝ) + 1) / 2) * aPt) = (4 / 5 : ℝ) ^ (4 * j + 1) := by
    rw [← exp_neg_half, ← Real.exp_nat_mul]
    push_cast
    congr 1; ring
  rw [e2]
  field_simp
  ring

theorem integral_Gcl_aPt_gt : (1022 / 1000 : ℝ) < ∫ s in (0 : ℝ)..aPt, Gcl s := by
  have hint : ∀ j ∈ Finset.range 16, IntervalIntegrable
      (fun s : ℝ => 2 * Real.exp (-s / 2) ^ (4 * j + 1) / (4 * j + 1)) MeasureTheory.volume 0 aPt := by
    intro j _
    apply Continuous.intervalIntegrable
    fun_prop
  have hsum : IntervalIntegrable (fun s : ℝ => ∑ j ∈ Finset.range 16,
      2 * Real.exp (-s / 2) ^ (4 * j + 1) / (4 * j + 1)) MeasureTheory.volume 0 aPt :=
    IntervalIntegrable.sum _ hint
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo aPt_pos.le hsum
    (intervalIntegrable_Gcl aPt_pos) (fun s hs => Gcl_ge_series hs.1 16)
  rw [intervalIntegral.integral_finsetSum hint] at hmono
  simp only [integral_term] at hmono
  have hq : ((1022 / 1000 : ℚ) : ℝ) < (ILowQ : ℝ) := by exact_mod_cast ILowQ_gt
  have hq' : (ILowQ : ℝ) = ∑ j ∈ Finset.range 16,
      4 * (1 - (4 / 5 : ℝ) ^ (4 * j + 1)) / (4 * j + 1) ^ 2 := by
    unfold ILowQ; push_cast; rfl
  push_cast at hq
  linarith

/-! ### The constant `C∞` and the assembly -/

theorem Cinf_ge : (-53726 / 10000 : ℝ) ≤ GppArchimedeanFloor.archimedeanFloor := by
  unfold GppArchimedeanFloor.archimedeanFloor
  have h1 := GppFirstPrime.euler_lt
  have h2 := GppFirstPrime.log_pi_lt
  have h3 := Real.pi_lt_d4
  have h4 := Real.log_two_lt_d9
  norm_num at h1 h2 h3 h4 ⊢
  linarith

theorem Vm_Clo_aPt_pos : (45 / 1000 : ℝ) < Vm (-53726 / 10000) aPt := by
  unfold Vm
  rw [cosh_half]
  have hI := integral_Gcl_aPt_gt
  have ha := aPt_le
  have hp := aPt_pos
  nlinarith

theorem vslope_Clo_aPt_neg : vslope (-53726 / 10000) aPt < 0 := by
  unfold vslope
  rw [sinh_half]
  have := Gcl_aPt_lt
  linarith

theorem vslope_Clo_aPt_gt : (-3 / 100 : ℝ) < vslope (-53726 / 10000) aPt := by
  unfold vslope
  rw [sinh_half]
  have := Gcl_aPt_gt
  linarith

theorem Vm_Clo_cert :
    vslope (-53726 / 10000) aPt ^ 2 < 2 * (2 * curv aPt) * Vm (-53726 / 10000) aPt := by
  have h1 := vslope_Clo_aPt_neg
  have h2 := vslope_Clo_aPt_gt
  have h3 := Vm_Clo_aPt_pos
  have h4 := curv_aPt_gt
  nlinarith

/-- **`Vm C > 0` on `(0, log 2]` for `C = −5.3726`.** -/
theorem Vm_Clo_pos {L : ℝ} (hL : L ∈ Ioc 0 (Real.log 2)) : 0 < Vm (-53726 / 10000) L :=
  Vm_pos tStar_lt_aPt aPt_lt_log_two.le vslope_Clo_aPt_neg Vm_Clo_cert hL

/-- The prime part vanishes on `(0, log 2]`. -/
theorem primeBox_zero {L : ℝ} (h : L ≤ Real.log 2) : primeBox L = 0 := by
  unfold primeBox
  have hsum : ∑ n ∈ Finset.Icc 1 ⌊Real.exp L⌋₊,
      (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n * (L - Real.log n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [Finset.mem_Icc] at hn
    obtain ⟨hn1, hn2'⟩ := hn
    have hle : (n : ℝ) ≤ Real.exp L :=
      (Nat.cast_le.mpr hn2').trans (Nat.floor_le (Real.exp_pos L).le)
    have h2 : Real.exp L ≤ 2 := by
      calc Real.exp L ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr h
        _ = 2 := Real.exp_log (by norm_num)
    have hn2 : n ≤ 2 := by exact_mod_cast hle.trans h2
    interval_cases n
    · simp
    · have : (2 : ℝ) ≤ Real.exp L := by exact_mod_cast hle
      have hL2 : Real.log 2 ≤ L := by
        rw [Real.log_le_iff_le_exp (by norm_num)]; exact this
      have : L = Real.log 2 := le_antisymm h hL2
      simp [this]
  rw [hsum]; ring

/-- **The box form is positive on the whole first prime-free interval `(0, log 2]`:**
`16 (cosh(L/2) − 1) + archBox L + primeBox L > 0`, where `archBox L = C∞ L + 2∫₀^∞ w(t) min(t, L) dt`. -/
theorem box_pos_first_interval {L : ℝ} (hL : 0 < L) (h : L ≤ Real.log 2) :
    0 < 16 * (Real.cosh (L / 2) - 1) + archBox L + primeBox L := by
  rw [primeBox_zero h, add_zero, archBox_eq hL]
  have hV := Vm_Clo_pos (L := L) ⟨hL, h⟩
  have hC := Cinf_ge
  unfold Vm at hV
  nlinarith

end GppBoxNumerics

#print axioms GppBoxNumerics.box_pos_first_interval
#print axioms GppBoxInitial.Vm_pos
