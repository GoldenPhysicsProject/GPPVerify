/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude; statement from Codex / GPT, audited by Turbo)
-/
import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Algebra.Order.Floor.Semifield
import GppVerify.RiemannHypothesis.MobiusEchoPassivity
import GppVerify.RiemannHypothesis.CausalTailEstimate

/-!
# Causal kernels and the identity `h = k ⋆ B` (Part B of the causal proof of `EnergyZeroInequality`)

**Unconditional; this is a lemma, not RH.** Part B of the four-part formalization of Codex's causal
proof (`causal_zero_bound.md` §2, GPPDiscovery2 `cae0656`, Turbo-audited).

Kernels on `t ≥ 0`, zero elsewhere: `g_j(t) = e^{-t} t^{j-1}/(j-1)!`, `w = g₃ − (3/2) g₄`,
`w′ = g₂ − (5/2) g₃ + (3/2) g₄` (`wd`; `integral_wd` checks `∫₀ᵀ w′ = w(T)`, using `w(0) = 0`),
`ν = Σ n^{-1/2} δ_{log n}` acting as the locally finite sum `nuConv f (t) = Σ_{n ≤ e^t} f(t − log n)/√n`,
`Z = ν ∗ w`, `k = ν ∗ w′` (`kk`), `h = w − cZ` (`hh`).

**Main result** `causal_identity`: for `t ≥ 0`, `h(t) = ∫₀ᵗ k(s) B(t − s) ds`, where `B` is
`GppMobiusEcho.B` (`B(u) = Σ_{n ≤ e^u} μ(n)/√n − c`). The proof is the one in the note: the inner
convolution `∫₀ᵀ w′(v) B(T − v) dv = Σ_{m ≤ e^T} a(m) w(T − log m) − c w(T)` (`cw_formula`, from the step
structure of `B` and `w(0) = 0`), then the finite divisor collapse `Σ_{d | N} μ(d) = [N = 1]` regroups
`Σ_n Σ_m` into `w(t)` (`sum_double_moebius`). No Laplace uniqueness theorem and no distribution API.
`causal_identity_rconv` restates it as the hypothesis `hconv` of `GppCausalTail.causal_tail_estimate`.

**Not in this file:** the transforms at a zero (Part C), and the norm bounds `‖Z‖₂ ≤ 9`, `‖w‖₂ ≤ 5/2`,
`‖k‖₁ ≤ 18` (Part D).
-/

open MeasureTheory Set ArithmeticFunction

namespace GppCausalKernels

/-- `g_j(t) = e^{-t} t^{j-1}/(j-1)!` for `t ≥ 0`, zero elsewhere. -/
noncomputable def g (j : ℕ) (t : ℝ) : ℝ :=
  if 0 ≤ t then Real.exp (-t) * t ^ (j - 1) / ((j - 1).factorial : ℝ) else 0

/-- `w = g₃ − (3/2) g₄`. -/
noncomputable def w (t : ℝ) : ℝ := g 3 t - (3 / 2) * g 4 t

/-- `w′ = g₂ − (5/2) g₃ + (3/2) g₄` (the derivative of `w`; checked below). -/
noncomputable def wd (t : ℝ) : ℝ := g 2 t - (5 / 2) * g 3 t + (3 / 2) * g 4 t

theorem w_of_nonneg {t : ℝ} (ht : 0 ≤ t) : w t = Real.exp (-t) * (t ^ 2 / 2 - t ^ 3 / 4) := by
  simp only [w, g, if_pos ht]
  norm_num [Nat.factorial]
  ring

theorem wd_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    wd t = Real.exp (-t) * (t - 5 / 4 * t ^ 2 + t ^ 3 / 4) := by
  simp only [wd, g, if_pos ht]
  norm_num [Nat.factorial]
  ring

theorem w_of_neg {t : ℝ} (ht : t < 0) : w t = 0 := by
  simp [w, g, not_le.2 ht]

theorem wd_of_neg {t : ℝ} (ht : t < 0) : wd t = 0 := by
  simp [wd, g, not_le.2 ht]

theorem wd_of_nonpos {t : ℝ} (ht : t ≤ 0) : wd t = 0 := by
  rcases lt_or_eq_of_le ht with h | h
  · exact wd_of_neg h
  · rw [h, wd_of_nonneg le_rfl]; simp

theorem w_zero : w 0 = 0 := by rw [w_of_nonneg le_rfl]; simp

/-- Continuity of `wd` (all the pieces vanish at `0`). -/
theorem continuous_wd : Continuous wd := by
  have : wd = fun t => Real.exp (-(max t 0)) *
      (max t 0 - 5 / 4 * max t 0 ^ 2 + max t 0 ^ 3 / 4) := by
    funext t
    rcases le_or_gt 0 t with ht | ht
    · rw [wd_of_nonneg ht, max_eq_left ht]
    · rw [wd_of_neg ht, max_eq_right ht.le]; simp
  rw [this]
  fun_prop

/-- `w` is a primitive of `wd` on `[0, ∞)`: `∫₀ᵀ w′ = w(T)`. -/
theorem integral_wd {T : ℝ} (hT : 0 ≤ T) : ∫ v in (0 : ℝ)..T, wd v = w T := by
  have hd : ∀ x ∈ uIcc (0 : ℝ) T, HasDerivAt (fun t : ℝ => Real.exp (-t) * (t ^ 2 / 2 - t ^ 3 / 4))
      (Real.exp (-x) * (x - 5 / 4 * x ^ 2 + x ^ 3 / 4)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-x)) x := by
      refine (hasDerivAt_neg x).exp.congr_deriv ?_
      ring
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2 / 2 - t ^ 3 / 4) (x - 3 / 4 * x ^ 2) x := by
      refine (((hasDerivAt_pow 2 x).div_const 2).sub ((hasDerivAt_pow 3 x).div_const 4)).congr_deriv ?_
      push_cast; ring
    refine (h1.mul h2).congr_deriv ?_
    ring
  have hint : IntervalIntegrable (fun x : ℝ => Real.exp (-x) * (x - 5 / 4 * x ^ 2 + x ^ 3 / 4))
      volume 0 T := (by fun_prop : Continuous fun x : ℝ =>
        Real.exp (-x) * (x - 5 / 4 * x ^ 2 + x ^ 3 / 4)).intervalIntegrable _ _
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [intervalIntegral.integral_congr (g := fun x : ℝ =>
      Real.exp (-x) * (x - 5 / 4 * x ^ 2 + x ^ 3 / 4)) (fun x hx => by
        rw [uIcc_of_le hT] at hx; exact wd_of_nonneg hx.1), this, w_of_nonneg hT]
  simp


/-- `∫₀ᵀ w′(v) 1[v ≤ s] dv = w(s)` for `0 ≤ s ≤ T`. -/
theorem intervalIntegrable_wd_ind (s a b : ℝ) :
    IntervalIntegrable (fun v => wd v * (if v ≤ s then (1:ℝ) else 0)) volume a b := by
  have hm : Measurable fun v : ℝ => wd v * (if v ≤ s then (1:ℝ) else 0) :=
    continuous_wd.measurable.mul (Measurable.ite measurableSet_Iic measurable_const measurable_const)
  refine (continuous_wd.intervalIntegrable a b).mono_fun hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  by_cases h : v ≤ s <;> simp [h]

theorem integral_wd_indicator {T s : ℝ} (hs0 : 0 ≤ s) (hsT : s ≤ T) :
    ∫ v in (0 : ℝ)..T, wd v * (if v ≤ s then 1 else 0) = w s := by
  have hc := intervalIntegrable_wd_ind s
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc 0 s) (hc s T)]
  have h1 : ∫ v in (0 : ℝ)..s, wd v * (if v ≤ s then 1 else 0) = ∫ v in (0 : ℝ)..s, wd v := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le hs0] at hv
    simp [hv.2]
  have h2 : ∫ v in s..T, wd v * (if v ≤ s then 1 else 0) = 0 := by
    have : ∀ᵐ v : ℝ, v ∈ uIoc s T → wd v * (if v ≤ s then (1:ℝ) else 0) = 0 := by
      refine Filter.Eventually.of_forall fun v hv => ?_
      rw [uIoc_of_le hsT] at hv
      simp [not_le.2 hv.1]
    rw [intervalIntegral.integral_congr_ae this]
    simp
  rw [h1, h2, add_zero, integral_wd hs0]


open GppMobiusEcho in
/-- `S j` as a sum over a larger range with an indicator. -/
theorem S_eq_sum_ite {j M : ℕ} (hj : j ≤ M) :
    S j = ∑ m ∈ Finset.Icc 1 M, if m ≤ j then a m else 0 := by
  rw [← Finset.sum_filter, S]
  congr 1
  ext m
  simp only [Finset.mem_Icc, Finset.mem_filter]
  omega

open GppMobiusEcho in
/-- **The inner convolution.** For `T ≥ 0`:
`∫₀ᵀ w′(v) B(T − v) dv = Σ_{m ≤ e^T} a(m) w(T − log m) − c w(T)`. -/
theorem cw_formula (c : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ v in (0 : ℝ)..T, wd v * B c (T - v) =
      ∑ m ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, a m * w (T - Real.log m) - c * w T := by
  set M := ⌊Real.exp T⌋₊ with hM
  have hpt : ∀ v ∈ uIcc (0 : ℝ) T, wd v * B c (T - v) =
      (∑ m ∈ Finset.Icc 1 M, a m * (wd v * (if v ≤ T - Real.log m then (1:ℝ) else 0))) -
        c * wd v := by
    intro v hv
    rw [uIcc_of_le hT] at hv
    have hle : ⌊Real.exp (T - v)⌋₊ ≤ M :=
      Nat.floor_le_floor (Real.exp_le_exp.2 (by linarith [hv.1]))
    have hB : B c (T - v) = (∑ m ∈ Finset.Icc 1 M, if v ≤ T - Real.log m then a m else 0) - c := by
      unfold B b
      rw [S_eq_sum_ite hle]
      congr 1
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
      have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
      have : m ≤ ⌊Real.exp (T - v)⌋₊ ↔ v ≤ T - Real.log m := by
        rw [Nat.le_floor_iff (Real.exp_pos _).le, ← Real.log_le_iff_le_exp hmpos]
        constructor <;> intro h <;> linarith
      simp only [this]
    rw [hB, mul_sub, Finset.mul_sum, mul_comm (wd v) c]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases h : v ≤ T - Real.log m <;> simp [h, mul_comm]
  rw [intervalIntegral.integral_congr hpt]
  have hint : ∀ m ∈ Finset.Icc 1 M, IntervalIntegrable
      (fun v => a m * (wd v * (if v ≤ T - Real.log m then (1:ℝ) else 0))) volume 0 T :=
    fun m _ => (intervalIntegrable_wd_ind _ 0 T).const_mul _
  have hsum : IntervalIntegrable (fun x => ∑ m ∈ Finset.Icc 1 M,
      a m * (wd x * (if x ≤ T - Real.log m then (1:ℝ) else 0))) volume 0 T := by
    have := IntervalIntegrable.sum (Finset.Icc 1 M) hint
    rwa [Finset.sum_fn] at this
  rw [intervalIntegral.integral_sub hsum
      (continuous_wd.intervalIntegrable 0 T |>.const_mul c),
    intervalIntegral.integral_finsetSum hint, intervalIntegral.integral_const_mul,
    integral_wd hT]
  congr 1
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
  have hmM : m ≤ M := (Finset.mem_Icc.1 hm).2
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hlog0 : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm1)
  have hlogT : Real.log m ≤ T := by
    have : (m : ℝ) ≤ Real.exp T := by
      have := (Nat.le_floor_iff (Real.exp_pos T).le).1 hmM
      exact this
    calc Real.log m ≤ Real.log (Real.exp T) := Real.log_le_log hmpos this
      _ = T := Real.log_exp T
  rw [intervalIntegral.integral_const_mul, integral_wd_indicator (by linarith) (by linarith)]


open GppMobiusEcho in
theorem measurable_B (c : ℝ) : Measurable (B c) :=
  (measurable_from_nat (f := b c)).comp (Measurable.nat_floor Real.measurable_exp)

open GppMobiusEcho in
theorem intervalIntegrable_B (c : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (B c) volume 0 T := by
  set M := ⌊Real.exp T⌋₊
  set C : ℝ := ∑ j ∈ Finset.range (M + 1), |b c j|
  refine (intervalIntegrable_const (c := C)).mono_fun (measurable_B c).aestronglyMeasurable ?_
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
  refine Filter.Eventually.of_forall fun u hu => ?_
  rw [uIoc_of_le hT] at hu
  have hle : ⌊Real.exp u⌋₊ ≤ M := Nat.floor_le_floor (Real.exp_le_exp.2 hu.2)
  have : |b c ⌊Real.exp u⌋₊| ≤ C :=
    Finset.single_le_sum (f := fun j => |b c j|) (fun j _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hle))
  simpa [B] using this.trans (le_abs_self C)

open GppMobiusEcho in
theorem intervalIntegrable_wd_shift_B (c : ℝ) (L t : ℝ) (ht : 0 ≤ t) :
    IntervalIntegrable (fun s => wd (s - L) * B c (t - s)) volume 0 t := by
  have h1 : IntervalIntegrable (fun s => B c (t - s)) volume 0 t := by
    have := (intervalIntegrable_B c ht).comp_sub_left t
    simpa using this.symm
  exact h1.continuousOn_mul (continuous_wd.comp (continuous_id.sub continuous_const)).continuousOn

/-- The shifted inner convolution: for `0 ≤ L ≤ t`,
`∫₀ᵗ w′(s − L) B(t − s) ds = ∫₀^{t−L} w′(v) B(t − L − v) dv`. -/
theorem shift_integral (c : ℝ) {L t : ℝ} (hL : 0 ≤ L) (hLt : L ≤ t) :
    ∫ s in (0 : ℝ)..t, wd (s - L) * GppMobiusEcho.B c (t - s) =
      ∫ v in (0 : ℝ)..(t - L), wd v * GppMobiusEcho.B c (t - L - v) := by
  have ht : 0 ≤ t := hL.trans hLt
  have hint := intervalIntegrable_wd_shift_B c L t ht
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := L) (hint.mono_set (by
      rw [uIcc_of_le hL, uIcc_of_le ht]; exact Icc_subset_Icc le_rfl hLt)) (hint.mono_set (by
      rw [uIcc_of_le hLt, uIcc_of_le ht]; exact Icc_subset_Icc hL le_rfl))]
  have h0 : ∫ s in (0 : ℝ)..L, wd (s - L) * GppMobiusEcho.B c (t - s) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_]
    · simp
    · rw [uIcc_of_le hL] at hs
      simp [wd_of_nonpos (by linarith [hs.2] : s - L ≤ 0)]
  rw [h0, zero_add]
  have := intervalIntegral.integral_comp_add_right
    (fun s => wd (s - L) * GppMobiusEcho.B c (t - s)) (a := 0) (b := t - L) L
  rw [zero_add, sub_add_cancel] at this
  rw [← this]
  refine intervalIntegral.integral_congr fun v _ => ?_
  show wd (v + L - L) * GppMobiusEcho.B c (t - (v + L)) = wd v * GppMobiusEcho.B c (t - L - v)
  rw [add_sub_cancel_right]
  congr 2
  ring


section NT
open Finset

theorem sum_antidiag_moebius (k : ℕ) :
    ∑ x ∈ k.divisorsAntidiagonal, (moebius x.2 : ℝ) = if k = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f k) (coe_zeta_mul_coe_moebius (R := ℝ))
  simp only [mul_apply, natCoe_apply, intCoe_apply, zeta_apply, one_apply] at h
  rw [← h]
  refine sum_congr rfl fun x hx => ?_
  have : x.1 ≠ 0 := by
    have := (Nat.mem_divisorsAntidiagonal.1 hx)
    intro h0; simp [h0] at this
    exact this.2 this.1.symm
  simp [this]

/-- Regrouping `Σ_{n ≤ N} Σ_{m ≤ N/n} μ(m) G(nm) = G(1)` (`N ≥ 1`) via `Σ_{d | k} μ(d) = [k = 1]`. -/
theorem sum_double_moebius (G : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, ∑ m ∈ Finset.Ioc 0 (N / n), (moebius m : ℝ) * G (n * m) =
      if 1 ≤ N then G 1 else 0 := by
  have h1 : ∑ n ∈ Finset.Ioc 0 N, ∑ m ∈ Finset.Ioc 0 (N / n), (moebius m : ℝ) * G (n * m) =
      ∑ x ∈ (Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N).filter (fun x => x.1 * x.2 ≤ N),
        (moebius x.2 : ℝ) * G (x.1 * x.2) := by
    rw [sum_filter, sum_product]
    refine sum_congr rfl fun n hn => ?_
    rw [← sum_filter]
    refine sum_congr ?_ (fun _ _ => rfl)
    ext m
    simp only [Finset.mem_Ioc, mem_filter] at hn ⊢
    have hn0 : 0 < n := hn.1
    constructor
    · rintro ⟨h0, h2⟩
      have h3 : m * n ≤ N := (Nat.le_div_iff_mul_le hn0).1 h2
      refine ⟨⟨h0, by nlinarith⟩, by linarith [mul_comm n m]⟩
    · rintro ⟨⟨h0, _⟩, h3⟩
      exact ⟨h0, (Nat.le_div_iff_mul_le hn0).2 (by linarith [mul_comm n m])⟩
  rw [h1, ← sum_fiberwise_of_maps_to (g := fun x : ℕ × ℕ => x.1 * x.2) (t := Finset.Ioc 0 N)]
  · have : ∀ k ∈ Finset.Ioc 0 N, ∑ x ∈ ((Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N).filter (fun x => x.1 * x.2 ≤ N)).filter
        (fun x => x.1 * x.2 = k), (moebius x.2 : ℝ) * G (x.1 * x.2) =
        G k * (if k = 1 then 1 else 0) := by
      intro k hk
      have hk' := Finset.mem_Ioc.1 hk
      have hfib : ((Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N).filter (fun x => x.1 * x.2 ≤ N)).filter
          (fun x => x.1 * x.2 = k) = k.divisorsAntidiagonal := by
        rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le hk'.1.ne' hk'.2]
        ext x
        simp only [mem_filter]
        constructor
        · rintro ⟨⟨h, _⟩, h2⟩; exact ⟨h, h2⟩
        · rintro ⟨h, h2⟩; exact ⟨⟨h, by rw [h2]; exact hk'.2⟩, h2⟩
      rw [hfib]
      have : ∀ x ∈ k.divisorsAntidiagonal, (moebius x.2 : ℝ) * G (x.1 * x.2) =
          G k * (moebius x.2 : ℝ) := by
        intro x hx
        rw [(Nat.mem_divisorsAntidiagonal.1 hx).1, mul_comm]
      rw [sum_congr rfl this, ← mul_sum, sum_antidiag_moebius]
    rw [sum_congr rfl this]
    by_cases hN : 1 ≤ N
    · rw [if_pos hN]
      rw [sum_eq_single 1]
      · simp
      · intro k _ hk1; simp [hk1]
      · intro h; exact absurd (Finset.mem_Ioc.2 ⟨Nat.one_pos, hN⟩) h
    · rw [if_neg hN]
      have : Finset.Ioc 0 N = ∅ := by
        ext k; simp only [Finset.mem_Ioc, Finset.notMem_empty, iff_false]; intro h; exact hN (by omega)
      simp [this]
  · intro x hx
    simp only [mem_filter, mem_product, Finset.mem_Ioc] at hx ⊢
    exact ⟨Nat.mul_pos hx.1.1.1 hx.1.2.1, hx.2⟩


end NT

/-- The convolution with the measure `ν = Σ n^{-1/2} δ_{log n}`, as a locally finite sum. -/
noncomputable def nuConv (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, f (t - Real.log n) / Real.sqrt n

/-- `Z = ν ∗ w`. -/
noncomputable def Z (t : ℝ) : ℝ := nuConv w t

/-- `k = ν ∗ w′`. -/
noncomputable def kk (t : ℝ) : ℝ := nuConv wd t

/-- `h = w − c Z`. -/
noncomputable def hh (c t : ℝ) : ℝ := w t - c * Z t

/-- For `s ≤ t`, the terms of `k(s)` beyond `e^s` vanish, so `k(s)` can be summed to `e^t`. -/
theorem kk_eq_sum {s t : ℝ} (hst : s ≤ t) :
    kk s = ∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, wd (s - Real.log n) / Real.sqrt n := by
  unfold kk nuConv
  refine Finset.sum_subset ?_ ?_
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans (Nat.floor_le_floor (Real.exp_le_exp.2 hst))⟩
  · intro n hn hn'
    have h1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    simp only [Finset.mem_Icc, not_and, not_le] at hn'
    have hnpos : (0 : ℝ) < n := by exact_mod_cast h1
    have : Real.exp s < n := by
      have := hn' h1
      have h2 : ⌊Real.exp s⌋₊ < n := this
      exact (Nat.floor_lt (Real.exp_pos s).le).1 h2
    have hlog : s < Real.log n := (Real.lt_log_iff_exp_lt hnpos).2 this
    simp [wd_of_neg (by linarith : s - Real.log n < 0)]


open GppMobiusEcho in
/-- **Part B: the causal identity** `h = k ⋆ B` on `[0, ∞)`, in the form
`h(t) = ∫₀ᵗ k(s) B(t − s) ds` for `t ≥ 0`, where `h = w − cZ`, `k = ν ∗ w′`,
`B(u) = Σ_{n ≤ e^u} μ(n)/√n − c`. The proof is the finite divisor collapse `Σ_{d|N} μ(d) = [N = 1]`. -/
theorem causal_identity (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    hh c t = ∫ s in (0 : ℝ)..t, kk s * B c (t - s) := by
  set N := ⌊Real.exp t⌋₊ with hN
  have hN1 : 1 ≤ N := by
    rw [hN]; exact Nat.le_floor (by simpa using Real.one_le_exp ht)
  -- step 1: expand `k` as a finite sum on `[0, t]`
  have h1 : ∫ s in (0 : ℝ)..t, kk s * B c (t - s) =
      ∫ s in (0 : ℝ)..t, ∑ n ∈ Finset.Icc 1 N, (1 / Real.sqrt n) * (wd (s - Real.log n) * B c (t - s)) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht] at hs
    rw [kk_eq_sum hs.2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  -- step 2: pull the sum out
  have hint : ∀ n ∈ Finset.Icc 1 N, IntervalIntegrable
      (fun s => (1 / Real.sqrt n) * (wd (s - Real.log n) * B c (t - s))) volume 0 t :=
    fun n _ => (intervalIntegrable_wd_shift_B c (Real.log n) t ht).const_mul _
  rw [h1, intervalIntegral.integral_finsetSum hint]
  -- step 3: each summand
  have h2 : ∀ n ∈ Finset.Icc 1 N,
      ∫ s in (0 : ℝ)..t, (1 / Real.sqrt n) * (wd (s - Real.log n) * B c (t - s)) =
        (1 / Real.sqrt n) * (∑ m ∈ Finset.Icc 1 (N / n),
          a m * w (t - Real.log n - Real.log m) - c * w (t - Real.log n)) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnN : (n : ℝ) ≤ Real.exp t :=
      (Nat.le_floor_iff (Real.exp_pos t).le).1 (Finset.mem_Icc.1 hn).2
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    have hlogt : Real.log n ≤ t := by
      calc Real.log n ≤ Real.log (Real.exp t) := Real.log_le_log hnpos hnN
        _ = t := Real.log_exp t
    rw [intervalIntegral.integral_const_mul, shift_integral c hlog0 hlogt,
      cw_formula c (by linarith : 0 ≤ t - Real.log n)]
    congr 3
    rw [Real.exp_sub, Real.exp_log hnpos, hN, Nat.floor_div_natCast]
  rw [Finset.sum_congr rfl h2]
  have hIcc : ∀ X : ℕ, Finset.Icc 1 X = Finset.Ioc 0 X := by
    intro X; ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hG := sum_double_moebius (fun k : ℕ => w (t - Real.log k) / Real.sqrt k) N
  rw [if_pos hN1] at hG
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      (1 / Real.sqrt n) * (∑ m ∈ Finset.Icc 1 (N / n),
          a m * w (t - Real.log n - Real.log m) - c * w (t - Real.log n)) =
        (∑ m ∈ Finset.Ioc 0 (N / n), (moebius m : ℝ) *
            (fun k : ℕ => w (t - Real.log k) / Real.sqrt k) (n * m)) -
          c * (w (t - Real.log n) / Real.sqrt n) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [mul_sub, Finset.mul_sum, hIcc (N / n)]
    congr 1
    · refine Finset.sum_congr rfl fun m hm => ?_
      have hm1 : 0 < m := (Finset.mem_Ioc.1 hm).1
      have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
      simp only [a, Nat.cast_mul]
      rw [Real.log_mul hnpos.ne' hmpos.ne', Real.sqrt_mul hnpos.le]
      have : t - Real.log n - Real.log m = t - (Real.log n + Real.log m) := by ring
      rw [this]
      have hs1 : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
      have hs2 : 0 < Real.sqrt m := Real.sqrt_pos.2 hmpos
      field_simp
    · field_simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [hIcc N] at hG ⊢
  rw [hG]
  have hZ : Z t = ∑ n ∈ Finset.Ioc 0 N, w (t - Real.log n) / Real.sqrt n := by
    unfold Z nuConv
    rw [← hN, hIcc]
  unfold hh
  rw [hZ]
  simp


/-- **Interface to Part A.** For `t ∈ (0, L]`, `h(t) = (k₀ ⋆ B₀)(t)` where `k₀ = k·1_{(0,∞)}`,
`B₀ = B·1_{(0,L]}` and `⋆` is `GppCausalTail.rconv` — exactly the hypothesis `hconv` of
`GppCausalTail.causal_tail_estimate`. -/
theorem causal_identity_rconv (c L : ℝ) {t : ℝ} (ht : t ∈ Ioc 0 L) :
    hh c t = GppCausalTail.rconv ((Ioi (0:ℝ)).indicator kk)
      ((Ioc (0:ℝ) L).indicator (GppMobiusEcho.B c)) t := by
  rw [GppCausalTail.rconv_apply]
  have hF : (fun s : ℝ => (Ioi (0:ℝ)).indicator kk s *
      (Ioc (0:ℝ) L).indicator (GppMobiusEcho.B c) (t - s)) =
      (Ioo (0:ℝ) t).indicator (fun s => kk s * GppMobiusEcho.B c (t - s)) := by
    funext s
    by_cases hs : s ∈ Ioo (0:ℝ) t
    · have h1 : s ∈ Ioi (0:ℝ) := hs.1
      have h2 : t - s ∈ Ioc (0:ℝ) L := ⟨by linarith [hs.2], by linarith [hs.1, ht.2]⟩
      simp [indicator_of_mem hs, indicator_of_mem h1, indicator_of_mem h2]
    · rw [indicator_of_notMem hs]
      by_cases h1 : s ∈ Ioi (0:ℝ)
      · have h2 : t - s ∉ Ioc (0:ℝ) L := by
          intro h
          exact hs ⟨h1, by linarith [h.1]⟩
        simp [indicator_of_notMem h2]
      · simp [indicator_of_notMem h1]
  rw [hF, integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le ht.1.le]
  exact causal_identity c ht.1.le

end GppCausalKernels
