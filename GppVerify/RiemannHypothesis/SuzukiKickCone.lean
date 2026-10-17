import GppVerify.RiemannHypothesis.GammaFreeDuality
import GppVerify.RiemannHypothesis.CramerIntensityBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The gamma-free prime-kick cone: exact identities and the starting enclosure

Source: Codex/GPP, `work/codex/2026-10-16_suzuki_gamma_free_prime_kick_barrier_pivot.md`
(PR11 comment 6215141315); asks by Grok S40/S41 ("kick identities", "starting cone"). The scalar
`T = V − A` is Suzuki's gamma-free negative nonarchimedean screw function (JLMS 108 (2023);
Ramanujan J. 68 (2025), Cor. 1); this file formalizes only the **elementary dynamics** Codex built on
it, for a finite list of events `(w j, u j)` as in `GppGammaFreeDuality`.

Notation (`V` from `GppGammaFreeDuality`): `a0 t = 2 cosh(t/2) = V''(t)`, and on the gap after the first
`k` events `P k t = 4 sinh(t/2) − B_k = T'(t)`, `Tk k t = V t − (B_k t − C_k)`, and
`E k t = 2·a0·T − P²`.
* `hasDerivAt_Tk`, `hasDerivAt_P`, `hasDerivAt_a0`, `hasDerivAt_E`: `T' = P`, `P' = a0`,
  `a0' = sinh(t/2)`, hence **`E' = 2·sinh(t/2)·T`** inside a gap.
* `Tk_continuous_at_event`, `P_jump`, `E_jump`: at an event `u_k` of weight `w_k`, `T` is continuous,
  `P` drops by `w_k`, and `E⁺ − E⁻ = 2 w_k P⁻ − w_k²`.
* `Nplus_jump`, `Nminus_jump`: with `X = √(2 a0 T)`, `N± = X ± P`, `N⁺` drops by `w` and `N⁻` rises by `w`.
* `start_*`: at the first prime power `n = 2` (`w = log 2/√2`, `u = log 2`): `T = 4(3/√2 − 2)`,
  `a0 = 3/√2`, `P⁺ = √2 − log 2/√2`, and `E⁺ = 36 − 24√2 − 2(1 − log 2/2)² > 1.2`, so the starting cone
  `E, N⁺, N⁻ > 0` holds (the note's value `1.20494…`).

**Scope, stated plainly.** Exact calculus and algebra of the cone only. The one inequality the note
needs for all `n`, `N⁺((log n)⁻) ≥ Λ(n)/√n`, and Suzuki's criterion plus Landau's theorem, are **not**
formalized and nothing here proves `T ≥ 0` for the real prime list. No RH claim.
-/

namespace GppSuzukiKickCone

open GppGammaFreeDuality Real

/-- `a0 = V'' = 2 cosh (t/2)`. -/
noncomputable def a0 (t : ℝ) : ℝ := 2 * cosh (t / 2)

/-- `P0 = T'` on the gap after `k` events: `4 sinh (t/2) − B_k`. -/
noncomputable def P (w : ℕ → ℝ) (k : ℕ) (t : ℝ) : ℝ := 4 * sinh (t / 2) - Bs w k

/-- `T` on the gap after `k` events: `V t − (B_k t − C_k)`. -/
noncomputable def Tk (w u : ℕ → ℝ) (k : ℕ) (t : ℝ) : ℝ := V t - (Bs w k * t - Cs w u k)

/-- The energy `E0 = 2 a0 T − P²`. -/
noncomputable def E (w u : ℕ → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  2 * a0 t * Tk w u k t - P w k t ^ 2

theorem hasDerivAt_a0 (t : ℝ) : HasDerivAt a0 (sinh (t / 2)) t := by
  have h := ((Real.hasDerivAt_cosh (t / 2)).comp t ((hasDerivAt_id t).div_const 2)).const_mul 2
  refine h.congr_deriv ?_
  ring

theorem hasDerivAt_V (t : ℝ) : HasDerivAt V (4 * sinh (t / 2)) t := by
  have h := (((Real.hasDerivAt_cosh (t / 2)).comp t ((hasDerivAt_id t).div_const 2)).sub_const 1).const_mul 8
  unfold V
  refine h.congr_deriv ?_
  ring

theorem hasDerivAt_Tk (w u : ℕ → ℝ) (k : ℕ) (t : ℝ) : HasDerivAt (Tk w u k) (P w k t) t := by
  have h := (hasDerivAt_V t).sub (((hasDerivAt_id t).const_mul (Bs w k)).sub_const (Cs w u k))
  unfold Tk P
  refine h.congr_deriv ?_
  ring

theorem hasDerivAt_P (w : ℕ → ℝ) (k : ℕ) (t : ℝ) : HasDerivAt (P w k) (a0 t) t := by
  have h := (((Real.hasDerivAt_sinh (t / 2)).comp t ((hasDerivAt_id t).div_const 2)).const_mul 4).sub_const (Bs w k)
  unfold P a0
  refine h.congr_deriv ?_
  ring

/-- **`E' = 2 sinh (t/2) · T`** inside a prime-free gap. -/
theorem hasDerivAt_E (w u : ℕ → ℝ) (k : ℕ) (t : ℝ) :
    HasDerivAt (E w u k) (2 * sinh (t / 2) * Tk w u k t) t := by
  have h1 := ((hasDerivAt_a0 t).const_mul 2).mul (hasDerivAt_Tk w u k t)
  have h2 := ((hasDerivAt_P w k t).pow 2)
  have h := h1.sub h2
  unfold E
  refine h.congr_deriv ?_
  unfold a0 P Tk
  rw [show (4 * sinh (t / 2) - Bs w k : ℝ) = P w k t from rfl]
  ring

/-! ### Prime kicks -/

/-- `T` is continuous across the event `u k` (both pieces agree there). -/
theorem Tk_continuous_at_event (w u : ℕ → ℝ) (k : ℕ) :
    Tk w u (k + 1) (u k) = Tk w u k (u k) := by
  simp only [Tk, Bs, Cs, Finset.sum_range_succ]
  ring

/-- `P` drops by the weight `w k` at the event. -/
theorem P_jump (w : ℕ → ℝ) (k : ℕ) (t : ℝ) : P w (k + 1) t = P w k t - w k := by
  simp only [P, Bs, Finset.sum_range_succ]
  ring

/-- **Kick identity**: `E⁺ − E⁻ = 2 w P⁻ − w²` at the event `u k`. -/
theorem E_jump (w u : ℕ → ℝ) (k : ℕ) :
    E w u (k + 1) (u k) - E w u k (u k) = 2 * w k * P w k (u k) - w k ^ 2 := by
  unfold E
  rw [Tk_continuous_at_event, P_jump]
  ring

/-- `X = √(2 a0 T)`. -/
noncomputable def X (w u : ℕ → ℝ) (k : ℕ) (t : ℝ) : ℝ := √(2 * a0 t * Tk w u k t)

/-- `N⁺ = X + P`, `N⁻ = X − P`. -/
noncomputable def Nplus (w u : ℕ → ℝ) (k : ℕ) (t : ℝ) : ℝ := X w u k t + P w k t
noncomputable def Nminus (w u : ℕ → ℝ) (k : ℕ) (t : ℝ) : ℝ := X w u k t - P w k t

/-- Kick: `N⁺` drops by `w`, `N⁻` rises by `w`. -/
theorem Nplus_jump (w u : ℕ → ℝ) (k : ℕ) :
    Nplus w u (k + 1) (u k) = Nplus w u k (u k) - w k := by
  unfold Nplus X
  rw [Tk_continuous_at_event, P_jump]
  ring

theorem Nminus_jump (w u : ℕ → ℝ) (k : ℕ) :
    Nminus w u (k + 1) (u k) = Nminus w u k (u k) + w k := by
  unfold Nminus X
  rw [Tk_continuous_at_event, P_jump]
  ring

/-- Where `T ≥ 0`, `E = X² − P² = N⁺ N⁻`. -/
theorem E_eq_Nplus_mul_Nminus (w u : ℕ → ℝ) (k : ℕ) (t : ℝ) (hT : 0 ≤ Tk w u k t) :
    E w u k t = Nplus w u k t * Nminus w u k t := by
  have h : 0 ≤ 2 * a0 t * Tk w u k t := by
    have : 0 < a0 t := by unfold a0; have := cosh_pos (t / 2); linarith
    positivity
  have hs : X w u k t ^ 2 = 2 * a0 t * Tk w u k t := Real.sq_sqrt h
  unfold Nplus Nminus E
  nlinarith [hs]

/-! ### The starting cone at the first prime power `n = 2` -/

theorem start_B (w : ℕ → ℝ) (hw : w 0 = Real.log 2 / √2) : Bs w 1 = Real.log 2 / √2 := by
  simp [Bs, hw]

theorem start_C (w u : ℕ → ℝ) (hw : w 0 = Real.log 2 / √2) (hu : u 0 = Real.log 2) :
    Cs w u 1 = Real.log 2 / √2 * Real.log 2 := by
  simp [Cs, hw, hu]

/-- `T(log 2) = V(log 2)` (no event has fired before `n = 2`), `= 4(3/√2 − 2)`. -/
theorem start_T (w u : ℕ → ℝ) (hw : w 0 = Real.log 2 / √2) (hu : u 0 = Real.log 2) :
    Tk w u 1 (Real.log 2) = 4 * (3 / √2 - 2) := by
  have hs : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hc : cosh (Real.log 2 / 2) = (√2 + 1 / √2) / 2 := by
    rw [Real.cosh_eq, GppCramerIntensityBound.exp_log_half (by norm_num : (0 : ℝ) < 2), Real.exp_neg,
      GppCramerIntensityBound.exp_log_half (by norm_num : (0 : ℝ) < 2)]
    ring
  unfold Tk V
  rw [start_B w hw, start_C w u hw hu, hc]
  field_simp
  nlinarith [h2]



/-- `a0(log 2) = 3/√2`. -/
theorem start_a0 : a0 (Real.log 2) = 3 / √2 := by
  have hs : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hc : cosh (Real.log 2 / 2) = (√2 + 1 / √2) / 2 := by
    rw [Real.cosh_eq, GppCramerIntensityBound.exp_log_half (by norm_num : (0 : ℝ) < 2), Real.exp_neg,
      GppCramerIntensityBound.exp_log_half (by norm_num : (0 : ℝ) < 2)]
    ring
  unfold a0
  rw [hc]
  field_simp
  nlinarith [h2]

/-- `P0(log 2⁺) = √2 − log 2/√2`. -/
theorem start_P (w : ℕ → ℝ) (hw : w 0 = Real.log 2 / √2) :
    P w 1 (Real.log 2) = √2 - Real.log 2 / √2 := by
  have hs : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsh : sinh (Real.log 2 / 2) = (2 - 1) / (2 * √2) :=
    GppCramerIntensityBound.sinh_log_half (by norm_num : (0 : ℝ) < 2)
  unfold P
  rw [start_B w hw, hsh]
  field_simp
  nlinarith [h2]

/-- Closed form `E0(log 2⁺) = 36 − 24√2 − 2 (1 − log 2 / 2)²`. -/
theorem start_E (w u : ℕ → ℝ) (hw : w 0 = Real.log 2 / √2) (hu : u 0 = Real.log 2) :
    E w u 1 (Real.log 2) = 36 - 24 * √2 - 2 * (1 - Real.log 2 / 2) ^ 2 := by
  have hs : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have e1 : 3 / √2 = 3 * √2 / 2 := by field_simp; nlinarith [h2]
  have e2 : Real.log 2 / √2 = Real.log 2 * √2 / 2 := by field_simp; nlinarith [h2]
  unfold E
  rw [start_T w u hw hu, start_P w hw, start_a0, e1, e2]
  linear_combination (18 - (1 - Real.log 2 / 2) ^ 2) * h2

/-- The starting energy exceeds `1.2` (the note's value is `1.20494…`). -/
theorem start_E_gt (w u : ℕ → ℝ) (hw : w 0 = Real.log 2 / √2) (hu : u 0 = Real.log 2) :
    (6 : ℝ) / 5 < E w u 1 (Real.log 2) := by
  rw [start_E w u hw hu]
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg _
  have hs : √2 < 1.4143 := by nlinarith [h2]
  have hl := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  nlinarith [mul_self_nonneg (1 - Real.log 2 / 2)]

/-- **Starting cone at `log 2⁺`**: `T, P, E, N⁺, N⁻ > 0`. -/
theorem start_cone (w u : ℕ → ℝ) (hw : w 0 = Real.log 2 / √2) (hu : u 0 = Real.log 2) :
    0 < Tk w u 1 (Real.log 2) ∧ 0 < P w 1 (Real.log 2) ∧ 0 < E w u 1 (Real.log 2) ∧
      0 < Nplus w u 1 (Real.log 2) ∧ 0 < Nminus w u 1 (Real.log 2) := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hs : √2 < 1.4143 := by nlinarith [h2]
  have hs' : 1.4142 < √2 := by nlinarith [h2]
  have hl := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have hT : 0 < Tk w u 1 (Real.log 2) := by
    rw [start_T w u hw hu]
    have : 3 / √2 = 3 * √2 / 2 := by field_simp; nlinarith [h2]
    rw [this]; nlinarith
  have hP : 0 < P w 1 (Real.log 2) := by
    rw [start_P w hw]
    have : Real.log 2 / √2 = Real.log 2 * √2 / 2 := by field_simp; nlinarith [h2]
    rw [this]; nlinarith
  have hE : 0 < E w u 1 (Real.log 2) := by
    have := start_E_gt w u hw hu; linarith
  have hX : P w 1 (Real.log 2) < X w u 1 (Real.log 2) := by
    unfold X
    apply Real.lt_sqrt_of_sq_lt
    have : E w u 1 (Real.log 2) = 2 * a0 (Real.log 2) * Tk w u 1 (Real.log 2) - P w 1 (Real.log 2) ^ 2 :=
      rfl
    nlinarith
  refine ⟨hT, hP, hE, ?_, ?_⟩
  · unfold Nplus; linarith
  · unfold Nminus; linarith

end GppSuzukiKickCone
