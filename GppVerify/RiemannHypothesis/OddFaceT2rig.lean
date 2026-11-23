import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# OddFace(0.5), (T2-rig): the 5/4 step and the exact trigonometric reduction

Heart's Round 12 (GPP-bridge PR #11, comment 6890806135; GPPDiscovery5 `1da974d`) closes (T2-rig)
at `L = 0.5`: `|ω_j⁴ ρ_j(δ)| ≤ 19.5770` for `j ≥ 13`. Turbo's audit (bridge CONVERSATION.md, fa7c6ec)
banks it, with one **named gap for formalisation**: Lemma B's factor `5/4` in the unimodal
sum-vs-integral step "is stated in one line in the note, not derived there … any proof-grade or Lean
use needs that step written out." This file writes it out and proves it.

* **`unimodal_tsum_sub_integral`** (general): let `f` be continuous, `≥ 0` on `[0, ∞)`, nondecreasing
  on `[0, m]` and nonincreasing on `[m, ∞)`, and integrable on `(0, ∞)`. Then for `θ ≥ 0`,
  `n ↦ f(n + θ)` is summable and `|Σ_n f(n + θ) − ∫₀^∞ f| ≤ (1 + θ) f(m)`.
  Proof: `f = g + h − f(m)` with `g = f(min · m)` monotone and `h = f(max · m)` antitone. Each
  comparison costs at most `f(m)`, with opposite signs, so `|Σ − ∫_θ^∞| ≤ f(m)`. The piece
  `∫₀^θ f ∈ [0, θ f(m)]` adds the `θ`.
* **`lemmaB`** (Heart's Lemma B, the `5/4` constant): for `t > 0`,
  `|Σ_{n≥0} b(n+¼)/((n+¼)² + b²)² − 1/t| ≤ κ/t²` with `b = t/2` and `κ = (5/4)·9/(4√3)`.
 The unimodal profile `x ↦ bx/(x² + b²)²` peaks at `m = b/√3`
  with value `9/(16√3 b²)`, and integrates to `1/(2b)`.
* **`P_expand`** (R12 reduction, CHECKED → PROVED):
  `sin⁴(t/2) sin²(t/4) = 3/16 − cos(t/2)/16 − cos t/4 + 3cos(3t/2)/32 + cos(2t)/16 − cos(5t/2)/32`.
* **`sin_half_mode`**: at `ω = 4mπ` every `sin(kω/2)` is `0`. This is why the `A(ω)` and `log π`
  parts of `Q` drop out exactly at `L = 0.5`.

**Scope.**
 OddFace(0.5) proof-grade is OPEN (pending (H-A), (H-ρ), items 3′/4); RH is
OPEN. No `sorry`, no axioms.
-/

namespace GppOddFaceT2rig

open Real MeasureTheory Set Filter Topology Finset

/-! ### The unimodal sum–integral comparison -/

/-- Finite core: `|Σ_{i<N} f(θ+i) − ∫_θ^{θ+N} f| ≤ f(m)` for unimodal `f ≥ 0` peaking at `m`. -/
theorem unimodal_sum_sub_integral_le {f : ℝ → ℝ} {θ m : ℝ} (hθ : 0 ≤ θ) (hm : 0 ≤ m)
    (hc : Continuous f) (hf0 : ∀ x, 0 ≤ x → 0 ≤ f x)
    (hinc : ∀ x y, 0 ≤ x → x ≤ y → y ≤ m → f x ≤ f y)
    (hdec : ∀ x y, m ≤ x → x ≤ y → f y ≤ f x) (N : ℕ) :
    |∑ i ∈ range N, f (θ + i) - ∫ x in θ..θ + N, f x| ≤ f m := by
  set g : ℝ → ℝ := fun x => f (min x m) with hg
  set h : ℝ → ℝ := fun x => f (max x m) with hh
  have hgc : Continuous g := hc.comp (continuous_id.min continuous_const)
  have hhc : Continuous h := hc.comp (continuous_id.max continuous_const)
  have hsplit : ∀ x, f x = g x + h x - f m := fun x => by
    simp only [hg, hh]
    rcases le_total x m with hx | hx
    · rw [min_eq_left hx, max_eq_right hx]; ring
    · rw [min_eq_right hx, max_eq_left hx]; ring
  have gmono : MonotoneOn g (Icc θ (θ + N)) := fun x hx y hy hxy => by
    simp only [hg]
    exact hinc _ _ (le_min (hθ.trans hx.1) hm) (min_le_min_right m hxy) (min_le_right _ _)
  have hanti : AntitoneOn h (Icc θ (θ + N)) := fun x _ y _ hxy => by
    simp only [hh]
    exact hdec _ _ (le_max_right _ _) (max_le_max_right m hxy)
  have g0 : 0 ≤ g θ := hf0 _ (le_min hθ hm)
  have gM : g (θ + N) ≤ f m := hinc _ _ (le_min (by positivity) hm) (min_le_right _ _) le_rfl
  have h0 : 0 ≤ h (θ + N) := hf0 _ (hm.trans (le_max_right _ _))
  have hM : h θ ≤ f m := hdec _ _ le_rfl (le_max_right _ _)
  -- Monotone `g`: `Σ g(θ+i) ≤ ∫ g ≤ Σ g(θ+i+1)`; antitone `h`: the reverse.
  have g1 := gmono.sum_le_integral
  have g2 := gmono.integral_le_sum
  have h1 := hanti.sum_le_integral
  have h2 := hanti.integral_le_sum
  have tg : ∑ i ∈ range N, g (θ + ↑(i + 1)) - ∑ i ∈ range N, g (θ + i) = g (θ + N) - g θ := by
    rw [← Finset.sum_sub_distrib]
    have := Finset.sum_range_sub (fun i : ℕ => g (θ + i)) N
    simpa using this
  have th : ∑ i ∈ range N, h (θ + ↑(i + 1)) - ∑ i ∈ range N, h (θ + i) = h (θ + N) - h θ := by
    rw [← Finset.sum_sub_distrib]
    have := Finset.sum_range_sub (fun i : ℕ => h (θ + i)) N
    simpa using this
  -- Decompose the sum and the integral of `f`.
  have hsum : ∑ i ∈ range N, f (θ + i)
      = ∑ i ∈ range N, g (θ + i) + ∑ i ∈ range N, h (θ + i) - N * f m := by
    rw [Finset.sum_congr rfl (fun (i : ℕ) _ => hsplit (θ + (i : ℝ)))]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  have hint : ∫ x in θ..θ + N, f x
      = (∫ x in θ..θ + N, g x) + (∫ x in θ..θ + N, h x) - N * f m := by
    rw [intervalIntegral.integral_congr (g := fun x => g x + h x - f m) (fun x _ => hsplit x)]
    have e1 : ∫ x in θ..θ + N, (g x + h x - f m)
        = (∫ x in θ..θ + N, (g x + h x)) - ∫ _ in θ..θ + N, f m :=
      intervalIntegral.integral_sub ((hgc.add hhc).intervalIntegrable _ _) intervalIntegrable_const
    have e2 : ∫ x in θ..θ + N, (g x + h x) = (∫ x in θ..θ + N, g x) + ∫ x in θ..θ + N, h x :=
      intervalIntegral.integral_add (hgc.intervalIntegrable _ _) (hhc.intervalIntegrable _ _)
    rw [e1, e2, intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hsum, hint, abs_le]
  constructor <;> linarith

/-- **The unimodal sum–integral bound with offset `θ`.** -/
theorem unimodal_tsum_sub_integral {f : ℝ → ℝ} {θ m : ℝ} (hθ : 0 ≤ θ) (hm : 0 ≤ m)
    (hc : Continuous f) (hf0 : ∀ x, 0 ≤ x → 0 ≤ f x)
    (hinc : ∀ x y, 0 ≤ x → x ≤ y → y ≤ m → f x ≤ f y)
    (hdec : ∀ x y, m ≤ x → x ≤ y → f y ≤ f x) (hI : IntegrableOn f (Ioi 0)) :
    Summable (fun n : ℕ => f (θ + n)) ∧
      |∑' n : ℕ, f (θ + n) - ∫ x in Ioi 0, f x| ≤ (1 + θ) * f m := by
  have hfM : ∀ x, 0 ≤ x → f x ≤ f m := fun x hx => by
    rcases le_total x m with h | h
    · exact hinc _ _ hx h le_rfl
    · exact hdec _ _ le_rfl h
  have core := unimodal_sum_sub_integral_le hθ hm hc hf0 hinc hdec
  -- `∫_θ^{θ+N} f ≤ ∫_{(0,∞)} f`.
  have hsub : ∀ N : ℕ, ∫ x in θ..θ + N, f x ≤ ∫ x in Ioi 0, f x := fun N => by
    rw [intervalIntegral.integral_of_le (by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])]
    refine setIntegral_mono_set hI ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hf0 x (le_of_lt hx)
    · exact (show Ioc θ (θ + N) ⊆ Ioi 0 from fun x hx => lt_of_le_of_lt hθ hx.1).eventuallyLE
  have hS : Summable (fun n : ℕ => f (θ + n)) := by
    refine summable_of_sum_range_le (fun n => hf0 _ (by positivity)) (c := f m + ∫ x in Ioi 0, f x)
      fun N => ?_
    have := (abs_le.1 (core N)).2
    linarith [hsub N]
  refine ⟨hS, ?_⟩
  -- `0 ≤ ∫₀^θ f ≤ θ f(m)`.
  have hA0 : 0 ≤ ∫ x in (0:ℝ)..θ, f x :=
    intervalIntegral.integral_nonneg hθ fun x hx => hf0 x hx.1
  have hA1 : ∫ x in (0:ℝ)..θ, f x ≤ θ * f m := by
    have := intervalIntegral.integral_mono_on hθ (hc.intervalIntegrable _ _)
      (intervalIntegrable_const (μ := volume) (c := f m)) fun x hx => hfM x hx.1
    simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using this
  -- Pass to the limit `N → ∞` in `Σ_{i<N} f(θ+i) − ∫₀^{θ+N} f`.
  have hT : Tendsto (fun N : ℕ => θ + (N : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ θ tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => ∑ i ∈ range N, f (θ + i) - ∫ x in (0:ℝ)..θ + N, f x) atTop
      (𝓝 (∑' n : ℕ, f (θ + n) - ∫ x in Ioi 0, f x)) :=
    hS.hasSum.tendsto_sum_nat.sub (intervalIntegral_tendsto_integral_Ioi 0 hI hT)
  have hsplit : ∀ N : ℕ, ∫ x in (0:ℝ)..θ + N, f x
      = (∫ x in (0:ℝ)..θ, f x) + ∫ x in θ..θ + N, f x := fun N =>
    (intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)).symm
  have hlo : ∀ N : ℕ, -((1 + θ) * f m) ≤
      ∑ i ∈ range N, f (θ + i) - ∫ x in (0:ℝ)..θ + N, f x := fun N => by
    rw [hsplit]; have := (abs_le.1 (core N)).1; nlinarith
  have hhi : ∀ N : ℕ, ∑ i ∈ range N, f (θ + i) - ∫ x in (0:ℝ)..θ + N, f x ≤ (1 + θ) * f m :=
    fun N => by
      rw [hsplit]; have := (abs_le.1 (core N)).2
      have : 0 ≤ θ * f m := mul_nonneg hθ (hf0 m hm)
      nlinarith
  rw [abs_le]
  exact ⟨ge_of_tendsto' hlim hlo, le_of_tendsto' hlim hhi⟩

/-! ### Heart's Lemma B -/

/-- The profile `x ↦ b x / (x² + b²)²` of the series for `A'(t)`, `b = t/2`. -/
noncomputable def prof (b x : ℝ) : ℝ := b * x / (x ^ 2 + b ^ 2) ^ 2

theorem prof_cross (b x y : ℝ) :
    y * (x ^ 2 + b ^ 2) ^ 2 - x * (y ^ 2 + b ^ 2) ^ 2
      = (y - x) * (b ^ 4 - 2 * x * y * b ^ 2 - x * y * (x ^ 2 + x * y + y ^ 2)) := by ring

theorem prof_le_iff {b x y : ℝ} (hb : 0 < b) :
    prof b x ≤ prof b y ↔ b * x * (y ^ 2 + b ^ 2) ^ 2 ≤ b * y * (x ^ 2 + b ^ 2) ^ 2 := by
  unfold prof
  rw [div_le_div_iff₀ (by positivity) (by positivity)]

/-- The peak value: `prof b (b/√3) = 9/(16√3 b²)`, and `prof b x ≤` that for `x ≥ 0`. -/
theorem prof_peak {b : ℝ} (hb : 0 < b) : prof b (b / √3) = 9 / (16 * √3 * b ^ 2) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  unfold prof
  field_simp
  rw [show √3 ^ 4 = (√3 ^ 2) ^ 2 by ring, h3]
  nlinarith [h3]

theorem prof_inc {b : ℝ} (hb : 0 < b) :
    ∀ x y, 0 ≤ x → x ≤ y → y ≤ b / √3 → prof b x ≤ prof b y := fun x y hx hxy hy => by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have hy0 : 0 ≤ y := hx.trans hxy
  have hm2 : (b / √3) ^ 2 = b ^ 2 / 3 := by rw [div_pow, h3]
  have hyy : y ^ 2 ≤ b ^ 2 / 3 := by rw [← hm2]; exact pow_le_pow_left₀ hy0 hy 2
  have hxy2 : x * y ≤ b ^ 2 / 3 := by nlinarith
  have hs : x ^ 2 + x * y + y ^ 2 ≤ b ^ 2 := by nlinarith
  have hp : 0 ≤ x * y := mul_nonneg hx hy0
  have hbr : 0 ≤ b ^ 4 - 2 * x * y * b ^ 2 - x * y * (x ^ 2 + x * y + y ^ 2) := by
    have := mul_le_mul hxy2 hs (by positivity) (by positivity)
    nlinarith
  rw [prof_le_iff hb]
  have := prof_cross b x y
  nlinarith [mul_nonneg (sub_nonneg.2 hxy) hbr]

theorem prof_dec {b : ℝ} (hb : 0 < b) :
    ∀ x y, b / √3 ≤ x → x ≤ y → prof b y ≤ prof b x := fun x y hx hxy => by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have hm0 : 0 ≤ b / √3 := by positivity
  have hx0 : 0 ≤ x := hm0.trans hx
  have hm2 : (b / √3) ^ 2 = b ^ 2 / 3 := by rw [div_pow, h3]
  have hxx : b ^ 2 / 3 ≤ x ^ 2 := by rw [← hm2]; exact pow_le_pow_left₀ hm0 hx 2
  have hxy2 : b ^ 2 / 3 ≤ x * y := by nlinarith
  have hs : b ^ 2 ≤ x ^ 2 + x * y + y ^ 2 := by nlinarith
  have hbr : b ^ 4 - 2 * x * y * b ^ 2 - x * y * (x ^ 2 + x * y + y ^ 2) ≤ 0 := by
    have := mul_le_mul hxy2 hs (by positivity) (by nlinarith)
    nlinarith
  rw [prof_le_iff hb]
  have := prof_cross b y x
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hxy) hbr]

theorem prof_integral {b : ℝ} (hb : 0 < b) :
    IntegrableOn (prof b) (Ioi 0) ∧ ∫ x in Ioi 0, prof b x = 1 / (2 * b) := by
  set F : ℝ → ℝ := fun x => -b / (2 * (x ^ 2 + b ^ 2)) with hF
  have hd : ∀ x, HasDerivAt F (prof b x) x := fun x => by
    have hpos : 0 < 2 * (x ^ 2 + b ^ 2) := by positivity
    have h1 : HasDerivAt (fun x : ℝ => 2 * (x ^ 2 + b ^ 2)) (2 * (2 * x)) x := by
      have := ((hasDerivAt_pow 2 x).add_const (b ^ 2)).const_mul 2
      simpa using this
    have := (hasDerivAt_const x (-b)).div h1 hpos.ne'
    refine this.congr_deriv ?_
    unfold prof
    field_simp
    ring
  have hcont : ContinuousWithinAt F (Ici 0) 0 :=
    (Continuous.div continuous_const (by fun_prop) fun x => by positivity :
      Continuous F).continuousAt.continuousWithinAt
  have hnn : ∀ x ∈ Ioi (0:ℝ), 0 ≤ prof b x := fun x hx => by
    unfold prof; have : (0:ℝ) < x := hx; positivity
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => 2 * (x ^ 2 + b ^ 2)) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num)
        (tendsto_atTop_add_const_right _ _ (tendsto_pow_atTop two_ne_zero))
    have := h.inv_tendsto_atTop.const_mul (-b)
    simpa [F, div_eq_mul_inv] using this
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hcont (fun x _ => hd x) hnn hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont (fun x _ => hd x) hnn hlim]
  simp only [F]
  field_simp
  ring

/-- **Heart's Lemma B, with the `5/4` written out.** For `b > 0`,
`|Σ_{n≥0} b(n+¼)/((n+¼)² + b²)² − 1/(2b)| ≤ (5/4) · 9/(16√3 b²)`. -/
theorem lemmaB_b {b : ℝ} (hb : 0 < b) :
    |∑' n : ℕ, prof b (1 / 4 + n) - 1 / (2 * b)| ≤ 5 / 4 * (9 / (16 * √3 * b ^ 2)) := by
  have hr : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have hc : Continuous (prof b) := by
    unfold prof
    exact Continuous.div (by fun_prop) (by fun_prop) fun x => by positivity
  have hf0 : ∀ x, 0 ≤ x → 0 ≤ prof b x := fun x hx => by unfold prof; positivity
  obtain ⟨hI, hval⟩ := prof_integral hb
  have := (unimodal_tsum_sub_integral (θ := 1 / 4) (m := b / √3) (by norm_num) (by positivity)
    hc hf0 (prof_inc hb) (prof_dec hb) hI).2
  rw [hval, prof_peak hb] at this
  convert this using 2
  norm_num

/-- **Lemma B in Heart's variable** `t = 2b`: `|A'(t) − 1/t| ≤ κ/t²`, `κ = (5/4)·9/(4√3)`, with
`A'(t)` written as the series `Σ_{n≥0} (t/2)(n+¼)/((n+¼)² + (t/2)²)²`. -/
theorem lemmaB {t : ℝ} (ht : 0 < t) :
    |∑' n : ℕ, prof (t / 2) (1 / 4 + n) - 1 / t| ≤ 5 / 4 * (9 / (4 * √3)) / t ^ 2 := by
  have := lemmaB_b (b := t / 2) (by positivity)
  have hr : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  convert this using 2
  · field_simp
  · field_simp
    ring

/-! ### The exact reduction (R12.1) -/

/-- **`P(t) = sin⁴(t/2) sin²(t/4) = Σ_{k≤5} c_k cos(kt/2)`**, with
`c = (3/16, −1/16, −1/4, 3/32, 1/16, −1/32)`. -/
theorem P_expand (t : ℝ) :
    sin (t / 2) ^ 4 * sin (t / 4) ^ 2
      = 3 / 16 - 1 / 16 * cos (t / 2) - 1 / 4 * cos t + 3 / 32 * cos (3 * (t / 2))
        + 1 / 16 * cos (2 * t) - 1 / 32 * cos (5 * (t / 2)) := by
  set y := t / 2 with hy
  have h4 : sin (t / 4) ^ 2 = (1 - cos y) / 2 := by
    have : cos y = 1 - 2 * sin (t / 4) ^ 2 := by
      rw [hy, show t / 2 = 2 * (t / 4) by ring, Real.cos_two_mul, Real.cos_sq']; ring
    linarith
  have e1 : cos t = 2 * cos y ^ 2 - 1 := by rw [hy, ← Real.cos_two_mul]; ring_nf
  have e2 : cos (2 * t) = 2 * (2 * cos y ^ 2 - 1) ^ 2 - 1 := by
    rw [← e1, ← Real.cos_two_mul]
  have e3 : cos (5 * y) = cos (3 * y) * cos (2 * y) - sin (3 * y) * sin (2 * y) := by
    rw [← Real.cos_add]; ring_nf
  rw [h4, e1, e2, e3, Real.cos_three_mul, Real.sin_three_mul, Real.cos_two_mul, Real.sin_two_mul]
  have hsc := Real.sin_sq_add_cos_sq y
  linear_combination
    (-(-4 * cos y ^ 3 + 8 * cos y ^ 2 + 4 * cos y * sin y ^ 2 + 7 * cos y - 8 * sin y ^ 2 - 8) / 16)
      * hsc

/-- **At the `L = 0.5` mode frequencies `ω = 4mπ`, every `sin(kω/2)` vanishes.** -/
theorem sin_half_mode (k m : ℕ) : sin (k * (4 * m * π) / 2) = 0 := by
  have : (k : ℝ) * (4 * m * π) / 2 = ((2 * k * m : ℕ) : ℝ) * π := by push_cast; ring
  rw [this, Real.sin_nat_mul_pi]

end GppOddFaceT2rig

#print axioms GppOddFaceT2rig.unimodal_tsum_sub_integral
#print axioms GppOddFaceT2rig.lemmaB
#print axioms GppOddFaceT2rig.P_expand
