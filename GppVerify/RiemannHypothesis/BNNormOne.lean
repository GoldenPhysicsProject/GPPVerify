import GppVerify.RiemannHypothesis.BNLimit

/-!
# The norm-one limit of `C̄_{N,L}` (Turbo's build-order step (5))

For a fixed nonzero window vector `f ∈ V_L` and admissible cutoffs `L < log(N+1)`:

* **per-vector ratio** `‖C_N f‖² = b_N(f, f) − W(f)` with `W(f) = weilForm(f ⋆ f̃)` independent of `N`
  (`normSq_CNlin_eq`), so `‖C_N f‖² / b_N(f, f) = 1 − W(f)/b_N(f, f)`;
* `b_N(f, f) ≥ (θ(N) + κ_L)‖f‖² → ∞`, hence the ratio tends to `1` (`ratio_ge`);
* with `t_N(0)/(θ(N) + κ_L) → 1` (`tN0_div_le`) the bounded extension of `exists_bounded_extension`
  has `‖C̄_{N,L}‖² → 1` (`bounded_extension_norm_one`).

**Scope.** This is an asymptotic statement that holds *whatever the sign of `W`*: it erases the sign
of `W(f)`, so it carries no information about contractivity (`OB6At`), which stays open. It is the
obstruction Turbo's Theorem 6 records, not progress toward the positivity.

No `sorry`, no axiom.
-/

open MeasureTheory
open GppArithmeticReflection

noncomputable section

namespace GppShiftPresentation

/-- **Per-vector identity.** For admissible `N`, `‖C_N f‖² = b_N(f, f) − W(f)`, `W(f) = weilForm(f ⋆ f̃)`. -/
theorem normSq_CNlin_eq (N : ℕ) {L : ℝ} (f : windowSubmodule L) (hN : L < Real.log (N + 1)) :
    ‖CNlin N L f‖ ^ 2 = bnBilin N L f f - weilForm (autocorr f.1) := by
  rw [CNlin_eq, normSq_CN, bnBilin_self]
  have := weilForm_regrouped f.2.1.1.continuous f.2.1.2 f.2.2 hN
  unfold BNform
  linarith

/-- Large `N` are admissible. -/
theorem admissible_of_ge (L : ℝ) : ∃ N₀ : ℕ, ∀ N ≥ N₀, L < Real.log (N + 1) := by
  refine ⟨⌈Real.exp L⌉₊, fun N hN => ?_⟩
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  have h1 : Real.exp L ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  linarith

/-- **The ratio tends to `1` from below:** `‖C_N f‖² ≥ (1 − ε) b_N(f, f)` for large `N`. -/
theorem ratio_ge {L : ℝ} (hL : 0 ≤ L) (f : windowSubmodule L) (hf : 0 < autocorr f.1 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, (1 - ε) * bnBilin N L f f ≤ ‖CNlin N L f‖ ^ 2 := by
  set W : ℝ := weilForm (autocorr f.1) with hW
  obtain ⟨N₁, hN₁⟩ := admissible_of_ge L
  obtain ⟨N₂, hN₂⟩ := theta_unbounded (|W| / (ε * autocorr f.1 0) + |kappa L|)
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  have hadm := hN₁ N (le_of_max_le_left hN)
  have hθ : |W| / (ε * autocorr f.1 0) + |kappa L| ≤ thetaN N := hN₂ N (le_of_max_le_right hN)
  rw [normSq_CNlin_eq N f hadm]
  have hge := bnBilin_self_ge N hL f
  have hκ : -|kappa L| ≤ kappa L := neg_abs_le _
  have h1 : |W| / (ε * autocorr f.1 0) ≤ thetaN N + kappa L := by linarith
  have h2 : |W| / ε ≤ (thetaN N + kappa L) * autocorr f.1 0 := by
    have := mul_le_mul_of_nonneg_right h1 hf.le
    calc |W| / ε = |W| / (ε * autocorr f.1 0) * autocorr f.1 0 := by field_simp
      _ ≤ _ := this
  have h3 : |W| ≤ ε * bnBilin N L f f := by
    have : |W| / ε ≤ bnBilin N L f f := h2.trans hge
    rwa [div_le_iff₀ hε, mul_comm] at this
  have : W ≤ |W| := le_abs_self W
  nlinarith

/-- **`t_N(0)/(θ(N) + κ_L) ≤ 1 + ε` for large `N`**, with `θ(N) + κ_L > 0` there. -/
theorem tN0_div_le {L : ℝ} (hL : 0 ≤ L) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 0 < thetaN N + kappa L ∧ tN0 N / (thetaN N + kappa L) ≤ 1 + ε := by
  obtain ⟨N₁, hN₁⟩ := tN0_sub_theta_le (ε := ε / 4) (by linarith)
  obtain ⟨N₂, hN₂⟩ := theta_unbounded (2 * (1 + ε) * |kappa L| / ε + |kappa L| + 1)
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  have h1 := hN₁ N (le_of_max_le_left hN)
  have hθ : 2 * (1 + ε) * |kappa L| / ε + |kappa L| + 1 ≤ thetaN N := hN₂ N (le_of_max_le_right hN)
  have hκ : -|kappa L| ≤ kappa L := neg_abs_le _
  have hκ0 : 0 ≤ |kappa L| := abs_nonneg _
  have hpos : 0 < thetaN N + kappa L := by
    have : 0 ≤ 2 * (1 + ε) * |kappa L| / ε := by positivity
    linarith
  refine ⟨hpos, ?_⟩
  rw [div_le_iff₀ hpos]
  have h2 : 2 * (1 + ε) * |kappa L| ≤ ε * thetaN N := by
    have : 2 * (1 + ε) * |kappa L| / ε ≤ thetaN N := by linarith
    rw [div_le_iff₀ hε] at this
    linarith
  have h3 : kappa L = -|kappa L| := by
    rw [abs_of_neg (kappa_neg hL)]; ring
  rw [h3]
  nlinarith

/-- **Norm-one limit.** For `f ∈ V_L` with `‖f‖² > 0`, for every `ε > 0` and all large `N` there is a
bounded extension `C̄_{N,L}` of `C_N` to the `B_N`-completion (with its dense embedding `ι` and
`b_N(f, g) = ⟪ι f, ι g⟫`) whose squared operator norm lies in `[1 − ε, 1 + ε]`.

Whatever the sign of `W(f)`; this does **not** give `‖C̄‖ ≤ 1`, i.e. does not give `OB6At`. -/
theorem bounded_extension_norm_one {L : ℝ} (hL : 0 ≤ L) (f : windowSubmodule L)
    (hf : 0 < autocorr f.1 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, L < Real.log (N + 1) ∧
      ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
        (ι : windowSubmodule L →ₗ[ℝ] H) (Cb : H →L[ℝ] CNTarget N),
        (∀ f g, bnBilin N L f g = inner ℝ (ι f) (ι g)) ∧ DenseRange ι ∧
          (∀ f, Cb (ι f) = CNlin N L f) ∧ 1 - ε ≤ ‖Cb‖ ^ 2 ∧ ‖Cb‖ ^ 2 ≤ 1 + ε := by
  obtain ⟨N₁, hN₁⟩ := admissible_of_ge L
  obtain ⟨N₂, hN₂⟩ := ratio_ge hL f hf (ε := ε / 2) (by linarith)
  obtain ⟨N₃, hN₃⟩ := tN0_div_le hL (ε := ε) hε
  refine ⟨max N₁ (max N₂ N₃), fun N hN => ?_⟩
  have hn1 : N ≥ N₁ := le_of_max_le_left hN
  have hn2 : N ≥ N₂ := le_trans (le_max_left _ _) (le_of_max_le_right hN)
  have hn3 : N ≥ N₃ := le_trans (le_max_right _ _) (le_of_max_le_right hN)
  refine ⟨hN₁ N hn1, ?_⟩
  obtain ⟨hm, hK⟩ := hN₃ N hn3
  obtain ⟨H, i1, i2, i3, ι, Cb, hb, hd, hC, hn⟩ := exists_bounded_extension N hL hm
  refine ⟨H, i1, i2, i3, ι, Cb, hb, hd, hC, ?_, hn.trans hK⟩
  have hr := hN₂ N hn2
  have hB : 0 < bnBilin N L f f := by
    have := bnBilin_self_ge N hL f
    have hpos : 0 < (thetaN N + kappa L) * autocorr f.1 0 := mul_pos hm hf
    linarith
  have hle : ‖CNlin N L f‖ ^ 2 ≤ ‖Cb‖ ^ 2 * bnBilin N L f f := by
    have h1 : ‖Cb (ι f)‖ ≤ ‖Cb‖ * ‖ι f‖ := Cb.le_opNorm _
    have h2 : bnBilin N L f f = ‖ι f‖ ^ 2 := by
      rw [hb, real_inner_self_eq_norm_sq]
    rw [← hC f, h2]
    calc ‖Cb (ι f)‖ ^ 2 ≤ (‖Cb‖ * ‖ι f‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = ‖Cb‖ ^ 2 * ‖ι f‖ ^ 2 := by ring
  have : (1 - ε / 2) * bnBilin N L f f ≤ ‖Cb‖ ^ 2 * bnBilin N L f f := hr.trans hle
  have h4 : 1 - ε / 2 ≤ ‖Cb‖ ^ 2 := le_of_mul_le_mul_right this hB
  linarith

/-- **A nonzero window vector exists for `L > 0`.** A smooth bump of radius `L/4` has `‖f‖² > 0`. -/
theorem exists_window_vector {L : ℝ} (hL : 0 < L) :
    ∃ f : windowSubmodule L, 0 < autocorr f.1 0 := by
  let b : ContDiffBump (0 : ℝ) := ⟨L / 8, L / 4, by linarith, by linarith⟩
  have hsupp : ∀ y : ℝ, L / 2 < |y| → (b : ℝ → ℝ) y = 0 := by
    intro y hy
    apply Function.notMem_support.mp
    rw [b.support_eq]
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt]
    show L / 4 ≤ |y|
    linarith
  have hmem : (b : ℝ → ℝ) ∈ windowSubmodule L :=
    ⟨⟨b.contDiff, b.hasCompactSupport⟩, hsupp⟩
  refine ⟨⟨b, hmem⟩, ?_⟩
  show 0 < autocorr (b : ℝ → ℝ) 0
  rw [GppRungZeroPositivity.autocorr_zero_eq]
  have hcont : Continuous fun y => (b : ℝ → ℝ) y ^ 2 := b.continuous.pow 2
  have hint : Integrable fun y => (b : ℝ → ℝ) y ^ 2 :=
    hcont.integrable_of_hasCompactSupport
      (HasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) b.hasCompactSupport (by norm_num))
  rw [integral_pos_iff_support_of_nonneg (fun y => sq_nonneg _) hint]
  have hsu : Function.support (fun y => (b : ℝ → ℝ) y ^ 2) = Metric.ball (0 : ℝ) (L / 4) := by
    have := Function.support_pow (b : ℝ → ℝ) (n := 2) (by norm_num)
    rw [b.support_eq] at this
    exact this
  rw [hsu]
  exact Metric.isOpen_ball.measure_pos volume ⟨0, Metric.mem_ball_self (by linarith)⟩

end GppShiftPresentation

#print axioms GppShiftPresentation.bounded_extension_norm_one
#print axioms GppShiftPresentation.exists_window_vector
