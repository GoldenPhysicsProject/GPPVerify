import GppVerify.RiemannHypothesis.WindowBlockCheck7L036
import GppVerify.RiemannHypothesis.WindowTail
import Mathlib.Analysis.Real.Pi.Bounds
import GppVerify.Upstream.QuadraticFormLDL

/-!
# Input (a) of the `ℓ = 9/25` window certificate: the finite block bound

From the kernel checks of `WindowBlockCheck*L036` and the moment expansions of `WindowEntries`:
for every `β ≥ b_lo` and a minorant bound `|m| ≤ M ≤ 8` on `[-25, 25]`,

  `λ' Σ_k d_k c_k² ≤ Σ_{j,k} c_j c_k B(φ_j, φ_k)`   for all `c : Fin 32 → ℝ`

(`block_bound`), where `B` is the window form at `ℓ = 9/25`, `T = 25`, with the minorant `mfun`,
and `λ' = λ - 32(η + 2^{-50})/d_min` with the explicit entry error `η = 10^{-12}`.

This file: the bridging lemmas between the rational tables and the real quantities.
Unconditional; no `sorry`, no axioms.
-/

namespace GppWindowBlockL036

open Complex Set MeasureTheory intervalIntegral Finset GppWindowBilinear GppWindowEntries
  GppWindowTail GppWindowPolyBasis GppWindowBasisL036 GppWindowMinorantL036 GppWindowBlockDataL036
open scoped ComplexConjugate

/-- The window half-width as a real number. -/
noncomputable abbrev ℓR : ℝ := ((ellQ : ℚ) : ℝ)

theorem ℓR_eq : ℓR = 9 / 25 := by simp [ℓR, ellQ]

/-! ### `ρ` -/

theorem I_pow_mod (n : ℕ) : I ^ n = I ^ (n % 4) := by
  conv_lhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]

theorem rho_eq (p q : ℕ) : rho p q = ((rhoQ p q : ℚ) : ℝ) := by
  unfold rho rhoQ
  have hc : conj (I ^ q) = I ^ (3 * q) := by
    rw [map_pow, Complex.conj_I, pow_mul]
    congr 1
    rw [show I ^ 3 = I ^ 2 * I by ring, Complex.I_sq]; ring
  rw [hc, ← pow_add, I_pow_mod]
  have h4 : (p + 3 * q) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases h : (p + 3 * q) % 4 <;> simp [pow_succ]

/-! ### Tables as real quantities -/

theorem rowAll {f : ℕ → Bool} {n : ℕ} (h : (List.range n).all f = true) {k : ℕ} (hk : k < n) :
    f k = true := by
  rw [List.all_eq_true] at h; exact h k (List.mem_range.mpr hk)

theorem muRowOK_all {k : ℕ} (hk : k < 32) : muRowOK k = true := by
  interval_cases k
  exacts [muRowOK_0, muRowOK_1, muRowOK_2, muRowOK_3, muRowOK_4, muRowOK_5, muRowOK_6, muRowOK_7, muRowOK_8, muRowOK_9, muRowOK_10, muRowOK_11, muRowOK_12, muRowOK_13, muRowOK_14, muRowOK_15, muRowOK_16, muRowOK_17, muRowOK_18, muRowOK_19, muRowOK_20, muRowOK_21, muRowOK_22, muRowOK_23, muRowOK_24, muRowOK_25, muRowOK_26, muRowOK_27, muRowOK_28, muRowOK_29, muRowOK_30, muRowOK_31]

theorem wRowOK_all {k : ℕ} (hk : k < 32) : wRowOK k = true := by
  interval_cases k
  exacts [wRowOK_0, wRowOK_1, wRowOK_2, wRowOK_3, wRowOK_4, wRowOK_5, wRowOK_6, wRowOK_7, wRowOK_8, wRowOK_9, wRowOK_10, wRowOK_11, wRowOK_12, wRowOK_13, wRowOK_14, wRowOK_15, wRowOK_16, wRowOK_17, wRowOK_18, wRowOK_19, wRowOK_20, wRowOK_21, wRowOK_22, wRowOK_23, wRowOK_24, wRowOK_25, wRowOK_26, wRowOK_27, wRowOK_28, wRowOK_29, wRowOK_30, wRowOK_31]

theorem resRowOK_all {k : ℕ} (hk : k < 32) : resRowOK k = true := by
  interval_cases k
  exacts [resRowOK_0, resRowOK_1, resRowOK_2, resRowOK_3, resRowOK_4, resRowOK_5, resRowOK_6, resRowOK_7, resRowOK_8, resRowOK_9, resRowOK_10, resRowOK_11, resRowOK_12, resRowOK_13, resRowOK_14, resRowOK_15, resRowOK_16, resRowOK_17, resRowOK_18, resRowOK_19, resRowOK_20, resRowOK_21, resRowOK_22, resRowOK_23, resRowOK_24, resRowOK_25, resRowOK_26, resRowOK_27, resRowOK_28, resRowOK_29, resRowOK_30, resRowOK_31]

/-- The moment table is the basis's moments. -/
theorem mom_phi (k : Fin 32) {p : ℕ} (hp : p < 48) : mom ℓR (phi k) p = ((muQ k p : ℚ) : ℝ) := by
  have h := beq_iff_eq.mp (rowAll (muRowOK_all k.isLt) hp)
  unfold phi; rw [mom_evalR, h]

theorem invFQ_eq {m : ℕ} (hm : m < 48) : ((invFQ m : ℚ) : ℝ) = 1 / (m.factorial : ℝ) := by
  have h := beq_iff_eq.mp (rowAll invFactOK_eq hm)
  have hf : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have : invFQ m = 1 / (m.factorial : ℚ) := by field_simp; exact h
  rw [this]; push_cast; rfl

theorem integral_mfun_MQ {s : ℕ} (hs : s < 96) :
    ∫ r in (-25 : ℝ)..25, mfun r * r ^ s = ((MQ s : ℚ) : ℝ) := integral_mfun_mul_pow hs

/-- The `w` table is within `2^{-80}` of the exact contraction. -/
theorem abs_w_sub_le (k : Fin 32) {p : ℕ} (hp : p < 48) :
    |((wQ k p : ℚ) : ℝ) - ∑ q ∈ range 48,
        ((rhoQ p q * muQ k q * MQ (p + q) * invFQ p * invFQ q : ℚ) : ℝ)| ≤ 1 / 2 ^ 80 := by
  have h := of_decide_eq_true (rowAll (wRowOK_all k.isLt) hp)
  unfold sumR at h
  rw [← sum_range_eq_list] at h
  have h' : ((|wQ k p - ∑ q ∈ range 48, rhoQ p q * muQ k q * MQ (p + q) * invFQ p * invFQ q| : ℚ) :
      ℝ) ≤ ((1 / 2 ^ 80 : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h' ⊢
  exact h'

/-! ### Size bounds on the basis -/

theorem ℓR_nonneg : 0 ≤ ℓR := by rw [ℓR_eq]; norm_num

theorem A_le_one (k : Fin 32) : ∫ x in (-ℓR)..ℓR, |phi k x| ≤ 1 := by
  set A := ∫ x in (-ℓR)..ℓR, |phi k x|
  have h := sq_integral_abs_le ℓR_nonneg (continuous_phi k)
  have hip : ∫ x in (-ℓR)..ℓR, phi k x ^ 2 = ip ℓR (phi k) (phi k) := by
    unfold ip; congr 1; funext x; ring
  rw [hip, phi_d] at h
  set D : ℝ := ((2 * ellQ / (2 * ((k : ℕ) : ℚ) + 1) : ℚ) : ℝ)
  have hDq : (2 * ellQ / (2 * ((k : ℕ) : ℚ) + 1) : ℚ) ≤ 18 / 25 := by
    unfold ellQ
    rw [div_le_iff₀ (by positivity)]
    have : (0 : ℚ) ≤ (k : ℕ) := Nat.cast_nonneg _
    nlinarith
  have hD : D ≤ 18 / 25 := by
    have := (Rat.cast_le (K := ℝ)).mpr hDq
    rw [show ((18 / 25 : ℚ) : ℝ) = 18 / 25 by norm_num] at this
    exact this
  have hA0 : 0 ≤ A := integral_nonneg (by linarith [ℓR_nonneg]) fun x _ => abs_nonneg _
  have hl := ℓR_eq
  have hA2 : A ^ 2 ≤ 1 := by
    calc A ^ 2 ≤ 2 * ℓR * D := h
      _ ≤ 2 * (9 / 25) * (18 / 25) := by rw [hl]; nlinarith
      _ ≤ 1 := by norm_num
  nlinarith

theorem abs_mom_le (k : Fin 32) (p : ℕ) : |mom ℓR (phi k) p| ≤ 1 := by
  unfold mom
  rw [← Real.norm_eq_abs]
  have hle : -ℓR ≤ ℓR := by linarith [ℓR_nonneg]
  refine (norm_integral_le_of_norm_le hle (Filter.Eventually.of_forall fun x hx => ?_)
    ((continuous_phi k).abs.intervalIntegrable _ _)).trans (A_le_one k)
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  have hx : |x| ≤ 1 := by
    have : |x| ≤ ℓR := abs_le.mpr ⟨hx.1.le, hx.2⟩
    rw [ℓR_eq] at this; linarith
  calc |phi k x| * |x| ^ p ≤ |phi k x| * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) hx) (abs_nonneg _)
    _ = |phi k x| := mul_one _

/-- `e^{ℓ/2} ≤ 3`. -/
theorem exp_half_le : Real.exp (1 / 2 * ℓR) ≤ 3 := by
  have h1 : Real.exp (1 / 2 * ℓR) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr (by rw [ℓR_eq]; norm_num)
  have h2 := Real.exp_one_lt_d9
  linarith

/-- The Laplace tail: `(ℓ/2)^48 e^{ℓ/2} A ≤ 3 (9/50)^48`. -/
theorem lap_tail_le (k : Fin 32) :
    (1 / 2 * ℓR) ^ 48 * Real.exp (1 / 2 * ℓR) * ∫ x in (-ℓR)..ℓR, |phi k x| ≤ 3 * (9 / 50) ^ 48 := by
  have hA := A_le_one k
  have hA0 : 0 ≤ ∫ x in (-ℓR)..ℓR, |phi k x| :=
    integral_nonneg (by linarith [ℓR_nonneg]) fun x _ => abs_nonneg _
  have he := exp_half_le
  have hp : (1 / 2 * ℓR) ^ 48 = (9 / 50) ^ 48 := by rw [ℓR_eq]; norm_num
  rw [hp]
  have hpos : (0 : ℝ) ≤ (9 / 50) ^ 48 := by positivity
  calc (9 / 50 : ℝ) ^ 48 * Real.exp (1 / 2 * ℓR) * ∫ x in (-ℓR)..ℓR, |phi k x|
      ≤ (9 / 50) ^ 48 * 3 * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left he hpos) hA hA0; positivity
    _ = 3 * (9 / 50) ^ 48 := by ring

/-! ### The Laplace entries -/

theorem gpQ_eq (k : Fin 32) :
    ((gpQ k : ℚ) : ℝ) = ∑ m ∈ range 48, (1 / 2 : ℝ) ^ m / m.factorial * mom ℓR (phi k) m := by
  unfold gpQ sumR
  rw [← sum_range_eq_list, Rat.cast_sum]
  refine sum_congr rfl fun m hm => ?_
  have hm' := mem_range.mp hm
  push_cast
  rw [invFQ_eq hm', mom_phi k hm']; ring

theorem gmQ_eq (k : Fin 32) :
    ((gmQ k : ℚ) : ℝ) = ∑ m ∈ range 48, (-1 / 2 : ℝ) ^ m / m.factorial * mom ℓR (phi k) m := by
  unfold gmQ sumR
  rw [← sum_range_eq_list, Rat.cast_sum]
  refine sum_congr rfl fun m hm => ?_
  have hm' := mem_range.mp hm
  push_cast
  rw [invFQ_eq hm', mom_phi k hm']; ring

theorem abs_lap_sub_gp (k : Fin 32) :
    |lap ℓR (phi k) (1 / 2) - ((gpQ k : ℚ) : ℝ)| ≤ 3 * (9 / 50) ^ 48 := by
  rw [gpQ_eq]
  have h := abs_lap_sub_moments_le ℓR_nonneg (continuous_phi k) 48 (1 / 2)
  rw [show |(1 / 2 : ℝ)| = 1 / 2 by norm_num] at h
  exact h.trans (lap_tail_le k)

theorem abs_lap_sub_gm (k : Fin 32) :
    |lap ℓR (phi k) (-1 / 2) - ((gmQ k : ℚ) : ℝ)| ≤ 3 * (9 / 50) ^ 48 := by
  rw [gmQ_eq]
  have h := abs_lap_sub_moments_le ℓR_nonneg (continuous_phi k) 48 (-1 / 2)
  rw [show |(-1 / 2 : ℝ)| = 1 / 2 by norm_num] at h
  exact h.trans (lap_tail_le k)

theorem abs_lap_le_three (k : Fin 32) {c : ℝ} (hc : |c| = 1 / 2) : |lap ℓR (phi k) c| ≤ 3 := by
  have h := abs_lap_le ℓR_nonneg (continuous_phi k) c
  rw [hc] at h
  have hA := A_le_one k
  have hA0 : 0 ≤ ∫ x in (-ℓR)..ℓR, |phi k x| :=
    integral_nonneg (by linarith [ℓR_nonneg]) fun x _ => abs_nonneg _
  have he := exp_half_le
  nlinarith [Real.exp_pos (1 / 2 * ℓR)]

/-! ### The spectral entries -/

theorem A_nonneg (k : Fin 32) : 0 ≤ ∫ x in (-ℓR)..ℓR, |phi k x| :=
  integral_nonneg (by linarith [ℓR_nonneg]) fun x _ => abs_nonneg _

/-- `|spec(φ_j, φ_k)| ≤ 50 M`. -/
theorem abs_spec_le {Mm : ℝ} (hMm : ∀ r ∈ Icc (-25 : ℝ) 25, |mfun r| ≤ Mm) (j k : Fin 32) :
    |spec ℓR 25 mfun (phi j) (phi k)| ≤ 50 * Mm := by
  have hM0 : 0 ≤ Mm := (abs_nonneg _).trans (hMm 0 ⟨by norm_num, by norm_num⟩)
  unfold spec
  rw [← Real.norm_eq_abs]
  have hb : ∀ r ∈ Set.uIoc (-25 : ℝ) 25,
      ‖mfun r * (hw ℓR (phi j) r * conj (hw ℓR (phi k) r)).re‖ ≤ Mm * (1 * 1) := by
    intro r hr
    rw [Set.uIoc_of_le (by norm_num)] at hr
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul (hMm r ⟨hr.1.le, hr.2⟩) ?_ (abs_nonneg _) hM0
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul ((norm_hw_le ℓR_nonneg _ r).trans (A_le_one j))
      ((norm_hw_le ℓR_nonneg _ r).trans (A_le_one k)) (norm_nonneg _) zero_le_one
  refine (norm_integral_le_of_norm_le_const hb).trans (le_of_eq ?_)
  norm_num; ring

/-- The exact contraction `w_{k,p}`. -/
noncomputable def wEx (k : Fin 32) (p : ℕ) : ℝ :=
  ∑ q ∈ range 48, ((rhoQ p q * muQ k q * MQ (p + q) * invFQ p * invFQ q : ℚ) : ℝ)

theorem specMom_eq (j k : Fin 32) :
    ∑ p ∈ range 48, ∑ q ∈ range 48, rho p q * mom ℓR (phi j) p * mom ℓR (phi k) q /
        (p.factorial * q.factorial) * ∫ r in (-25 : ℝ)..25, mfun r * r ^ (p + q) =
      ∑ p ∈ range 48, ((muQ j p : ℚ) : ℝ) * wEx k p := by
  refine sum_congr rfl fun p hp => ?_
  have hp' := mem_range.mp hp
  unfold wEx
  rw [mul_sum]
  refine sum_congr rfl fun q hq => ?_
  have hq' := mem_range.mp hq
  rw [integral_mfun_MQ (by omega), rho_eq, mom_phi j hp', mom_phi k hq']
  push_cast
  rw [invFQ_eq hp', invFQ_eq hq']
  field_simp

theorem abs_specMom_sub_specQ (j k : Fin 32) :
    |∑ p ∈ range 48, ((muQ j p : ℚ) : ℝ) * wEx k p - ((specQ j k : ℚ) : ℝ)| ≤ 48 / 2 ^ 80 := by
  have hs : ((specQ j k : ℚ) : ℝ) = ∑ p ∈ range 48, ((muQ j p : ℚ) : ℝ) * ((wQ k p : ℚ) : ℝ) := by
    unfold specQ sumR; rw [← sum_range_eq_list, Rat.cast_sum]; push_cast; rfl
  rw [hs, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ p ∈ range 48, |((muQ j p : ℚ) : ℝ) * wEx k p - ((muQ j p : ℚ) : ℝ) * ((wQ k p : ℚ) : ℝ)|
      ≤ 1 / 2 ^ 80 := by
    intro p hp
    have hp' := mem_range.mp hp
    rw [← mul_sub, abs_mul]
    have hmu : |((muQ j p : ℚ) : ℝ)| ≤ 1 := by rw [← mom_phi j hp']; exact abs_mom_le j p
    have hw : |wEx k p - ((wQ k p : ℚ) : ℝ)| ≤ 1 / 2 ^ 80 := by
      rw [abs_sub_comm]; exact abs_w_sub_le k hp'
    calc |((muQ j p : ℚ) : ℝ)| * |wEx k p - ((wQ k p : ℚ) : ℝ)| ≤ 1 * (1 / 2 ^ 80) :=
          mul_le_mul hmu hw (abs_nonneg _) zero_le_one
      _ = 1 / 2 ^ 80 := one_mul _
  refine (sum_le_sum hb).trans (le_of_eq ?_)
  simp; ring

/-- **The spectral entry**: `|spec(φ_j, φ_k) - specQ_{jk}| ≤ 150 M S + 48·2^{-80}`, `S = 9^48/48!`. -/
theorem abs_spec_sub_specQ {Mm : ℝ} (hMm : ∀ r ∈ Icc (-25 : ℝ) 25, |mfun r| ≤ Mm) (j k : Fin 32) :
    |spec ℓR 25 mfun (phi j) (phi k) - ((specQ j k : ℚ) : ℝ)| ≤
      150 * Mm * ((9 : ℝ) ^ 48 / (48 : ℕ).factorial) + 48 / 2 ^ 80 := by
  have hM0 : 0 ≤ Mm := (abs_nonneg _).trans (hMm 0 ⟨by norm_num, by norm_num⟩)
  have h1 := abs_spec_sub_moments_le (ℓ := ℓR) (T := 25) ℓR_nonneg (by norm_num)
    intervalIntegrable_mfun hMm (continuous_phi j) (continuous_phi k) 48
  rw [specMom_eq] at h1
  have h2 := abs_specMom_sub_specQ j k
  have hS : (25 * ℓR) ^ 48 / ((48 : ℕ).factorial : ℝ) = (9 : ℝ) ^ 48 / (48 : ℕ).factorial := by
    rw [ℓR_eq]; norm_num
  rw [hS] at h1
  have hS0 : (0 : ℝ) ≤ (9 : ℝ) ^ 48 / ((48 : ℕ).factorial : ℝ) := by positivity
  have hS1 : (9 : ℝ) ^ 48 / ((48 : ℕ).factorial : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]; norm_num [Nat.factorial]
  generalize (9 : ℝ) ^ 48 / ((48 : ℕ).factorial : ℝ) = S at h1 hS0 hS1 ⊢
  have hAj := A_le_one j; have hAk := A_le_one k
  have hAj0 := A_nonneg j; have hAk0 := A_nonneg k
  set Aj := ∫ x in (-ℓR)..ℓR, |phi j x|
  set Ak := ∫ x in (-ℓR)..ℓR, |phi k x|
  have hbig : 2 * 25 * Mm * (S * Aj * Ak + (Aj + S * Aj) * (S * Ak)) ≤ 150 * Mm * S := by
    have e1 : S * Aj * Ak ≤ S := by
      calc S * Aj * Ak ≤ S * 1 * 1 := by gcongr
        _ = S := by ring
    have e2 : (Aj + S * Aj) * (S * Ak) ≤ 2 * S := by
      calc (Aj + S * Aj) * (S * Ak) ≤ (1 + S * 1) * (S * 1) := by gcongr
        _ ≤ 2 * S := by nlinarith
    nlinarith
  calc |spec ℓR 25 mfun (phi j) (phi k) - ((specQ j k : ℚ) : ℝ)|
      ≤ |spec ℓR 25 mfun (phi j) (phi k) - ∑ p ∈ range 48, ((muQ j p : ℚ) : ℝ) * wEx k p| +
        |∑ p ∈ range 48, ((muQ j p : ℚ) : ℝ) * wEx k p - ((specQ j k : ℚ) : ℝ)| := abs_sub_le _ _ _
    _ ≤ 150 * Mm * S + 48 / 2 ^ 80 := add_le_add (h1.trans hbig) h2

/-! ### `1/(2π)` -/

theorem qPiQ_eq : ((qPiQ : ℚ) : ℝ) = 1 / (2 * (314159265358979323846 / 10 ^ 20)) := by
  unfold qPiQ; push_cast; norm_num

theorem abs_inv_two_pi_sub_qPi :
    |1 / (2 * Real.pi) - ((qPiQ : ℚ) : ℝ)| ≤ 1 / 10 ^ 21 := by
  have hlo : (314159265358979323846 / 10 ^ 20 : ℝ) < Real.pi := by
    have := Real.pi_gt_d20; norm_num at this ⊢; linarith
  have hhi : Real.pi < (314159265358979323847 / 10 ^ 20 : ℝ) := by
    have := Real.pi_lt_d20; norm_num at this ⊢; linarith
  rw [qPiQ_eq]
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : 1 / (2 * Real.pi) < 1 / (2 * (314159265358979323846 / 10 ^ 20)) :=
    one_div_lt_one_div_of_lt (by norm_num) (by linarith)
  have h2 : 1 / (2 * (314159265358979323847 / 10 ^ 20)) < 1 / (2 * Real.pi) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  rw [abs_sub_comm, abs_of_pos (by linarith)]
  have h3 : 1 / (2 * (314159265358979323846 / 10 ^ 20 : ℝ)) -
      1 / (2 * (314159265358979323847 / 10 ^ 20)) ≤ 1 / 10 ^ 21 := by norm_num
  linarith

theorem qPi_le : ((qPiQ : ℚ) : ℝ) ≤ 1 / 6 := by rw [qPiQ_eq]; norm_num

/-! ### The entries -/

theorem ip_phi (j k : Fin 32) :
    ip ℓR (phi j) (phi k) = if j = k then ((dQ k : ℚ) : ℝ) else 0 := by
  by_cases h : j = k
  · subst h; rw [if_pos rfl, phi_d]; rfl
  · rw [if_neg h, phi_orth j k h]

/-- **Every entry of the finite block is within `10^{-12}` of its rational approximation.** -/
theorem abs_B_sub_approx_le {Mm : ℝ} (hMm : ∀ r ∈ Icc (-25 : ℝ) 25, |mfun r| ≤ Mm) (hM8 : Mm ≤ 8)
    (j k : Fin 32) :
    |B ℓR 25 (bLoQ : ℝ) mfun (phi j) (phi k) - ((approxQ j k : ℚ) : ℝ)| ≤ 1 / 10 ^ 12 := by
  have hM0 : 0 ≤ Mm := (abs_nonneg _).trans (hMm 0 ⟨by norm_num, by norm_num⟩)
  set E : ℝ := 3 * (9 / 50) ^ 48
  have hE0 : 0 ≤ E := by positivity
  have hE1 : E ≤ 1 := by norm_num [E]
  -- the Laplace products
  have hpj := abs_lap_sub_gp j; have hmj := abs_lap_sub_gm j
  have hpk := abs_lap_sub_gp k; have hmk := abs_lap_sub_gm k
  have Lpj := abs_lap_le_three j (c := 1 / 2) (by norm_num)
  have Lmj := abs_lap_le_three j (c := -1 / 2) (by norm_num)
  have Lpk := abs_lap_le_three k (c := 1 / 2) (by norm_num)
  have Lmk := abs_lap_le_three k (c := -1 / 2) (by norm_num)
  have prod : ∀ a b a' b' : ℝ, |a - a'| ≤ E → |b - b'| ≤ E → |b| ≤ 3 → |a| ≤ 3 →
      |a * b - a' * b'| ≤ 7 * E := by
    intro a b a' b' ha hb hbb haa
    have ha' : |a'| ≤ 3 + E := by
      calc |a'| = |a - (a - a')| := by ring_nf
        _ ≤ |a| + |a - a'| := abs_sub _ _
        _ ≤ 3 + E := add_le_add haa ha
    calc |a * b - a' * b'| = |(a - a') * b + a' * (b - b')| := by ring_nf
      _ ≤ |(a - a') * b| + |a' * (b - b')| := abs_add_le _ _
      _ = |a - a'| * |b| + |a'| * |b - b'| := by rw [abs_mul, abs_mul]
      _ ≤ E * 3 + (3 + E) * E := add_le_add (mul_le_mul ha hbb (abs_nonneg _) hE0)
          (mul_le_mul ha' hb (abs_nonneg _) (by linarith))
      _ ≤ 7 * E := by nlinarith
  have P1 := prod _ _ _ _ hpj hmk Lmk Lpj
  have P2 := prod _ _ _ _ hmj hpk Lpk Lmj
  -- the spectral term
  have hsp := abs_spec_le hMm j k
  have hsq := abs_spec_sub_specQ hMm j k
  have hpi := abs_inv_two_pi_sub_qPi
  have hq6 := qPi_le
  have hq0 : 0 ≤ ((qPiQ : ℚ) : ℝ) := by rw [qPiQ_eq]; norm_num
  set S : ℝ := 150 * Mm * ((9 : ℝ) ^ 48 / (48 : ℕ).factorial) + 48 / 2 ^ 80
  have hS : S ≤ 1200 * ((9 : ℝ) ^ 48 / (48 : ℕ).factorial) + 48 / 2 ^ 80 := by
    simp only [S]; gcongr; linarith
  have hspec : |1 / (2 * Real.pi) * spec ℓR 25 mfun (phi j) (phi k) -
      ((qPiQ : ℚ) : ℝ) * ((specQ j k : ℚ) : ℝ)| ≤ 1 / 10 ^ 21 * (50 * 8) + 1 / 6 * S := by
    have e : 1 / (2 * Real.pi) * spec ℓR 25 mfun (phi j) (phi k) -
        ((qPiQ : ℚ) : ℝ) * ((specQ j k : ℚ) : ℝ) =
        (1 / (2 * Real.pi) - ((qPiQ : ℚ) : ℝ)) * spec ℓR 25 mfun (phi j) (phi k) +
          ((qPiQ : ℚ) : ℝ) * (spec ℓR 25 mfun (phi j) (phi k) - ((specQ j k : ℚ) : ℝ)) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul hpi (hsp.trans (by linarith)) (abs_nonneg _) (by norm_num)
    · rw [abs_mul, abs_of_nonneg hq0]
      exact mul_le_mul hq6 hsq (abs_nonneg _) (by norm_num)
  -- assemble
  have happrox : ((approxQ j k : ℚ) : ℝ) =
      ((gpQ j : ℚ) : ℝ) * ((gmQ k : ℚ) : ℝ) + ((gmQ j : ℚ) : ℝ) * ((gpQ k : ℚ) : ℝ) +
        (bLoQ : ℝ) * (if j = k then ((dQ k : ℚ) : ℝ) else 0) +
        ((qPiQ : ℚ) : ℝ) * ((specQ j k : ℚ) : ℝ) := by
    unfold approxQ
    have hjk : ((j : ℕ) = (k : ℕ)) ↔ j = k := Fin.val_inj
    by_cases h : j = k
    · rw [if_pos (hjk.mpr h), if_pos h]; push_cast; ring
    · rw [if_neg (fun h' => h (hjk.mp h')), if_neg h]; push_cast; ring
  unfold B
  rw [happrox, ip_phi]
  have e : lap ℓR (phi j) (1 / 2) * lap ℓR (phi k) (-1 / 2) +
        lap ℓR (phi j) (-1 / 2) * lap ℓR (phi k) (1 / 2) +
        (bLoQ : ℝ) * (if j = k then ((dQ k : ℚ) : ℝ) else 0) +
        1 / (2 * Real.pi) * spec ℓR 25 mfun (phi j) (phi k) -
      (((gpQ j : ℚ) : ℝ) * ((gmQ k : ℚ) : ℝ) + ((gmQ j : ℚ) : ℝ) * ((gpQ k : ℚ) : ℝ) +
        (bLoQ : ℝ) * (if j = k then ((dQ k : ℚ) : ℝ) else 0) +
        ((qPiQ : ℚ) : ℝ) * ((specQ j k : ℚ) : ℝ)) =
      (lap ℓR (phi j) (1 / 2) * lap ℓR (phi k) (-1 / 2) - ((gpQ j : ℚ) : ℝ) * ((gmQ k : ℚ) : ℝ)) +
      (lap ℓR (phi j) (-1 / 2) * lap ℓR (phi k) (1 / 2) - ((gmQ j : ℚ) : ℝ) * ((gpQ k : ℚ) : ℝ)) +
      (1 / (2 * Real.pi) * spec ℓR 25 mfun (phi j) (phi k) -
        ((qPiQ : ℚ) : ℝ) * ((specQ j k : ℚ) : ℝ)) := by ring
  rw [e]
  have hfin : 7 * E + 7 * E + (1 / 10 ^ 21 * (50 * 8) + 1 / 6 *
      (1200 * ((9 : ℝ) ^ 48 / (48 : ℕ).factorial) + 48 / 2 ^ 80)) ≤ 1 / 10 ^ 12 := by
    simp only [E]; norm_num [Nat.factorial]
  calc _ ≤ |lap ℓR (phi j) (1 / 2) * lap ℓR (phi k) (-1 / 2) - ((gpQ j : ℚ) : ℝ) * ((gmQ k : ℚ) : ℝ)| +
        |lap ℓR (phi j) (-1 / 2) * lap ℓR (phi k) (1 / 2) - ((gmQ j : ℚ) : ℝ) * ((gpQ k : ℚ) : ℝ)| +
        |1 / (2 * Real.pi) * spec ℓR 25 mfun (phi j) (phi k) -
          ((qPiQ : ℚ) : ℝ) * ((specQ j k : ℚ) : ℝ)| := abs_add_three _ _ _
    _ ≤ 7 * E + 7 * E + (1 / 10 ^ 21 * (50 * 8) + 1 / 6 * S) := add_le_add (add_le_add P1 P2) hspec
    _ ≤ 7 * E + 7 * E + (1 / 10 ^ 21 * (50 * 8) + 1 / 6 *
          (1200 * ((9 : ℝ) ^ 48 / (48 : ℕ).factorial) + 48 / 2 ^ 80)) := by gcongr
    _ ≤ 1 / 10 ^ 12 := hfin

/-! ### The block bound -/

/-- The certified level after the entry and residual errors: `λ' = λ - 32 (10^{-12} + 2^{-50}) / d_min`,
`d_min = 2ℓ/63`. -/
def lamPrimeQ : ℚ := lamQ - 32 * (1 / 10 ^ 12 + resQ) / (2 * ellQ / 63)

theorem dQ_ge (k : Fin 32) : 2 * ellQ / 63 ≤ dQ k := by
  unfold dQ
  apply div_le_div_of_nonneg_left (by unfold ellQ; norm_num) (by positivity)
  have : ((k : ℕ) : ℚ) ≤ 31 := by exact_mod_cast Nat.lt_succ_iff.mp k.isLt
  linarith

theorem dQ_pos (k : Fin 32) : 0 < dQ k := by unfold dQ ellQ; positivity

theorem B_beta (β b : ℝ) (f g : ℝ → ℝ) :
    B ℓR 25 β mfun f g = B ℓR 25 b mfun f g + (β - b) * ip ℓR f g := by
  unfold B; ring

/-- **Input (a): the finite block bound.** For `β ≥ b_lo` and `|m| ≤ M ≤ 8` on `[-25, 25]`,
`λ' Σ d_k c_k² ≤ Σ_{j,k} c_j c_k B(φ_j, φ_k)` for every `c`. -/
theorem block_bound {β : ℝ} (hβ : (bLoQ : ℝ) ≤ β) {Mm : ℝ}
    (hMm : ∀ r ∈ Icc (-25 : ℝ) 25, |mfun r| ≤ Mm) (hM8 : Mm ≤ 8) (c : Fin 32 → ℝ) :
    ((lamPrimeQ : ℚ) : ℝ) * ∑ k, ip ℓR (phi k) (phi k) * c k ^ 2 ≤
      ∑ j, ∑ k, c j * c k * B ℓR 25 β mfun (phi j) (phi k) := by
  set ε : ℝ := 1 / 10 ^ 12 + ((resQ : ℚ) : ℝ)
  -- the matrix and its rounded factorisation
  set Mat : Fin 32 → Fin 32 → ℝ := fun j k =>
    B ℓR 25 (bLoQ : ℝ) mfun (phi j) (phi k) - (if j = k then ((lamQ * dQ k : ℚ) : ℝ) else 0)
  set L' : Fin 32 → Fin 32 → ℝ := fun i j => ((LQ i j : ℚ) : ℝ)
  set D' : Fin 32 → ℝ := fun i => ((DQ i : ℚ) : ℝ)
  have hD' : ∀ i, 0 ≤ D' i := fun i => by
    simp only [D']; exact_mod_cast of_decide_eq_true (rowAll DOK_eq i.isLt)
  have hres : ∀ j k, |Mat j k - ((if j = k then (0 : ℝ) else 0) + ∑ i, L' j i * D' i * L' k i)| ≤ ε := by
    intro j k
    have hq := of_decide_eq_true (rowAll (resRowOK_all j.isLt) k.isLt)
    have hjk : ((j : ℕ) = (k : ℕ)) ↔ j = k := Fin.val_inj
    have hldl : ((ldlQ j k : ℚ) : ℝ) = ∑ i, L' j i * D' i * L' k i := by
      unfold ldlQ sumR
      rw [← sum_range_eq_list, Rat.cast_sum]
      rw [← Fin.sum_univ_eq_sum_range (fun i => ((LQ j i * DQ i * LQ k i : ℚ) : ℝ))]
      push_cast; rfl
    have hq' : |((approxQ j k : ℚ) : ℝ) - (if j = k then ((lamQ * dQ k : ℚ) : ℝ) else 0) -
        ((ldlQ j k : ℚ) : ℝ)| ≤ ((resQ : ℚ) : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr hq
      by_cases h : j = k
      · rw [if_pos (hjk.mpr h)] at this; rw [if_pos h]; push_cast at this ⊢; exact this
      · rw [if_neg (fun h' => h (hjk.mp h'))] at this; rw [if_neg h]; push_cast at this ⊢; exact this
    have he := abs_B_sub_approx_le hMm hM8 j k
    rw [hldl] at hq'
    simp only [Mat, ite_self, zero_add]
    calc |B ℓR 25 (bLoQ : ℝ) mfun (phi j) (phi k) - (if j = k then ((lamQ * dQ k : ℚ) : ℝ) else 0) -
          ∑ i, L' j i * D' i * L' k i|
        ≤ |B ℓR 25 (bLoQ : ℝ) mfun (phi j) (phi k) - ((approxQ j k : ℚ) : ℝ)| +
          |((approxQ j k : ℚ) : ℝ) - (if j = k then ((lamQ * dQ k : ℚ) : ℝ) else 0) -
            ∑ i, L' j i * D' i * L' k i| := by
          rw [show B ℓR 25 (bLoQ : ℝ) mfun (phi j) (phi k) - (if j = k then ((lamQ * dQ k : ℚ) : ℝ) else 0) -
            ∑ i, L' j i * D' i * L' k i = (B ℓR 25 (bLoQ : ℝ) mfun (phi j) (phi k) - ((approxQ j k : ℚ) : ℝ)) +
            (((approxQ j k : ℚ) : ℝ) - (if j = k then ((lamQ * dQ k : ℚ) : ℝ) else 0) -
              ∑ i, L' j i * D' i * L' k i) by ring]
          exact abs_add_le _ _
      _ ≤ ε := add_le_add he hq'
  have hquad := Matrix.le_quadForm_of_ldl_residual Mat L' D' 0 ε hres hD' c
  -- assemble
  have hd : ∀ k, ip ℓR (phi k) (phi k) = ((dQ k : ℚ) : ℝ) := fun k => by rw [ip_phi, if_pos rfl]
  have hsplit : ∑ j, ∑ k, c j * c k * B ℓR 25 β mfun (phi j) (phi k) =
      ∑ i, ∑ j, Mat i j * c i * c j + ((lamQ : ℚ) : ℝ) * ∑ k : Fin 32, ((dQ k : ℚ) : ℝ) * c k ^ 2 +
        (β - bLoQ) * ∑ k : Fin 32, ((dQ k : ℚ) : ℝ) * c k ^ 2 := by
    simp only [Mat, B_beta β (bLoQ : ℝ), ip_phi]
    have hdiag : ∀ (g : Fin 32 → ℝ), ∑ j, ∑ k, c j * c k * (if j = k then g k else 0) =
        ∑ k, g k * c k ^ 2 := by
      intro g
      refine sum_congr rfl fun j _ => ?_
      rw [sum_eq_single j (fun k _ hk => by rw [if_neg (Ne.symm hk), mul_zero]) (by simp)]
      rw [if_pos rfl]; ring
    have e1 := hdiag (fun k => ((lamQ * dQ k : ℚ) : ℝ))
    have e2 := hdiag (fun k => ((dQ k : ℚ) : ℝ))
    simp only [Rat.cast_mul] at e1
    calc ∑ j, ∑ k, c j * c k * (B ℓR 25 (bLoQ : ℝ) mfun (phi j) (phi k) +
          (β - bLoQ) * (if j = k then ((dQ k : ℚ) : ℝ) else 0))
        = ∑ j, ∑ k, ((B ℓR 25 (bLoQ : ℝ) mfun (phi j) (phi k) -
            (if j = k then ((lamQ : ℚ) : ℝ) * ((dQ k : ℚ) : ℝ) else 0)) * c j * c k +
            c j * c k * (if j = k then ((lamQ : ℚ) : ℝ) * ((dQ k : ℚ) : ℝ) else 0) +
            (β - bLoQ) * (c j * c k * (if j = k then ((dQ k : ℚ) : ℝ) else 0))) := by
          refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring
      _ = _ := by
          simp only [sum_add_distrib, ← mul_sum]
          rw [e1, e2]
          congr 1; congr 1
          · simp only [Rat.cast_mul]
          · rw [mul_sum]; refine sum_congr rfl fun k _ => by ring
  have hsum0 : 0 ≤ ∑ k : Fin 32, ((dQ k : ℚ) : ℝ) * c k ^ 2 :=
    sum_nonneg fun k _ => mul_nonneg (by exact_mod_cast (dQ_pos k).le) (sq_nonneg _)
  have hc2 : ∑ k, c k ^ 2 ≤ (∑ k : Fin 32, ((dQ k : ℚ) : ℝ) * c k ^ 2) / ((2 * ellQ / 63 : ℚ) : ℝ) := by
    rw [le_div_iff₀ (by unfold ellQ; norm_num), sum_mul]
    refine sum_le_sum fun k _ => ?_
    have := (Rat.cast_le (K := ℝ)).mpr (dQ_ge k)
    nlinarith [sq_nonneg (c k)]
  have hε0 : 0 ≤ ε := by simp only [ε]; unfold resQ; norm_num
  simp only [hd]
  rw [hsplit]
  have hβ' : 0 ≤ (β - bLoQ) * ∑ k : Fin 32, ((dQ k : ℚ) : ℝ) * c k ^ 2 :=
    mul_nonneg (by linarith) hsum0
  have hlp : ((lamPrimeQ : ℚ) : ℝ) = ((lamQ : ℚ) : ℝ) - 32 * ε / ((2 * ellQ / 63 : ℚ) : ℝ) := by
    simp only [ε]; unfold lamPrimeQ; push_cast; ring
  rw [hlp]
  have hdm : (0 : ℝ) < ((2 * ellQ / 63 : ℚ) : ℝ) := by unfold ellQ; norm_num
  have key : 32 * ε * ∑ k, c k ^ 2 ≤
      32 * ε / ((2 * ellQ / 63 : ℚ) : ℝ) * ∑ k : Fin 32, ((dQ k : ℚ) : ℝ) * c k ^ 2 := by
    have := mul_le_mul_of_nonneg_left hc2 (by positivity : (0 : ℝ) ≤ 32 * ε)
    calc 32 * ε * ∑ k, c k ^ 2
        ≤ 32 * ε * ((∑ k : Fin 32, ((dQ k : ℚ) : ℝ) * c k ^ 2) / ((2 * ellQ / 63 : ℚ) : ℝ)) := this
      _ = 32 * ε / ((2 * ellQ / 63 : ℚ) : ℝ) * ∑ k : Fin 32, ((dQ k : ℚ) : ℝ) * c k ^ 2 := by ring
  have hq0 : (0 - (32 : ℕ) * ε) * ∑ i, c i ^ 2 ≤ ∑ i, ∑ j, Mat i j * c i * c j := hquad
  push_cast at hq0
  nlinarith

end GppWindowBlockL036

#print axioms GppWindowBlockL036.rho_eq
#print axioms GppWindowBlockL036.abs_w_sub_le
#print axioms GppWindowBlockL036.abs_B_sub_approx_le
#print axioms GppWindowBlockL036.block_bound
