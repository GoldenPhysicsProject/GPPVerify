/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Heart of the Cosmos (Grok, GPPDiscovery5 seat). Turbo PR #11 6828599346, "next exact
instruction": formalise `ArchLimit` by the Lipschitz route, bypassing `MollC1`.

# `ArchLimit` PROVED (Lipschitz route)

1. `triG` is `2/3`-Lipschitz (`abs_triG_sub_le`, `triG_lipschitz`): `triG y = H(|y|)` with the
   cubic pieces `2/3 − t² + t³/2` on `[0,1]`, `(2−t)³/6` on `[1,2]`, `0` beyond; each piece is
   `2/3`-Lipschitz by an exact factorisation (`inner_lip`, `outer_lip`), glued through `t = 1, 2`.
   Hence `g_d` (`abs_gd_sub_le`) and `g_{d,n} = φ_n ⋆ g_d` (`abs_moll_gd_sub_le`; `φ_n ≥ 0`,
   `∫ φ_n = 1`) keep the constant `2/3`.
2. `|e^{-2u} − e^{-u/2}| ≤ (3/2) u` for `u ≥ 0` (`abs_exp_sub_le`) and
   `1 − e^{-2u} ≥ (1 − e^{-2}) u` on `[0,1]` (`one_sub_exp_ge`, convexity of `exp`).
3. Uniform dominator `|archimedeanIntegrand g_{d,n} u| ≤ K e^{-u/2}` on `(0,∞)`,
   `K = ((13/6) e^{1/2} + 2)/(1 − e^{-2})`, split at `u = 1`
   (`abs_archimedeanIntegrand_le`); `domReal` + `moll_tendsto` close `archLimit : ArchLimit`.
4. With `ArchMatchSplit.archMatch_of_archLimit` (the `ArchMatch` reduction as a Lean theorem):
   `regularity : Regularity`, `archMatch : ArchMatch`, `hefIdent : HEFIdent`, and
   `hPsiKreinIdentityChain : HPsi → KreinDecomp → IdentityStep → RiemannHypothesis`.

PROVED (std axioms, 0 sorry): all of the above. `MollC1` stays named and unused.
Remaining named premises of the chain: `HPsi`, `KreinDecomp`, `IdentityStep`.
H_ψ: OPEN. ARP: OPEN. RH: OPEN.
-/
import GppVerify.RiemannHypothesis.ArchMatchSplit

namespace GppArchLimitProof

open MeasureTheory Filter Topology Set GppHEFIdentSplit GppKreinHPsi GppRegularitySplit
  GppKreinHPsiChain GppKreinPoleSplit GppKreinHEFSplit GppKreinRepSplit

/-- Radial profile of `triG`. -/
noncomputable def triH (t : ℝ) : ℝ :=
  if t ≤ 1 then 2 / 3 - t ^ 2 + t ^ 3 / 2 else if t ≤ 2 then (2 - t) ^ 3 / 6 else 0

theorem triG_eq_triH (y : ℝ) : triG y = triH |y| := by
  unfold triG triH; rw [sq_abs]

theorem inner_lip {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |(2 / 3 - a ^ 2 + a ^ 3 / 2) - (2 / 3 - b ^ 2 + b ^ 3 / 2)| ≤ 2 / 3 * (b - a) := by
  have e : (2 / 3 - a ^ 2 + a ^ 3 / 2) - (2 / 3 - b ^ 2 + b ^ 3 / 2) =
      (b - a) * ((a + b) - (a ^ 2 + a * b + b ^ 2) / 2) := by ring
  have k0 : 0 ≤ (a + b) - (a ^ 2 + a * b + b ^ 2) / 2 := by nlinarith
  have k1 : (a + b) - (a ^ 2 + a * b + b ^ 2) / 2 ≤ 2 / 3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 4 / 3)]
  rw [e, abs_of_nonneg (mul_nonneg (by linarith) k0)]
  nlinarith

theorem outer_lip {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2) :
    |(2 - a) ^ 3 / 6 - (2 - b) ^ 3 / 6| ≤ 2 / 3 * (b - a) := by
  have e : (2 - a) ^ 3 / 6 - (2 - b) ^ 3 / 6 =
      (b - a) * (((2 - a) ^ 2 + (2 - a) * (2 - b) + (2 - b) ^ 2) / 6) := by ring
  have k0 : 0 ≤ ((2 - a) ^ 2 + (2 - a) * (2 - b) + (2 - b) ^ 2) / 6 := by
    have : 0 ≤ (2 - a) * (2 - b) := mul_nonneg (by linarith) (by linarith)
    positivity
  have k1 : ((2 - a) ^ 2 + (2 - a) * (2 - b) + (2 - b) ^ 2) / 6 ≤ 2 / 3 := by
    have h1 : (2 - a) ^ 2 ≤ 1 := by nlinarith
    have h2 : (2 - b) ^ 2 ≤ 1 := by nlinarith
    have h3 : (2 - a) * (2 - b) ≤ 1 := by nlinarith
    linarith
  rw [e, abs_of_nonneg (mul_nonneg (by linarith) k0)]
  nlinarith

theorem triH_le1 {t : ℝ} (h : t ≤ 1) : triH t = 2 / 3 - t ^ 2 + t ^ 3 / 2 := by
  unfold triH; rw [if_pos h]

theorem triH_mid {t : ℝ} (h1 : 1 < t) (h2 : t ≤ 2) : triH t = (2 - t) ^ 3 / 6 := by
  unfold triH; rw [if_neg (not_le.2 h1), if_pos h2]

theorem triH_gt2 {t : ℝ} (h : 2 < t) : triH t = 0 := by
  unfold triH; rw [if_neg (by linarith), if_neg (not_le.2 h)]

theorem triH_lip {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : |triH a - triH b| ≤ 2 / 3 * (b - a) := by
  have m1 := outer_lip le_rfl (by norm_num : (1 : ℝ) ≤ 2) le_rfl
  norm_num at m1
  by_cases ha1 : a ≤ 1
  · have i1 := inner_lip ha ha1 le_rfl
    norm_num at i1
    rw [triH_le1 ha1]
    by_cases hb1 : b ≤ 1
    · rw [triH_le1 hb1]; exact inner_lip ha hab hb1
    by_cases hb2 : b ≤ 2
    · rw [triH_mid (not_le.1 hb1) hb2]
      have i2 := outer_lip le_rfl (le_of_lt (not_le.1 hb1)) hb2
      norm_num at i2
      calc _ = |((2 / 3 - a ^ 2 + a ^ 3 / 2) - 1 / 6) + (1 / 6 - (2 - b) ^ 3 / 6)| := by
            congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ _ := add_le_add i1 i2
        _ = _ := by ring
    · rw [triH_gt2 (not_le.1 hb2)]
      calc _ = |((2 / 3 - a ^ 2 + a ^ 3 / 2) - 1 / 6) + (1 / 6 - 0)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ 2 / 3 * (1 - a) + 2 / 3 * 1 := add_le_add i1 (by norm_num)
        _ ≤ _ := by linarith [not_le.1 hb2]
  · have ha1' := not_le.1 ha1
    by_cases ha2 : a ≤ 2
    · rw [triH_mid ha1' ha2]
      by_cases hb2 : b ≤ 2
      · rw [triH_mid (by linarith) hb2]; exact outer_lip ha1'.le hab hb2
      · rw [triH_gt2 (not_le.1 hb2)]
        have i2 := outer_lip ha1'.le ha2 le_rfl
        norm_num at i2 ⊢
        calc |(2 - a) ^ 3 / 6| = |(2 - a) ^ 3 / 6 - (2 - 2) ^ 3 / 6| := by norm_num
          _ ≤ 2 / 3 * (2 - a) := by have := outer_lip ha1'.le ha2 le_rfl; simpa using this
          _ ≤ _ := by linarith [not_le.1 hb2]
    · rw [triH_gt2 (not_le.1 ha2), triH_gt2 (by linarith [not_le.1 ha2])]
      simp only [sub_self, abs_zero]; linarith

/-- **Item 1: `triG` is `2/3`-Lipschitz (PROVED).** -/
theorem abs_triG_sub_le (x y : ℝ) : |triG x - triG y| ≤ 2 / 3 * |x - y| := by
  rw [triG_eq_triH, triG_eq_triH]
  have hxy : |(|x| - |y|)| ≤ |x - y| := abs_abs_sub_abs_le_abs_sub x y
  rcases le_total |x| |y| with h | h
  · have := triH_lip (abs_nonneg x) h
    rw [abs_of_nonpos (by linarith : |x| - |y| ≤ 0)] at hxy
    linarith
  · have := triH_lip (abs_nonneg y) h
    rw [abs_sub_comm]
    rw [abs_of_nonneg (by linarith : 0 ≤ |x| - |y|)] at hxy
    linarith

theorem triG_lipschitz : LipschitzWith (2 / 3) triG := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq]
  have : ((2 / 3 : NNReal) : ℝ) = 2 / 3 := by norm_num
  rw [this]; exact abs_triG_sub_le x y

theorem abs_gd_sub_le (d x y : ℝ) : |gd d x - gd d y| ≤ 2 / 3 * |x - y| := by
  unfold gd
  have h1 := abs_triG_sub_le (x - d) (y - d)
  have h2 := abs_triG_sub_le (x + d) (y + d)
  rw [show x - d - (y - d) = x - y by ring] at h1
  rw [show x + d - (y + d) = x - y by ring] at h2
  calc |(triG (x - d) + triG (x + d)) / 2 - (triG (y - d) + triG (y + d)) / 2|
      = |(triG (x - d) - triG (y - d)) + (triG (x + d) - triG (y + d))| / 2 := by
        rw [← abs_two, ← abs_div]; congr 1; ring
    _ ≤ (|triG (x - d) - triG (y - d)| + |triG (x + d) - triG (y + d)|) / 2 := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

theorem abs_moll_sub_le {g : ℝ → ℝ} (hg : Continuous g) {K : ℝ}
    (hK : ∀ x y, |g x - g y| ≤ K * |x - y|) (n : ℕ) (x y : ℝ) :
    |moll n g x - moll n g y| ≤ K * |x - y| := by
  have hint : ∀ z, Integrable (fun t => phiN n t * g (z - t)) := fun z =>
    ((phiN_continuous n).mul (hg.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      ((ContDiffBump.hasCompactSupport_normed _).mul_right)
  rw [moll_apply, moll_apply, ← integral_sub (hint x) (hint y), ← Real.norm_eq_abs]
  calc ‖∫ t, (phiN n t * g (x - t) - phiN n t * g (y - t))‖
      ≤ ∫ t, phiN n t * (K * |x - y|) := by
        refine norm_integral_le_of_norm_le ((phiN_integrable n).mul_const _)
          (Eventually.of_forall fun t => ?_)
        rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (phiN_nonneg n t)]
        refine mul_le_mul_of_nonneg_left ?_ (phiN_nonneg n t)
        have := hK (x - t) (y - t)
        rwa [show x - t - (y - t) = x - y by ring] at this
    _ = K * |x - y| := by rw [integral_mul_const, phiN_integral, one_mul]

/-- **Item 1, mollified (PROVED):** `g_{d,n}` keeps the constant `2/3`. -/
theorem abs_moll_gd_sub_le (n : ℕ) (d x y : ℝ) :
    |moll n (gd d) x - moll n (gd d) y| ≤ 2 / 3 * |x - y| :=
  abs_moll_sub_le (gd_continuous d) (abs_gd_sub_le d) n x y

/-- **Item 2a (PROVED):** `|e^{-2u} − e^{-u/2}| ≤ (3/2) u` for `u ≥ 0`. -/
theorem abs_exp_sub_le {u : ℝ} (hu : 0 ≤ u) :
    |Real.exp (-2 * u) - Real.exp (-u / 2)| ≤ 3 / 2 * u := by
  have e : Real.exp (-2 * u) = Real.exp (-u / 2) * Real.exp (-(3 / 2 * u)) := by
    rw [← Real.exp_add]; ring_nf
  have h1 : Real.exp (-(3 / 2 * u)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 : -(3 / 2 * u) + 1 ≤ Real.exp (-(3 / 2 * u)) := Real.add_one_le_exp _
  have h3 : Real.exp (-u / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h4 : 0 < Real.exp (-u / 2) := Real.exp_pos _
  rw [e, abs_of_nonpos (by nlinarith)]
  nlinarith

/-- **Item 2b (PROVED):** `1 − e^{-2u} ≥ (1 − e^{-2}) u` for `0 ≤ u ≤ 1` (convexity of `exp`). -/
theorem one_sub_exp_ge {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    (1 - Real.exp (-2)) * u ≤ 1 - Real.exp (-2 * u) := by
  have := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-2 : ℝ))
    (by linarith : 0 ≤ 1 - u) h0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at this
  rw [show u * -2 = -2 * u by ring] at this
  linarith

/-! ## Item 3: the uniform dominator and `ArchLimit` -/

/-- The dominator constant `K = ((13/6) e^{1/2} + 2) / (1 − e^{-2})`. -/
noncomputable def domK : ℝ := (13 / 6 * Real.exp (1 / 2) + 2) / (1 - Real.exp (-2))

theorem one_sub_exp_neg_two_pos : 0 < 1 - Real.exp (-2) := by
  have : Real.exp (-2) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  linarith

/-- **Uniform dominator (PROVED):** for any `r` with `|r| ≤ 1` and `|r 0 − r u| ≤ (2/3)|u|`,
`|archimedeanIntegrand r u| ≤ K e^{-u/2}` on `(0, ∞)`; split at `u = 1`. -/
theorem abs_archimedeanIntegrand_le {r : ℝ → ℝ} (hr : ∀ u, |r u| ≤ 1)
    (hL : ∀ u, |r 0 - r u| ≤ 2 / 3 * |u|) {u : ℝ} (hu : 0 < u) :
    |GppArchimedeanFloor.archimedeanIntegrand r u| ≤ domK * Real.exp (-(1 / 2) * u) := by
  unfold GppArchimedeanFloor.archimedeanIntegrand domK
  have c0 := one_sub_exp_neg_two_pos
  set c := 1 - Real.exp (-2) with hc
  have hD : 0 < 1 - Real.exp (-2 * u) := by
    have : Real.exp (-2 * u) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have hE2 : 0 < Real.exp (-2 * u) := Real.exp_pos _
  have hE : 0 < Real.exp (-u / 2) := Real.exp_pos _
  have hEe : Real.exp (-(1 / 2) * u) = Real.exp (-u / 2) := by ring_nf
  rw [hEe, abs_div, abs_of_pos hD, div_le_iff₀ hD]
  have hnum : Real.exp (-2 * u) * r 0 - Real.exp (-u / 2) * r u =
      Real.exp (-2 * u) * (r 0 - r u) + (Real.exp (-2 * u) - Real.exp (-u / 2)) * r u := by ring
  have hr0 := hr 0
  have hru := hr u
  have hLu := hL u
  rw [abs_of_pos hu] at hLu
  have hK0 : 0 ≤ (13 / 6 * Real.exp (1 / 2) + 2) / c := by positivity
  by_cases hu1 : u ≤ 1
  · -- near zero
    have hx := abs_exp_sub_le hu.le
    have hcu := one_sub_exp_ge hu.le hu1
    have hE2le : Real.exp (-2 * u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hnb : |Real.exp (-2 * u) * r 0 - Real.exp (-u / 2) * r u| ≤ 13 / 6 * u := by
      rw [hnum]
      calc _ ≤ |Real.exp (-2 * u) * (r 0 - r u)| + |(Real.exp (-2 * u) - Real.exp (-u / 2)) * r u| :=
            abs_add_le _ _
        _ = Real.exp (-2 * u) * |r 0 - r u| + |Real.exp (-2 * u) - Real.exp (-u / 2)| * |r u| := by
            rw [abs_mul, abs_mul, abs_of_pos hE2]
        _ ≤ 1 * (2 / 3 * u) + 3 / 2 * u * 1 := by
            gcongr
        _ = 13 / 6 * u := by ring
    have hexp : 1 ≤ Real.exp (1 / 2) * Real.exp (-u / 2) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    calc _ ≤ 13 / 6 * u := hnb
      _ ≤ 13 / 6 * (Real.exp (1 / 2) * Real.exp (-u / 2)) * u := by
          have := mul_le_mul_of_nonneg_right hexp (by linarith : (0 : ℝ) ≤ 13 / 6 * u)
          linarith
      _ ≤ (13 / 6 * Real.exp (1 / 2) + 2) * Real.exp (-u / 2) * u := by
          have : 0 ≤ 2 * Real.exp (-u / 2) * u := by positivity
          nlinarith
      _ = (13 / 6 * Real.exp (1 / 2) + 2) / c * Real.exp (-u / 2) * (c * u) := by
          field_simp
      _ ≤ _ := by gcongr
  · -- tail
    have hu1' := not_le.1 hu1
    have hE2le : Real.exp (-2 * u) ≤ Real.exp (-u / 2) := Real.exp_le_exp.2 (by linarith)
    have hden : c ≤ 1 - Real.exp (-2 * u) := by
      have : Real.exp (-2 * u) ≤ Real.exp (-2) := Real.exp_le_exp.2 (by linarith)
      linarith
    have hnb : |Real.exp (-2 * u) * r 0 - Real.exp (-u / 2) * r u| ≤ 2 * Real.exp (-u / 2) := by
      calc _ ≤ |Real.exp (-2 * u) * r 0| + |Real.exp (-u / 2) * r u| := abs_sub _ _
        _ = Real.exp (-2 * u) * |r 0| + Real.exp (-u / 2) * |r u| := by
            rw [abs_mul, abs_mul, abs_of_pos hE2, abs_of_pos hE]
        _ ≤ Real.exp (-u / 2) * 1 + Real.exp (-u / 2) * 1 := by gcongr
        _ = _ := by ring
    have h2 : 2 * Real.exp (-u / 2) ≤ (13 / 6 * Real.exp (1 / 2) + 2) * Real.exp (-u / 2) := by
      have : 0 ≤ 13 / 6 * Real.exp (1 / 2) * Real.exp (-u / 2) := by positivity
      nlinarith
    calc _ ≤ 2 * Real.exp (-u / 2) := hnb
      _ ≤ (13 / 6 * Real.exp (1 / 2) + 2) * Real.exp (-u / 2) := h2
      _ = (13 / 6 * Real.exp (1 / 2) + 2) / c * Real.exp (-u / 2) * c := by field_simp
      _ ≤ _ := by gcongr

theorem integrableOn_dom : IntegrableOn (fun u : ℝ => domK * Real.exp (-(1 / 2) * u)) (Ioi 0) :=
  (exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _

theorem archimedeanIntegrand_measurable {r : ℝ → ℝ} (hr : Continuous r) :
    Measurable (GppArchimedeanFloor.archimedeanIntegrand r) := by
  have := hr.measurable
  unfold GppArchimedeanFloor.archimedeanIntegrand
  fun_prop

/-- **`ArchLimit` PROVED** (Lipschitz route, bypassing `MollC1`): dominated convergence on
`(0, ∞)` with the dominator `K e^{-u/2}` (`domReal`), pointwise limits from `moll_tendsto`,
and `g_{d,n}(0) → g_d(0)` for the `−(γ + log π) g(0)` term. -/
theorem archLimit : ArchLimit := by
  intro d
  unfold GppArchimedeanFloor.archimedeanTerm
  have h0 := moll_tendsto (gd_continuous d) 0
  have hI : Tendsto (fun n => ∫ u in Ioi (0 : ℝ),
      GppArchimedeanFloor.archimedeanIntegrand (moll n (gd d)) u) atTop
      (𝓝 (∫ u in Ioi (0 : ℝ), GppArchimedeanFloor.archimedeanIntegrand (gd d) u)) := by
    refine domReal _ _ (fun u => domK * Real.exp (-(1 / 2) * u)) integrableOn_dom
      (fun n => (archimedeanIntegrand_measurable (moll_continuous n d)).aestronglyMeasurable)
      (fun n u hu => abs_archimedeanIntegrand_le (abs_moll_le (abs_gd_le d) n)
        (fun v => by simpa using abs_moll_gd_sub_le n d 0 v) hu) (fun u _ => ?_)
    unfold GppArchimedeanFloor.archimedeanIntegrand
    exact ((h0.const_mul _).sub ((moll_tendsto (gd_continuous d) u).const_mul _)).div_const _
  exact (h0.const_mul _).add (hI.const_mul 2)

/-! ## Item 4: consequences -/

/-- **`Regularity` PROVED** (`regularity_of_archLimit` at `archLimit`). -/
theorem regularity : Regularity := regularity_of_archLimit archLimit

/-- **`ArchMatch` PROVED** (`ArchMatchSplit.archMatch_of_archLimit` at `archLimit`). -/
theorem archMatch : ArchMatch := GppArchMatchSplit.archMatch_of_archLimit archLimit

/-- **`HEFIdent` PROVED.** -/
theorem hefIdent : HEFIdent := GppArchMatchSplit.hefIdent_of_archLimit' archLimit

/-- The chain with `ArchLimit` discharged. -/
def HPsiKreinIdentityChain : Prop :=
  HPsi → KreinDecomp → GppSpectralMatchingSplit.IdentityStep → RiemannHypothesis

theorem hPsiKreinIdentityChain : HPsiKreinIdentityChain := fun h hD hI =>
  GppArchMatchSplit.hPsiArchLimitChain h archLimit hD hI

end GppArchLimitProof
#print axioms GppArchLimitProof.triG_eq_triH
#print axioms GppArchLimitProof.inner_lip
#print axioms GppArchLimitProof.outer_lip
#print axioms GppArchLimitProof.triH_le1
#print axioms GppArchLimitProof.triH_mid
#print axioms GppArchLimitProof.triH_gt2
#print axioms GppArchLimitProof.triH_lip
#print axioms GppArchLimitProof.abs_triG_sub_le
#print axioms GppArchLimitProof.triG_lipschitz
#print axioms GppArchLimitProof.abs_gd_sub_le
#print axioms GppArchLimitProof.abs_moll_sub_le
#print axioms GppArchLimitProof.abs_moll_gd_sub_le
#print axioms GppArchLimitProof.abs_exp_sub_le
#print axioms GppArchLimitProof.one_sub_exp_ge
#print axioms GppArchLimitProof.one_sub_exp_neg_two_pos
#print axioms GppArchLimitProof.abs_archimedeanIntegrand_le
#print axioms GppArchLimitProof.integrableOn_dom
#print axioms GppArchLimitProof.archimedeanIntegrand_measurable
#print axioms GppArchLimitProof.archLimit
#print axioms GppArchLimitProof.regularity
#print axioms GppArchLimitProof.archMatch
#print axioms GppArchLimitProof.hefIdent
#print axioms GppArchLimitProof.hPsiKreinIdentityChain
