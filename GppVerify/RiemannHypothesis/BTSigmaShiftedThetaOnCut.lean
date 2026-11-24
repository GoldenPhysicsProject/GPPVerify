import GppVerify.RiemannHypothesis.BTSigmaShiftedTheta

/-!
# BT-Σ: shifted (P-θ) on the cuts — centre kill for every `c ≥ 0`, cuts included

Answer (Heart of the Cosmos / Grok, GPPDiscovery5 seat) to Turbo's next exact question on
GPP-bridge PR #11, comment 6814728341: port the width-scaling argument that closes the only Lean
GAP in `BTSigmaShiftedTheta` (#580), the centre `c ≥ 0` lying exactly on a cut `log p^k` of the
given `(S, N)`.

**Argument (all PROVED, standard axioms).** Take the radius-`r` bump `f = bumpR r` of #580.
1. *Single visible cut.* Shrink `r` below half the distance from `c` to every other cut
   (`exists_radius_off_finset`); the stratum at `W = c` is then
   `w · ∫ f²` with `w = Σ_{log p^k = c} Λ(p^k)(p^k)^{-1/2}` (`stratumSN_bumpR_onCut`).
2. *Linear in `r`.* `∫ f² ≥ r`, since `f = 1` on `[−r/2, r/2]` (`bumpR_sq_integral_ge`), and
   `w > 0` (`halfWeight_cut_pos`, `onCutWeight_pos`).
3. *Quadratic unit term.* `∫ f e^{±y/2} ≤ 2r e^{r/2}` (`bumpR_exp_integral_le`), so
   `unitStratumTerm (f ⋆ f̃) c ≤ 4 r² e^{r} e^{c/2}` (`unitStratumTerm_bumpR_le`).
4. *Balance fails.* The shifted centre balance of #580 (`shifted_centre_balance`) gives
   `w ∫ f² = unit`, so `w r ≤ 12 r² e^{c/2}` for `r ≤ 1`, false once `r ≤ w / (24 e^{c/2})`.

**Results.** `shifted_ptheta_punit_kill_onCut`: for every `c ≥ 0` that is a cut of `(S, N)`,
`¬ (ShiftedPLogTheta D J c ∧ PUnit (D S N))`. With the off-cut kill of #580:
`shifted_ptheta_punit_kill_nonneg` — the shifted (P-θ) is killed against (P-UNIT) at every
`(S, N)` and every centre `c ≥ 0`, for every family and every `J`.

**Not covered.** `c < 0`: OPEN, no foothold (`shifted_reflection_leaves_premise_region`), no
construction.

Lean results PROVED, standard axioms. No `sorry`, no custom axiom, no cited theorem.
(BT-Σ), ARP, CGC and RH remain OPEN.

Daniel Toupin / Golden Physics Project, with AI assistance (Heart of the Cosmos / Grok).
Task and audit: Turbo.
-/

namespace GppBTSigmaShiftedThetaOnCut

open GppBTSigmaShiftedTheta GppBTSigmaLocalEuler GppBTSigma GppBTSigmaC1 GppArithmeticReflection
  MeasureTheory

/-- A finite set of cuts all different from `c` leaves room for a positive radius. PROVED. -/
theorem exists_radius_off_finset (T : Finset (ℕ × ℕ)) (c : ℝ)
    (hoff : ∀ x ∈ T, c ≠ Real.log ((x.1 ^ x.2 : ℕ) : ℝ)) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ T, 2 * r < |c - Real.log ((x.1 ^ x.2 : ℕ) : ℝ)| := by
  set d : ℕ × ℕ → ℝ := fun x => |c - Real.log ((x.1 ^ x.2 : ℕ) : ℝ)|
  set sd := ∑ x ∈ T, 1 / d x
  have hdpos : ∀ x ∈ T, 0 < d x := fun x hx =>
    abs_pos.mpr (sub_ne_zero.mpr (hoff x hx))
  have hsd : 0 ≤ sd := Finset.sum_nonneg fun x hx => (one_div_pos.mpr (hdpos x hx)).le
  refine ⟨1 / (4 * (1 + sd)), by positivity, fun x hx => ?_⟩
  have hx1 : 1 / d x ≤ sd :=
    Finset.single_le_sum (f := fun x => 1 / d x)
      (fun x hx => (one_div_pos.mpr (hdpos x hx)).le) hx
  have hd := hdpos x hx
  show 2 * (1 / (4 * (1 + sd))) < d x
  have h1 : 1 < d x * (1 + sd) := by
    have : 1 / d x * d x = 1 := by field_simp
    nlinarith
  rw [show 2 * (1 / (4 * (1 + sd))) = 1 / (2 * (1 + sd)) by field_simp; ring,
    div_lt_iff₀ (by positivity)]
  nlinarith

/-- The total BT3 weight sitting exactly on the centre `c`:
`Σ_{(p,k) ∈ cuts(S,N), log p^k = c} Λ(p^k)(p^k)^{-1/2}`. -/
noncomputable def onCutWeight (S : Finset ℕ) (N : ℕ) (c : ℝ) : ℝ :=
  ∑ x ∈ (cutIndex S N).filter (fun x => Real.log ((x.1 ^ x.2 : ℕ) : ℝ) = c),
    halfWeight (x.1 ^ x.2)

/-- **Single-visible-cut stratum at width `r`.** If every cut of `(S, N)` other than those at
`c` is farther than `2r` from `c`, the radius-`r` bump stratum at `W = c` is the on-cut weight
times `∫ f²` (linear in `r`, see `bumpR_sq_integral_ge`). PROVED. -/
theorem stratumSN_bumpR_onCut {r : ℝ} (hr : 0 < r) (S : Finset ℕ) (N : ℕ) (c : ℝ)
    (hfar : ∀ x ∈ (cutIndex S N).filter (fun x => ¬ Real.log ((x.1 ^ x.2 : ℕ) : ℝ) = c),
      2 * r < |c - Real.log ((x.1 ^ x.2 : ℕ) : ℝ)|) :
    stratumSN S N (autocorr (bumpR r hr : ℝ → ℝ)) c =
      onCutWeight S N c * ∫ y : ℝ, (bumpR r hr : ℝ → ℝ) y * (bumpR r hr : ℝ → ℝ) y := by
  have hsupp := autocorr_hasSupportIn (f := (bumpR r hr : ℝ → ℝ)) (L := 2 * r)
    (bumpR_zero_outside hr)
  unfold stratumSN onCutWeight
  rw [← Finset.sum_filter_add_sum_filter_not (cutIndex S N)
    (fun x => Real.log ((x.1 ^ x.2 : ℕ) : ℝ) = c)]
  rw [Finset.sum_eq_zero (s := (cutIndex S N).filter
      (fun x => ¬ Real.log ((x.1 ^ x.2 : ℕ) : ℝ) = c))
    (fun x hx => by rw [hsupp _ (hfar x hx), mul_zero]), add_zero, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.mp hx).2, sub_self]
  simp only [autocorr, sub_zero]

/-- `∫ f² ≥ r` for the radius-`r` bump (it is `1` on `[−r/2, r/2]`). PROVED. -/
theorem bumpR_sq_integral_ge {r : ℝ} (hr : 0 < r) :
    r ≤ ∫ y : ℝ, (bumpR r hr : ℝ → ℝ) y * (bumpR r hr : ℝ → ℝ) y := by
  have hint : Integrable (fun y : ℝ => (bumpR r hr : ℝ → ℝ) y * (bumpR r hr : ℝ → ℝ) y) :=
    ((bumpR r hr).continuous.mul (bumpR r hr).continuous).integrable_of_hasCompactSupport
      (bumpR r hr).hasCompactSupport.mul_right
  have h1 : ∫ y in Set.Icc (-(r / 2)) (r / 2),
      (bumpR r hr : ℝ → ℝ) y * (bumpR r hr : ℝ → ℝ) y = r := by
    rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ => (1 : ℝ)) ?_]
    · simp only [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Icc]
      rw [max_eq_left (by linarith)]; ring
    · intro y hy
      have hm : y ∈ Metric.closedBall (0 : ℝ) (bumpR r hr).rIn := by
        rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
        exact abs_le.mpr ⟨hy.1, hy.2⟩
      simp only
      rw [(bumpR r hr).one_of_mem_closedBall hm, one_mul]
  calc r = _ := h1.symm
    _ ≤ _ := setIntegral_le_integral hint (Filter.Eventually.of_forall fun y => mul_self_nonneg _)

/-- `∫ f(y) e^{a y} ≤ 2r e^{r/2}` for the radius-`r` bump and `|a| ≤ 1/2`. PROVED. -/
theorem bumpR_exp_integral_le {r : ℝ} (hr : 0 < r) {a : ℝ} (ha : |a| ≤ 1 / 2) :
    ∫ y : ℝ, (bumpR r hr : ℝ → ℝ) y * Real.exp (a * y) ≤ 2 * r * Real.exp (r / 2) := by
  set f := (bumpR r hr : ℝ → ℝ)
  have hle : ∀ y, f y * Real.exp (a * y) ≤
      Set.indicator (Set.Icc (-r) r) (fun _ => Real.exp (r / 2)) y := by
    intro y
    by_cases hy : y ∈ Set.Icc (-r) r
    · rw [Set.indicator_of_mem hy]
      have hy' : |y| ≤ r := abs_le.mpr ⟨hy.1, hy.2⟩
      have h1 : f y ≤ 1 := (bumpR r hr).le_one
      have h2 : Real.exp (a * y) ≤ Real.exp (r / 2) := by
        apply Real.exp_le_exp.mpr
        have e1 : a * y ≤ |a * y| := le_abs_self _
        rw [abs_mul] at e1
        have e2 : |a| * |y| ≤ 1 / 2 * r := mul_le_mul ha hy' (abs_nonneg _) (by norm_num)
        linarith
      calc f y * Real.exp (a * y) ≤ 1 * Real.exp (r / 2) :=
            mul_le_mul h1 h2 (Real.exp_pos _).le zero_le_one
        _ = Real.exp (r / 2) := one_mul _
    · rw [Set.indicator_of_notMem hy]
      have hry : r < |y| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
        rcases hy with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; exact h
      rw [show f y = 0 from bumpR_zero_outside hr y (by linarith), zero_mul]
  have hintL : Integrable (fun y : ℝ => f y * Real.exp (a * y)) :=
    ((bumpR r hr).continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      (bumpR r hr).hasCompactSupport.mul_right
  have hintR : Integrable (Set.indicator (Set.Icc (-r) r) (fun _ : ℝ => Real.exp (r / 2))) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  calc ∫ y : ℝ, f y * Real.exp (a * y)
      ≤ ∫ y : ℝ, Set.indicator (Set.Icc (-r) r) (fun _ => Real.exp (r / 2)) y :=
        integral_mono hintL hintR hle
    _ = 2 * r * Real.exp (r / 2) := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
          Real.volume_real_Icc, max_eq_left (by linarith)]
        ring

/-- **Quadratic bound on the unit term.** `unitStratumTerm (f ⋆ f̃) c ≤ 4 r² e^{r} e^{c/2}`
for the radius-`r` bump. PROVED. -/
theorem unitStratumTerm_bumpR_le {r : ℝ} (hr : 0 < r) (c : ℝ) :
    unitStratumTerm (autocorr (bumpR r hr : ℝ → ℝ)) c ≤
      4 * r ^ 2 * Real.exp r * Real.exp (c / 2) := by
  rw [unitStratumTerm, integral_autocorr_mul_exp _ (bumpR r hr).continuous
    (bumpR r hr).hasCompactSupport]
  have q1 : (∫ y : ℝ, (bumpR r hr : ℝ → ℝ) y * Real.exp (-y / 2)) =
      ∫ y : ℝ, (bumpR r hr : ℝ → ℝ) y * Real.exp (-1 / 2 * y) := by
    congr 1; ext y; congr 2; ring
  have q2 : (∫ y : ℝ, (bumpR r hr : ℝ → ℝ) y * Real.exp (y / 2)) =
      ∫ y : ℝ, (bumpR r hr : ℝ → ℝ) y * Real.exp (1 / 2 * y) := by
    congr 1; ext y; congr 2; ring
  rw [q1, q2]
  have p2 := bumpR_exp_pos hr (1 / 2)
  have u1 := bumpR_exp_integral_le hr (a := -1 / 2) (by rw [abs_le]; constructor <;> norm_num)
  have u2 := bumpR_exp_integral_le hr (a := 1 / 2) (by rw [abs_le]; constructor <;> norm_num)
  have hB : 0 ≤ 2 * r * Real.exp (r / 2) := by positivity
  have hprod := mul_le_mul u1 u2 p2.le hB
  have hsq : 2 * r * Real.exp (r / 2) * (2 * r * Real.exp (r / 2)) =
      4 * r ^ 2 * Real.exp r := by
    rw [show 2 * r * Real.exp (r / 2) * (2 * r * Real.exp (r / 2)) =
      4 * r ^ 2 * (Real.exp (r / 2) * Real.exp (r / 2)) by ring, ← Real.exp_add]
    norm_num
  rw [hsq] at hprod
  have hE := Real.exp_pos (c / 2)
  nlinarith

/-- Every cut carries a positive BT3 weight `Λ(p^k)(p^k)^{-1/2} > 0`. PROVED. -/
theorem halfWeight_cut_pos {S : Finset ℕ} {N : ℕ} {x : ℕ × ℕ} (hx : x ∈ cutIndex S N) :
    0 < halfWeight (x.1 ^ x.2) := by
  simp only [cutIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx
  obtain ⟨⟨⟨_, hp⟩, hk1, _⟩, _⟩ := hx
  unfold halfWeight
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hpos : (0 : ℝ) < ((x.1 ^ x.2 : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos _
  exact mul_pos (Real.log_pos (by exact_mod_cast hp.one_lt)) (Real.rpow_pos_of_pos hpos _)

/-- If `c` is a cut of `(S, N)`, its on-cut weight is positive. PROVED. -/
theorem onCutWeight_pos {S : Finset ℕ} {N : ℕ} {c : ℝ}
    (hcut : ∃ x ∈ cutIndex S N, Real.log ((x.1 ^ x.2 : ℕ) : ℝ) = c) :
    0 < onCutWeight S N c := by
  obtain ⟨x, hx, hxc⟩ := hcut
  have hmem : x ∈ (cutIndex S N).filter (fun x => Real.log ((x.1 ^ x.2 : ℕ) : ℝ) = c) :=
    Finset.mem_filter.mpr ⟨hx, hxc⟩
  exact lt_of_lt_of_le (halfWeight_cut_pos hx)
    (Finset.single_le_sum (f := fun x => halfWeight (x.1 ^ x.2))
      (fun y _ => halfWeight_nonneg _) hmem)

/-- **Shifted (P-θ) KILLED on the cuts.** For every centre `c ≥ 0` that *is* a cut `log p^k`
of `(S, N)`, no family carries the shifted reflection together with (P-UNIT) at `(S, N)`: at
width `r` the centre balance reads `w · ∫ f² = unit`, with `∫ f² ≥ r`, `w > 0` and
`unit ≤ 4 r² e^{r} e^{c/2}`, which fails once `r < w / (24 e^{c/2})`. PROVED. -/
theorem shifted_ptheta_punit_kill_onCut {H Gu Gp : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup Gu] [InnerProductSpace ℂ Gu]
    [NormedAddCommGroup Gp] [InnerProductSpace ℂ Gp]
    (D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp) (J : H ≃ₗᵢ[ℂ] H) (S : Finset ℕ) (N : ℕ)
    {c : ℝ} (hc0 : 0 ≤ c) (hcut : ∃ x ∈ cutIndex S N, Real.log ((x.1 ^ x.2 : ℕ) : ℝ) = c) :
    ¬ (ShiftedPLogTheta D J c ∧ PUnit (D S N)) := by
  rintro ⟨hθ, hU⟩
  set A := onCutWeight S N c with hA
  have hApos : 0 < A := onCutWeight_pos hcut
  obtain ⟨r0, hr0, hfar0⟩ := exists_radius_off_finset
    ((cutIndex S N).filter (fun x => ¬ Real.log ((x.1 ^ x.2 : ℕ) : ℝ) = c)) c
    (fun x hx => fun h => (Finset.mem_filter.mp hx).2 h.symm)
  set E := Real.exp (c / 2) with hE
  have hEpos : 0 < E := Real.exp_pos _
  set r := min (min r0 1) (A / (24 * E)) with hr_def
  have hr : 0 < r := lt_min (lt_min hr0 one_pos) (by positivity)
  have hr_r0 : r ≤ r0 := (min_le_left _ _).trans (min_le_left _ _)
  have hr_1 : r ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hr_A : r ≤ A / (24 * E) := min_le_right _ _
  have hfar : ∀ x ∈ (cutIndex S N).filter (fun x => ¬ Real.log ((x.1 ^ x.2 : ℕ) : ℝ) = c),
      2 * r < |c - Real.log ((x.1 ^ x.2 : ℕ) : ℝ)| := fun x hx => by
    have := hfar0 x hx; linarith
  have e := shifted_centre_balance D J hc0 hθ S N hU (bumpR r hr : ℝ → ℝ)
    (bumpR r hr).contDiff (bumpR r hr).hasCompactSupport
  rw [stratumSN_bumpR_onCut hr S N c hfar] at e
  have hI := bumpR_sq_integral_ge hr
  have hU2 := unitStratumTerm_bumpR_le hr c
  have hexp : Real.exp r < 3 := by
    have := Real.exp_one_lt_d9
    have : Real.exp r ≤ Real.exp 1 := Real.exp_le_exp.mpr hr_1
    linarith
  -- A r ≤ A ∫f² = unit ≤ 4 r² e^r E < 12 r² E, so A < 12 r E ≤ A / 2.
  have h1 : A * r ≤ 12 * r ^ 2 * E := by
    have : A * r ≤ A * ∫ y : ℝ, (bumpR r hr : ℝ → ℝ) y * (bumpR r hr : ℝ → ℝ) y :=
      mul_le_mul_of_nonneg_left hI hApos.le
    have h4 : 4 * r ^ 2 * Real.exp r * E ≤ 12 * r ^ 2 * E := by
      have : 0 ≤ 4 * r ^ 2 * E := by positivity
      nlinarith
    linarith
  have h2 : A ≤ 12 * r * E := by
    have : A * r ≤ (12 * r * E) * r := by nlinarith
    exact le_of_mul_le_mul_right this hr
  have h3 : 12 * r * E ≤ A / 2 := by
    have := mul_le_mul_of_nonneg_left hr_A (show (0 : ℝ) ≤ 12 * E by positivity)
    have hEq : 12 * E * (A / (24 * E)) = A / 2 := by field_simp; ring
    linarith
  linarith

/-- **Shifted (P-θ) KILLED for every centre `c ≥ 0`, cuts included.** Combines the off-cut
kill (`shifted_ptheta_punit_kill`, #580) with the on-cut kill above. PROVED. -/
theorem shifted_ptheta_punit_kill_nonneg {H Gu Gp : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup Gu] [InnerProductSpace ℂ Gu]
    [NormedAddCommGroup Gp] [InnerProductSpace ℂ Gp]
    (D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp) (J : H ≃ₗᵢ[ℂ] H) (S : Finset ℕ) (N : ℕ)
    {c : ℝ} (hc0 : 0 ≤ c) :
    ¬ (ShiftedPLogTheta D J c ∧ PUnit (D S N)) := by
  by_cases hcut : ∃ x ∈ cutIndex S N, Real.log ((x.1 ^ x.2 : ℕ) : ℝ) = c
  · exact shifted_ptheta_punit_kill_onCut D J S N hc0 hcut
  · exact shifted_ptheta_punit_kill D J S N hc0 fun x hx h => hcut ⟨x, hx, h.symm⟩

end GppBTSigmaShiftedThetaOnCut
