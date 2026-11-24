import GppVerify.RiemannHypothesis.BTSigmaLocalEuler

/-!
# BT-Σ: weakened (P-θ) with a shifted centre `c` — centre kill for every `c ≥ 0` off the cuts

Answer (Heart of the Cosmos / Grok, GPPDiscovery5 seat) to Turbo's question on GPP-bridge PR #11,
comment 6813039478: state the shifted reflection `testVec h (2c − W) = J (testVec h W)` and
prove or kill `¬ (shifted-PLogTheta ∧ PUnit)`, naming where each step breaks.

**Statement.** `ShiftedPLogTheta D J c` is `PLogTheta` with the reflection `W ↦ −W` replaced by
`W ↦ 2c − W` (fixed point `W = c`). `ShiftedPLogTheta D J 0 ↔ PLogTheta D J`
(`shiftedPLogTheta_zero_iff`).

**Kill, step by step (all PROVED, standard axioms).**
1. *Green flip.* An anticommuting unitary flips the Green form (`greenForm_anticomm`), so a
   `J`-fixed domain vector has zero Green form (`greenForm_eq_zero_of_fixed`).
2. *Centre balance — needs `c ≥ 0`.* The fixed vector is `testVec h c`. BT3 and (P-UNIT) are
   only asserted on `W ≥ 0`, so for `c ≥ 0` they give `stratumSN S N h c = unitStratumTerm h c`
   for every `h = f ⋆ f̃` (`shifted_centre_balance`). For `c < 0` this step breaks: the
   reflection sends the whole premise region `W ≥ 0` into `W ≤ 2c < 0`
   (`shifted_reflection_leaves_premise_region`), so the reflection never meets BT3/(P-UNIT).
3. *Bump step — needs `c` off the cut set.* For a bump of radius `r`, `f ⋆ f̃` vanishes outside
   `[−2r, 2r]`, so the stratum at `c` is zero as soon as every cut has `2r < |c − log p^k|`
   (`stratumSN_bumpR_eq_zero`). Since the cut set of an `(S, N)` truncation is finite, such
   an `r > 0` exists for every `c` that is not itself a cut `log p^k`
   (`exists_radius_off_cuts`). Turbo's fixed radius-`1/4` bump is the special case
   `|c − log p^k| > 1/2`, which holds for all cuts when `0 ≤ c < log 2 − 1/2`.
4. *Unit term positive.* `unitStratumTerm (f ⋆ f̃) c = e^{c/2} (∫ f e^{−y/2})(∫ f e^{y/2}) > 0`
   for a bump (`integral_autocorr_mul_exp`, `bumpR_exp_pos`).

**Results.** `shifted_ptheta_punit_kill`: for every `c ≥ 0` that is not a cut of `(S, N)`,
`¬ (ShiftedPLogTheta D J c ∧ PUnit (D S N))`, for every family and every `J`.
Corollaries: `shifted_kill_small_centre` (`0 ≤ c < log 2 − 1/2`, every `(S, N)`, Turbo's
window); `shifted_kill_empty_cut` (every `c ≥ 0`, using (P-UNIT) on the empty truncation
`S = ∅`); `ptheta_punit_kill` (`c = 0`, the earlier GPPDiscovery5 c755de5 kill, reproved).

**Not covered here.** `c < 0`: the kill route has no foothold (step 2), status OPEN, no
construction either. `c ≥ 0` exactly on a cut `log p^k` of the given `(S, N)`: the fixed-bump
stratum is `w · ∫ f² ≠ 0`; a width-scaling argument (stratum `∝ r`, unit term `∝ r²`) kills it on
paper, Lean GAP.

Lean results PROVED, standard axioms. No `sorry`, no custom axiom, no cited theorem.
(BT-Σ), ARP, CGC and RH remain OPEN.

Daniel Toupin / Golden Physics Project, with AI assistance (Heart of the Cosmos / Grok).
Task and audit: Turbo.
-/

namespace GppBTSigmaShiftedTheta

open GppBTSigmaLocalEuler GppBTSigma GppArithmeticReflection Complex MeasureTheory
open scoped InnerProductSpace ContDiff

section Green

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An anticommuting unitary flips the sign of the Green form. PROVED. -/
theorem greenForm_anticomm (T : E →ₗ.[ℂ] E) (J : E ≃ₗᵢ[ℂ] E) (x y x' y' : T.domain)
    (hx : (x' : E) = J x) (hTx : T x' = -J (T x))
    (hy : (y' : E) = J y) (hTy : T y' = -J (T y)) :
    greenForm T x' y' = -greenForm T x y := by
  simp only [greenForm, hx, hTx, hy, hTy, inner_neg_left, inner_neg_right,
    LinearIsometryEquiv.inner_map_map]
  ring

/-- A `J`-fixed domain vector whose image is in the domain with `T (J x) = −J (T x)` has zero
diagonal Green form. PROVED. -/
theorem greenForm_eq_zero_of_fixed (T : E →ₗ.[ℂ] E) (J : E ≃ₗᵢ[ℂ] E) (x : T.domain)
    (hanti : ∃ y : T.domain, (y : E) = J x ∧ T y = -J (T x)) (hfix : (x : E) = J x) :
    greenForm T x x = 0 := by
  obtain ⟨y, hy, hTy⟩ := hanti
  have hyx : y = x := Subtype.ext (hy.trans hfix.symm)
  subst hyx
  have e := greenForm_anticomm T J y y y y hy hTy hy hTy
  have : (2 : ℂ) * greenForm T y y = 0 := by linear_combination e
  simpa using this

end Green

section Datum

variable {H Gu Gp : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup Gu] [InnerProductSpace ℂ Gu]
  [NormedAddCommGroup Gp] [InnerProductSpace ℂ Gp]

/-- **Weakened (P-θ), shifted centre `c`.** As `PLogTheta`, but the reflection acts on the test
family as `W ↦ 2c − W`, fixed point `W = c`. -/
def ShiftedPLogTheta (D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp) (J : H ≃ₗᵢ[ℂ] H) (c : ℝ) :
    Prop :=
  (∀ S N, BTSigmaTraceSN (D S N) S N) ∧
  (∀ x : H, J (J x) = x) ∧
  (∀ S N (x : (D S N).Tstar.domain), ∃ y : (D S N).Tstar.domain,
      (y : H) = J x ∧ (D S N).Tstar y = -J ((D S N).Tstar x)) ∧
  (∀ S N (h : ℝ → ℝ) (W : ℝ),
      (((D S N).testVec h (2 * c - W) : (D S N).Tstar.domain) : H) = J ((D S N).testVec h W))

/-- The unshifted case is the tree's `PLogTheta`. PROVED. -/
theorem shiftedPLogTheta_zero_iff (D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp)
    (J : H ≃ₗᵢ[ℂ] H) : ShiftedPLogTheta D J 0 ↔ PLogTheta D J := by
  unfold ShiftedPLogTheta PLogTheta
  simp only [mul_zero, zero_sub]

/-- **Where step 2 breaks for `c < 0`.** The shifted reflection maps the whole premise region
`W ≥ 0` (where BT3 and (P-UNIT) are asserted) strictly into `W < 0`. PROVED. -/
theorem shifted_reflection_leaves_premise_region {c : ℝ} (hc : c < 0) {W : ℝ} (hW : 0 ≤ W) :
    2 * c - W < 0 := by linarith

/-- **Shifted centre balance (needs `c ≥ 0`).** The shifted (P-θ) clauses with (P-UNIT) force,
at the fixed point `W = c`, the truncated prime stratum to equal the unit stratum. PROVED. -/
theorem shifted_centre_balance (D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp) (J : H ≃ₗᵢ[ℂ] H)
    {c : ℝ} (hc0 : 0 ≤ c) (hθ : ShiftedPLogTheta D J c) (S : Finset ℕ) (N : ℕ)
    (hU : PUnit (D S N)) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    stratumSN S N (autocorr f) c = unitStratumTerm (autocorr f) c := by
  obtain ⟨hBT3, -, hanti, hrefl⟩ := hθ
  have hfix := hrefl S N (autocorr f) c
  rw [show 2 * c - c = c by ring] at hfix
  have hz := greenForm_eq_zero_of_fixed (D S N).Tstar J ((D S N).testVec (autocorr f) c)
    (hanti S N _) hfix
  rw [green_testVec_of_premises (D S N) S N (hBT3 S N) hU f hf hc c hc0] at hz
  have h2 := (mul_eq_zero.mp hz).resolve_left Complex.I_ne_zero
  have h3 : stratumSN S N (autocorr f) c - unitStratumTerm (autocorr f) c = 0 := by
    exact_mod_cast h2
  linarith

end Datum

section Integral

/-- `∫ (f ⋆ f̃)(v) e^{−v/2} dv = (∫ f e^{−y/2}) (∫ f e^{u/2})`. PROVED. -/
theorem integral_autocorr_mul_exp (f : ℝ → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    ∫ v : ℝ, autocorr f v * Real.exp (-v / 2) =
      (∫ y : ℝ, f y * Real.exp (-y / 2)) * ∫ u : ℝ, f u * Real.exp (u / 2) := by
  set C := ∫ u : ℝ, f u * Real.exp (u / 2)
  have h1 : ∀ v, autocorr f v * Real.exp (-v / 2) =
      ∫ y : ℝ, f y * f (y - v) * Real.exp (-v / 2) := by
    intro v; simp only [autocorr]; rw [integral_mul_const]
  simp_rw [h1]
  have hint : Integrable (Function.uncurry fun v y : ℝ => f y * f (y - v) * Real.exp (-v / 2))
      (volume.prod volume) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (by fun_prop : Continuous fun p : ℝ × ℝ => f p.2 * f (p.2 - p.1) * Real.exp (-p.1 / 2))
    · set K := tsupport f
      have hK : IsCompact K := hc.isCompact
      set M := (fun q : ℝ × ℝ => q.1 - q.2) '' (K ×ˢ K)
      have hM : IsCompact M := (hK.prod hK).image (by fun_prop)
      refine HasCompactSupport.intro (hM.prod hK) ?_
      rintro ⟨v, y⟩ hp
      simp only [Function.uncurry_apply_pair]
      by_cases hy : y ∈ K
      · have hv : v ∉ M := fun h => hp ⟨h, hy⟩
        have : f (y - v) = 0 := by
          by_contra hne
          exact hv ⟨(y, y - v), ⟨hy, subset_tsupport f hne⟩, by simp⟩
        simp [this]
      · simp [image_eq_zero_of_notMem_tsupport hy]
  rw [integral_integral_swap hint]
  have h2 : ∀ y : ℝ, ∫ v : ℝ, f y * f (y - v) * Real.exp (-v / 2) =
      f y * Real.exp (-y / 2) * C := by
    intro y
    have e : ∫ v : ℝ, f (y - v) * Real.exp (-v / 2) = Real.exp (-y / 2) * C := by
      have := integral_sub_left_eq_self (fun u : ℝ => f u * Real.exp (-(y - u) / 2)) volume y
      simp only [sub_sub_cancel] at this
      rw [this, ← integral_const_mul]
      congr 1; ext u
      rw [show -(y - u) / 2 = -y / 2 + u / 2 by ring, Real.exp_add]; ring
    simp_rw [mul_assoc]
    rw [integral_const_mul, e]
  simp_rw [h2]
  rw [integral_mul_const]

end Integral

section Kill

/-- Bump of radius `r`: plateau `r/2`, support the open ball of radius `r`. -/
noncomputable def bumpR (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : ℝ) :=
  ⟨r / 2, r, by positivity, by linarith⟩

theorem bumpR_zero_outside {r : ℝ} (hr : 0 < r) (y : ℝ) (hy : (2 * r) / 2 < |y|) :
    (bumpR r hr : ℝ → ℝ) y = 0 := by
  have : y ∉ Function.support (bumpR r hr : ℝ → ℝ) := by
    rw [ContDiffBump.support_eq]; simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    show ¬ |y| < r; linarith
  simpa using this

/-- **Bump step.** If every cut of `(S, N)` is farther than `2r` from `c`, the radius-`r` bump
sees no prime cut at `W = c`. PROVED. -/
theorem stratumSN_bumpR_eq_zero {r : ℝ} (hr : 0 < r) (S : Finset ℕ) (N : ℕ) (c : ℝ)
    (hfar : ∀ x ∈ cutIndex S N, 2 * r < |c - Real.log ((x.1 ^ x.2 : ℕ) : ℝ)|) :
    stratumSN S N (autocorr (bumpR r hr : ℝ → ℝ)) c = 0 := by
  have hsupp := autocorr_hasSupportIn (f := (bumpR r hr : ℝ → ℝ)) (L := 2 * r)
    (bumpR_zero_outside hr)
  unfold stratumSN
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [hsupp _ (hfar x hx), mul_zero]

theorem bumpR_exp_pos {r : ℝ} (hr : 0 < r) (a : ℝ) :
    0 < ∫ y : ℝ, (bumpR r hr : ℝ → ℝ) y * Real.exp (a * y) := by
  have hcont : Continuous fun y : ℝ => (bumpR r hr : ℝ → ℝ) y * Real.exp (a * y) :=
    (bumpR r hr).continuous.mul (by fun_prop)
  refine hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
    ((bumpR r hr).hasCompactSupport.mul_right)
    (fun y => mul_nonneg (bumpR r hr).nonneg (Real.exp_pos _).le) ?_
  rw [(bumpR r hr).one_of_mem_closedBall (Metric.mem_closedBall_self (by simp [bumpR]; linarith))]
  simp

/-- The unit stratum of a bump autocorrelation is positive at every centre. PROVED. -/
theorem unitStratumTerm_bumpR_pos {r : ℝ} (hr : 0 < r) (c : ℝ) :
    0 < unitStratumTerm (autocorr (bumpR r hr : ℝ → ℝ)) c := by
  rw [unitStratumTerm, integral_autocorr_mul_exp _ (bumpR r hr).continuous
    (bumpR r hr).hasCompactSupport]
  have p1 := bumpR_exp_pos hr (-1 / 2)
  have p2 := bumpR_exp_pos hr (1 / 2)
  have q1 : (∫ y : ℝ, (bumpR r hr : ℝ → ℝ) y * Real.exp (-y / 2)) =
      ∫ y : ℝ, (bumpR r hr : ℝ → ℝ) y * Real.exp (-1 / 2 * y) := by
    congr 1; ext y; congr 2; ring
  have q2 : (∫ y : ℝ, (bumpR r hr : ℝ → ℝ) y * Real.exp (y / 2)) =
      ∫ y : ℝ, (bumpR r hr : ℝ → ℝ) y * Real.exp (1 / 2 * y) := by
    congr 1; ext y; congr 2; ring
  rw [q1, q2]
  exact mul_pos (Real.exp_pos _) (mul_pos p1 p2)

/-- A finite cut set off `c` leaves room for a positive radius. PROVED. -/
theorem exists_radius_off_cuts (S : Finset ℕ) (N : ℕ) (c : ℝ)
    (hoff : ∀ x ∈ cutIndex S N, c ≠ Real.log ((x.1 ^ x.2 : ℕ) : ℝ)) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ cutIndex S N, 2 * r < |c - Real.log ((x.1 ^ x.2 : ℕ) : ℝ)| := by
  set d : ℕ × ℕ → ℝ := fun x => |c - Real.log ((x.1 ^ x.2 : ℕ) : ℝ)|
  set sd := ∑ x ∈ cutIndex S N, 1 / d x
  have hdpos : ∀ x ∈ cutIndex S N, 0 < d x := fun x hx =>
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

/-- **Shifted (P-θ) KILLED off the cuts.** For every centre `c ≥ 0` that is not a cut
`log p^k` of `(S, N)`, no family of genuine boundary triplets carries the shifted reflection
together with (P-UNIT) at `(S, N)`: at the fixed point `W = c` a small bump has zero prime
stratum but positive unit stratum. PROVED. -/
theorem shifted_ptheta_punit_kill {H Gu Gp : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup Gu] [InnerProductSpace ℂ Gu]
    [NormedAddCommGroup Gp] [InnerProductSpace ℂ Gp]
    (D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp) (J : H ≃ₗᵢ[ℂ] H) (S : Finset ℕ) (N : ℕ)
    {c : ℝ} (hc0 : 0 ≤ c) (hoff : ∀ x ∈ cutIndex S N, c ≠ Real.log ((x.1 ^ x.2 : ℕ) : ℝ)) :
    ¬ (ShiftedPLogTheta D J c ∧ PUnit (D S N)) := by
  rintro ⟨hθ, hU⟩
  obtain ⟨r, hr, hfar⟩ := exists_radius_off_cuts S N c hoff
  have e := shifted_centre_balance D J hc0 hθ S N hU (bumpR r hr : ℝ → ℝ)
    (bumpR r hr).contDiff (bumpR r hr).hasCompactSupport
  rw [stratumSN_bumpR_eq_zero hr S N c hfar] at e
  have := unitStratumTerm_bumpR_pos hr c
  linarith

/-- Every cut of a truncation sits at `log p^k ≥ log 2`. PROVED. -/
theorem log_two_le_cut {S : Finset ℕ} {N : ℕ} {x : ℕ × ℕ} (hx : x ∈ cutIndex S N) :
    Real.log 2 ≤ Real.log ((x.1 ^ x.2 : ℕ) : ℝ) := by
  simp only [cutIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx
  obtain ⟨⟨⟨_, hp⟩, hk1, _⟩, _⟩ := hx
  have h2 : (2 : ℝ) ≤ ((x.1 ^ x.2 : ℕ) : ℝ) := by
    have : 2 ≤ x.1 ^ x.2 := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
    exact_mod_cast this
  exact Real.log_le_log (by norm_num) h2

/-- **Turbo's window.** For `0 ≤ c < log 2 − 1/2` the shifted (P-θ) is killed against (P-UNIT)
at every truncation `(S, N)`. PROVED. -/
theorem shifted_kill_small_centre {H Gu Gp : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup Gu] [InnerProductSpace ℂ Gu]
    [NormedAddCommGroup Gp] [InnerProductSpace ℂ Gp]
    (D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp) (J : H ≃ₗᵢ[ℂ] H) (S : Finset ℕ) (N : ℕ)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < Real.log 2 - 1 / 2) :
    ¬ (ShiftedPLogTheta D J c ∧ PUnit (D S N)) :=
  shifted_ptheta_punit_kill D J S N hc0 fun x hx => by
    have := log_two_le_cut hx; intro h; linarith

/-- **Every `c ≥ 0`, via the empty truncation.** The cut set of `S = ∅` is empty, so (P-UNIT)
at `(∅, N)` already kills the shifted reflection at every centre `c ≥ 0`. PROVED. -/
theorem shifted_kill_empty_cut {H Gu Gp : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup Gu] [InnerProductSpace ℂ Gu]
    [NormedAddCommGroup Gp] [InnerProductSpace ℂ Gp]
    (D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp) (J : H ≃ₗᵢ[ℂ] H) (N : ℕ)
    {c : ℝ} (hc0 : 0 ≤ c) :
    ¬ (ShiftedPLogTheta D J c ∧ PUnit (D ∅ N)) :=
  shifted_ptheta_punit_kill D J ∅ N hc0 fun x hx => by simp [cutIndex] at hx

/-- **The unshifted kill (`c = 0`) recovered.** PROVED. -/
theorem ptheta_punit_kill {H Gu Gp : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup Gu] [InnerProductSpace ℂ Gu]
    [NormedAddCommGroup Gp] [InnerProductSpace ℂ Gp]
    (D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp) (J : H ≃ₗᵢ[ℂ] H) (S : Finset ℕ) (N : ℕ) :
    ¬ (PLogTheta D J ∧ PUnit (D S N)) := by
  rw [← shiftedPLogTheta_zero_iff]
  exact shifted_kill_small_centre D J S N le_rfl (by have := Real.log_two_gt_d9; linarith)

end Kill

end GppBTSigmaShiftedTheta
