import GppVerify.RiemannHypothesis.OneSidedPsiRH
import GppVerify.RiemannHypothesis.SineSquarePacket
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The ground-state hypothesis implies the Riemann Hypothesis (conditional theorem)

Sources (GPP-bridge): Codex,
`work/codex/2026-10-22_single_packet_detecting_train_stationary_sewing_frontier.md` §3–§4
(the bounded-detector criterion and the proposed stationary sewing); Astra,
`work/2026-10-22_astra_detector_kms_sewing_audit.md` §1 (the finite prime-sum form of the detector);
Turbo, `MuseResearch/turbo-note-2026-10-23-boundary-ontology.md` (the border (BND) and the warning
against assuming ground-state stationarity silently). On 2026-10-23 Daniel directed that the
ground-state property be adopted as an explicit working hypothesis, to be proved or refuted. This
file makes that hypothesis precise and kernel-checks what it implies. Daniel Toupin / Golden Physics
Project, with AI assistance from Codex, Astra and Turbo (statements) and Claude Code
(formalization).

With the window `w(u) = sin²(πu)` on `[0, 1]`, the weights `a_n = Λ(n)/√n` for `n ≥ 3`, and
`c = S(1/2) = ∫₀¹ e^{u/2} sin²(πu) du`, the detector signal is the prime side alone:

  `K(t) = ∑_{n ≥ 3} Λ(n) n^{−1/2} w(log n − t) − c e^{t/2}`.

No zeros of ζ enter its definition.

* `laplace_K_eq`: if `K` is bounded on `t > 0`, then for `Re z > 1`,
  `ℒK(z) = S(z) (L(Λ, z + 1/2) − T₂(z)) − S(1/2)/(z − 1/2)`, with `T₂` the `n = 2` term.
* `riemannZeta₁_ne_zero_of_bounded`: a bounded `K` forces `(s − 1)ζ(s) ≠ 0` for `Re s > 1/2`.
  The holomorphy of `ℒK` on `Re z > 0`, the non-vanishing of `S` off the imaginary axis
  (`GppSineSquarePacket.S_ne_zero`), and the removable singularity of `(S(z) − S(1/2))/(z − 1/2)`
  make `A = (ℒK − dslope S)/S + T₂` holomorphic on `Re s > 1/2`, with `Z' = −A Z` for
  `Z = (s − 1)ζ(s)`. An entire `Z` solving that equation has no zeros there.
* `riemannHypothesis_of_bounded`: bounded `K` ⇒ RH.
* `riemannHypothesis_of_ground_state` (**GS ⇒ RH**): if, for `t > 0`,
  `K(t) = Re ⟨v, U_t v⟩ + r(t)` for linear isometries `U_t` of a complex inner-product space, a
  vector `v`, and a bounded remainder `r`, then RH holds.

**Scope and honesty.**
* This is a conditional theorem; it does not prove RH. The converse direction (RH ⇒ `K` bounded,
  via the explicit formula) is classical and is not formalized here, since Mathlib has no explicit
  formula.
* With `v = 0` the (GS) hypothesis is bare boundedness of `K`, which is RH-equivalent. So (GS) has
  content only when `(v, U_t)` is constructed from the arithmetic boundary state, and that
  construction is open (Turbo's (BND), equivalently (DOM±)).
* A sieve to `10⁸` (bridge, 2026-10-23) gives `|K(t)| ≤ 0.035` for `3 ≤ t ≤ 17.4`. That is
  evidence, not proof.
* Omitting `n = 2` changes `K` only for `t < log 2`, so it does not affect boundedness.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ArithmeticFunction.vonMangoldt
open GppLandauLaplace GppOneSidedRH

namespace GppGroundStateDetector

/-- The window `w(u) = sin²(πu)` on `[0, 1]`, zero elsewhere. -/
noncomputable def w (u : ℝ) : ℝ :=
  Set.indicator (Icc (0 : ℝ) 1) (fun u => Real.sin (Real.pi * u) ^ 2) u

/-- The prime weights `Λ(n)/√n`, for `n ≥ 3`. -/
noncomputable def a (n : ℕ) : ℝ := if 3 ≤ n then Λ n / Real.sqrt n else 0

/-- The continuum constant `c = S(1/2) = ∫₀¹ e^{u/2} sin²(πu) du`. -/
noncomputable def c : ℝ := ∫ u in (0 : ℝ)..1, Real.exp (u / 2) * Real.sin (Real.pi * u) ^ 2

/-- **The detector signal.** `K(t) = ∑_{n ≥ 3} Λ(n) n^{−1/2} w(log n − t) − c e^{t/2}`. -/
noncomputable def K (t : ℝ) : ℝ := (∑' n : ℕ, a n * w (Real.log n - t)) - c * Real.exp (t / 2)

lemma w_nonneg (u : ℝ) : 0 ≤ w u := by
  unfold w; exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) u

lemma w_le_one (u : ℝ) : w u ≤ 1 := by
  unfold w
  by_cases h : u ∈ Icc (0 : ℝ) 1
  · rw [Set.indicator_of_mem h]
    have := Real.sin_sq_le_one (Real.pi * u)
    exact this
  · rw [Set.indicator_of_notMem h]; norm_num

lemma measurable_w : Measurable w :=
  (Measurable.indicator (by fun_prop) measurableSet_Icc)

lemma a_nonneg (n : ℕ) : 0 ≤ a n := by
  unfold a; split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · rfl

lemma w_eq_zero_of_lt {u : ℝ} (h : u < 0) : w u = 0 := by
  unfold w; exact Set.indicator_of_notMem (fun hu => absurd hu.1 (not_le.mpr h)) _

lemma w_eq_zero_of_gt {u : ℝ} (h : 1 < u) : w u = 0 := by
  unfold w; exact Set.indicator_of_notMem (fun hu => absurd hu.2 (not_le.mpr h)) _

/-- For each `t`, only finitely many `n` contribute. -/
lemma summable_terms (t : ℝ) : Summable fun n : ℕ => a n * w (Real.log n - t) := by
  refine summable_of_ne_finset_zero (s := Finset.range (⌈Real.exp (t + 1)⌉₊ + 1)) fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  have hn' : Real.exp (t + 1) < n := by
    have := Nat.le_ceil (Real.exp (t + 1))
    have h2 : ((⌈Real.exp (t + 1)⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  have hpos : (0 : ℝ) < n := lt_trans (Real.exp_pos _) hn'
  have : 1 < Real.log n - t := by
    have := Real.log_lt_log (Real.exp_pos _) hn'
    rw [Real.log_exp] at this; linarith
  rw [w_eq_zero_of_gt this, mul_zero]

lemma measurable_K : Measurable K := by
  have hpart : ∀ N : ℕ, Measurable fun t : ℝ =>
      ∑ n ∈ Finset.range N, a n * w (Real.log n - t) := fun N =>
    Finset.measurable_sum _ fun n _ =>
      measurable_const.mul (measurable_w.comp (measurable_const.sub measurable_id))
  have htsum : Measurable fun t : ℝ => ∑' n : ℕ, a n * w (Real.log n - t) :=
    measurable_of_tendsto_metrizable hpart
      (tendsto_pi_nhds.mpr fun t => (summable_terms t).hasSum.tendsto_sum_nat)
  exact htsum.sub (measurable_const.mul (Real.continuous_exp.measurable.comp
    (measurable_id.div_const 2)))

lemma one_lt_log {n : ℕ} (hn : 3 ≤ n) : 1 < Real.log n := by
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have := Real.exp_one_lt_d9
  linarith

/-- **One prime's Laplace term.** For `n ≥ 3`, `∫₀^∞ w(log n − t) e^{−zt} dt = n^{−z} S(z)`. -/
lemma integral_term {n : ℕ} (hn : 3 ≤ n) (z : ℂ) :
    ∫ t in Ioi (0 : ℝ), ((w (Real.log n - t) : ℝ) : ℂ) * Complex.exp (-z * t) =
      Complex.exp (-z * Real.log n) * GppSineSquarePacket.S z := by
  set L := Real.log n with hLdef
  have hL : 1 < L := one_lt_log hn
  have hind : (fun t : ℝ => ((w (L - t) : ℝ) : ℂ) * Complex.exp (-z * t)) =
      Set.indicator (Icc (L - 1) L) (fun t : ℝ =>
        ((Real.sin (Real.pi * (L - t)) ^ 2 : ℝ) : ℂ) * Complex.exp (-z * t)) := by
    ext t
    by_cases ht : t ∈ Icc (L - 1) L
    · rw [Set.indicator_of_mem ht, w, Set.indicator_of_mem]
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    · rw [Set.indicator_of_notMem ht, w, Set.indicator_of_notMem, Complex.ofReal_zero, zero_mul]
      intro hu; exact ht ⟨by linarith [hu.2], by linarith [hu.1]⟩
  rw [hind, setIntegral_indicator measurableSet_Icc,
    Set.inter_eq_right.mpr (show Icc (L - 1) L ⊆ Ioi (0 : ℝ) from
      fun t ht => show (0 : ℝ) < t by linarith [ht.1]),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have hsub := intervalIntegral.integral_comp_sub_left (fun u : ℝ =>
    ((Real.sin (Real.pi * u) ^ 2 : ℝ) : ℂ) * Complex.exp (-z * (L - u))) L (a := L - 1) (b := L)
  simp only [sub_sub_cancel, sub_self] at hsub
  have hcast : ∀ x : ℝ, -z * ((L : ℂ) - ((L - x : ℝ) : ℂ)) = -z * x := fun x => by
    push_cast; ring
  simp only [hcast] at hsub
  rw [hsub, GppSineSquarePacket.S, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [show -z * ((L : ℝ) - (u : ℝ) : ℂ) = -z * L + z * u by ring, Complex.exp_add]
  push_cast
  ring

/-- The weight `Λ(n)/√n · n^{−z}` is the `L`-series term of `Λ` at `z + 1/2`. -/
lemma a_mul_exp_eq_term {n : ℕ} (hn : 3 ≤ n) (z : ℂ) :
    (a n : ℂ) * Complex.exp (-z * Real.log n) =
      LSeries.term (fun n ↦ (Λ n : ℂ)) (z + 1 / 2) n := by
  have hn0 : n ≠ 0 := by omega
  have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  rw [LSeries.term_of_ne_zero hn0, a, if_pos hn,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hn0), ← Complex.natCast_log,
    Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos]
  push_cast
  rw [div_eq_mul_inv, mul_assoc, ← Complex.exp_neg]
  rw [← Complex.exp_add, eq_div_iff (Complex.exp_ne_zero _), mul_assoc, ← Complex.exp_add]
  rw [show -(Complex.log n * (1 / 2)) + -z * Complex.log n + Complex.log n * (z + 1 / 2) = 0
    by ring, Complex.exp_zero, mul_one]

/-- Pointwise domination of one prime's integrand by a box. -/
lemma norm_term_le_indicator (n : ℕ) (z : ℂ) (hz : 0 ≤ z.re) (t : ℝ) :
    ‖((a n * w (Real.log n - t) : ℝ) : ℂ) * Complex.exp (-z * t)‖ ≤
      Set.indicator (Icc (Real.log n - 1) (Real.log n))
        (fun _ => a n * Real.exp (-z.re * (Real.log n - 1))) t := by
  set L := Real.log n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (a_nonneg n) (w_nonneg _)), Complex.norm_exp]
  have hre : (-z * (t : ℂ)).re = -z.re * t := by simp
  rw [hre]
  by_cases ht : t ∈ Icc (L - 1) L
  · rw [Set.indicator_of_mem ht]
    have h1 : Real.exp (-z.re * t) ≤ Real.exp (-z.re * (L - 1)) :=
      Real.exp_le_exp.mpr (by nlinarith [ht.1])
    calc a n * w (L - t) * Real.exp (-z.re * t) ≤ a n * 1 * Real.exp (-z.re * (L - 1)) := by
          gcongr
          · exact mul_nonneg (a_nonneg n) zero_le_one
          · exact a_nonneg n
          · exact w_le_one _
      _ = _ := by ring
  · rw [Set.indicator_of_notMem ht]
    have : w (L - t) = 0 := by
      unfold w; refine Set.indicator_of_notMem (fun hu => ht ⟨?_, ?_⟩) _
      · linarith [hu.2]
      · linarith [hu.1]
    rw [this]; simp

lemma integrableOn_box (n : ℕ) (x : ℝ) : IntegrableOn
    (Set.indicator (Icc (Real.log n - 1) (Real.log n))
      (fun _ : ℝ => a n * Real.exp (-x * (Real.log n - 1)))) (Ioi 0) :=
  ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc).integrableOn

lemma measurable_term (n : ℕ) (z : ℂ) : Measurable fun t : ℝ =>
    ((a n * w (Real.log n - t) : ℝ) : ℂ) * Complex.exp (-z * t) :=
  (Complex.measurable_ofReal.comp (measurable_const.mul
    (measurable_w.comp (measurable_const.sub measurable_id)))).mul
    (by fun_prop : Continuous fun t : ℝ => Complex.exp (-z * t)).measurable

lemma integrable_term (n : ℕ) (z : ℂ) (hz : 0 ≤ z.re) : IntegrableOn (fun t : ℝ =>
    ((a n * w (Real.log n - t) : ℝ) : ℂ) * Complex.exp (-z * t)) (Ioi 0) := by
  by_cases hn : 3 ≤ n
  · exact (integrableOn_box n z.re).mono' (measurable_term n z).aestronglyMeasurable
      (Eventually.of_forall (norm_term_le_indicator n z hz))
  · have : a n = 0 := by unfold a; rw [if_neg hn]
    simp [this]

/-- **Bound on one prime's term.** For `n ≥ 3` and `x = Re z ≥ 0`. -/
lemma integral_norm_term_le {n : ℕ} (hn : 3 ≤ n) (z : ℂ) (hz : 0 ≤ z.re) :
    ∫ t in Ioi (0 : ℝ), ‖((a n * w (Real.log n - t) : ℝ) : ℂ) * Complex.exp (-z * t)‖ ≤
      a n * Real.exp (-z.re * (Real.log n - 1)) := by
  have hL : 1 < Real.log n := one_lt_log hn
  calc _ ≤ ∫ t in Ioi (0 : ℝ), Set.indicator (Icc (Real.log n - 1) (Real.log n))
        (fun _ => a n * Real.exp (-z.re * (Real.log n - 1))) t :=
        integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
          (integrableOn_box n z.re)
          (Eventually.of_forall (norm_term_le_indicator n z hz))
    _ = _ := by
      rw [setIntegral_indicator measurableSet_Icc,
        Set.inter_eq_right.mpr (show Icc (Real.log n - 1) (Real.log n) ⊆ Ioi (0 : ℝ) from
          fun t ht => show (0 : ℝ) < t by linarith [ht.1])]
      simp

lemma summable_bound {x : ℝ} (hx : 1 / 2 < x) :
    Summable fun n : ℕ => a n * Real.exp (-x * (Real.log n - 1)) := by
  have hs : LSeriesSummable (fun n ↦ (Λ n : ℂ)) ((x : ℂ) + 1 / 2) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simp; linarith)
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (a_nonneg n) (Real.exp_pos _).le)
    (fun n => ?_) (hs.norm.mul_left (Real.exp x))
  by_cases hn : 3 ≤ n
  · rw [← a_mul_exp_eq_term hn, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (a_nonneg n), Complex.norm_exp]
    have : (-(x : ℂ) * ((Real.log n : ℝ) : ℂ)).re = -x * Real.log n := by
      rw [show -(x : ℂ) * ((Real.log n : ℝ) : ℂ) = ((-x * Real.log n : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_re]
    rw [this, show -x * (Real.log n - 1) = x + -x * Real.log n by ring, Real.exp_add]
    ring_nf; rfl
  · have : a n = 0 := by unfold a; rw [if_neg hn]
    rw [this, zero_mul]; positivity

lemma c_eq : ((c : ℝ) : ℂ) = GppSineSquarePacket.S (1 / 2) := by
  rw [c, GppSineSquarePacket.S, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun u _ => ?_
  push_cast
  congr 2
  ring

/-- The term of `Λ`'s `L`-series at `n = 2`, an entire function of `z`. -/
noncomputable def T2 (z : ℂ) : ℂ := (Λ 2 : ℂ) * Complex.exp (-(z + 1 / 2) * Real.log 2)

lemma term_two (z : ℂ) : LSeries.term (fun n ↦ (Λ n : ℂ)) (z + 1 / 2) 2 = T2 z := by
  rw [LSeries.term_of_ne_zero (by norm_num), T2, Complex.cpow_def_of_ne_zero (by norm_num),
    div_eq_mul_inv, ← Complex.exp_neg]
  congr 2
  rw [show ((2 : ℕ) : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num)]
  ring

/-- **The Laplace identity.** If `K` is bounded on `t > 0`, then for `Re z > 1`,
`ℒK(z) = S(z) (L(Λ, z + 1/2) − T₂(z)) − S(1/2)/(z − 1/2)`. -/
theorem laplace_K_eq {B : ℝ} (hB : ∀ t, 0 < t → |K t| ≤ B) {z : ℂ} (hz : 1 < z.re) :
    laplace K z = GppSineSquarePacket.S z * (LSeries (fun n ↦ (Λ n : ℂ)) (z + 1 / 2) - T2 z) -
      GppSineSquarePacket.S (1 / 2) / (z - 1 / 2) := by
  have hz0 : 0 ≤ z.re := by linarith
  set F : ℕ → ℝ → ℂ := fun n t =>
    ((a n * w (Real.log n - t) : ℝ) : ℂ) * Complex.exp (-z * t) with hF
  -- the prime part, term by term
  have hFint : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := fun n =>
    integrable_term n z hz0
  have hFsum : Summable fun n => ∫ t in Ioi (0 : ℝ), ‖F n t‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _)
      (fun n => ?_) (summable_bound (x := z.re) (by linarith))
    by_cases hn : 3 ≤ n
    · exact integral_norm_term_le hn z hz0
    · have : a n = 0 := by unfold a; rw [if_neg hn]
      simp [hF, this]
  have hswap := integral_tsum_of_summable_integral_norm hFint hFsum
  have hterm : ∀ n, ∫ t in Ioi (0 : ℝ), F n t =
      (LSeries.term (fun n ↦ (Λ n : ℂ)) (z + 1 / 2) n -
        if n = 2 then T2 z else 0) * GppSineSquarePacket.S z := by
    intro n
    by_cases hn : 3 ≤ n
    · have : ∀ t : ℝ, F n t =
          (a n : ℂ) * (((w (Real.log n - t) : ℝ) : ℂ) * Complex.exp (-z * t)) := fun t => by
        simp only [hF]; push_cast; ring
      simp_rw [this]
      rw [integral_const_mul, integral_term hn, if_neg (by omega), sub_zero, ← mul_assoc,
        a_mul_exp_eq_term hn]
    · have ha : a n = 0 := by unfold a; rw [if_neg hn]
      have hlhs : ∫ t in Ioi (0 : ℝ), F n t = 0 := by simp [hF, ha]
      rw [hlhs]
      interval_cases n
      · simp
      · simp [LSeries.term_of_ne_zero, ArithmeticFunction.vonMangoldt_apply_one]
      · rw [if_pos rfl, term_two, sub_self, zero_mul]
  have hsumF : ∀ t, ∑' n, F n t =
      ((∑' n : ℕ, a n * w (Real.log n - t) : ℝ) : ℂ) * Complex.exp (-z * t) := fun t => by
    simp only [hF]; rw [Complex.ofReal_tsum, tsum_mul_right]
  have hLS : LSeriesSummable (fun n ↦ (Λ n : ℂ)) (z + 1 / 2) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simp; linarith)
  have hprime : ∫ t in Ioi (0 : ℝ),
      ((∑' n : ℕ, a n * w (Real.log n - t) : ℝ) : ℂ) * Complex.exp (-z * t) =
      GppSineSquarePacket.S z * (LSeries (fun n ↦ (Λ n : ℂ)) (z + 1 / 2) - T2 z) := by
    simp_rw [← hsumF]
    rw [← hswap]
    simp_rw [hterm]
    rw [tsum_mul_right, Summable.tsum_sub hLS (summable_of_ne_finset_zero
      (s := {2}) fun n hn => by rw [if_neg (by simpa using hn)]), tsum_ite_eq, LSeries]
    ring
  -- the continuum part
  have hre : ((1 / 2 : ℂ) - z).re < 0 := by simp; linarith
  have hcont_int : IntegrableOn (fun t : ℝ =>
      ((c * Real.exp (t / 2) : ℝ) : ℂ) * Complex.exp (-z * t)) (Ioi 0) := by
    have : IntegrableOn (fun t : ℝ => (c : ℂ) * Complex.exp ((1 / 2 - z) * t)) (Ioi 0) :=
      (integrableOn_exp_mul_complex_Ioi hre 0).const_mul (c : ℂ)
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    push_cast
    rw [mul_assoc, ← Complex.exp_add]
    congr 2; ring
  have hcont : ∫ t in Ioi (0 : ℝ), ((c * Real.exp (t / 2) : ℝ) : ℂ) * Complex.exp (-z * t) =
      GppSineSquarePacket.S (1 / 2) / (z - 1 / 2) := by
    have : ∀ t : ℝ, ((c * Real.exp (t / 2) : ℝ) : ℂ) * Complex.exp (-z * t) =
        (c : ℂ) * Complex.exp ((1 / 2 - z) * t) := fun t => by
      push_cast; rw [mul_assoc, ← Complex.exp_add]; congr 2; ring
    simp_rw [this]
    rw [integral_const_mul, integral_exp_mul_complex_Ioi hre 0, c_eq]
    have hz2 : z - 1 / 2 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [show (1 / 2 : ℂ) - z = -(z - 1 / 2) by ring]
    field_simp
  -- the bounded signal is integrable
  have hK_int : IntegrableOn (fun t : ℝ => (K t : ℂ) * Complex.exp (-z * t)) (Ioi 0) := by
    have hexp : IntegrableOn (fun t : ℝ => B * Real.exp (-z.re * t)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 (b := z.re) (by linarith)).const_mul B
    refine hexp.mono' ((Complex.measurable_ofReal.comp measurable_K).mul
      (by fun_prop : Continuous fun t : ℝ => Complex.exp (-z * t)).measurable).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have : (-z * (t : ℂ)).re = -z.re * t := by simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (hB t ht) (Real.exp_pos _).le
  have hP_int : IntegrableOn (fun t : ℝ =>
      ((∑' n : ℕ, a n * w (Real.log n - t) : ℝ) : ℂ) * Complex.exp (-z * t)) (Ioi 0) := by
    refine (hK_int.add hcont_int).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply, K]; push_cast; ring
  rw [laplace]
  have : ∀ t : ℝ, (K t : ℂ) * Complex.exp (-z * t) =
      ((∑' n : ℕ, a n * w (Real.log n - t) : ℝ) : ℂ) * Complex.exp (-z * t) -
        ((c * Real.exp (t / 2) : ℝ) : ℂ) * Complex.exp (-z * t) := fun t => by
    simp only [K]; push_cast; ring
  simp_rw [this]
  rw [integral_sub hP_int hcont_int, hprime, hcont]

/-! ### Holomorphy of `ℒK` and the zero-free half-plane -/

lemma integrable_of_bounded {g : ℝ → ℝ} (hgm : Measurable g) {B : ℝ}
    (hB : ∀ t, 0 < t → |g t| ≤ B) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => g t * Real.exp (-x * t)) (Ioi 0) := by
  refine ((exp_neg_integrableOn_Ioi 0 hx).const_mul B).mono'
    (hgm.mul (by fun_prop : Continuous fun t : ℝ =>
      Real.exp (-x * t)).measurable).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (hB t ht) (Real.exp_pos _).le

lemma differentiableOn_laplace_of_bounded {g : ℝ → ℝ} (hgm : Measurable g) {B : ℝ}
    (hB : ∀ t, 0 < t → |g t| ≤ B) :
    DifferentiableOn ℂ (laplace g) {z : ℂ | 0 < z.re} := by
  set gp : ℝ → ℝ := fun t => max (g t) 0
  set gm : ℝ → ℝ := fun t => max (-g t) 0
  have hgp : ∀ t, 0 ≤ gp t := fun t => le_max_right _ _
  have hgm' : ∀ t, 0 ≤ gm t := fun t => le_max_right _ _
  have mp : Measurable gp := hgm.max measurable_const
  have mm : Measurable gm := hgm.neg.max measurable_const
  have bp : ∀ t, 0 < t → |gp t| ≤ B := fun t ht => by
    rw [abs_of_nonneg (hgp t)]
    exact max_le (le_trans (le_abs_self _) (hB t ht)) (le_trans (abs_nonneg _) (hB t ht))
  have bm : ∀ t, 0 < t → |gm t| ≤ B := fun t ht => by
    rw [abs_of_nonneg (hgm' t)]
    exact max_le (le_trans (neg_le_abs _) (hB t ht)) (le_trans (abs_nonneg _) (hB t ht))
  have conv : ∀ {f : ℝ → ℝ}, Measurable f → (∀ t, 0 < t → |f t| ≤ B) → ∀ r : ℝ, 0 < r →
      ∫⁻ t in Ioi 0, ENNReal.ofReal (f t * Real.exp (-r * t)) < ⊤ :=
    fun hf hfB r hr => (integrable_of_bounded hf hfB hr).lintegral_lt_top
  have hp := differentiableOn_laplace hgp mp (a := 0) (conv mp bp)
  have hm := differentiableOn_laplace hgm' mm (a := 0) (conv mm bm)
  refine (hp.sub hm).congr fun z hz => ?_
  have hz' : 0 < z.re := hz
  have cint : ∀ {f : ℝ → ℝ}, Measurable f → (∀ t, 0 < t → |f t| ≤ B) →
      IntegrableOn (fun t : ℝ => (f t : ℂ) * Complex.exp (-z * t)) (Ioi 0) := by
    intro f hf hfB
    refine (integrable_of_bounded hf hfB hz').norm.mono'
      ((Complex.measurable_ofReal.comp hf).mul (by fun_prop : Continuous fun t : ℝ =>
        Complex.exp (-z * t)).measurable).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_exp,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    have : (-z * (t : ℂ)).re = -z.re * t := by simp
    rw [this]
  show laplace g z = laplace gp z - laplace gm z
  rw [laplace, laplace, laplace, ← integral_sub (cint mp bp) (cint mm bm)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have : g t = gp t - gm t := by
    simp only [gp, gm]; rcases le_total (g t) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  rw [this]; push_cast; ring

lemma re_pos_facts {z : ℂ} (h : 0 < z.re) : z ≠ 0 ∧ z ^ 2 + 4 * (Real.pi : ℂ) ^ 2 ≠ 0 := by
  refine ⟨fun h0 => by rw [h0, Complex.zero_re] at h; exact lt_irrefl _ h, fun h0 => ?_⟩
  have hre := congrArg Complex.re h0
  have him := congrArg Complex.im h0
  simp only [sq, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im,
    Complex.zero_re, Complex.zero_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat] at hre him
  have hzi : z.im = 0 :=
    (mul_eq_zero.mp (show z.re * z.im = 0 by linarith)).resolve_left h.ne'
  rw [hzi] at hre
  nlinarith [sq_nonneg z.re, Real.pi_pos]

lemma differentiableOn_S : DifferentiableOn ℂ GppSineSquarePacket.S {z : ℂ | 0 < z.re} := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  intro z hz
  obtain ⟨h0, h1⟩ := re_pos_facts hz
  have hev : (fun w : ℂ => 2 * (Real.pi : ℂ) ^ 2 * (Complex.exp w - 1) /
      (w * (w ^ 2 + 4 * (Real.pi : ℂ) ^ 2))) =ᶠ[𝓝 z] GppSineSquarePacket.S := by
    filter_upwards [hU.mem_nhds hz] with w hw
    obtain ⟨hw0, hw1⟩ := re_pos_facts hw
    exact (GppSineSquarePacket.S_eq hw0 hw1).symm
  have hd : DifferentiableAt ℂ (fun w : ℂ => 2 * (Real.pi : ℂ) ^ 2 * (Complex.exp w - 1) /
      (w * (w ^ 2 + 4 * (Real.pi : ℂ) ^ 2))) z := by
    have : z * (z ^ 2 + 4 * (Real.pi : ℂ) ^ 2) ≠ 0 := mul_ne_zero h0 h1
    fun_prop (disch := assumption)
  exact (hd.congr_of_eventuallyEq hev.symm).differentiableWithinAt

/-- **Bounded detector ⇒ no zeros of `(s − 1)ζ(s)` with `Re s > 1/2`.** -/
theorem riemannZeta₁_ne_zero_of_bounded {B : ℝ} (hB : ∀ t, 0 < t → |K t| ≤ B) {s : ℂ}
    (hs : 1 / 2 < s.re) : riemannZeta₁ s ≠ 0 := by
  set U0 : Set ℂ := {z : ℂ | 0 < z.re}
  set V : Set ℂ := {s : ℂ | 1 / 2 < s.re}
  have hU0 : IsOpen U0 := isOpen_lt continuous_const Complex.continuous_re
  have hVo : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hmaps : MapsTo (fun s : ℂ => s - 1 / 2) V U0 := fun s hs => by
    show 0 < (s - 1 / 2).re; simp only [Complex.sub_re]; norm_num; exact hs
  have hL := differentiableOn_laplace_of_bounded measurable_K hB
  have hhalf : (1 / 2 : ℂ) ∈ U0 := by show (0 : ℝ) < (1 / 2 : ℂ).re; norm_num
  have hds : DifferentiableOn ℂ (dslope GppSineSquarePacket.S (1 / 2)) U0 :=
    (differentiableOn_dslope (hU0.mem_nhds hhalf)).mpr differentiableOn_S
  have hSne : ∀ z ∈ U0, GppSineSquarePacket.S z ≠ 0 := fun z hz =>
    GppSineSquarePacket.S_ne_zero (ne_of_gt (show 0 < z.re from hz))
  set A : ℂ → ℂ := fun s =>
    (laplace K (s - 1 / 2) - dslope GppSineSquarePacket.S (1 / 2) (s - 1 / 2)) /
      GppSineSquarePacket.S (s - 1 / 2) + T2 (s - 1 / 2)
  have hsub : DifferentiableOn ℂ (fun s : ℂ => s - 1 / 2) V :=
    (differentiable_id.sub_const _).differentiableOn
  have hA : DifferentiableOn ℂ A V := by
    refine ((((hL.comp hsub hmaps).sub (hds.comp hsub hmaps)).div
      (differentiableOn_S.comp hsub hmaps) fun s hs => hSne _ (hmaps hs)).add ?_)
    exact (by unfold T2; fun_prop : Differentiable ℂ fun s : ℂ => T2 (s - 1 / 2)).differentiableOn
  have hAeq : ∀ s : ℂ, 3 / 2 < s.re →
      A s = LSeries (fun n ↦ (Λ n : ℂ)) s - 1 / (s - 1) := by
    intro s hs
    have hz : 1 < (s - 1 / 2).re := by simp only [Complex.sub_re]; norm_num; linarith
    have hz0 : s - 1 / 2 ∈ U0 := by show 0 < (s - 1 / 2).re; linarith
    have hSz := hSne _ hz0
    have hne : s - 1 / 2 ≠ 1 / 2 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hs1 : s - 1 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    simp only [A]
    rw [laplace_K_eq hB hz, dslope_of_ne _ hne, slope_def_field,
      show s - 1 / 2 + 1 / 2 = s by ring, show s - 1 / 2 - 1 / 2 = s - 1 by ring]
    generalize GppSineSquarePacket.S (s - 1 / 2) = X at hSz ⊢
    generalize LSeries (fun n ↦ (Λ n : ℂ)) s = Ls
    generalize T2 (s - 1 / 2) = T
    generalize GppSineSquarePacket.S (1 / 2) = c0
    field_simp
    ring
  have hZd := differentiable_riemannZeta₁
  have hZd' := differentiable_deriv_riemannZeta₁
  set H : ℂ → ℂ := fun z => riemannZeta₁ z * A z + deriv riemannZeta₁ z
  have hH : AnalyticOnNhd ℂ H V :=
    ((hZd.differentiableOn.mul hA).add hZd'.differentiableOn).analyticOnNhd hVo
  have h2V : (2 : ℂ) ∈ V := by show (1 / 2 : ℝ) < (2 : ℂ).re; norm_num
  have hHev : H =ᶠ[𝓝 2] 0 := by
    have hW : IsOpen {z : ℂ | 3 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hW.mem_nhds (show (3 / 2 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    have hz' : 3 / 2 < z.re := hz
    show riemannZeta₁ z * A z + deriv riemannZeta₁ z = 0
    rw [hAeq z hz']
    exact zeta_identity (by linarith)
  have hH0 : Set.EqOn H 0 V :=
    hH.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_halfSpace_re_gt (1 / 2 : ℝ)).isPreconnected h2V hHev
  have hode : ∀ z ∈ V, deriv riemannZeta₁ z = -(A z * riemannZeta₁ z) := by
    intro z hz
    have := hH0 hz
    simp only [H, Pi.zero_apply] at this
    linear_combination this
  refine ne_zero_of_deriv_eq_neg_mul hZd riemannZeta₁_two_ne_zero
    (hA.analyticAt (hVo.mem_nhds hs)) ?_
  filter_upwards [hVo.mem_nhds hs] with z hz using hode z hz

/-- **A bounded detector signal implies the Riemann Hypothesis.** -/
theorem riemannHypothesis_of_bounded {B : ℝ} (hB : ∀ t, 0 < t → |K t| ≤ B) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_ne_zero fun s hs => ?_
  by_cases hs1 : s = 1
  · exact riemannZeta_ne_zero_of_one_le_re (by rw [hs1, Complex.one_re])
  · intro h
    exact riemannZeta₁_ne_zero_of_bounded hB hs (by rw [riemannZeta₁_eq_mul hs1, h, mul_zero])

/-- **The ground-state hypothesis (GS) implies the Riemann Hypothesis.** If, for `t > 0`, the
detector signal is a stationary correlation `Re ⟨v, U_t v⟩` of a family of linear isometries plus
a bounded remainder `r`, then RH holds. -/
theorem riemannHypothesis_of_ground_state {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (U : ℝ → E →ₗᵢ[ℂ] E) (v : E) (r : ℝ → ℝ) {R : ℝ}
    (hr : ∀ t, 0 < t → |r t| ≤ R)
    (hK : ∀ t, 0 < t → K t = (@inner ℂ E _ v (U t v)).re + r t) : RiemannHypothesis := by
  refine riemannHypothesis_of_bounded (B := ‖v‖ ^ 2 + R) fun t ht => ?_
  rw [hK t ht]
  have h1 : |(@inner ℂ E _ v (U t v)).re| ≤ ‖v‖ ^ 2 := by
    calc _ ≤ ‖@inner ℂ E _ v (U t v)‖ := Complex.abs_re_le_norm _
      _ ≤ ‖v‖ * ‖U t v‖ := norm_inner_le_norm _ _
      _ = ‖v‖ ^ 2 := by rw [(U t).norm_map]; ring
  calc _ ≤ |(@inner ℂ E _ v (U t v)).re| + |r t| := abs_add_le _ _
    _ ≤ _ := add_le_add h1 (hr t ht)

end GppGroundStateDetector
