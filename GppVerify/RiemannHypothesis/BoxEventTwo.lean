import GppVerify.RiemannHypothesis.BoxInitialNumerics

/-!
# The first prime-power event `q = 2`: the box form is positive on `(0, log 3)`

`BoxInitialNumerics` showed the box form positive on the prime-free interval `(0, log 2]`.  This file continues
through the first event:

* **Generic event-gap lemma** (`Wn_pos_on_gap`): `Wn C n L = Vm C L + primeAff n L` has second derivative
  `2·curv` on a gap with the prime floor frozen at `n`, and `curv` is monotone, so the event-parabola step applies
  from the event `a`: `(Vm' a + primeSlope n)² < 2 (2 curv a)·Wn C n a` ⇒ `Wn C n > 0` on `[a, b]`.
* **The event `q = 2`** at `a = log 2`, where `e^{−a/2} = 1/√2`: the slope jumps by `−√2 log 2`
  (`primeSlope 2`), `curv(log 2) = 5√2/6`, and `Gcl(log 2)`, `∫₀^{log 2} Gcl` are bounded by the positive series of
  `GclSeries.lean` (`Gcl(log 2) = √2·Σ_j 4^{−j}/(4j+1)` up to a geometric tail).

The conclusion `box_pos_to_log_three`: `0 < 16 (cosh(L/2) − 1) + archBox L + primeBox L` for every `0 < L < log 3`.

**Scope.** First event only: two of the `665 134` prime-power events of GPP's `10⁷` certificate.  Same scope
as `BoxInitialNumerics`: the explicit-formula box expression, `weilForm` not identified, nothing is the Weil
criterion.  ARP, RH, OB-6, UB are OPEN.

No `sorry`, no axiom.
-/

open Real Set MeasureTheory Filter Topology
open scoped ArithmeticFunction.vonMangoldt
open GppBoxCurvature GppGclSeries GppEventParabola GppPlastic GppBoxArchimedean GppBoxInitial GppBoxNumerics

noncomputable section

namespace GppBoxEvent

/-- The box model with archimedean constant `C` and prime floor frozen at `n`. -/
def Wn (C : ℝ) (n : ℕ) (L : ℝ) : ℝ := Vm C L + primeAff n L

theorem hasDerivAt_Wn (C : ℝ) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (Wn C n) (vslope C y + primeSlope n) y :=
  (hasDerivAt_Vm C hy).add (hasDerivAt_primeAff n y)

theorem hasDerivAt_wslope (C : ℝ) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun z => vslope C z + primeSlope n) (2 * curv y) y :=
  (hasDerivAt_vslope C hy).add_const _

/-- **Event-gap positivity.**  On `[a, b] ⊂ (0, ∞)` with the floor frozen at `n`: if `curv a > 0` and
`(vslope C a + primeSlope n)² < 2 (2 curv a)·Wn C n a`, then `Wn C n > 0` on `[a, b]`. -/
theorem Wn_pos_on_gap {C : ℝ} {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hcurv : 0 < curv a)
    (hcert : (vslope C a + primeSlope n) ^ 2 < 2 * (2 * curv a) * Wn C n a) {t : ℝ}
    (ht : t ∈ Icc a b) : 0 < Wn C n t := by
  refine gap_positive (f := Wn C n) (g := fun z => vslope C z + primeSlope n)
    (h := fun y => 2 * curv y) (k := 2 * curv a) hab (by linarith)
    (fun y hy => (hasDerivAt_Wn C n (lt_of_lt_of_le ha hy.1)).continuousAt.continuousWithinAt)
    (fun y hy => (hasDerivAt_wslope C n (lt_of_lt_of_le ha hy.1)).continuousAt.continuousWithinAt)
    ?_ ?_ ?_ hcert ht
  · intro x hx; exact hasDerivAt_Wn C n (ha.trans hx.1)
  · intro x hx; exact hasDerivAt_wslope C n (ha.trans hx.1)
  · intro x hx
    have := curv_monotoneOn (mem_Ioi.mpr ha) (mem_Ioi.mpr (ha.trans hx.1)) hx.1.le
    linarith

/-! ### Facts at `a = log 2` -/

theorem exp_half_log_two : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
  rw [← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.exp_log (Real.sqrt_pos.mpr (by norm_num))]

theorem exp_neg_half_log_two : Real.exp (-Real.log 2 / 2) = Real.sqrt 2 / 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [show -Real.log 2 / 2 = -(Real.log 2 / 2) by ring, Real.exp_neg, exp_half_log_two]
  field_simp
  nlinarith

theorem cosh_half_log_two : Real.cosh (Real.log 2 / 2) = 3 * Real.sqrt 2 / 4 := by
  rw [Real.cosh_eq, exp_half_log_two, show -(Real.log 2 / 2) = -Real.log 2 / 2 by ring,
    exp_neg_half_log_two]
  ring

theorem sinh_half_log_two : Real.sinh (Real.log 2 / 2) = Real.sqrt 2 / 4 := by
  rw [Real.sinh_eq, exp_half_log_two, show -(Real.log 2 / 2) = -Real.log 2 / 2 by ring,
    exp_neg_half_log_two]
  ring

theorem curv_log_two : curv (Real.log 2) = 5 * Real.sqrt 2 / 6 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  unfold curv kappaGamma
  have e1 : Real.exp (-5 * Real.log 2 / 2) = (Real.sqrt 2 / 2) ^ 5 := by
    rw [show -5 * Real.log 2 / 2 = (5 : ℕ) * (-Real.log 2 / 2) by push_cast; ring, Real.exp_nat_mul,
      exp_neg_half_log_two]
  have e2 : Real.exp (-2 * Real.log 2) = 1 / 4 := by
    rw [show -2 * Real.log 2 = -(2 * Real.log 2) by ring, Real.exp_neg,
      show 2 * Real.log 2 = Real.log 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num,
      Real.exp_log (by norm_num)]
    norm_num
  rw [exp_half_log_two, e1, e2]
  have h5 : (Real.sqrt 2 / 2) ^ 5 = Real.sqrt 2 / 8 := by
    have : (Real.sqrt 2) ^ 5 = 4 * Real.sqrt 2 := by
      calc (Real.sqrt 2) ^ 5 = (Real.sqrt 2 * Real.sqrt 2) ^ 2 * Real.sqrt 2 := by ring
        _ = 4 * Real.sqrt 2 := by rw [h2]; norm_num
    calc (Real.sqrt 2 / 2) ^ 5 = (Real.sqrt 2) ^ 5 / 32 := by ring
      _ = Real.sqrt 2 / 8 := by rw [this]; ring
  rw [h5]
  ring

theorem sqrt_two_gt : (141421 / 100000 : ℝ) < Real.sqrt 2 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

theorem sqrt_two_lt : Real.sqrt 2 < 141422 / 100000 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem primeSlope_two : primeSlope 2 = -(Real.sqrt 2 * Real.log 2) := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  unfold primeSlope
  rw [show Finset.Icc 1 2 = {1, 2} from by decide, Finset.sum_pair (by norm_num)]
  simp only [ArithmeticFunction.vonMangoldt_apply_one, ArithmeticFunction.vonMangoldt_apply_prime
    Nat.prime_two]
  push_cast
  simp
  field_simp
  nlinarith

theorem primeAff_two_log_two : primeAff 2 (Real.log 2) = 0 := by
  unfold primeAff
  have : ∑ m ∈ Finset.Icc 1 2, (Λ m : ℝ) / Real.sqrt m * (Real.log 2 - Real.log m) = 0 := by
    rw [show Finset.Icc 1 2 = {1, 2} from by decide, Finset.sum_pair (by norm_num)]
    simp
  rw [this]; ring

/-! ### `Gcl` at `log 2` -/

/-- `Σ_{j<12} 4^{−j}/(4j+1)`. -/
def Sq : ℚ := ∑ j ∈ Finset.range 12, 1 / ((4 : ℚ) ^ j * (4 * j + 1))

theorem Sq_gt : (1058435 / 1000000 : ℚ) < Sq := by unfold Sq; decide +kernel
theorem Sq_lt : Sq < (1058436 / 1000000 : ℚ) := by unfold Sq; decide +kernel

theorem upow (u : ℝ) (hu : u ^ 2 = 1 / 2) (j : ℕ) : u ^ (4 * j + 1) = u * (1 / 4) ^ j := by
  rw [pow_succ, pow_mul, show u ^ 4 = (1 / 4) by
    rw [show u ^ 4 = (u ^ 2) ^ 2 by ring, hu]; norm_num]
  ring

theorem partial_log_two (P : ℕ) :
    ∑ k ∈ Finset.range (2 * P), gterm (Real.sqrt 2 / 2) k =
      Real.sqrt 2 * ∑ j ∈ Finset.range P, 1 / ((4 : ℝ) ^ j * (4 * j + 1)) := by
  have hu2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  rw [partial_reindex, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [upow _ hu2, one_div_pow]
  have : (4 * (j : ℝ) + 1) ≠ 0 := by positivity
  field_simp

theorem Sq_cast : ((Sq : ℚ) : ℝ) = ∑ j ∈ Finset.range 12, 1 / ((4 : ℝ) ^ j * (4 * j + 1)) := by
  unfold Sq; push_cast; rfl

theorem Gcl_log_two_gt : (149684 / 100000 : ℝ) < Gcl (Real.log 2) := by
  have h := Gcl_ge_partial (show 0 < Real.log 2 from Real.log_pos (by norm_num)) 24
  rw [exp_neg_half_log_two, show (24 : ℕ) = 2 * 12 by norm_num, partial_log_two, ← Sq_cast] at h
  have hq : ((1058435 / 1000000 : ℚ) : ℝ) < (Sq : ℝ) := by exact_mod_cast Sq_gt
  push_cast at hq
  have := sqrt_two_gt
  nlinarith

theorem Gcl_log_two_lt : Gcl (Real.log 2) < 149687 / 100000 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := Gcl_le_partial_add_tail hl 24
  rw [exp_neg_half_log_two, show (24 : ℕ) = 2 * 12 by norm_num, partial_log_two, ← Sq_cast] at h
  have hu2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have htail : 2 * (Real.sqrt 2 / 2) ^ (2 * (2 * 12) + 1) / (1 - (Real.sqrt 2 / 2) ^ 2) <
      1 / 10 ^ 6 := by
    have e : (Real.sqrt 2 / 2) ^ (2 * (2 * 12) + 1) = (Real.sqrt 2 / 2) * (1 / 4) ^ 12 := by
      rw [show 2 * (2 * 12) + 1 = 4 * 12 + 1 by norm_num]; exact upow _ hu2 12
    rw [e, hu2]
    have := sqrt_two_lt
    have h12 : ((1 : ℝ) / 4) ^ 12 = 1 / 16777216 := by norm_num
    rw [h12]
    rw [div_lt_iff₀ (by norm_num)]
    nlinarith
  have hq : (Sq : ℝ) < ((1058436 / 1000000 : ℚ) : ℝ) := by exact_mod_cast Sq_lt
  push_cast at hq
  have := sqrt_two_lt
  have hs := Real.sqrt_nonneg 2
  nlinarith

/-! ### `∫₀^{log 2} Gcl` -/

theorem integral_term_gen (t : ℝ) (j : ℕ) :
    ∫ s in (0 : ℝ)..t, 2 * Real.exp (-s / 2) ^ (4 * j + 1) / (4 * j + 1) =
      4 * (1 - Real.exp (-t / 2) ^ (4 * j + 1)) / (4 * j + 1) ^ 2 := by
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
  have e2 : Real.exp (-((4 * (j : ℝ) + 1) / 2) * t) = Real.exp (-t / 2) ^ (4 * j + 1) := by
    rw [← Real.exp_nat_mul]
    push_cast
    congr 1; ring
  rw [e2]
  field_simp
  ring

theorem integral_Gcl_ge_series {t : ℝ} (ht : 0 < t) (P : ℕ) :
    ∑ j ∈ Finset.range P, 4 * (1 - Real.exp (-t / 2) ^ (4 * j + 1)) / (4 * j + 1) ^ 2 ≤
      ∫ s in (0 : ℝ)..t, Gcl s := by
  have hint : ∀ j ∈ Finset.range P, IntervalIntegrable
      (fun s : ℝ => 2 * Real.exp (-s / 2) ^ (4 * j + 1) / (4 * j + 1)) MeasureTheory.volume 0 t := by
    intro j _
    apply Continuous.intervalIntegrable
    fun_prop
  have hsum : IntervalIntegrable (fun s : ℝ => ∑ j ∈ Finset.range P,
      2 * Real.exp (-s / 2) ^ (4 * j + 1) / (4 * j + 1)) MeasureTheory.volume 0 t := by
    apply Continuous.intervalIntegrable
    exact continuous_finsetSum _ (fun j _ => by fun_prop)
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo ht.le hsum
    (intervalIntegrable_Gcl ht) (fun s hs => Gcl_ge_series hs.1 P)
  rw [intervalIntegral.integral_finsetSum hint] at hmono
  simpa only [integral_term_gen] using hmono

/-- `Σ_{j<40} 4 (1 − 0.70711·4^{−j})/(4j+1)²`. -/
def ILowQ2 : ℚ := ∑ j ∈ Finset.range 40, 4 * (1 - (70711 / 100000) * (1 / 4) ^ j) / (4 * j + 1) ^ 2

theorem ILowQ2_gt : (14338 / 10000 : ℚ) < ILowQ2 := by unfold ILowQ2; decide +kernel

theorem integral_Gcl_log_two_gt : (14338 / 10000 : ℝ) < ∫ s in (0 : ℝ)..Real.log 2, Gcl s := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := integral_Gcl_ge_series hl 40
  rw [exp_neg_half_log_two] at h
  have hu2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hu : Real.sqrt 2 / 2 < 70711 / 100000 := by
    have := sqrt_two_lt; linarith
  have hterm : ∀ j ∈ Finset.range 40,
      4 * (1 - (70711 / 100000 : ℝ) * (1 / 4) ^ j) / (4 * j + 1) ^ 2 ≤
        4 * (1 - (Real.sqrt 2 / 2) ^ (4 * j + 1)) / (4 * j + 1) ^ 2 := by
    intro j _
    rw [upow _ hu2]
    have hp : 0 ≤ ((1 : ℝ) / 4) ^ j := by positivity
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hq : ((14338 / 10000 : ℚ) : ℝ) < (ILowQ2 : ℝ) := by exact_mod_cast ILowQ2_gt
  have hq' : (ILowQ2 : ℝ) = ∑ j ∈ Finset.range 40,
      4 * (1 - (70711 / 100000 : ℝ) * (1 / 4) ^ j) / (4 * j + 1) ^ 2 := by
    unfold ILowQ2; push_cast; rfl
  push_cast at hq
  have := Finset.sum_le_sum hterm
  linarith

/-! ### The event certificate at `q = 2` and the continuation to `log 3` -/

/-- Rational archimedean constant. -/
def Clo : ℝ := -53726 / 10000

theorem slope_event_two_neg : vslope Clo (Real.log 2) + primeSlope 2 < 0 := by
  have h1 := Gcl_log_two_lt
  have h2 := sqrt_two_gt
  have h3 := sqrt_two_lt
  have h4 := Real.log_two_gt_d9
  have hs := Real.sqrt_nonneg 2
  unfold vslope Clo
  rw [sinh_half_log_two, primeSlope_two]
  norm_num at h4 ⊢
  nlinarith

theorem slope_event_two_gt : (-531 / 1000 : ℝ) < vslope Clo (Real.log 2) + primeSlope 2 := by
  have h1 := Gcl_log_two_gt
  have h2 := sqrt_two_gt
  have h3 := sqrt_two_lt
  have h4 := Real.log_two_lt_d9
  have hs := Real.sqrt_nonneg 2
  unfold vslope Clo
  rw [sinh_half_log_two, primeSlope_two]
  norm_num at h4 ⊢
  nlinarith

theorem Wn_event_two_pos : (11 / 100 : ℝ) < Wn Clo 2 (Real.log 2) := by
  have h1 := integral_Gcl_log_two_gt
  have h2 := sqrt_two_gt
  have h4 := Real.log_two_lt_d9
  have h5 := Real.log_two_gt_d9
  unfold Wn Vm Clo
  rw [primeAff_two_log_two, cosh_half_log_two]
  norm_num at h4 h5 ⊢
  nlinarith

theorem event_two_cert :
    (vslope Clo (Real.log 2) + primeSlope 2) ^ 2 < 2 * (2 * curv (Real.log 2)) * Wn Clo 2 (Real.log 2) := by
  have h1 := slope_event_two_neg
  have h2 := slope_event_two_gt
  have h3 := Wn_event_two_pos
  have h4 : (117 / 100 : ℝ) < curv (Real.log 2) := by
    rw [curv_log_two]; have := sqrt_two_gt; nlinarith
  nlinarith

/-- The frozen-floor prime part agrees with the true prime part on `[log n, log (n+1))`. -/
theorem primeBox_eq_primeAff {n : ℕ} {L : ℝ} (hn : 1 ≤ n) (h1 : Real.log n ≤ L)
    (h2 : L < Real.log (n + 1)) : primeBox L = primeAff n L := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hfl : ⌊Real.exp L⌋₊ = n := by
    rw [Nat.floor_eq_iff (Real.exp_pos L).le]
    constructor
    · calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hn0).symm
        _ ≤ Real.exp L := Real.exp_le_exp.mpr h1
    · calc Real.exp L < Real.exp (Real.log (n + 1)) := Real.exp_lt_exp.mpr h2
        _ = n + 1 := Real.exp_log (by positivity)
  simp [primeBox, primeAff, hfl]

/-- **The box form is positive on `[log 2, log 3)`.** -/
theorem box_pos_second_gap {L : ℝ} (h1 : Real.log 2 ≤ L) (h2 : L < Real.log 3) :
    0 < 16 * (Real.cosh (L / 2) - 1) + archBox L + primeBox L := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 < L := hl2.trans_le h1
  have hpb : primeBox L = primeAff 2 L :=
    primeBox_eq_primeAff (by norm_num) (by simpa using h1) (by norm_num; exact h2)
  have hpos : 0 < Wn Clo 2 L := by
    have hc : 0 < curv (Real.log 2) := by
      rw [curv_log_two]; have := sqrt_two_gt; nlinarith
    exact Wn_pos_on_gap (C := Clo) (n := 2) (a := Real.log 2) (b := L) hl2 h1 hc event_two_cert
      ⟨h1, le_rfl⟩
  rw [hpb, archBox_eq hL]
  have hC := Cinf_ge
  unfold Wn Vm Clo at hpos
  nlinarith

/-- **The box form is positive on the whole of `(0, log 3)`**: the first prime-free interval and the first
prime-power event `q = 2`. -/
theorem box_pos_to_log_three {L : ℝ} (hL : 0 < L) (h : L < Real.log 3) :
    0 < 16 * (Real.cosh (L / 2) - 1) + archBox L + primeBox L := by
  by_cases h2 : L ≤ Real.log 2
  · exact box_pos_first_interval hL h2
  · exact box_pos_second_gap (le_of_lt (not_le.mp h2)) h

end GppBoxEvent

#print axioms GppBoxEvent.box_pos_to_log_three
