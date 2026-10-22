import Mathlib.NumberTheory.Chebyshev
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Uniform variation of the normalized Chebyshev function on logarithmic blocks

Source: Codex, `work/codex/2026-10-21_arithmetic_logblock_BV_ultraviolet_tail_alltime.md` §1
(GPP-bridge), audited independently by Grok (`work/grok/2026-10-22_s79_codex_audit.md` §1). Daniel
Toupin / Golden Physics Project, with AI assistance from Codex (statement and proof sketch) and
Claude Code (formalization).

Let `φ(t) = e^{-t} ψ(eᵗ)`; Codex's `q(t) = φ(t) − 1` has the same variation.

* `eVariationOn_phi_le`: if `ψ(x) ≤ K x` for every `x ≥ 1`, then for `0 ≤ a ≤ b`,
  `Var_{[a,b]} φ ≤ K (2(b − a) + 1)`.
* `eVariationOn_phi_unit_le`: on a unit block, `Var_{[a,a+1]} φ ≤ 3K` (Codex's statement).
* `eVariationOn_phi_unit_le_chebyshev`: the same with Mathlib's constant `K = log 4 + 4`, so
  unconditionally `Var_{[a,a+1]} φ ≤ 3(log 4 + 4)`.

**Proof.** On `[a, b]` write `φ = g − k` with `g(t) = ∑_{eᵃ < n ≤ eᵗ} Λ(n)/n` (the jumps,
nondecreasing) and `k = g − φ`, which is also nondecreasing (`cont_monotoneOn`, a termwise check).
So `Var φ ≤ (g(b) − g(a)) + (k(b) − k(a))`. The Abel identity in logarithmic time,
`k(b) − k(a) = ∫_a^b φ` (`cont_sub_eq`), together with `g = k + φ`, gives
`Var φ ≤ 2∫_a^b φ + φ(b) − φ(a) ≤ 2K(b − a) + K`.

**Scope.** The other sections of the note, the BV Fourier-tail bound `|ĝ_a(n)| ≤ V/(2π²n²)` and the
all-time ultraviolet budget, are not formalized here. As the note says, this is a regularity input
built from Chebyshev's bound alone, so it holds equally for Beurling-type prime systems that have
off-line zeros. It carries no RH content.
-/

open Real MeasureTheory Set Finset
open scoped ArithmeticFunction.vonMangoldt Chebyshev

namespace GppLogBlockVariation

/-- `φ(t) = e^{-t} ψ(e^t)`, the normalized Chebyshev function in logarithmic time. -/
noncomputable def phi (t : ℝ) : ℝ := Real.exp (-t) * ψ (Real.exp t)

/-- `ind n t = 1` if `n ≤ eᵗ`, else `0`. -/
noncomputable def ind (n : ℕ) (t : ℝ) : ℝ := if (n : ℝ) ≤ Real.exp t then 1 else 0

lemma ind_nonneg (n : ℕ) (t : ℝ) : 0 ≤ ind n t := by unfold ind; split_ifs <;> norm_num

lemma ind_mono {n : ℕ} {s t : ℝ} (hst : s ≤ t) : ind n s ≤ ind n t := by
  unfold ind
  split_ifs with h1 h2 h2 <;> try norm_num
  exact h2 (h1.trans (Real.exp_le_exp.mpr hst))

/-- On `t ≤ b`, `ψ(eᵗ)` is a finite sum over `n ≤ N = ⌊e^b⌋`. -/
lemma psi_exp_eq_sum {b t : ℝ} (htb : t ≤ b) :
    ψ (Real.exp t) = ∑ n ∈ range (⌊Real.exp b⌋₊ + 1), Λ n * ind n t := by
  rw [Chebyshev.psi_eq_sum_Icc]
  simp only [ind, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n
  simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range, zero_le, true_and]
  rw [Nat.le_floor_iff (Real.exp_pos t).le]
  constructor
  · intro h
    refine ⟨?_, h⟩
    have : n ≤ ⌊Real.exp b⌋₊ :=
      (Nat.le_floor_iff (Real.exp_pos b).le).mpr (h.trans (Real.exp_le_exp.mpr htb))
    omega
  · exact fun h => h.2

/-- Coefficient of the jump part: `1/n` for `n > eᵃ`, else `0`. -/
noncomputable def coef (a : ℝ) (n : ℕ) : ℝ := if Real.exp a < n then 1 / n else 0

/-- `g(t) = ∑_{eᵃ < n ≤ eᵗ} Λ(n)/n` (summed over `n ≤ ⌊e^b⌋`), the jump part of `φ`. -/
noncomputable def jump (a b t : ℝ) : ℝ :=
  ∑ n ∈ range (⌊Real.exp b⌋₊ + 1), Λ n * coef a n * ind n t

/-- `k = g − φ` (`cont_eq`): the negative of the continuous, decreasing part of `φ`. -/
noncomputable def cont (a b t : ℝ) : ℝ :=
  ∑ n ∈ range (⌊Real.exp b⌋₊ + 1), Λ n * ((coef a n - Real.exp (-t)) * ind n t)

lemma cont_eq {a b t : ℝ} (htb : t ≤ b) : cont a b t = jump a b t - phi t := by
  rw [cont, jump, phi, psi_exp_eq_sum htb, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

lemma jump_monotoneOn (a b : ℝ) : MonotoneOn (jump a b) (Icc a b) := by
  intro s _ t _ hst
  refine Finset.sum_le_sum fun n _ => ?_
  have hc : 0 ≤ coef a n := by unfold coef; split_ifs <;> positivity
  exact mul_le_mul_of_nonneg_left (ind_mono hst)
    (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hc)

lemma cont_monotoneOn (a b : ℝ) : MonotoneOn (cont a b) (Icc a b) := by
  intro s hs t _ hst
  refine Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left ?_
    ArithmeticFunction.vonMangoldt_nonneg
  have het : Real.exp (-t) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
  unfold ind
  by_cases h1 : (n : ℝ) ≤ Real.exp s
  · have h2 : (n : ℝ) ≤ Real.exp t := h1.trans (Real.exp_le_exp.mpr hst)
    rw [if_pos h1, if_pos h2]; linarith
  · rw [if_neg h1, mul_zero]
    by_cases h2 : (n : ℝ) ≤ Real.exp t
    · rw [if_pos h2, mul_one]
      have hsn : Real.exp a < n := lt_of_le_of_lt (Real.exp_le_exp.mpr hs.1) (not_le.mp h1)
      have hn0 : (0 : ℝ) < n := lt_trans (Real.exp_pos a) hsn
      unfold coef
      rw [if_pos hsn, Real.exp_neg]
      have : 1 / Real.exp t ≤ 1 / (n : ℝ) := one_div_le_one_div_of_le hn0 h2
      rw [one_div] at this; linarith
    · rw [if_neg h2, mul_zero]

/-- Variation of a difference is at most the sum of the variations. -/
lemma eVariationOn_sub_le (f g : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => f x - g x) s ≤ eVariationOn f s + eVariationOn g s := by
  refine iSup_le fun p => ?_
  calc ∑ i ∈ range p.1, edist (f (p.2.1 (i + 1)) - g (p.2.1 (i + 1))) (f (p.2.1 i) - g (p.2.1 i))
      ≤ ∑ i ∈ range p.1, (edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) +
          edist (g (p.2.1 (i + 1))) (g (p.2.1 i))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [edist_dist, edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.dist_eq, Real.dist_eq, Real.dist_eq]
        calc |f (p.2.1 (i + 1)) - g (p.2.1 (i + 1)) - (f (p.2.1 i) - g (p.2.1 i))|
            = |(f (p.2.1 (i + 1)) - f (p.2.1 i)) - (g (p.2.1 (i + 1)) - g (p.2.1 i))| := by
              ring_nf
          _ ≤ _ := abs_sub _ _
    _ = ∑ i ∈ range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) +
          ∑ i ∈ range p.1, edist (g (p.2.1 (i + 1))) (g (p.2.1 i)) := Finset.sum_add_distrib
    _ ≤ eVariationOn f s + eVariationOn g s :=
        add_le_add (eVariationOn.sum_le (f := f) (n := p.1) p.2.2.1 p.2.2.2)
          (eVariationOn.sum_le (f := g) (n := p.1) p.2.2.1 p.2.2.2)

lemma intervalIntegrable_term (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t => Real.exp (-t) * ind n t) volume a b := by
  refine IntervalIntegrable.mono_fun
    ((Real.continuous_exp.comp continuous_neg).intervalIntegrable a b) ?_ ?_
  · exact ((Real.continuous_exp.comp continuous_neg).measurable.mul
      (Measurable.ite (measurableSet_le measurable_const Real.continuous_exp.measurable)
        measurable_const measurable_const)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t => ?_
    simp only [Function.comp, Real.norm_eq_abs, abs_mul, abs_of_nonneg (ind_nonneg n t)]
    unfold ind; split_ifs <;> simp [(Real.exp_pos _).le]

lemma integral_exp_neg (a b : ℝ) :
    ∫ t in a..b, Real.exp (-t) = Real.exp (-a) - Real.exp (-b) := by
  rw [intervalIntegral.integral_comp_neg (fun t => Real.exp t), integral_exp]

/-- The per-term Abel identity: `∫_a^b e^{-t}·1[n ≤ eᵗ] dt` is the increment over `[a, b]` of the
`n`-th term of `cont`. -/
lemma integral_term {a b : ℝ} (hab : a ≤ b) {n : ℕ} (hn : 0 < n) :
    ∫ t in a..b, Real.exp (-t) * ind n t =
      (coef a n - Real.exp (-b)) * ind n b - (coef a n - Real.exp (-a)) * ind n a := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : ∀ t, ((n : ℝ) ≤ Real.exp t ↔ Real.log n ≤ t) := fun t => by
    rw [← Real.log_le_log_iff hn' (Real.exp_pos t), Real.log_exp]
  by_cases h1 : (n : ℝ) ≤ Real.exp a
  · have h2 : (n : ℝ) ≤ Real.exp b := h1.trans (Real.exp_le_exp.mpr hab)
    have hc : coef a n = 0 := by unfold coef; rw [if_neg (not_lt.mpr h1)]
    have : ∫ t in a..b, Real.exp (-t) * ind n t = ∫ t in a..b, Real.exp (-t) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hab] at ht
      simp only [ind, if_pos (h1.trans (Real.exp_le_exp.mpr ht.1)), mul_one]
    rw [this, integral_exp_neg, hc]
    simp only [ind, if_pos h1, if_pos h2]; ring
  · by_cases h2 : (n : ℝ) ≤ Real.exp b
    · have hc : coef a n = 1 / n := by unfold coef; rw [if_pos (not_le.mp h1)]
      have hla : a ≤ Real.log n := ((hlog a).not.mp h1 |> not_le.mp).le
      have hlb : Real.log n ≤ b := (hlog b).mp h2
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := Real.log n)
        (intervalIntegrable_term n _ _) (intervalIntegrable_term n _ _)]
      have hzero : ∫ t in a..Real.log n, Real.exp (-t) * ind n t = 0 := by
        rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ))]
        · simp
        · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton (Real.log n))]
            with t ht hmem
          rw [uIoc_of_le hla] at hmem
          have htl : t < Real.log n := lt_of_le_of_ne hmem.2 (by simpa using ht)
          simp only [ind, if_neg (fun h => absurd ((hlog t).mp h) (not_le.mpr htl)), mul_zero]
      have hone : ∫ t in Real.log n..b, Real.exp (-t) * ind n t = ∫ t in Real.log n..b,
          Real.exp (-t) := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le hlb] at ht
        simp only [ind, if_pos ((hlog t).mpr ht.1), mul_one]
      rw [hzero, hone, integral_exp_neg, zero_add, hc, Real.exp_neg (Real.log n),
        Real.exp_log hn']
      simp only [ind, if_neg h1, if_pos h2]; ring
    · have : ∫ t in a..b, Real.exp (-t) * ind n t = ∫ t in a..b, (0 : ℝ) := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le hab] at ht
        have : ¬ (n : ℝ) ≤ Real.exp t := fun h => h2 (h.trans (Real.exp_le_exp.mpr ht.2))
        simp only [ind, if_neg this, mul_zero]
      rw [this]
      simp only [ind, if_neg h1, if_neg h2]; simp

/-- The finite-sum form of `φ` used for integration. -/
noncomputable def phiSum (b t : ℝ) : ℝ :=
  ∑ n ∈ range (⌊Real.exp b⌋₊ + 1), Λ n * (Real.exp (-t) * ind n t)

lemma phiSum_eq {b t : ℝ} (htb : t ≤ b) : phiSum b t = phi t := by
  rw [phiSum, phi, psi_exp_eq_sum htb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- **Abel identity in logarithmic time.** The decrease of the continuous part of `φ` over `[a, b]`
is `∫_a^b φ`. -/
lemma cont_sub_eq {a b : ℝ} (hab : a ≤ b) :
    cont a b b - cont a b a = ∫ t in a..b, phiSum b t := by
  unfold phiSum
  rw [intervalIntegral.integral_finsetSum fun n _ =>
    (intervalIntegrable_term n a b).const_mul _, cont, cont, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [intervalIntegral.integral_const_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [integral_term hab hn]; ring

lemma phi_nonneg (t : ℝ) : 0 ≤ phi t :=
  mul_nonneg (Real.exp_pos _).le (Chebyshev.psi_nonneg _)

lemma phi_le {K : ℝ} (hK : ∀ x : ℝ, 1 ≤ x → ψ x ≤ K * x) {t : ℝ} (ht : 0 ≤ t) : phi t ≤ K := by
  have h := hK (Real.exp t) (Real.one_le_exp ht)
  rw [phi]
  calc Real.exp (-t) * ψ (Real.exp t) ≤ Real.exp (-t) * (K * Real.exp t) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = K := by rw [mul_left_comm, ← Real.exp_add]; simp

/-- **Uniform variation bound in logarithmic time.** If `ψ(x) ≤ K x` for all `x ≥ 1`, then for
`0 ≤ a ≤ b` the total variation of `φ(t) = e^{-t} ψ(eᵗ)` on `[a, b]` is at most `K (2(b − a) + 1)`.
On a unit block this is `3K`. -/
theorem eVariationOn_phi_le {K : ℝ} (hK : ∀ x : ℝ, 1 ≤ x → ψ x ≤ K * x) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    eVariationOn phi (Icc a b) ≤ ENNReal.ofReal (K * (2 * (b - a) + 1)) := by
  have hEq : Set.EqOn phi (fun t => jump a b t - cont a b t) (Icc a b) := fun t ht => by
    simp only; rw [cont_eq ht.2]; ring
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hJ := (jump_monotoneOn a b).eVariationOn_eq haI hbI |>.le
  have hC := (cont_monotoneOn a b).eVariationOn_eq haI hbI |>.le
  rw [Set.inter_self] at hJ hC
  have hJ0 : 0 ≤ jump a b b - jump a b a := sub_nonneg.mpr (jump_monotoneOn a b haI hbI hab)
  have hC0 : 0 ≤ cont a b b - cont a b a := sub_nonneg.mpr (cont_monotoneOn a b haI hbI hab)
  -- the integral of `φ` over `[a, b]` is at most `K (b - a)`
  have hint : ∫ t in a..b, phiSum b t ≤ K * (b - a) := by
    have hI : IntervalIntegrable (phiSum b) volume a b := by
      have h := IntervalIntegrable.sum (range (⌊Real.exp b⌋₊ + 1)) fun n _ =>
        (intervalIntegrable_term n a b).const_mul (Λ n)
      have hfun : phiSum b = ∑ n ∈ range (⌊Real.exp b⌋₊ + 1),
          fun t => Λ n * (Real.exp (-t) * ind n t) := by
        funext t; simp [phiSum, Finset.sum_apply]
      rw [hfun]; exact h
    have := intervalIntegral.integral_mono_on hab hI intervalIntegrable_const
      (fun t ht => (phiSum_eq ht.2).trans_le (phi_le hK (ha.trans ht.1)))
    simpa [mul_comm] using this
  have hjump : jump a b b - jump a b a =
      (cont a b b - cont a b a) + (phi b - phi a) := by
    rw [cont_eq le_rfl, cont_eq hab]; ring
  calc eVariationOn phi (Icc a b)
      = eVariationOn (fun t => jump a b t - cont a b t) (Icc a b) := eVariationOn.eq_of_eqOn hEq
    _ ≤ eVariationOn (jump a b) (Icc a b) + eVariationOn (cont a b) (Icc a b) :=
        eVariationOn_sub_le _ _ _
    _ ≤ ENNReal.ofReal (jump a b b - jump a b a) + ENNReal.ofReal (cont a b b - cont a b a) :=
        add_le_add hJ hC
    _ = ENNReal.ofReal ((jump a b b - jump a b a) + (cont a b b - cont a b a)) :=
        (ENNReal.ofReal_add hJ0 hC0).symm
    _ ≤ ENNReal.ofReal (K * (2 * (b - a) + 1)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hjump, cont_sub_eq hab]
        have h1 := phi_le hK (ha.trans hab)
        have h2 := phi_nonneg a
        nlinarith

/-- **The unit-block bound `Var_{[a,a+1]} φ ≤ 3K`** (Codex, 2026-10-21). -/
theorem eVariationOn_phi_unit_le {K : ℝ} (hK : ∀ x : ℝ, 1 ≤ x → ψ x ≤ K * x) {a : ℝ}
    (ha : 0 ≤ a) : eVariationOn phi (Icc a (a + 1)) ≤ ENNReal.ofReal (3 * K) := by
  have := eVariationOn_phi_le hK ha (by linarith : a ≤ a + 1)
  rwa [show K * (2 * (a + 1 - a) + 1) = 3 * K by ring] at this

/-- **Unconditional form**, with Mathlib's Chebyshev constant `K = log 4 + 4`. -/
theorem eVariationOn_phi_unit_le_chebyshev {a : ℝ} (ha : 0 ≤ a) :
    eVariationOn phi (Icc a (a + 1)) ≤ ENNReal.ofReal (3 * (Real.log 4 + 4)) :=
  eVariationOn_phi_unit_le (fun x hx => by
    rw [mul_comm]; exact (Chebyshev.psi_le_const_mul_self (by linarith)).trans (by
      rw [mul_comm])) ha

end GppLogBlockVariation
