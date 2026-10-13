import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# All-prime Hellinger threshold for prime occupation laws: β = 1 is the critical temperature

Source: Codex, private bridge `work/codex/2026-10-13_all_prime_kakutani_fisher_critical_temperature_boundary.md`
(GPP-bridge PR #11 comment, 2026-10-13).

The local prime occupation law at inverse temperature `β` is geometric:
`μ_{p,β}(n) = (1 − p^{−β}) p^{−βn}`. In the variables `s = p^{−β_a/2}` and `r = p^{−β_b/2}` this file
proves:
* `hasSum_affinity`: the one-prime Hellinger affinity `Σ_n √(μ_a(n) μ_b(n))` equals
  `u = √((1 − s²)(1 − r²)) / (1 − sr)`.
* `one_sub_affinity_sq`: `1 − u² = (s − r)² / (1 − sr)²`, exactly.
* `summable_defect_iff`: for `0 < a < b`,
  `Σ_p (1 − u_p²)` converges **iff `1 < a`**, i.e. iff `min(β_a, β_b) > 1`. The proof bounds
  `1 − u_p² ≍ p^{−a}` above and below and uses Mathlib's `Σ_p p^r < ∞ ⟺ r < −1`
  (Euler's divergence of `Σ 1/p`).
* `shifted_fake_defect_not_summable`: for the shifted fake `F_θ`, `β± = 1 ± 2θ` with
  `0 < θ < ½`, the defect series diverges.

By Kakutani's dichotomy, a convergent `Σ(1 − u_p)` (equivalent to convergent `Σ(1 − u_p²)`, since
`0 ≤ u_p ≤ 1`) is exactly the condition for the two infinite-product occupation measures to be
equivalent rather than mutually singular. **Kakutani's theorem itself is cited, not formalized
here**, and so are the Borel–Cantelli and Fisher-information readings. Thermodynamic
distinguishability is not Weil positivity, and nothing here constructs zeta zeros as Gibbs data.
**No RH claim.**
-/

namespace GppPrimeHellingerThreshold

open Real

/-- The one-prime Hellinger affinity in the square-root variables `s, r ∈ [0,1)`. -/
noncomputable def affinity (s r : ℝ) : ℝ := Real.sqrt ((1 - s ^ 2) * (1 - r ^ 2)) / (1 - s * r)

theorem sr_lt_one {s r : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (_hr0 : 0 ≤ r) (hr1 : r < 1) : s * r < 1 := by
  nlinarith

/-- **Exact one-prime affinity**: `Σ_n √(μ_a(n) μ_b(n)) = √((1−s²)(1−r²))/(1−sr)`. -/
theorem hasSum_affinity {s r : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => Real.sqrt ((1 - s ^ 2) * (s ^ 2) ^ n * ((1 - r ^ 2) * (r ^ 2) ^ n)))
      (affinity s r) := by
  have hsr0 : 0 ≤ s * r := mul_nonneg hs0 hr0
  have hg := (hasSum_geometric_of_lt_one hsr0 (sr_lt_one hs0 hs1 hr0 hr1)).mul_left
    (Real.sqrt ((1 - s ^ 2) * (1 - r ^ 2)))
  refine hg.congr_fun fun n => ?_
  have h1 : 0 ≤ (1 - s ^ 2) * (1 - r ^ 2) := by
    apply mul_nonneg <;> nlinarith
  have : (1 - s ^ 2) * (s ^ 2) ^ n * ((1 - r ^ 2) * (r ^ 2) ^ n) =
      ((1 - s ^ 2) * (1 - r ^ 2)) * ((s * r) ^ n) ^ 2 := by ring
  rw [this, Real.sqrt_mul h1, Real.sqrt_sq (pow_nonneg hsr0 n)]

/-- **Exact defect**: `1 − u² = (s − r)²/(1 − sr)²`. -/
theorem one_sub_affinity_sq {s r : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    1 - affinity s r ^ 2 = (s - r) ^ 2 / (1 - s * r) ^ 2 := by
  have hsr := sr_lt_one hs0 hs1 hr0 hr1
  have hd : (1 - s * r) ≠ 0 := by linarith
  have h1 : 0 ≤ (1 - s ^ 2) * (1 - r ^ 2) := by apply mul_nonneg <;> nlinarith
  unfold affinity
  rw [div_pow, Real.sq_sqrt h1]
  field_simp
  ring

theorem affinity_le_one {s r : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    affinity s r ≤ 1 := by
  have hd : 0 < (1 - s * r) := by linarith [sr_lt_one hs0 hs1 hr0 hr1]
  have h := one_sub_affinity_sq hs0 hs1 hr0 hr1
  have hnn : 0 ≤ affinity s r := by unfold affinity; positivity
  have : 0 ≤ 1 - affinity s r ^ 2 := by rw [h]; positivity
  nlinarith

/-- The square-root variable `p^{−β/2}`. -/
noncomputable def sv (β : ℝ) (p : Nat.Primes) : ℝ := ((p : ℕ) : ℝ) ^ (-(β / 2))

theorem two_le (p : Nat.Primes) : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le

theorem sv_nonneg (β : ℝ) (p : Nat.Primes) : 0 ≤ sv β p := by unfold sv; positivity

theorem sv_le_two {β : ℝ} (hβ : 0 < β) (p : Nat.Primes) : sv β p ≤ (2 : ℝ) ^ (-(β / 2)) :=
  Real.rpow_le_rpow_of_nonpos (by norm_num) (two_le p) (by linarith)

theorem two_rpow_lt_one {c : ℝ} (hc : 0 < c) : (2 : ℝ) ^ (-c) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

theorem sv_lt_one {β : ℝ} (hβ : 0 < β) (p : Nat.Primes) : sv β p < 1 :=
  (sv_le_two hβ p).trans_lt (two_rpow_lt_one (by linarith))

theorem sv_sq (β : ℝ) (p : Nat.Primes) : sv β p ^ 2 = ((p : ℕ) : ℝ) ^ (-β) := by
  unfold sv
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1; push_cast; ring

theorem sv_split (a b : ℝ) (p : Nat.Primes) :
    sv b p = sv a p * ((p : ℕ) : ℝ) ^ (-((b - a) / 2)) := by
  unfold sv
  rw [← Real.rpow_add (by linarith [two_le p])]
  congr 1; ring

/-- The all-prime defect `1 − u_p²` between inverse temperatures `a` and `b`. -/
noncomputable def defect (a b : ℝ) (p : Nat.Primes) : ℝ := 1 - affinity (sv a p) (sv b p) ^ 2

/-- **The critical temperature**: for `0 < a < b`, `Σ_p (1 − u_p²) < ∞ ⟺ 1 < a`. -/
theorem summable_defect_iff {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Summable (defect a b) ↔ 1 < a := by
  have hb : 0 < b := ha.trans hab
  set c := (2 : ℝ) ^ (-(a / 2)) with hc
  set d := 1 - (2 : ℝ) ^ (-((b - a) / 2)) with hd
  have hc1 : c < 1 := two_rpow_lt_one (by linarith)
  have hd0 : 0 < d := by rw [hd]; linarith [two_rpow_lt_one (c := (b - a) / 2) (by linarith)]
  have hfac : ∀ p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-((b - a) / 2)) ≤ 1 - d := by
    intro p; rw [hd, sub_sub_cancel]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) (two_le p) (by linarith)
  have hform : ∀ p, defect a b p = (sv a p - sv b p) ^ 2 / (1 - sv a p * sv b p) ^ 2 := fun p =>
    one_sub_affinity_sq (sv_nonneg a p) (sv_lt_one ha p) (sv_nonneg b p) (sv_lt_one hb p)
  have hpow : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-a)) ↔ 1 < a := by
    rw [Nat.Primes.summable_rpow]; constructor <;> intro h <;> linarith
  rw [← hpow]
  constructor
  · intro hs
    -- lower bound: defect ≥ d² p^{−a}
    refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) (hs.div_const (d ^ 2))
    have hsa := sv_nonneg a p
    have hlo : d * sv a p ≤ sv a p - sv b p := by
      rw [sv_split a b p]
      have := hfac p
      nlinarith
    have hden : 0 < (1 - sv a p * sv b p) ^ 2 := by
      have := sr_lt_one hsa (sv_lt_one ha p) (sv_nonneg b p) (sv_lt_one hb p); positivity
    have hden1 : (1 - sv a p * sv b p) ^ 2 ≤ 1 := by
      have h0 := mul_nonneg hsa (sv_nonneg b p)
      have := sr_lt_one hsa (sv_lt_one ha p) (sv_nonneg b p) (sv_lt_one hb p)
      nlinarith
    rw [le_div_iff₀ (by positivity), hform p, ← sv_sq]
    have hsq : (d * sv a p) ^ 2 ≤ (sv a p - sv b p) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlo 2
    have : (sv a p - sv b p) ^ 2 / (1 - sv a p * sv b p) ^ 2 ≥ (sv a p - sv b p) ^ 2 := by
      rw [ge_iff_le, le_div_iff₀ hden]; nlinarith [sq_nonneg (sv a p - sv b p)]
    nlinarith
  · intro hs
    -- upper bound: defect ≤ p^{−a}/(1−c)²
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) (hs.div_const ((1 - c) ^ 2))
    · rw [hform p]; positivity
    · have hsa := sv_nonneg a p
      have hsb := sv_nonneg b p
      have hba : sv b p ≤ sv a p := by
        rw [sv_split a b p]
        have := hfac p
        nlinarith
      have hsac : sv a p ≤ c := sv_le_two ha p
      have hsb1 := sv_lt_one hb p
      have hden : (1 - c) ^ 2 ≤ (1 - sv a p * sv b p) ^ 2 := by
        have h1 : sv a p * sv b p ≤ c := by nlinarith
        have h2 : 0 ≤ 1 - c := by linarith
        exact pow_le_pow_left₀ h2 (by linarith) 2
      have hpos : 0 < (1 - sv a p * sv b p) ^ 2 := by
        have : 0 < 1 - sv a p * sv b p := by linarith [sr_lt_one hsa (sv_lt_one ha p) hsb hsb1]
        positivity
      have hc2 : 0 < (1 - c) ^ 2 := by
        have : 0 < 1 - c := by linarith
        positivity
      rw [hform p, ← sv_sq, div_le_div_iff₀ hpos hc2]
      have hnum : (sv a p - sv b p) ^ 2 ≤ sv a p ^ 2 := by nlinarith
      exact mul_le_mul hnum hden (by positivity) (by positivity)

/-- **The shifted fake is singular**: for `β± = 1 ± 2θ`, `0 < θ < ½`, the defect series diverges. -/
theorem shifted_fake_defect_not_summable {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1 / 2) :
    ¬ Summable (defect (1 - 2 * θ) (1 + 2 * θ)) := by
  rw [summable_defect_iff (by linarith) (by linarith)]; linarith

end GppPrimeHellingerThreshold
