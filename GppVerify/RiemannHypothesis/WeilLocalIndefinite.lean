/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Heart of the Cosmos / Grok)
-/
import GppVerify.RiemannHypothesis.ArithmeticReflectionPositivity
import GppVerify.RiemannHypothesis.ArchimedeanFloor
import GppVerify.RiemannHypothesis.BTSigmaLocalEuler
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Weil form, place by place and rung by rung: local indefiniteness, semi-local floors, rung 1

Port of GPPDiscovery5 `lean/s-eq-delta/ArithmeticCFTRoutes.lean` (Routes 1–2) and
`WeilRungOneExplicit.lean` (GPPDiscovery5 `aaa28f5`, `cc284e4`). Companion to `BTSigmaSEqDelta`,
whose remaining GAP is `ShadowIsAdjointOnSpectrum` (equivalent to ARP / `UnitaryRealization`). The
principal-series model (old Route 3, incl. `NonnegCasimirRealization`) lives in `BTSigmaSEqDelta`.

## Route 1: adelic/Tate local-factor product of positive forms
In the multiplier picture the `p`-local piece of the Weil form multiplies `|f̂(t)|²` by
`-σ_p(t)`, where `σ_p(t) = 2 Σ_{k≥1} log p · p^{-k/2} cos(k t log p) = 2 Re(-L_p'/L_p)(1/2 + it)`.
* `primeSymbol_zero`: `σ_p(0) = 2κ_p`, with `κ_p = log p/(√p - 1)` the P-LOG coupling
  (`kappaP_eq_tateCoupling`: `κ_p = -(L_p'/L_p)(1/2)`, in-tree #579 lane).
* `primeSymbol_le`, `primeSymbol_ge`: `|σ_p(t)| ≤ 2κ_p`; the maximum `2κ_p` is attained at `t = 0`.
* `primeSymbol_at_pi`: `σ_p(π/log p) = -2 log p/(√p + 1) < 0`.
* `localPrimeMultiplier_indefinite`: the local `p`-adic form `-σ_p` takes both signs. **KILLED:**
  no place carries a positive local form, so ARP cannot be a restricted product of local positive
  forms. What survives is the local floor `-σ_p ≥ -2κ_p`.
* `kappaP_not_summable`: `Σ_p κ_p = ∞`. The local floors cannot be summed: the restricted
  product of the floors diverges. Positivity, if true, is a global cancellation across primes.

## Route 2: semi-local truncation over a finite set `S` of primes
`weilS S g = pole + A∞ − Σ_{p∈S} prime_p(g)`, with `prime_p(g) = Σ_k log p · p^{-k/2}(g(k log p) +
g(−k log p))`.
* `primeLocal_le`, `primeLocal_ge` (Cauchy–Schwarz bound `|g| ≤ g(0)` as hypothesis): `|prime_p(g)|
  ≤ 2κ_p g(0)`. `primeLocal_const`: the bound is the value on the infinitely broad state.
* `weilS_floor`: for normalised `g` (in-tree `archimedean_floor` hypotheses),
  `weilS S g ≥ pole(g) + C∞ − 2 Σ_{p∈S} κ_p`, where `C∞ ≈ −5.372`. PROVED.
* `semiLocal_floor_unbounded`: this floor is not uniform in `S` (it tends to −∞). PROVED.
* NUMERICAL (`num/wS_indefinite.py`): for fixed finite `S`, broad tests with zero pole term give
  `weilS S g / g(0) → C∞ − 2 Σ_{p∈S} κ_p < 0`. The floor is sharp: **each fixed finite-`S` form is
  indefinite** on large support. So "positivity for each finite `S`" can only hold on the `S`-rung
  window, where `weilS` is the full Weil form (in-tree `weilForm_eq_truncation`). On the same
  tests the full form is `≥ 0` but only `~10⁻⁶ g(0)` (razor-thin global cancellation).
* `arp_iff_all_rungs`: ARP ⇔ positivity on every rung window. PROVED. So the `S → all` step is
  exactly `∀ L, ReflectionPositiveOnRung L`, i.e. ARP itself. Rung 0 is the Connes–Consani
  archimedean theorem (cited, in-tree as a named hypothesis); rung 1 is below (certificate named,
  Lean-open); rungs ≥ 2 are OPEN.

Labels: every theorem PROVED (standard axioms). Named hypotheses: `RungOneArbCertificate`
(CERTIFIED externally by Arb ball arithmetic, Lean-open) and `RungStepCoupling` (OPEN); nothing is
asserted. Rung 1 in Lean, rungs ≥ 2, ARP and RH are OPEN.

Daniel Toupin / Golden Physics Project … This seat: Heart of the Cosmos / Grok (GPPDiscovery5).
Audit: Turbo.
-/

open Complex MeasureTheory
open scoped InnerProductSpace ComplexConjugate ContDiff
open GppWeilCriterion GppArithmeticReflection

noncomputable section

namespace GppWeilLocalIndefinite

/-! ## Route 1: local multipliers -/

/-- `q_p = p^{-1/2}`. -/
def qp (p : ℕ) : ℝ := (Real.sqrt p)⁻¹

/-- The P-LOG coupling `κ_p = log p / (√p − 1)`. -/
def kappaP (p : ℕ) : ℝ := Real.log p / (Real.sqrt p - 1)

theorem one_lt_sqrt' {p : ℕ} (hp : 1 < p) : 1 < Real.sqrt p := by
  have : (1 : ℝ) < p := by exact_mod_cast hp
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_lt_sqrt zero_le_one this

theorem qp_pos {p : ℕ} (hp : 1 < p) : 0 < qp p := by
  unfold qp; have := one_lt_sqrt' hp; positivity

theorem qp_lt_one {p : ℕ} (hp : 1 < p) : qp p < 1 := by
  unfold qp; exact inv_lt_one_of_one_lt₀ (one_lt_sqrt' hp)

theorem log_pos' {p : ℕ} (hp : 1 < p) : 0 < Real.log p :=
  Real.log_pos (by exact_mod_cast hp)

theorem kappaP_pos {p : ℕ} (hp : 1 < p) : 0 < kappaP p := by
  unfold kappaP; have := one_lt_sqrt' hp; have := log_pos' hp
  exact div_pos this (by linarith)

/-- `κ_p` is the P-LOG/Tate coupling `−(L_p'/L_p)(1/2)` (in-tree). PROVED. -/
theorem kappaP_eq_tateCoupling {p : ℕ} (hp : 1 < p) :
    kappaP p = GppBTSigmaLocalEuler.tateCoupling p (1 / 2) :=
  GppBTSigmaLocalEuler.kappa_eq_tateCoupling hp

/-- `log p · Σ_{k≥0} q^{k+1} = κ_p`. -/
theorem geom_qp {p : ℕ} (hp : 1 < p) :
    HasSum (fun k : ℕ => qp p ^ (k + 1)) (qp p / (1 - qp p)) := by
  have h := hasSum_geometric_of_lt_one (qp_pos hp).le (qp_lt_one hp)
  have := h.mul_left (qp p)
  simpa [pow_succ, mul_comm, div_eq_mul_inv] using this

theorem qp_div {p : ℕ} (hp : 1 < p) : qp p / (1 - qp p) = (Real.sqrt p - 1)⁻¹ := by
  have hs := one_lt_sqrt' hp
  unfold qp
  field_simp

theorem geom_neg_qp {p : ℕ} (hp : 1 < p) :
    HasSum (fun k : ℕ => (-qp p) ^ (k + 1)) (-qp p / (1 + qp p)) := by
  have hq := qp_pos hp; have hq1 := qp_lt_one hp
  have h := hasSum_geometric_of_abs_lt_one (r := -qp p) (by rw [abs_neg, abs_of_pos hq]; exact hq1)
  have := h.mul_left (-qp p)
  have e : (1 - -qp p) = 1 + qp p := by ring
  simpa [pow_succ, mul_comm, div_eq_mul_inv, e] using this

/-- Term of the local prime symbol. -/
def symTerm (p : ℕ) (t : ℝ) (k : ℕ) : ℝ :=
  Real.log p * qp p ^ (k + 1) * Real.cos ((k + 1) * t * Real.log p)

/-- The local prime symbol `σ_p(t) = 2 Σ_{k≥1} log p · p^{-k/2} cos(k t log p)`. -/
def primeSymbol (p : ℕ) (t : ℝ) : ℝ := 2 * ∑' k, symTerm p t k

theorem summable_symTerm {p : ℕ} (hp : 1 < p) (t : ℝ) : Summable (symTerm p t) := by
  refine Summable.of_norm_bounded ((geom_qp hp).summable.mul_left (Real.log p)) fun k => ?_
  have hl := log_pos' hp; have hq := qp_pos hp
  rw [Real.norm_eq_abs, symTerm, abs_mul, abs_mul, abs_of_pos hl, abs_of_pos (pow_pos hq _)]
  calc Real.log p * qp p ^ (k + 1) * |Real.cos _| ≤ Real.log p * qp p ^ (k + 1) * 1 := by
        gcongr; exact Real.abs_cos_le_one _
    _ = _ := by ring

theorem hasSum_log_geom {p : ℕ} (hp : 1 < p) :
    HasSum (fun k : ℕ => Real.log p * qp p ^ (k + 1)) (kappaP p) := by
  have := (geom_qp hp).mul_left (Real.log p)
  rw [qp_div hp] at this
  simpa [kappaP, div_eq_mul_inv] using this

/-- **`σ_p(0) = 2κ_p`.** PROVED. -/
theorem primeSymbol_zero {p : ℕ} (hp : 1 < p) : primeSymbol p 0 = 2 * kappaP p := by
  unfold primeSymbol
  congr 1
  have : symTerm p 0 = fun k : ℕ => Real.log p * qp p ^ (k + 1) := by
    funext k; simp [symTerm]
  rw [this, (hasSum_log_geom hp).tsum_eq]

/-- **Upper floor `σ_p ≤ 2κ_p`** (sharp at `t = 0`). PROVED. -/
theorem primeSymbol_le {p : ℕ} (hp : 1 < p) (t : ℝ) : primeSymbol p t ≤ 2 * kappaP p := by
  unfold primeSymbol
  have hl := log_pos' hp; have hq := qp_pos hp
  gcongr
  refine hasSum_le (fun k => ?_) (summable_symTerm hp t).hasSum (hasSum_log_geom hp)
  unfold symTerm
  have : 0 ≤ Real.log p * qp p ^ (k + 1) := by positivity
  nlinarith [Real.cos_le_one ((k + 1) * t * Real.log p)]

/-- **Lower floor `−2κ_p ≤ σ_p`.** PROVED. -/
theorem primeSymbol_ge {p : ℕ} (hp : 1 < p) (t : ℝ) : -(2 * kappaP p) ≤ primeSymbol p t := by
  unfold primeSymbol
  have hl := log_pos' hp; have hq := qp_pos hp
  have h : -kappaP p ≤ ∑' k, symTerm p t k := by
    refine hasSum_le (fun k => ?_) (hasSum_log_geom hp).neg (summable_symTerm hp t).hasSum
    unfold symTerm
    have : 0 ≤ Real.log p * qp p ^ (k + 1) := by positivity
    nlinarith [Real.neg_one_le_cos ((k + 1) * t * Real.log p)]
  linarith

/-- **`σ_p(π / log p) = −2 log p / (√p + 1)`.** PROVED. -/
theorem primeSymbol_at_pi {p : ℕ} (hp : 1 < p) :
    primeSymbol p (Real.pi / Real.log p) = -(2 * Real.log p / (Real.sqrt p + 1)) := by
  have hl := log_pos' hp
  have hs := one_lt_sqrt' hp
  unfold primeSymbol
  have hterm : symTerm p (Real.pi / Real.log p) = fun k : ℕ => Real.log p * (-qp p) ^ (k + 1) := by
    funext k
    unfold symTerm
    have e : ((k : ℝ) + 1) * (Real.pi / Real.log p) * Real.log p = ((k + 1 : ℕ) : ℝ) * Real.pi := by
      field_simp; push_cast; ring
    rw [e, Real.cos_nat_mul_pi, neg_pow, mul_comm ((-1 : ℝ) ^ (k + 1))]; ring
  rw [hterm, ((geom_neg_qp hp).mul_left (Real.log p)).tsum_eq]
  unfold qp
  field_simp

/-- **Route 1 kill: the local `p`-adic form is indefinite.** The multiplier `−σ_p` is `−2κ_p < 0`
at `t = 0` and `> 0` at `t = π / log p`. PROVED. -/
theorem localPrimeMultiplier_indefinite {p : ℕ} (hp : 1 < p) :
    -primeSymbol p 0 < 0 ∧ 0 < -primeSymbol p (Real.pi / Real.log p) := by
  have hk := kappaP_pos hp; have hl := log_pos' hp; have hs := one_lt_sqrt' hp
  refine ⟨by rw [primeSymbol_zero hp]; linarith, ?_⟩
  rw [primeSymbol_at_pi hp, neg_neg]; positivity

/-- **The local floors cannot be summed:** `Σ_p κ_p = ∞`. PROVED (comparison with `Σ 1/p`). -/
theorem kappaP_not_summable : ¬ Summable (fun p : Nat.Primes => kappaP p) := by
  intro h
  apply Nat.Primes.not_summable_one_div
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) h
  have hp : 1 < (p : ℕ) := p.2.one_lt
  have hl := log_pos' hp; have hs := one_lt_sqrt' hp
  have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
  have hl2 : (1 / 2 : ℝ) ≤ Real.log (p : ℕ) := by
    have h2 : Real.log 2 ≤ Real.log (p : ℕ) := Real.log_le_log (by norm_num) hp2
    have := Real.log_two_gt_d9; linarith
  have hsq : Real.sqrt ((p : ℕ) : ℝ) ^ 2 = (p : ℕ) := Real.sq_sqrt (by positivity)
  unfold kappaP
  rw [div_le_div_iff₀ (by positivity) (by linarith)]
  nlinarith [sq_nonneg (Real.sqrt ((p : ℕ) : ℝ) - 1)]

/-! ## Route 2: semi-local truncation -/

/-- The `p`-local prime functional `Σ_{k≥1} log p · p^{-k/2} (g(k log p) + g(−k log p))`. -/
def primeLocal (p : ℕ) (g : ℝ → ℝ) : ℝ :=
  ∑' k : ℕ, Real.log p * qp p ^ (k + 1) *
    (g ((k + 1) * Real.log p) + g (-((k + 1) * Real.log p)))

theorem summable_primeLocal {p : ℕ} (hp : 1 < p) {g : ℝ → ℝ} (hb : ∀ x, |g x| ≤ g 0) :
    Summable fun k : ℕ => Real.log p * qp p ^ (k + 1) *
      (g ((k + 1) * Real.log p) + g (-((k + 1) * Real.log p))) := by
  refine Summable.of_norm_bounded ((hasSum_log_geom hp).summable.mul_right (2 * g 0)) fun k => ?_
  have hl := log_pos' hp; have hq := qp_pos hp
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < Real.log p * qp p ^ (k + 1))]
  have := abs_add_le (g ((k + 1) * Real.log p)) (g (-((k + 1) * Real.log p)))
  have h1 := hb ((k + 1) * Real.log p); have h2 := hb (-((k + 1) * Real.log p))
  have : 0 ≤ Real.log p * qp p ^ (k + 1) := by positivity
  nlinarith

/-- **`prime_p(g) ≤ 2κ_p g(0)`** under the Cauchy–Schwarz bound `|g| ≤ g(0)`. PROVED. -/
theorem primeLocal_le {p : ℕ} (hp : 1 < p) {g : ℝ → ℝ} (hb : ∀ x, |g x| ≤ g 0) :
    primeLocal p g ≤ 2 * kappaP p * g 0 := by
  have hs := (hasSum_log_geom hp).mul_right (2 * g 0)
  rw [show 2 * kappaP p * g 0 = kappaP p * (2 * g 0) by ring]
  refine hasSum_le (fun k => ?_) (summable_primeLocal hp hb).hasSum hs
  have hl := log_pos' hp; have hq := qp_pos hp
  have h1 := (abs_le.1 (hb ((k + 1) * Real.log p))).2
  have h2 := (abs_le.1 (hb (-((k + 1) * Real.log p)))).2
  have : 0 ≤ Real.log p * qp p ^ (k + 1) := by positivity
  nlinarith

/-- **`−2κ_p g(0) ≤ prime_p(g)`.** PROVED. -/
theorem primeLocal_ge {p : ℕ} (hp : 1 < p) {g : ℝ → ℝ} (hb : ∀ x, |g x| ≤ g 0) :
    -(2 * kappaP p * g 0) ≤ primeLocal p g := by
  have hs := ((hasSum_log_geom hp).mul_right (2 * g 0)).neg
  rw [show -(2 * kappaP p * g 0) = -(kappaP p * (2 * g 0)) by ring]
  refine hasSum_le (fun k => ?_) hs (summable_primeLocal hp hb).hasSum
  have hl := log_pos' hp; have hq := qp_pos hp
  have h1 := (abs_le.1 (hb ((k + 1) * Real.log p))).1
  have h2 := (abs_le.1 (hb (-((k + 1) * Real.log p)))).1
  have : 0 ≤ Real.log p * qp p ^ (k + 1) := by positivity
  nlinarith

/-- The envelope is attained by the infinitely broad state `g ≡ c`. PROVED. -/
theorem primeLocal_const {p : ℕ} (hp : 1 < p) (c : ℝ) :
    primeLocal p (fun _ => c) = 2 * kappaP p * c := by
  unfold primeLocal
  have := (hasSum_log_geom hp).mul_right (2 * c)
  rw [show 2 * kappaP p * c = kappaP p * (2 * c) by ring, ← this.tsum_eq]
  congr 1; funext k; ring

/-- The semi-local truncated Weil form over a finite set `S` of primes. -/
def weilS (S : Finset Nat.Primes) (g : ℝ → ℝ) : ℝ :=
  poleTerm g + GppArchimedeanFloor.archimedeanTerm g - ∑ p ∈ S, primeLocal p g

/-- **Semi-local floor.** For a normalised `g` (`g 0 = 1`, `|g| ≤ 1`, archimedean integrand
integrable): `weilS S g ≥ pole(g) + C∞ − 2 Σ_{p∈S} κ_p`. PROVED. -/
theorem weilS_floor (S : Finset Nat.Primes) {g : ℝ → ℝ} (h0 : g 0 = 1)
    (hb : ∀ x, |g x| ≤ g 0)
    (hint : IntegrableOn (GppArchimedeanFloor.archimedeanIntegrand g) (Set.Ioi 0)) :
    poleTerm g + GppArchimedeanFloor.archimedeanFloor - 2 * ∑ p ∈ S, kappaP p ≤ weilS S g := by
  have harch := GppArchimedeanFloor.archimedean_floor g h0
    (fun u _ => by have := (abs_le.1 (hb u)).2; linarith) hint
  have hpr : ∑ p ∈ S, primeLocal p g ≤ 2 * ∑ p ∈ S, kappaP p := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    have := primeLocal_le p.2.one_lt hb
    rw [h0, mul_one] at this; exact this
  unfold weilS; linarith

/-- **The floor is not uniform in `S`:** `Σ_{p∈S} κ_p` is unbounded over finite `S`. PROVED. -/
theorem semiLocal_floor_unbounded (M : ℝ) : ∃ S : Finset Nat.Primes, M < ∑ p ∈ S, kappaP p := by
  by_contra h
  simp only [not_exists, not_lt] at h
  apply kappaP_not_summable
  exact summable_of_sum_le (fun p => (kappaP_pos p.2.one_lt).le) h

/-- **ARP ⇔ positivity on every rung window.** The `S → all` limit is exactly ARP. PROVED. -/
theorem arp_iff_all_rungs :
    ArithmeticReflectionPositivity ↔ ∀ L : ℝ, ReflectionPositiveOnRung L := by
  refine ⟨fun h L => rung_of_reflectionPositivity h L, fun h f hf hc => ?_⟩
  obtain ⟨r, hr⟩ := hc.isCompact.isBounded.subset_closedBall 0
  refine h (2 * r) f hf hc fun y hy => ?_
  apply image_eq_zero_of_notMem_tsupport
  intro hy'
  have := hr hy'
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  linarith

/-!
## Rung 1 of the Weil support ladder: the window, the explicit form, the certificate, the induction

Follow-up to Route 2 above (`arp_iff_all_rungs`: ARP ⇔ every rung). In-tree
convention: `ReflectionPositiveOnRung L` quantifies over smooth `f` supported in `[-L/2, L/2]`, so
`g = autocorr f` is supported in `[-L, L]` and the prime power `n` is visible iff `log n < L`.

## The window
* Rung 0: `L < log 2`, no prime power. Connes–Consani (cited; a named hypothesis in tree).
* **Rung 1: `log 2 ≤ L ≤ log 3`**, `f` supported in `[-log 3/2, log 3/2] ≈ [-0.5493, 0.5493]`. Only
  `n = 2` enters. (At `L = log 3` the point `g(log 3)` is the boundary value of a convolution square,
  so it is `0`.) Rung `k` ends at the `k+1`-st prime power: 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, …
* `weilForm_rung_one` (PROVED): on rung 1,
  `weilForm (autocorr f) = poleTerm g + archimedeanTerm g − (log 2/√2)·2·g(log 2)`,
  using `autocorr_neg` (PROVED: `g(−x) = g(x)`).

## The finite-dimensional problem
The rung-1 form is `Pole (rank 2) + A∞ (the log-Lévy Dirichlet form, ≥ C∞ = −5.372 and
growing like `log|t|`) − K₂`, where `K₂ = (log 2/√2)(τ_{log 2} + τ_{−log 2})` is a partial shift of norm ≤ `√2 log 2
≈ 0.980` on `L²[−h, h]`. Above the frequency `T₁` where `log(t/2π) − 1/t ≥ √2 log 2` the form is
positive, so the problem is a finite Galerkin matrix plus explicit tails (Zhu's one-stroke,
reproduced in GPPDiscovery5/s27).

## Status of rung 1 (labels)
* CERTIFIED (Arb ball arithmetic, single implementation, Lean-open; `s27_onestroke_arb.py` at
  `h = 11/20`, `T = 100`, `K = 60`): `Q(f) ≥ 3.48·10⁻⁸ ‖f‖²` for every `f` on `[−0.55, 0.55]`
  (even sector binding; odd `≥ 9.96·10⁻⁶`). Since `log 3 < 1.1` (`log_three_lt`, PROVED), this covers
  the whole closed rung 1. The earlier S27 certificate on `[−0.8, 0.8]` already covered it.
  `RungOneArbCertificate` is that statement as a named Prop. `rung_one_of_certificate` (PROVED) gives
  `ReflectionPositiveOnRung (log 3)`.
* NUMERICAL (float64, independent code, in-tree time-domain formulas): at the rung-1 edge
  `h = 0.5493`, `λ_min ≈ 5.58·10⁻⁸`, from a true-form Rayleigh quotient of `5.5807·10⁻⁸` against
  `λ_min(R_T) = 5.5715·10⁻⁸` at `T = 3200`, which increases with `T`. The extremal test is even,
  nodeless and bell-shaped (Perron–Frobenius ground state). Budget: `pole/‖f‖² = 1.3044`,
  `A∞/‖f‖² = −1.2865`, `kick/‖f‖² = 0.0178` (`g(log 2)/g(0) = 0.0182`, against the Cauchy–Schwarz
  bound 1). The kick is about 3·10⁵ times the margin, and the extremal test keeps `g(log 2)` tiny.
  So rung 1 is **not** a perturbation of rung 0: the sufficient condition `pole + A∞ ≥ √2 log 2 ·
  g(0)` is false on the extremal.
* Lean proof of rung 1: OPEN. It would need the digamma envelope, quadrature error bounds and a
  verified PD check. Rung 0 itself is not in Lean either.

## Margin across rungs (lower bounds CERTIFIED by Arb; the rest NUMERICAL)
| rung edge | window `L` | certified `λ_min ≥` | NUMERICAL `λ_min ≈` |
|---|---|---|---|
| 0 | `log 2` | 1.30e−3 | 1.331e−3 |
| 1 | `log 3` | 4.81e−8 (h = 0.5493) | 5.58e−8 |
| 2 | `log 4` | 5.80e−13 | 8.5e−13 (float floor) |
| 3 (S27) | 1.6 < `log 5` | 1.02e−17 | — |
| (S27/28) | 2.0 | 4.12e−30 | — |
The fit `λ_min ≈ 10^{−4.9·e^L}`, i.e. `exp(−c·e^L)` with `c ≈ 11`, is NUMERICAL: the margin is
doubly exponential in the window.

## Induction k → k+1 and where it breaks
* The form does not change between rungs; only the test class grows. So rung `k+1` ⇒ rung `k`
  (`rung_mono`, PROVED), and nothing propagates upward.
* Splitting tests as (old window) ⊕ (new directions), the step is a Schur complement. In the 2×2
  model (`two_by_two_nonneg_iff`, PROVED), with `a = λ_k` the rung-`k` margin, `d` the diagonal of a
  new direction and `b` its coupling to the soft mode, positivity holds iff `b² ≤ λ_k·d`. With
  `λ_k ≈ exp(−c e^{L_k})` the coupling of every new direction to the rung-`k` ground state must be
  doubly-exponentially small. Nothing in rung `k` supplies that; it is a fresh arithmetic
  cancellation at every rung. **This is where the induction breaks**: rung `k` gives no quantitative
  input for rung `k+1`. `RungStepCoupling` names the needed bound.

Labels: theorems PROVED (standard axioms). `RungOneArbCertificate` is CERTIFIED externally (Arb)
and named here, not asserted. `RungStepCoupling` and Lean rung 1 are OPEN. ARP OPEN. RH OPEN.

-/

section RungOne

/-- **The autocorrelation is even:** `g(−x) = g(x)`. PROVED. -/
theorem autocorr_neg (f : ℝ → ℝ) (x : ℝ) : autocorr f (-x) = autocorr f x := by
  unfold autocorr
  have h := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun y => f y * f (y + x)) x
  simp only [sub_neg_eq_add, sub_add_cancel] at h ⊢
  rw [← h]
  congr 1; funext y; ring

/-- **The explicit rung-1 form.** For `f` supported in `[-L/2, L/2]` with `L < log 3`, only `n = 2`
is visible: `weilForm g = pole g + A∞ g − (log 2/√2)·2·g(log 2)`. PROVED. -/
theorem weilForm_rung_one {f : ℝ → ℝ} {L : ℝ} (hsupp : ∀ y : ℝ, L / 2 < |y| → f y = 0)
    (hL : L < Real.log 3) :
    weilForm (autocorr f) = poleTerm (autocorr f) + GppArchimedeanFloor.archimedeanTerm (autocorr f) -
      Real.log 2 / Real.sqrt 2 * (2 * autocorr f (Real.log 2)) := by
  have hN : L < Real.log ((2 : ℕ) + 1) := by norm_num; exact hL
  rw [weilForm_eq_truncation hsupp hN]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have h0 : ArithmeticFunction.vonMangoldt 0 = 0 := by simp
  have h1 : ArithmeticFunction.vonMangoldt 1 = 0 := by simp
  rw [h0, h1]
  push_cast
  rw [autocorr_neg f (Real.log 2)]
  ring

/-- **Monotonicity of rungs:** the form is the same at every rung; only the test class grows.
PROVED. -/
theorem rung_mono {L L' : ℝ} (h : ReflectionPositiveOnRung L) (hle : L' ≤ L) :
    ReflectionPositiveOnRung L' := fun f hf hc hs =>
  h f hf hc fun y hy => hs y (by linarith)

/-- `log 3 < 11/10` (so the certificate window `[−0.55, 0.55]` covers rung 1). PROVED. -/
theorem log_three_lt : Real.log 3 < 11 / 10 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.quadratic_le_exp_of_nonneg (x := 1 / 10) (by norm_num)
  have : Real.exp (11 / 10) = Real.exp 1 * Real.exp (1 / 10) := by
    rw [← Real.exp_add]; norm_num
  rw [this]
  nlinarith [Real.exp_pos (1 / 10)]

/-- **The rung-1 Arb certificate, as a named Prop** (CERTIFIED externally by ball arithmetic,
`s27_onestroke_arb.py --L 11/20 --T 100 --K 60`; single implementation; not a Lean proof):
`weilForm (autocorr f) ≥ 3.48·10⁻⁸ ∫ f²` for every smooth `f` supported in `[−11/20, 11/20]`. -/
def RungOneArbCertificate : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → (∀ y : ℝ, 11 / 20 < |y| → f y = 0) →
    (348 / 10 ^ 10 : ℝ) * ∫ y, f y ^ 2 ≤ weilForm (autocorr f)

/-- **Certificate ⇒ positivity on the whole closed rung 1** (`L = log 3`). PROVED (conditional on
the external certificate). -/
theorem rung_one_of_certificate (h : RungOneArbCertificate) :
    ReflectionPositiveOnRung (Real.log 3) := by
  have hwide : ReflectionPositiveOnRung (11 / 10) := fun f hf hc hs => by
    have := h f hf hc fun y hy => hs y (by linarith)
    have hint : 0 ≤ ∫ y, f y ^ 2 := integral_nonneg fun y => sq_nonneg _
    nlinarith
  exact rung_mono hwide log_three_lt.le

/-- **Schur step in the 2×2 model:** for `a > 0`, `a x² + 2bxy + d y² ≥ 0` for all `x, y` iff
`b² ≤ a d`. PROVED. -/
theorem two_by_two_nonneg_iff {a b d : ℝ} (ha : 0 < a) :
    (∀ x y : ℝ, 0 ≤ a * x ^ 2 + 2 * b * x * y + d * y ^ 2) ↔ b ^ 2 ≤ a * d := by
  constructor
  · intro h
    have := h (-b) a
    have h' : 0 ≤ a * (a * d - b ^ 2) := by nlinarith
    nlinarith [(mul_nonneg_iff_of_pos_left ha).1 h']
  · intro hb x y
    have key : a * (a * x ^ 2 + 2 * b * x * y + d * y ^ 2) =
        (a * x + b * y) ^ 2 + (a * d - b ^ 2) * y ^ 2 := by ring
    have : 0 ≤ a * (a * x ^ 2 + 2 * b * x * y + d * y ^ 2) := by
      rw [key]; nlinarith [sq_nonneg (a * x + b * y), sq_nonneg y]
    exact (mul_nonneg_iff_of_pos_left ha).1 this

/-- **The induction step needs a coupling bound** (named, OPEN). For the rung-`k` margin `lamK`,
every new direction's diagonal `d` and coupling `b` to the rung-`k` soft mode satisfy `b² ≤ lamK·d`.
In the 2×2 model this is exactly the step (`two_by_two_nonneg_iff`). -/
def RungStepCoupling (lamK : ℝ) (couplings : Set (ℝ × ℝ)) : Prop :=
  ∀ bd ∈ couplings, bd.1 ^ 2 ≤ lamK * bd.2

/-- In the model, the coupling bound is equivalent to positivity of every 2×2 step. PROVED. -/
theorem rungStepCoupling_iff {lamK : ℝ} (hl : 0 < lamK) (couplings : Set (ℝ × ℝ)) :
    RungStepCoupling lamK couplings ↔
      ∀ bd ∈ couplings, ∀ x y : ℝ, 0 ≤ lamK * x ^ 2 + 2 * bd.1 * x * y + bd.2 * y ^ 2 :=
  ⟨fun h bd hbd => (two_by_two_nonneg_iff hl).2 (h bd hbd),
    fun h bd hbd => (two_by_two_nonneg_iff hl).1 (h bd hbd)⟩

end RungOne

end GppWeilLocalIndefinite
