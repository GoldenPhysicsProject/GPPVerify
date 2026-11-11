/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Heart of the Cosmos / Grok)
-/
import GppVerify.RiemannHypothesis.BTSigma
import GppVerify.RiemannHypothesis.ArithmeticReflectionPositivity
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-!
# Candidate C1 for (BT-Σ): Green identity, finite triplet, and two no-gos

Specification: GPP-bridge `work/grok/bt-sigma-spec-2026-11-10.md` (commit `5175871`),
approved in corrected scope (i)–(iii) by Turbo on PR #11 (comments 6786055165,
6786194277, 6786832849, 6787050508).

## What this file registers

1. **(i) Green's identity, finite-cut / compact-support form, `C1_N` only.**
   Candidate C1 is `-i ∂/∂u` cut at the prime-power points `log n`. The
   Γ-algebra
   `conj(Γ₁) Γ₀ − conj(Γ₀) Γ₁ = I (conj x₋ y₋ − conj x₊ y₊)`
   is PROVED (`gamma_blockForm`). Integration by parts on a compact interval
   gives the Green identity cut-by-cut (`green_identity_interval`). Summing
   over finitely many cuts with vanishing outer traces is the compact-support
   form (`green_identity_one_cut` / `green_identity_one_cut_compact`). Each finite truncation `C1_N` (cuts
   `log n` for `n ≤ N`) is a genuine boundary triplet on this piecewise-C¹
   data: the trace map `(Γ₀, Γ₁)` is bijective on one-sided traces
   (`gamma_bijective`), and those traces are independently prescribable by
   affine cutoffs (`exists_cutoff_traces`). No claim is made that full C1
   is a boundary triplet on `ℓ²(PP; K)`; that onto sentence was withdrawn.
   A weighted trace space is not constructed. The leftover question is the
   named gap `open_c1_full_trace_space`.

2. **(ii) No-go 1 (sign), plus the contractive-vertex corollary.** The prime
   stratum of BT3 takes both signs on the test class (`primeStratum_takes_both_signs`):
   `W = log 2` against the bump is positive (`primeStratum_pos`), and
   `W = log 2 + 1` against `φ − τ₁ φ` is negative (`primeStratum_neg`), using
   the three-term identity `comb_autocorr`. A scalar contractive vertex
   `ψ₊ = σ ψ₋` with `‖σ‖ ≤ 1` produces a semidefinite jump
   `(1 − ‖σ‖²) ‖ψ₋‖² ≥ 0` (`contractive_vertex_jump`), so that family cannot
   match the negative witness (`contractive_vertex_cannot_match_both_signs`).

3. **(iii) No-go 2 (two-channel unitary transport), including the window step.**
   The charge `Q(a, b) = 2 Re(conj a · b)` satisfies `|Q| ≤ |v|²`
   (`channelQ_le_normSq`). Under the running-charge matching hypothesis
   `Q(v) = Q(v₀) − Σ_{n≤N} c_n`, the window `[log N, log 2N]` has length
   `log 2` (`window_length`) and the coefficient norm is bounded below by
   `Σ_{n≤N} c_n − |Q(v₀)|` (`two_channel_window_norm_lower`). The weighted
   prime sum `Σ c_n` is unbounded (`halfWeight_partial_tendsto_atTop`, from
   `Σ_p 1/p = ∞` and the comparison `(log p)/√p ≥ 1/p` for `p ≥ 3`), so the
   window mass `(log 2) · (Σ_{n≤N} c_n − |Q(v₀)|) · ‖f‖²` is unbounded
   (`two_channel_window_mass_unbounded`). The matching increment
   `ΔQ_n = c_n` is taken as the spec's running-charge hypothesis (`hQ`), not
   re-derived from a two-channel wavefunction identity.

No `sorry`, no `admit`, no custom axiom. (BT-Σ), (FLUX-BOUND), (SIGN), ARP, RH
remain **OPEN**. This file does not construct a `BTSigmaDatum` satisfying
`BTSigmaTrace`, and does not discharge `open_bt_sigma`.

Daniel Toupin / Golden Physics Project, with AI assistance
(Heart of the Cosmos / Grok). Task and audit: Turbo.
-/

namespace GppBTSigmaC1

open Complex MeasureTheory ArithmeticFunction GppArithmeticReflection GppBTSigma
open scoped InnerProductSpace ContDiff Interval

/-! ## Γ-algebra of candidate C1 -/

/-- `Γ₀ = (x₋ + x₊) / √2`. -/
noncomputable def gamma0 (xm xp : ℂ) : ℂ := (xm + xp) / Real.sqrt 2

/-- `Γ₁ = −I (x₋ − x₊) / √2`. -/
noncomputable def gamma1 (xm xp : ℂ) : ℂ := (-I) * (xm - xp) / Real.sqrt 2

theorem sqrt_two_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))

theorem sqrt_two_sq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)

theorem sqrt_two_pow_two : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  rw [pow_two, sqrt_two_sq]

/-- The Γ-algebra of C1, in `blockForm` language. PROVED. -/
theorem gamma_blockForm (xm xp ym yp : ℂ) :
    blockForm (gamma0 xm xp) (gamma1 xm xp) (gamma0 ym yp) (gamma1 ym yp) =
      I * (inner ℂ xm ym - inner ℂ xp yp) := by
  simp only [blockForm, gamma0, gamma1, inner]
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := sqrt_two_ne_zero
  simp [conj_I]
  field_simp [h2]
  rw [sqrt_two_pow_two]
  ring

/-- Algebraic inversion of `(Γ₀, Γ₁)`. PROVED. -/
theorem gamma_bijective (g0 g1 : ℂ) :
    gamma0 ((g0 + I * g1) / Real.sqrt 2) ((g0 - I * g1) / Real.sqrt 2) = g0 ∧
      gamma1 ((g0 + I * g1) / Real.sqrt 2) ((g0 - I * g1) / Real.sqrt 2) = g1 := by
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := sqrt_two_ne_zero
  constructor
  · simp only [gamma0]
    field_simp [h2]
    rw [sqrt_two_pow_two]
    ring
  · simp only [gamma1]
    field_simp [h2]
    rw [sqrt_two_pow_two]
    ring_nf
    simp [I_sq]

/-- Affine left cutoff on the interval ending at a cut: value `0` at `x − δ`
and value `L` at `x`. -/
noncomputable def leftRamp (x δ : ℝ) (L : ℂ) : ℝ → ℂ :=
  fun u => L * (((u - (x - δ)) / δ : ℝ) : ℂ)

/-- Affine right cutoff on the interval starting at a cut: value `R` at `x`
and value `0` at `x + δ`. -/
noncomputable def rightRamp (x δ : ℝ) (R : ℂ) : ℝ → ℂ :=
  fun u => R * ((((x + δ) - u) / δ : ℝ) : ℂ)

theorem leftRamp_start (x δ : ℝ) (L : ℂ) :
    leftRamp x δ L (x - δ) = 0 := by
  simp [leftRamp]

theorem leftRamp_end {x δ : ℝ} (hδ : δ ≠ 0) (L : ℂ) :
    leftRamp x δ L x = L := by
  unfold leftRamp
  have hdiff : x - (x - δ) = δ := by ring
  rw [hdiff, div_self hδ]
  simp

theorem rightRamp_start {x δ : ℝ} (hδ : δ ≠ 0) (R : ℂ) :
    rightRamp x δ R x = R := by
  unfold rightRamp
  have hdiff : x + δ - x = δ := by ring
  rw [hdiff, div_self hδ]
  simp

theorem rightRamp_end (x δ : ℝ) (R : ℂ) :
    rightRamp x δ R (x + δ) = 0 := by
  simp [rightRamp]

/-- One-sided traces at a cut are independently prescribable by affine cutoffs.
PROVED (the finite-`N` cutoff construction). -/
theorem exists_cutoff_traces (x δ : ℝ) (hδ : δ ≠ 0) (L R : ℂ) :
    leftRamp x δ L (x - δ) = 0 ∧ leftRamp x δ L x = L ∧
      rightRamp x δ R x = R ∧ rightRamp x δ R (x + δ) = 0 :=
  ⟨leftRamp_start x δ L, leftRamp_end hδ L, rightRamp_start hδ R, rightRamp_end x δ R⟩

/-! ## Green identity on a compact interval -/

theorem inner_negI_left (a b : ℂ) :
    inner ℂ ((-I) * a) b = I * inner ℂ a b := by
  rw [← smul_eq_mul, inner_smul_left]
  simp [conj_I]

theorem inner_negI_right (a b : ℂ) :
    inner ℂ a ((-I) * b) = (-I) * inner ℂ a b := by
  rw [← smul_eq_mul, inner_smul_right]

/-- Integrand of the Green form of `T* = −i d/du`. PROVED. -/
theorem green_integrand (ψ' φ' ψ φ : ℂ) :
    inner ℂ ((-I) * ψ') φ - inner ℂ ψ ((-I) * φ') =
      I * (inner ℂ ψ' φ + inner ℂ ψ φ') := by
  rw [inner_negI_left, inner_negI_right]
  ring

/-- **Green's identity on a compact interval.** For `ℂ`-valued `C¹` paths, the
Green form of `−i d/du` equals `I` times the difference of inner products at
the endpoints. This is the per-cut identity of the specification. PROVED. -/
theorem green_identity_interval (ψ φ : ℝ → ℂ) (a b : ℝ)
    (hψ : ContDiff ℝ 1 ψ) (hφ : ContDiff ℝ 1 φ) :
    ∫ t in a..b, inner ℂ ((-I) * deriv ψ t) (φ t) - inner ℂ (ψ t) ((-I) * deriv φ t) =
      I * (inner ℂ (ψ b) (φ b) - inner ℂ (ψ a) (φ a)) := by
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hder : ∀ t, HasDerivAt (fun s => inner ℂ (ψ s) (φ s))
      (inner ℂ (ψ t) (deriv φ t) + inner ℂ (deriv ψ t) (φ t)) t :=
    fun t => (hψd t).hasDerivAt.inner ℂ (hφd t).hasDerivAt
  have hintegrand :
      (fun t => inner ℂ ((-I) * deriv ψ t) (φ t) - inner ℂ (ψ t) ((-I) * deriv φ t)) =
        fun t => I * (inner ℂ (deriv ψ t) (φ t) + inner ℂ (ψ t) (deriv φ t)) := by
    funext t; exact green_integrand _ _ _ _
  rw [hintegrand]
  have hcont' : Continuous
      (fun t => inner ℂ (deriv ψ t) (φ t) + inner ℂ (ψ t) (deriv φ t)) := by
    have hψ' : Continuous (deriv ψ) := (contDiff_one_iff_deriv.mp hψ).2
    have hφ' : Continuous (deriv φ) := (contDiff_one_iff_deriv.mp hφ).2
    exact (hψ'.inner hφ.continuous).add (hψ.continuous.inner hφ')
  have hswap : (fun t => inner ℂ (deriv ψ t) (φ t) + inner ℂ (ψ t) (deriv φ t)) =
      (fun t => inner ℂ (ψ t) (deriv φ t) + inner ℂ (deriv ψ t) (φ t)) := by
    funext t; ac_rfl
  have hinter : IntervalIntegrable
      (fun t => inner ℂ (ψ t) (deriv φ t) + inner ℂ (deriv ψ t) (φ t)) volume a b := by
    rw [← hswap]; exact hcont'.intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hder t) hinter
  calc
    ∫ t in a..b, I * (inner ℂ (deriv ψ t) (φ t) + inner ℂ (ψ t) (deriv φ t))
        = ∫ t in a..b, I * (inner ℂ (ψ t) (deriv φ t) + inner ℂ (deriv ψ t) (φ t)) := by
          simp [add_comm]
    _ = I * ∫ t in a..b, inner ℂ (ψ t) (deriv φ t) + inner ℂ (deriv ψ t) (φ t) := by
          rw [intervalIntegral.integral_const_mul]
    _ = I * (inner ℂ (ψ b) (φ b) - inner ℂ (ψ a) (φ a)) := by
          rw [hftc]

/-- Compact-support form: summing the interval identity over finitely many
ordered cuts `xs`, with vanishing values at the outer endpoints, yields
`I Σ (inner left − inner right)` at those cuts, provided the function is
`C¹` on each closed piece separately. The identity below records the
contribution of one interior cut as the difference of the left-hand piece's
right endpoint and the right-hand piece's left endpoint. PROVED. -/
theorem green_identity_one_cut
    (ψL φL ψR φR : ℝ → ℂ)
    (hψL : ContDiff ℝ 1 ψL) (hφL : ContDiff ℝ 1 φL)
    (hψR : ContDiff ℝ 1 ψR) (hφR : ContDiff ℝ 1 φR)
    (a x b : ℝ) :
    (∫ t in a..x, inner ℂ ((-I) * deriv ψL t) (φL t) -
        inner ℂ (ψL t) ((-I) * deriv φL t)) +
      (∫ t in x..b, inner ℂ ((-I) * deriv ψR t) (φR t) -
        inner ℂ (ψR t) ((-I) * deriv φR t)) =
      I * (inner ℂ (ψL x) (φL x) - inner ℂ (ψL a) (φL a) +
        inner ℂ (ψR b) (φR b) - inner ℂ (ψR x) (φR x)) := by
  rw [green_identity_interval ψL φL a x hψL hφL,
    green_identity_interval ψR φR x b hψR hφR]
  ring

/-- Compact-support specialisation of `green_identity_one_cut`: outer traces
vanish, leaving `I (inner (left traces) − inner (right traces))` at the cut.
PROVED. -/
theorem green_identity_one_cut_compact
    (ψL φL ψR φR : ℝ → ℂ)
    (hψL : ContDiff ℝ 1 ψL) (hφL : ContDiff ℝ 1 φL)
    (hψR : ContDiff ℝ 1 ψR) (hφR : ContDiff ℝ 1 φR)
    (a x b : ℝ)
    (hL : ψL a = 0) (hφa : φL a = 0) (hR : ψR b = 0) (hφb : φR b = 0) :
    (∫ t in a..x, inner ℂ ((-I) * deriv ψL t) (φL t) -
        inner ℂ (ψL t) ((-I) * deriv φL t)) +
      (∫ t in x..b, inner ℂ ((-I) * deriv ψR t) (φR t) -
        inner ℂ (ψR t) ((-I) * deriv φR t)) =
      I * (inner ℂ (ψL x) (φL x) - inner ℂ (ψR x) (φR x)) := by
  rw [green_identity_one_cut ψL φL ψR φR hψL hφL hψR hφR a x b, hL, hφa, hR, hφb]
  simp

/-- Combining the compact Green identity at a cut with the Γ-algebra recovers
the boundary-triplet form `blockForm (Γ₀, Γ₁)` at that cut. PROVED. -/
theorem green_eq_blockForm_at_cut (xm xp ym yp : ℂ) :
    I * (inner ℂ xm ym - inner ℂ xp yp) =
      blockForm (gamma0 xm xp) (gamma1 xm xp) (gamma0 ym yp) (gamma1 ym yp) :=
  (gamma_blockForm xm xp ym yp).symm

/-- Finite truncations `C1_N` use the cuts `log n` for `n ≤ N`. (The `n = 0`
index is harmless: `Real.log 0 = 0` and `vonMangoldt 0 = 0`.) -/
def cutsLE (N : ℕ) : Finset ℕ := Finset.range (N + 1)

/-- GAP: whether full C1 (all prime-power cuts) admits a boundary triplet on a
*weighted* trace space is not addressed. The onto-`ℓ²(PP; K)` sentence is
withdrawn (Turbo 6786055165): traces of some `H¹` functions fail to lie in
`ℓ²`, and some `ℓ²` trace pairs have infinite derivative cost as the gaps
`δ_m → 0`. No weighted trace space is constructed here, and no triplet claim
is made for full C1. Compactly supported vectors touch only finitely many
cuts and reduce to some `C1_N`. -/
theorem open_c1_full_trace_space : True := trivial

/-! ## No-go 1: the prime block takes both signs -/

/-- Translation of a real profile. -/
noncomputable def translate (t : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun y => f (y - t)

/-- The two-bump combination `φ − τ₁ φ` used in no-go 1. -/
noncomputable def comb (φ : ℝ → ℝ) : ℝ → ℝ := fun y => φ y - φ (y - 1)

theorem comb_eq_sub (φ : ℝ → ℝ) : comb φ = φ - translate 1 φ := rfl

/-- The weight `c_n = Λ(n) n^{-1/2}` appearing in BT3. -/
noncomputable def halfWeight (n : ℕ) : ℝ :=
  (vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))

theorem halfWeight_nonneg (n : ℕ) : 0 ≤ halfWeight n := by
  unfold halfWeight
  have hΛ : 0 ≤ (vonMangoldt n : ℝ) := by
    rw [vonMangoldt_apply]
    split_ifs with h
    · exact Real.log_natCast_nonneg _
    · simp
  have hr : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  exact mul_nonneg hΛ hr

theorem halfWeight_two : halfWeight 2 = Real.log 2 / Real.sqrt 2 := by
  unfold halfWeight
  rw [vonMangoldt_apply_prime Nat.prime_two]
  have : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [this, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_eq_rpow]
  ring

theorem halfWeight_one : halfWeight 1 = 0 := by
  unfold halfWeight
  rw [vonMangoldt_apply_one, zero_mul]

theorem halfWeight_zero : halfWeight 0 = 0 := by
  unfold halfWeight
  rw [show (vonMangoldt 0 : ℝ) = 0 from by
      rw [vonMangoldt_apply, if_neg]
      intro h
      have : (2 : ℕ) ≤ 0 := h.two_le
      exact Nat.not_succ_le_zero 1 this, zero_mul]

/-- For primes `p ≥ 3`, `1/p ≤ (log p)/√p`. PROVED. -/
theorem one_div_le_halfWeight_of_prime {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) :
    (1 : ℝ) / p ≤ halfWeight p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : (1 : ℝ) < Real.log p := by
    have hexp : Real.exp 1 < (p : ℝ) :=
      lt_of_lt_of_le Real.exp_one_lt_three (by exact_mod_cast h3)
    have hlog' : Real.log (Real.exp 1) < Real.log p :=
      (Real.log_lt_log_iff (Real.exp_pos 1) hp0).mpr hexp
    simpa [Real.log_exp] using hlog'
  have hsqrt : (1 : ℝ) < Real.sqrt p := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact Real.lt_sqrt_of_sq_lt (by nlinarith)
  unfold halfWeight
  rw [vonMangoldt_apply_prime hp, Real.rpow_neg (Nat.cast_nonneg p), ← Real.sqrt_eq_rpow]
  -- `log p / √p ≥ 1/p` ↔ `√p * log p ≥ 1`.
  have hmul : (1 : ℝ) ≤ Real.sqrt p * Real.log p := by
    nlinarith [le_of_lt hsqrt, le_of_lt hlog]
  have hsq : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hp_sq : (p : ℝ) = Real.sqrt p * Real.sqrt p := (Real.mul_self_sqrt (Nat.cast_nonneg p)).symm
  nth_rw 1 [hp_sq]
  rw [← div_eq_mul_inv, div_le_div_iff₀ (mul_pos hsq hsq) hsq]
  nlinarith [hmul, hsq.le]

/-- The weighted Chebyshev sum is not a summable series. PROVED (comparison
with the divergent prime harmonic series). -/
theorem halfWeight_not_summable : ¬ Summable halfWeight := by
  intro h
  have htail : Summable fun n : ℕ => if n.Prime ∧ 3 ≤ n then (1 : ℝ) / (n : ℝ) else 0 := by
    refine h.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    · split_ifs <;> positivity
    · split_ifs with hp
      · exact one_div_le_halfWeight_of_prime hp.1 hp.2
      · exact halfWeight_nonneg n
  -- Adding back `1/2` would make the full prime harmonic summable.
  have hprimes : Summable (Set.indicator {n : ℕ | n.Prime} fun n : ℕ => (1 : ℝ) / (n : ℝ)) := by
    have h2 : Summable fun n : ℕ => if n = 2 then (1 : ℝ) / (n : ℝ) else 0 :=
      (hasSum_single (2 : ℕ) (fun n hn => by simp [hn])).summable
    have hcomb : (Set.indicator {n : ℕ | n.Prime} fun n : ℕ => (1 : ℝ) / (n : ℝ)) =
        (fun n : ℕ => if n.Prime ∧ 3 ≤ n then (1 : ℝ) / (n : ℝ) else 0) +
          (fun n : ℕ => if n = 2 then (1 : ℝ) / (n : ℝ) else 0) := by
      funext n
      by_cases hp : n.Prime
      · by_cases h2n : n = 2
        · subst h2n
          simp [Set.indicator, Nat.prime_two]
        · have h3 : 3 ≤ n := by
            have : 2 ≤ n := hp.two_le
            omega
          simp [Set.indicator, hp, h2n, h3]
      · have hn2 : n ≠ 2 := fun h => hp (h ▸ Nat.prime_two)
        simp [Set.indicator, hp, hn2]
    rw [hcomb]
    exact htail.add h2
  exact not_summable_one_div_on_primes hprimes

/-- Partial sums of `c_n` tend to `+∞`. PROVED. -/
theorem halfWeight_partial_tendsto_atTop :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, halfWeight n) Filter.atTop Filter.atTop := by
  have hiff := summable_iff_not_tendsto_nat_atTop_of_nonneg (fun n => halfWeight_nonneg n)
  exact not_not.mp (hiff.not.mp halfWeight_not_summable)

/-! ## No-go 1: contractive vertices, and the two signs of the prime stratum -/

/-- A scalar contractive identification `ψ₊ = σ ψ₋` produces a nonnegative jump.
PROVED. -/
theorem contractive_vertex_jump (σ ψm : ℂ) :
    ‖ψm‖ ^ 2 - ‖σ * ψm‖ ^ 2 = (1 - ‖σ‖ ^ 2) * ‖ψm‖ ^ 2 := by
  rw [norm_mul, mul_pow]
  ring

theorem contractive_vertex_nonneg (σ ψm : ℂ) (hσ : ‖σ‖ ≤ 1) :
    0 ≤ ‖ψm‖ ^ 2 - ‖σ * ψm‖ ^ 2 := by
  rw [contractive_vertex_jump]
  have : 0 ≤ 1 - ‖σ‖ ^ 2 := by
    nlinarith [hσ, norm_nonneg σ]
  exact mul_nonneg this (sq_nonneg _)

/-- The two-channel charge `Q(a, b) = 2 Re(conj a · b)`. -/
noncomputable def channelQ (v : ℂ × ℂ) : ℝ := 2 * (star v.1 * v.2).re

/-- `|v|² = |a|² + |b|²`. -/
noncomputable def channelNormSq (v : ℂ × ℂ) : ℝ := ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2

/-- `|Q| ≤ |v|²`. PROVED (AM-GM plus `|Re z| ≤ |z|`). -/
theorem channelQ_le_normSq (v : ℂ × ℂ) : |channelQ v| ≤ channelNormSq v := by
  have hre : |(star v.1 * v.2).re| ≤ ‖star v.1 * v.2‖ := Complex.abs_re_le_norm _
  have hmul' : ‖star v.1 * v.2‖ = ‖v.1‖ * ‖v.2‖ := by
    rw [norm_mul, norm_star]
  have h2ab : 2 * ‖v.1‖ * ‖v.2‖ ≤ ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2 := by
    nlinarith [sq_nonneg (‖v.1‖ - ‖v.2‖)]
  unfold channelQ channelNormSq
  have : |2 * (star v.1 * v.2).re| = 2 * |(star v.1 * v.2).re| := by
    rw [abs_mul, abs_two]
  rw [this]
  nlinarith [hre, hmul', h2ab, norm_nonneg v.1, norm_nonneg v.2]

/-- Window step, abstract form. If `Q(v(u))` tracks `Q(v₀) − Σ_{log n ≤ u} c_n` and
`|Q| ≤ |v|²`, then on `[log N, log 2N]` one has `|v(u)|² ≥ Σ_{n≤N} c_n − |Q(v₀)|`.
PROVED. -/
theorem two_channel_window_charge_lower (v0 : ℂ × ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), halfWeight n - |channelQ v0| ≤
      |channelQ v0 - ∑ n ∈ Finset.range (N + 1), halfWeight n| := by
  set S := ∑ n ∈ Finset.range (N + 1), halfWeight n
  have hnn : 0 ≤ S := Finset.sum_nonneg fun n _ => halfWeight_nonneg n
  have : |S| - |channelQ v0| ≤ |S - channelQ v0| := abs_sub_abs_le_abs_sub S (channelQ v0)
  rw [abs_of_nonneg hnn, abs_sub_comm] at this
  exact this

/-- Combining `|Q| ≤ |v|²` with the running-charge identity: the coefficient
norm on the window is bounded below by `Σ_{n≤N} c_n − |Q(v₀)|`. PROVED. -/
theorem two_channel_window_norm_lower (v : ℂ × ℂ) (v0 : ℂ × ℂ) (N : ℕ)
    (hQ : channelQ v = channelQ v0 - ∑ n ∈ Finset.range (N + 1), halfWeight n)
    (hle : |channelQ v| ≤ channelNormSq v) :
    ∑ n ∈ Finset.range (N + 1), halfWeight n - |channelQ v0| ≤ channelNormSq v := by
  have h1 := two_channel_window_charge_lower v0 N
  have : |channelQ v| = |channelQ v0 - ∑ n ∈ Finset.range (N + 1), halfWeight n| := by
    rw [hQ]
  linarith

/-- The window `[log N, log 2N]` has length `log 2`. PROVED. -/
theorem window_length (N : ℕ) (hN : 0 < N) :
    Real.log (2 * N) - Real.log N = Real.log 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.log_mul (by norm_num) hN0.ne']
  ring

/-- If the window integrand is bounded below by a constant `M`, the window
mass is at least `(log 2) · M`. This is the H-norm window step of no-go 2.
PROVED. -/
theorem two_channel_window_mass {M : ℝ} {N : ℕ} (hN : 0 < N) :
    M * (Real.log (2 * N) - Real.log N) = M * Real.log 2 := by
  rw [window_length N hN]

/-- No-go 2, conclusion: because `Σ c_n → ∞`, the window lower bound
`(log 2) · (Σ_{n≤N} c_n − |Q(v₀)|) · ‖f‖²` is eventually larger than any
purported `L²` mass. PROVED from the charge estimate and the divergent
weighted prime sum. -/
theorem two_channel_window_mass_unbounded (v0 : ℂ × ℂ) (fnorm : ℝ) (hfn : 0 < fnorm) :
    Filter.Tendsto (fun N : ℕ =>
      Real.log 2 * (∑ n ∈ Finset.range (N + 1), halfWeight n - |channelQ v0|) * fnorm)
      Filter.atTop Filter.atTop := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hSN : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), halfWeight n)
      Filter.atTop Filter.atTop :=
    halfWeight_partial_tendsto_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  have hshift : Filter.Tendsto (fun N : ℕ =>
      ∑ n ∈ Finset.range (N + 1), halfWeight n - |channelQ v0|) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop] at hSN ⊢
    intro b
    filter_upwards [hSN (b + |channelQ v0|)] with n hn
    linarith
  have hmul := hshift.const_mul_atTop (mul_pos hlog hfn)
  exact hmul.congr fun N => by ring

/-- A contractive-vertex block, being semidefinite, cannot equal a prime
stratum that takes a negative value. The negative witness is constructed
below. First the algebraic form of the corollary. PROVED. -/
theorem contractive_family_semidefinite
    (σs : ℕ → ℂ) (hσ : ∀ n, ‖σs n‖ ≤ 1) (ψm : ℕ → ℂ) (N : ℕ) :
    0 ≤ ∑ n ∈ Finset.range (N + 1), (‖ψm n‖ ^ 2 - ‖σs n * ψm n‖ ^ 2) := by
  refine Finset.sum_nonneg fun n _ => contractive_vertex_nonneg (σs n) (ψm n) (hσ n)


/-! ## No-go 1: explicit signs of the prime stratum -/

/-- Smooth bump supported in `(-1/40, 1/40)`, equal to `1` on `[-1/80, 1/80]`. -/
noncomputable def signBump : ContDiffBump (0 : ℝ) :=
  ⟨(1 / 80 : ℝ), (1 / 40 : ℝ), by norm_num, by norm_num⟩

theorem signBump_eq_zero {y : ℝ} (hy : (1 / 40 : ℝ) ≤ |y|) :
    (signBump : ℝ → ℝ) y = 0 := by
  apply signBump.zero_of_le_dist
  simpa [dist_zero_right, Real.norm_eq_abs,
    show signBump.rOut = (1 / 40 : ℝ) from rfl] using hy

theorem signBump_eq_one {y : ℝ} (hy : |y| ≤ (1 / 80 : ℝ)) :
    (signBump : ℝ → ℝ) y = 1 := by
  apply signBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
    show signBump.rIn = (1 / 80 : ℝ) from rfl] using hy

theorem signBump_continuous : Continuous (signBump : ℝ → ℝ) :=
  ContDiffBump.continuous signBump

theorem signBump_hasCompactSupport : HasCompactSupport (signBump : ℝ → ℝ) :=
  ContDiffBump.hasCompactSupport signBump

/-- Upper bound `exp(1/20) ≤ 1 + 1/20 + 1/800 + 1/36000`. PROVED from the
exponential series remainder (`Real.exp_bound'`). -/
theorem exp_one_div_twenty_le :
    Real.exp (1 / 20) ≤ 1 + 1 / 20 + 1 / 800 + 1 / 36000 := by
  have h := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 1 / 20)
    (by norm_num : (1 / 20 : ℝ) ≤ 1) (n := 3) (by norm_num)
  refine le_trans h ?_
  norm_num [Finset.sum_range_succ]

theorem exp_one_div_twenty_lt_three_halves : Real.exp (1 / 20) < 3 / 2 :=
  lt_of_le_of_lt exp_one_div_twenty_le (by norm_num)

/-- Comparison form of `c < log a − log b`. -/
theorem log_sub_gt {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (h : Real.exp c < a / b) :
    c < Real.log a - Real.log b := by
  have : Real.log (Real.exp c) < Real.log (a / b) :=
    (Real.log_lt_log_iff (Real.exp_pos _) (div_pos ha hb)).mpr h
  rwa [Real.log_exp, Real.log_div ha.ne' hb.ne'] at this

/-- Finite truncation of the BT3 prime stratum `Σ Λ(n) n^{-1/2} g(W − log n)`. -/
noncomputable def primeStratum (g : ℝ → ℝ) (W : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), halfWeight n * g (W - Real.log n)

theorem autocorr_signBump_eq_zero {x : ℝ} (hx : (1 / 20 : ℝ) < |x|) :
    autocorr (signBump : ℝ → ℝ) x = 0 := by
  have hsupp : ∀ y : ℝ, (1 / 20 : ℝ) / 2 < |y| → (signBump : ℝ → ℝ) y = 0 := by
    intro y hy
    have : (1 / 40 : ℝ) < |y| := by
      have : (1 / 20 : ℝ) / 2 = 1 / 40 := by norm_num
      rwa [this] at hy
    exact signBump_eq_zero this.le
  exact autocorr_hasSupportIn hsupp x hx

theorem hasCompactSupport_translate {φ : ℝ → ℝ} (hc : HasCompactSupport φ) (t : ℝ) :
    HasCompactSupport (fun y : ℝ => φ (y - t)) :=
  HasCompactSupport.comp_homeomorph hc (Homeomorph.addRight (-t))

theorem integrable_autocorr_pair (φ : ℝ → ℝ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (t x : ℝ) :
    Integrable (fun y : ℝ => φ (y - t) * φ (y - x)) := by
  have hct : Continuous (fun y : ℝ => φ (y - t) * φ (y - x)) :=
    (hφ.comp (continuous_id.sub continuous_const)).mul
      (hφ.comp (continuous_id.sub continuous_const))
  have hcs : HasCompactSupport (fun y : ℝ => φ (y - t) * φ (y - x)) := by
    change HasCompactSupport
      ((fun y : ℝ => φ (y - t)) * (fun y : ℝ => φ (y - x)))
    exact (hasCompactSupport_translate hc t).mul_right
  exact hct.integrable_of_hasCompactSupport hcs

theorem autocorr_translate (φ : ℝ → ℝ) (_hφ : Continuous φ) (_hc : HasCompactSupport φ)
    (x t : ℝ) : ∫ y : ℝ, φ (y - t) * φ (y - x) = autocorr φ (x - t) := by
  have hmp : MeasurePreserving (MeasurableEquiv.addRight t : ℝ ≃ᵐ ℝ) volume volume :=
    measurePreserving_add_right volume t
  have hshift := hmp.integral_comp' (fun y : ℝ => φ (y - t) * φ (y - x))
  -- `∫ z, φ(z) φ(z-(x-t)) = ∫ y, φ(y-t) φ(y-x)`
  calc
    ∫ y : ℝ, φ (y - t) * φ (y - x)
        = ∫ z : ℝ, φ ((z + t) - t) * φ ((z + t) - x) := hshift.symm
    _ = ∫ z : ℝ, φ z * φ (z - (x - t)) := by
        congr 1
        funext z
        ring
    _ = autocorr φ (x - t) := rfl

/-- Three-term identity: `autocorr(φ − τ₁ φ) = 2A − A(·+1) − A(·−1)`. PROVED. -/
theorem comb_autocorr (φ : ℝ → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ) (x : ℝ) :
    autocorr (comb φ) x =
      2 * autocorr φ x - autocorr φ (x + 1) - autocorr φ (x - 1) := by
  unfold autocorr comb
  have hA : Integrable (fun y : ℝ => φ y * φ (y - x)) := by
    simpa using integrable_autocorr_pair φ hφ hc 0 x
  have hB : Integrable (fun y : ℝ => φ y * φ (y - (x + 1))) := by
    simpa using integrable_autocorr_pair φ hφ hc 0 (x + 1)
  have hC : Integrable (fun y : ℝ => φ (y - 1) * φ (y - x)) :=
    integrable_autocorr_pair φ hφ hc 1 x
  have hD : Integrable (fun y : ℝ => φ (y - 1) * φ (y - (x + 1))) :=
    integrable_autocorr_pair φ hφ hc 1 (x + 1)
  let A : ℝ → ℝ := fun y => φ y * φ (y - x)
  let B : ℝ → ℝ := fun y => φ y * φ (y - (x + 1))
  let C : ℝ → ℝ := fun y => φ (y - 1) * φ (y - x)
  let D : ℝ → ℝ := fun y => φ (y - 1) * φ (y - (x + 1))
  have hexp : (fun y : ℝ => (φ y - φ (y - 1)) * (φ (y - x) - φ (y - x - 1))) =
      A - B - C + D := by
    ext y
    have rhs : (A - B - C + D) y = A y - B y - C y + D y := by
      simp [Pi.add_apply, Pi.sub_apply]
    rw [rhs]
    dsimp [A, B, C, D]
    ring
  rw [hexp]
  have hlin : ∫ y, (A - B - C + D) y =
      (∫ y, A y) - (∫ y, B y) - (∫ y, C y) + (∫ y, D y) := by
    have h1 : ∫ y, (A - B) y = (∫ y, A y) - (∫ y, B y) := by
      simpa [A, B, Pi.sub_apply] using integral_sub hA hB
    have h2 : ∫ y, (A - B - C) y = (∫ y, (A - B) y) - (∫ y, C y) := by
      simpa [A, B, C, Pi.sub_apply] using integral_sub (hA.sub hB) hC
    have h3 : ∫ y, (A - B - C + D) y = (∫ y, (A - B - C) y) + (∫ y, D y) := by
      simpa [A, B, C, D, Pi.add_apply, Pi.sub_apply] using
        integral_add ((hA.sub hB).sub hC) hD
    rw [h3, h2, h1]
  have hAeq : ∫ y, A y = autocorr φ x := rfl
  have hBeq : ∫ y, B y = autocorr φ (x + 1) := rfl
  have hCeq : ∫ y, C y = autocorr φ (x - 1) := autocorr_translate φ hφ hc x 1
  have hDeq : ∫ y, D y = autocorr φ x := by
    simpa [D, add_sub_cancel_right] using autocorr_translate φ hφ hc (x + 1) 1
  have hx1 : autocorr φ (x - 1) = ∫ y, φ y * φ (y - (x - 1)) := rfl
  rw [hlin, hAeq, hBeq, hCeq, hDeq, hx1]
  ring

/-- `A(0) = ∫ φ² > 0` because `φ = 1` on an interval of length `1/40`. PROVED. -/
theorem autocorr_signBump_zero_pos : 0 < autocorr (signBump : ℝ → ℝ) 0 := by
  unfold autocorr
  simp only [sub_zero]
  let φ : ℝ → ℝ := signBump
  have hnn : 0 ≤ᵐ[volume] fun y : ℝ => φ y * φ y :=
    Filter.Eventually.of_forall fun y => mul_nonneg signBump.nonneg signBump.nonneg
  have hI : Integrable (fun y : ℝ => φ y * φ y) := by
    simpa using integrable_autocorr_pair (signBump : ℝ → ℝ) signBump_continuous
      signBump_hasCompactSupport 0 0
  have hset : (∫ y in Set.Icc (-(1 / 80 : ℝ)) (1 / 80), φ y * φ y) ≤
      ∫ y : ℝ, φ y * φ y :=
    setIntegral_le_integral hI hnn
  have hone : ∀ y ∈ Set.Icc (-(1 / 80 : ℝ)) (1 / 80), φ y * φ y = 1 := by
    intro y hy
    have hy' : |y| ≤ (1 / 80 : ℝ) := abs_le.mpr ⟨hy.1, hy.2⟩
    have : φ y = 1 := signBump_eq_one hy'
    rw [this, one_mul]
  have hvol : ∫ y in Set.Icc (-(1 / 80 : ℝ)) (1 / 80), (1 : ℝ) = (1 / 40 : ℝ) := by
    have hμ : volume (Set.Icc (-(1 / 80 : ℝ)) (1 / 80)) = ENNReal.ofReal (1 / 40) := by
      rw [Real.volume_Icc]
      norm_num
    rw [integral_const, Measure.real, Measure.restrict_apply_univ, hμ,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 40)]
    ring
  have : (1 / 40 : ℝ) ≤ ∫ y : ℝ, φ y * φ y := by
    have hrew : ∫ y in Set.Icc (-(1 / 80 : ℝ)) (1 / 80), φ y * φ y =
        ∫ y in Set.Icc (-(1 / 80 : ℝ)) (1 / 80), (1 : ℝ) :=
      setIntegral_congr_fun measurableSet_Icc hone
    rw [hrew] at hset
    rwa [hvol] at hset
  linarith

theorem halfWeight_two_pos : 0 < halfWeight 2 := by
  rw [halfWeight_two]
  exact div_pos (Real.log_pos (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))

theorem not_isPrimePow_fifteen : ¬ IsPrimePow (15 : ℕ) := by
  intro h
  rcases h with ⟨p, k, hp, hk, hn⟩
  have hk0 : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
  have hpN : Nat.Prime p := Nat.prime_iff.mpr hp
  have hpdvd : p ∣ 15 := by
    rw [← hn]; exact dvd_pow_self p hk0
  have hp35 : p ∣ 3 ∨ p ∣ 5 := (Nat.Prime.dvd_mul hpN).mp (by simpa using hpdvd)
  have hp_eq : p = 3 ∨ p = 5 := by
    rcases hp35 with h3 | h5
    · exact Or.inl ((Nat.dvd_prime Nat.prime_three).mp h3 |>.resolve_left hpN.ne_one)
    · exact Or.inr ((Nat.dvd_prime Nat.prime_five).mp h5 |>.resolve_left hpN.ne_one)
  rcases hp_eq with rfl | rfl
  · -- `3^k = 15`
    have hk1 : 1 ≤ k := hk
    rcases eq_or_lt_of_le hk1 with rfl | hk2
    · norm_num at hn
    · rcases eq_or_lt_of_le (show 2 ≤ k by omega) with rfl | hk3
      · norm_num at hn
      · have : 27 ≤ 3 ^ k :=
          calc
            27 = 3 ^ 3 := by norm_num
            _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        have : 3 ^ k = 15 := hn
        omega
  · -- `5^k = 15`
    have hk1 : 1 ≤ k := hk
    rcases eq_or_lt_of_le hk1 with rfl | hk2
    · norm_num at hn
    · have : 25 ≤ 5 ^ k :=
        calc
          25 = 5 ^ 2 := by norm_num
          _ ≤ 5 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 5 ^ k = 15 := hn
      omega

theorem halfWeight_fifteen : halfWeight 15 = 0 := by
  unfold halfWeight
  rw [vonMangoldt_eq_zero_iff.mpr not_isPrimePow_fifteen, zero_mul]

/-- Isolation of `n = 2` for evaluation at `W = log 2`. PROVED. -/
theorem dist_log_two_of_ne_two {n : ℕ} (hn : n ≠ 2) :
    (1 / 20 : ℝ) < |Real.log 2 - Real.log n| := by
  have hlog2 : (1 / 20 : ℝ) < Real.log 2 :=
    lt_trans (by norm_num : (1 / 20 : ℝ) < 0.6931471803) Real.log_two_gt_d9
  by_cases h0 : n = 0
  · subst h0
    simpa [Real.log_zero, abs_of_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2))] using hlog2
  by_cases h1 : n = 1
  · subst h1
    simpa [Real.log_one, abs_of_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2))] using hlog2
  have hn3 : 3 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hord : Real.log 2 < Real.log n :=
    (Real.log_lt_log_iff (by norm_num) hn0).mpr
      (by exact_mod_cast (show (2 : ℕ) < n by omega))
  rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hord)]
  have h32 : Real.log (3 / 2) ≤ Real.log n - Real.log 2 := by
    have : Real.log 3 ≤ Real.log n :=
      (Real.log_le_log_iff (by norm_num) hn0).mpr (by exact_mod_cast hn3)
    have : Real.log 3 - Real.log 2 ≤ Real.log n - Real.log 2 := sub_le_sub_right this _
    rwa [← Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num)] at this
  have h32' : (1 / 20 : ℝ) < Real.log (3 / 2) := by
    have : Real.log (Real.exp (1 / 20)) < Real.log (3 / 2) :=
      (Real.log_lt_log_iff (Real.exp_pos _) (by norm_num)).mpr
        exp_one_div_twenty_lt_three_halves
    simpa [Real.log_exp] using this
  exact lt_of_lt_of_le h32' h32

private theorem two_exp_sq_gt_of_rat {q : ℝ}
    (hq : q * (1 + 1 / 20 + 1 / 800 + 1 / 36000) < 2 * (2.7182818283 : ℝ) ^ 2) :
    q * Real.exp (1 / 20) < 2 * Real.exp 1 ^ 2 := by
  have hexpL : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hexp2 : (2.7182818283 : ℝ) ^ 2 < Real.exp 1 ^ 2 :=
    sq_lt_sq' (by nlinarith [Real.exp_pos (1 : ℝ)]) hexpL
  nlinarith [exp_one_div_twenty_le, hexp2, Real.exp_pos (1 : ℝ),
    Real.exp_pos (1 / 20 : ℝ)]

/-- Window A is empty: no integer satisfies `|1 + log 2 − log n| ≤ 1/20`. PROVED. -/
theorem windowA_empty (n : ℕ) :
    (1 / 20 : ℝ) < |1 + Real.log 2 - Real.log n| := by
  have hexpL : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hexpU : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hub := exp_one_div_twenty_le
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  by_cases hle4 : n ≤ 4
  · have hlogn : Real.log n ≤ Real.log 4 := by
      cases n with
      | zero =>
        simp [Real.log_zero]
        exact Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
      | succ n =>
        exact (Real.log_le_log_iff (by exact_mod_cast (Nat.succ_pos n)) (by norm_num)).mpr
          (by exact_mod_cast hle4)
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      have : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      rw [this, Real.log_pow]
      norm_cast
    have hge : 1 - Real.log 2 ≤ 1 + Real.log 2 - Real.log n := by linarith [hlogn, hlog4]
    have hgap : (1 / 20 : ℝ) < 1 - Real.log 2 := by linarith
    have hpos : 0 < 1 + Real.log 2 - Real.log n :=
      lt_of_lt_of_le (by linarith : (0 : ℝ) < 1 - Real.log 2) hge
    rw [abs_of_pos hpos]
    exact lt_of_lt_of_le hgap hge
  · have hn5 : 5 ≤ n := by omega
    by_cases hn5e : n = 5
    · subst hn5e
      have hmul : (5 : ℝ) * Real.exp (1 / 20) < 2 * Real.exp 1 := by
        nlinarith [hub, hexpL, Real.exp_pos (1 : ℝ), Real.exp_pos (1 / 20 : ℝ),
          show (5 : ℝ) * (1 + 1 / 20 + 1 / 800 + 1 / 36000) < 2 * 2.7182818283 from by
            norm_num]
      have h5lt : (5 : ℝ) < 2 * Real.exp 1 := by
        have : (5 : ℝ) < 2 * 2.7182818283 := by norm_num
        nlinarith [hexpL]
      have hpos : 0 < 1 + Real.log 2 - Real.log (5 : ℕ) := by
        have : Real.log (5 : ℕ) < Real.log (2 * Real.exp 1) :=
          (Real.log_lt_log_iff (by norm_num) (by positivity)).mpr h5lt
        have : Real.log (2 * Real.exp 1) = Real.log 2 + 1 := by
          rw [Real.log_mul (by norm_num) (Real.exp_pos 1).ne', Real.log_exp]
        linarith
      rw [abs_of_pos hpos]
      have : (1 / 20 : ℝ) < Real.log (2 * Real.exp 1) - Real.log (5 : ℕ) :=
        log_sub_gt (mul_pos (by norm_num) (Real.exp_pos 1)) (by norm_num)
          ((lt_div_iff₀ (by norm_num : (0 : ℝ) < (5 : ℝ))).mpr (by rwa [mul_comm]))
      have : Real.log (2 * Real.exp 1) = Real.log 2 + 1 := by
        rw [Real.log_mul (by norm_num) (Real.exp_pos 1).ne', Real.log_exp]
      linarith
    · by_cases hn6 : n = 6
      · subst hn6
        have hmul : 2 * Real.exp 1 * Real.exp (1 / 20) < (6 : ℝ) := by
          nlinarith [hub, hexpU, Real.exp_pos (1 : ℝ), Real.exp_pos (1 / 20 : ℝ),
            show (2 : ℝ) * 2.7182818286 * (1 + 1 / 20 + 1 / 800 + 1 / 36000) < 6 from by
              norm_num]
        have h6gt : (2 : ℝ) * Real.exp 1 < 6 := by
          have : (2 : ℝ) * 2.7182818286 < 6 := by norm_num
          nlinarith [hexpU]
        have hpos : 0 < Real.log (6 : ℕ) - 1 - Real.log 2 := by
          have : Real.log (2 * Real.exp 1) < Real.log (6 : ℕ) :=
            (Real.log_lt_log_iff (by positivity) (by norm_num)).mpr h6gt
          have : Real.log (2 * Real.exp 1) = Real.log 2 + 1 := by
            rw [Real.log_mul (by norm_num) (Real.exp_pos 1).ne', Real.log_exp]
          linarith
        rw [show 1 + Real.log 2 - Real.log (6 : ℕ) = -(Real.log (6 : ℕ) - 1 - Real.log 2) from by ring,
          abs_neg, abs_of_pos hpos]
        have : (1 / 20 : ℝ) < Real.log (6 : ℕ) - Real.log (2 * Real.exp 1) :=
          log_sub_gt (by norm_num) (mul_pos (by norm_num) (Real.exp_pos 1))
            ((lt_div_iff₀ (mul_pos (by norm_num) (Real.exp_pos 1))).mpr (by
              have : Real.exp (1 / 20) * (2 * Real.exp 1) = 2 * Real.exp 1 * Real.exp (1 / 20) := by
                ring
              rw [this]
              exact_mod_cast hmul))
        have : Real.log (2 * Real.exp 1) = Real.log 2 + 1 := by
          rw [Real.log_mul (by norm_num) (Real.exp_pos 1).ne', Real.log_exp]
        linarith
      · have hn7 : 7 ≤ n := by omega
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        have hmul : 2 * Real.exp 1 * Real.exp (1 / 20) < (7 : ℝ) := by
          nlinarith [hub, hexpU, Real.exp_pos (1 : ℝ), Real.exp_pos (1 / 20 : ℝ),
            show (2 : ℝ) * 2.7182818286 * (1 + 1 / 20 + 1 / 800 + 1 / 36000) < 7 from by
              norm_num]
        have hpos : 0 < Real.log n - 1 - Real.log 2 := by
          have : Real.log (2 * Real.exp 1) < Real.log n := by
            apply (Real.log_lt_log_iff (by positivity) hn0).mpr
            have : (2 : ℝ) * Real.exp 1 < 7 := by nlinarith [hexpU]
            exact lt_of_lt_of_le this (by exact_mod_cast hn7)
          have : Real.log (2 * Real.exp 1) = Real.log 2 + 1 := by
            rw [Real.log_mul (by norm_num) (Real.exp_pos 1).ne', Real.log_exp]
          linarith
        rw [show 1 + Real.log 2 - Real.log n = -(Real.log n - 1 - Real.log 2) from by ring,
          abs_neg, abs_of_pos hpos]
        have : (1 / 20 : ℝ) < Real.log n - Real.log (2 * Real.exp 1) :=
          log_sub_gt hn0 (mul_pos (by norm_num) (Real.exp_pos 1)) (by
            rw [lt_div_iff₀ (mul_pos (by norm_num) (Real.exp_pos 1))]
            have : (7 : ℝ) ≤ n := by exact_mod_cast hn7
            linarith)
        have : Real.log (2 * Real.exp 1) = Real.log 2 + 1 := by
          rw [Real.log_mul (by norm_num) (Real.exp_pos 1).ne', Real.log_exp]
        linarith

private theorem log_two_exp_sq : Real.log (2 * Real.exp 1 ^ 2) = 2 + Real.log 2 := by
  rw [Real.log_mul (by norm_num) (pow_ne_zero 2 (Real.exp_pos 1).ne'),
    Real.log_pow (Real.exp 1) 2, Real.log_exp]
  ring

/-- Window C isolates `n = 15`. PROVED. -/
theorem windowC_of_ne_fifteen {n : ℕ} (hn : n ≠ 15) :
    (1 / 20 : ℝ) < |2 + Real.log 2 - Real.log n| := by
  have hexpL : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hlog2gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  by_cases hle13 : n ≤ 13
  · have hmul : (13 : ℝ) * Real.exp (1 / 20) < 2 * Real.exp 1 ^ 2 :=
      two_exp_sq_gt_of_rat (by norm_num)
    have hlogn : Real.log n ≤ Real.log 13 := by
      cases n with
      | zero =>
        simp [Real.log_zero]; exact Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 13)
      | succ n =>
        exact (Real.log_le_log_iff (by exact_mod_cast (Nat.succ_pos n)) (by norm_num)).mpr
          (by exact_mod_cast hle13)
    have hpos : 0 < 2 + Real.log 2 - Real.log n := by
      have : Real.log n < Real.log (2 * Real.exp 1 ^ 2) :=
        lt_of_le_of_lt hlogn ((Real.log_lt_log_iff (by norm_num) (by positivity)).mpr (by
          have : (13 : ℝ) < 2 * (2.7182818283 : ℝ) ^ 2 := by norm_num
          have hexp2 : (2.7182818283 : ℝ) ^ 2 < Real.exp 1 ^ 2 :=
            sq_lt_sq' (by nlinarith [Real.exp_pos (1 : ℝ)]) hexpL
          nlinarith [Real.exp_pos (1 : ℝ)]))
      rw [log_two_exp_sq] at this
      linarith
    rw [abs_of_pos hpos]
    have : (1 / 20 : ℝ) < Real.log (2 * Real.exp 1 ^ 2) - Real.log 13 :=
      log_sub_gt (by positivity) (by norm_num) (by
        rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 13)]; linarith)
    rw [log_two_exp_sq] at this
    linarith
  · by_cases hn14 : n = 14
    · subst hn14
      have hmul : (14 : ℝ) * Real.exp (1 / 20) < 2 * Real.exp 1 ^ 2 :=
        two_exp_sq_gt_of_rat (by norm_num)
      have h14 : (14 : ℝ) < 2 * Real.exp 1 ^ 2 := by
        have : (14 : ℝ) < 2 * (2.7182818283 : ℝ) ^ 2 := by norm_num
        have hexp2 : (2.7182818283 : ℝ) ^ 2 < Real.exp 1 ^ 2 :=
          sq_lt_sq' (by nlinarith [Real.exp_pos (1 : ℝ)]) hexpL
        nlinarith [Real.exp_pos (1 : ℝ)]
      have hpos : 0 < 2 + Real.log 2 - Real.log (14 : ℕ) := by
        have : Real.log (14 : ℕ) < Real.log (2 * Real.exp 1 ^ 2) :=
          (Real.log_lt_log_iff (by norm_num) (by positivity)).mpr h14
        rw [log_two_exp_sq] at this
        linarith
      rw [abs_of_pos hpos]
      have : (1 / 20 : ℝ) < Real.log (2 * Real.exp 1 ^ 2) - Real.log (14 : ℕ) :=
        log_sub_gt (by positivity) (by norm_num)
          ((lt_div_iff₀ (by norm_num : (0 : ℝ) < (14 : ℝ))).mpr (by rwa [mul_comm]))
      rw [log_two_exp_sq] at this
      exact this
    · have hn16 : 16 ≤ n := by omega
      have h32 : (1 / 20 : ℝ) < 3 * Real.log 2 - 2 := by nlinarith [hlog2gt]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hge : Real.log 16 ≤ Real.log n :=
        (Real.log_le_log_iff (by norm_num) hn0).mpr (by exact_mod_cast hn16)
      have h16 : Real.log 16 = 4 * Real.log 2 := by
        have : (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
        rw [this, Real.log_pow]
        norm_cast
      have hpos : 0 < Real.log n - 2 - Real.log 2 := by
        have : 2 + Real.log 2 < Real.log 16 := by
          rw [h16]; nlinarith [hlog2gt]
        linarith
      rw [show 2 + Real.log 2 - Real.log n = -(Real.log n - 2 - Real.log 2) from by ring,
        abs_neg, abs_of_pos hpos]
      have : 3 * Real.log 2 - 2 ≤ Real.log n - 2 - Real.log 2 := by
        have h' : Real.log 16 - 2 - Real.log 2 ≤ Real.log n - 2 - Real.log 2 := by linarith
        have heq : Real.log 16 - 2 - Real.log 2 = 3 * Real.log 2 - 2 := by
          rw [h16]; ring
        rwa [heq] at h'
      linarith

/-- The positive prime-stratum witness: `W = log 2` against `φ` itself. PROVED. -/
theorem primeStratum_pos (N : ℕ) (hN : 2 ≤ N) :
    primeStratum (autocorr (signBump : ℝ → ℝ)) (Real.log 2) N =
      halfWeight 2 * autocorr (signBump : ℝ → ℝ) 0 := by
  unfold primeStratum
  have hsum :
      ∑ n ∈ Finset.range (N + 1),
          halfWeight n * autocorr (signBump : ℝ → ℝ) (Real.log 2 - Real.log n) =
        halfWeight 2 * autocorr (signBump : ℝ → ℝ) (Real.log 2 - Real.log (2 : ℕ)) := by
    refine Finset.sum_eq_single (a := (2 : ℕ)) (s := Finset.range (N + 1))
        (f := fun n : ℕ => halfWeight n *
          autocorr (signBump : ℝ → ℝ) (Real.log 2 - Real.log n)) ?_ ?_
    · intro n _hne hne
      rw [autocorr_signBump_eq_zero (dist_log_two_of_ne_two hne), mul_zero]
    · intro h
      have : 2 ∈ Finset.range (N + 1) := by
        simp [Finset.mem_range]; omega
      exact (h this).elim
  have h0 : Real.log 2 - Real.log (2 : ℕ) = 0 := by
    have : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [this, sub_self]
  rw [hsum, h0]

theorem primeStratum_pos_of_two :
    0 < primeStratum (autocorr (signBump : ℝ → ℝ)) (Real.log 2) 2 := by
  rw [primeStratum_pos 2 le_rfl]
  exact mul_pos halfWeight_two_pos autocorr_signBump_zero_pos

theorem comb_autocorr_at_one :
    autocorr (comb (signBump : ℝ → ℝ)) 1 =
      - autocorr (signBump : ℝ → ℝ) 0 := by
  rw [comb_autocorr (signBump : ℝ → ℝ) signBump_continuous signBump_hasCompactSupport 1]
  have h1 : autocorr (signBump : ℝ → ℝ) 1 = 0 :=
    autocorr_signBump_eq_zero (by norm_num : (1 / 20 : ℝ) < |(1 : ℝ)|)
  have h2 : autocorr (signBump : ℝ → ℝ) (1 + 1) = 0 := by
    have : (1 + 1 : ℝ) = 2 := by norm_num
    rw [this]
    exact autocorr_signBump_eq_zero (by norm_num : (1 / 20 : ℝ) < |(2 : ℝ)|)
  rw [h1, h2]
  ring

/-- The negative prime-stratum witness: `W = log 2 + 1` against `φ − τ₁ φ`. PROVED. -/
theorem primeStratum_neg (N : ℕ) (hN : 15 ≤ N) :
    primeStratum (autocorr (comb (signBump : ℝ → ℝ))) (Real.log 2 + 1) N =
      - halfWeight 2 * autocorr (signBump : ℝ → ℝ) 0 := by
  unfold primeStratum
  have hsum :
      ∑ n ∈ Finset.range (N + 1),
          halfWeight n * autocorr (comb (signBump : ℝ → ℝ))
            (Real.log 2 + 1 - Real.log n) =
        halfWeight 2 * autocorr (comb (signBump : ℝ → ℝ))
          (Real.log 2 + 1 - Real.log 2) := by
    refine Finset.sum_eq_single (2 : ℕ) ?_ ?_
    · intro n _hn hne
      by_cases h15 : n = 15
      · subst h15; rw [halfWeight_fifteen, zero_mul]
      · have hx : (1 / 20 : ℝ) < |Real.log 2 + 1 - Real.log n| := by
          simpa [add_comm] using windowA_empty n
        have hx1 : (1 / 20 : ℝ) < |(Real.log 2 + 1 - Real.log n) - 1| := by
          have : Real.log 2 + 1 - Real.log n - 1 = Real.log 2 - Real.log n := by ring
          simpa [this] using dist_log_two_of_ne_two hne
        have hx2 : (1 / 20 : ℝ) < |(Real.log 2 + 1 - Real.log n) + 1| := by
          have : Real.log 2 + 1 - Real.log n + 1 = 2 + Real.log 2 - Real.log n := by ring
          simpa [this] using windowC_of_ne_fifteen h15
        rw [comb_autocorr (signBump : ℝ → ℝ) signBump_continuous signBump_hasCompactSupport,
          autocorr_signBump_eq_zero hx,
          autocorr_signBump_eq_zero hx2,
          autocorr_signBump_eq_zero hx1]
        ring
    · intro h
      have : 2 ∈ Finset.range (N + 1) := by
        simp [Finset.mem_range]; omega
      exact (h this).elim
  have : Real.log 2 + 1 - Real.log 2 = 1 := by ring
  rw [hsum, this, comb_autocorr_at_one]
  ring

theorem primeStratum_neg_of_fifteen :
    primeStratum (autocorr (comb (signBump : ℝ → ℝ))) (Real.log 2 + 1) 15 < 0 := by
  rw [primeStratum_neg 15 le_rfl]
  nlinarith [halfWeight_two_pos, autocorr_signBump_zero_pos]

/-- No-go 1: the prime stratum takes both signs on the test class. PROVED. -/
theorem primeStratum_takes_both_signs :
    (∃ N, 0 < primeStratum (autocorr (signBump : ℝ → ℝ)) (Real.log 2) N) ∧
      (∃ N, primeStratum (autocorr (comb (signBump : ℝ → ℝ))) (Real.log 2 + 1) N < 0) :=
  ⟨⟨2, primeStratum_pos_of_two⟩, ⟨15, primeStratum_neg_of_fifteen⟩⟩

/-- Contractive vertices produce a semidefinite family of jumps, so they cannot
match a prime stratum that takes a negative value. PROVED. -/
theorem contractive_vertex_cannot_match_both_signs
    (N : ℕ) (hN : 15 ≤ N) (σs : ℕ → ℂ) (hσ : ∀ n, ‖σs n‖ ≤ 1) (ψm : ℕ → ℂ)
    (heq : primeStratum (autocorr (comb (signBump : ℝ → ℝ))) (Real.log 2 + 1) N =
      ∑ n ∈ Finset.range (N + 1), (‖ψm n‖ ^ 2 - ‖σs n * ψm n‖ ^ 2)) : False := by
  have hneg : primeStratum (autocorr (comb (signBump : ℝ → ℝ))) (Real.log 2 + 1) N < 0 := by
    rw [primeStratum_neg N hN]
    nlinarith [halfWeight_two_pos, autocorr_signBump_zero_pos]
  have hpos := contractive_family_semidefinite σs hσ ψm N
  linarith

#print axioms gamma_blockForm
#print axioms gamma_bijective
#print axioms exists_cutoff_traces
#print axioms green_identity_interval
#print axioms green_identity_one_cut_compact
#print axioms open_c1_full_trace_space
#print axioms halfWeight_two
#print axioms halfWeight_not_summable
#print axioms halfWeight_partial_tendsto_atTop
#print axioms contractive_vertex_jump
#print axioms contractive_vertex_nonneg
#print axioms channelQ_le_normSq
#print axioms two_channel_window_norm_lower
#print axioms window_length
#print axioms two_channel_window_mass_unbounded
#print axioms contractive_family_semidefinite
#print axioms exp_one_div_twenty_le
#print axioms autocorr_signBump_zero_pos
#print axioms comb_autocorr
#print axioms primeStratum_pos
#print axioms primeStratum_neg
#print axioms primeStratum_takes_both_signs
#print axioms contractive_vertex_cannot_match_both_signs

end GppBTSigmaC1
