/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Heart of the Cosmos / Grok)
-/
import GppVerify.RiemannHypothesis.BTSigma
import GppVerify.RiemannHypothesis.WeilRungOne

/-!
# Local Euler decomposition of the flux / Weil prime side, and the `ζ` vs `F_θ` test

Turbo's next pass after the #558 / #559 / #560 merges (PR #11 comment 6785463913):
either discharge `FluxBound` directly, or produce a non-circular `BTSigmaDatum`
with `BTSigmaTrace`. This file records what can be proved from the Euler product
and the tree's `F_θ` convention *without* importing zeros or RH, and it names
exactly where the attack stops.

## What is already in the tree

* `weilForm g = poleTerm g + archimedeanTerm g - primeSide g`
  (`GppArithmeticReflection.weilForm`). Writing `W∞ g := pole + A∞` and
  `μ g := W∞ g - primeSide g`, one has `μ = weilForm` definitionally. ARP is
  `0 ≤ μ (f ⋆ f̃)`. No zeros enter that definition.
* `primeSide` is supported on prime powers (`Λ`), and on rung 1
  (`HasSupportIn g L` with `L < log 3`) it is exactly the `p = 2` kick
  (`GppWeilRungOne.primeSide_eq_kickTwo`).
* `fluxDefect h W = primeStratumTerm h W - unitStratumTerm h W` (PROVED,
  `rfl`). `(FLUX=∂)` in trace form is `FluxBound` (PROVED,
  `fluxEqBdryTrace_iff_fluxBound`).
* Circularity guard: if a prime block is *defined* as `I · fluxDefect`, then
  “the block stays bounded” is literally `FluxBound`
  (`defect_block_discharges_nothing`, PROVED).
* Axis unitarity of `S_arith` and of every real-tilt local factor is a theorem
  and does not control the sign of `μ` (banked no-go, #559). `SArithInner` is
  RH (`rh_of_SArith_inner`). Neither is used here.

## What this file proves

1. On each finite rung, `primeSide` is a sum of local Euler pairings
   `W_p(g) = Σ_k (log p) p^{-k/2} (g(k log p) + g(-k log p))`. Rung 1 is the
   `p = 2` term already in tree; the general finite-rung identity is
   `primeSide_eq_truncation`.
2. The tree's adversary `F_θ = ξ(s − 1/4) ξ(s + 1/4)` (`GppCelestialNodal.Ftheta`)
   has finite-place pairing
   `primeSideFtheta g = Σ_n Λ(n) n^{-1/2} (n^{1/4} + n^{-1/4}) (g(log n) + g(-log n))`,
   the critical-line weighting of `−ξ'/ξ(s−1/4) − ξ'/ξ(s+1/4)`. On rung 1 this
   is a different multiple of the same `p = 2` sample
   (`primeSideFtheta_eq_kickTwoFtheta`). The coefficient
   `2^{1/4} + 2^{-1/4}` is strictly larger than `1`, so the two pairings differ
   whenever the kick is visible (`primeSide_ne_primeSideFtheta_of_visible_two`).
3. The same distinction holds for the windowed prime stratum at `W = 0` on an
   even rung-1 profile (`primeStratum_ne_primeStratumFtheta_of_rung1`). The
   unit / pole term does not see `Λ`, so it cannot cancel the difference.
4. Therefore a single numerical “prime block” cannot equal both
   `I · primeStratumTerm` and `I · primeStratumFtheta` on such a profile
   (`cannot_match_zeta_and_ftheta_strata`). Any construction whose boundary
   form is identical for `ζ` and `F_θ` (the completed scale operator of
   round 8A, whose boundary form vanishes for both) cannot satisfy
   `BTSigmaTrace` for zeta's primes on that profile.

No `sorry`, no `admit`, no custom axiom. No new `open_` stub: the remaining
gaps are already named (`open_flux_bound`, `open_bt_sigma`,
`open_flux_bound_iff_arp`). The round-7A finite-window certificate (constant
`5.49`, Lemma M) lives on the held #558 and is not re-registered here; it is
a finite-window statement that uses zeros as DATA and does not discharge
exhaustion.

## Where the attack stops

* The sign of `μ` on the full cone is ARP, OPEN. The uniform bound on
  `fluxDefect` is `FluxBound`, OPEN, RH-strength given R1–R4 (round 3 R5).
* Round 7A bounds `|D_K|` on `[2, W]` by `Ztot_K + Arch + Tail_K(W)`. `Ztot`
  sums verified zeros (DATA). Lemma M (`|ζ'/ζ(−3/2+iξ)| ≤ 5.49 + ½ log(6.25+ξ²)`)
  is not RH-strength (LIBRARY GAP) and only feeds (HC). Passing from every
  finite `W` to `sup_W |D| < ∞` requires control of the zero sum at all
  heights, which is RH.
* C1 (`gaussian_annihilator`) and GW-EF-2 are already consumed as (H3) of the
  round-4 dictionary and by `rh_of_arp`. They do not estimate `fluxDefect`
  without zeros.
* Encoding the local samples `h(W − k log p)` as “boundary values” without an
  operator `T*` would make the prime block equal the stratum by algebra and
  trip `defect_block_discharges_nothing`. A non-circular (BT-Σ) must produce
  `Γ₀p, Γ₁p` from an operator whose Green's identity *proves* the pairing.
  That construction is `open_bt_sigma`. This file only constrains it: the
  pairing it computes has to be zeta's local Euler pairing, not `F_θ`'s and
  not the zero-side sum.

(FLUX-BOUND), (BT-Σ), (SIGN), ARP, RH: **OPEN**.

Daniel Toupin / Golden Physics Project, with AI assistance
(Heart of the Cosmos / Grok).
-/

namespace GppFluxBoundLocalEuler

open ArithmeticFunction GppWeilLadder GppWeilRungOne GppArithmeticReflection GppFluxBound
  GppBTSigma GppArchimedeanFloor
open scoped ContDiff ComplexConjugate

/-! ## Local Euler pairings for `ζ` and for `F_θ` -/

/-- The finite-place pairing of the tree's `F_θ = ξ(s − 1/4) ξ(s + 1/4)`:
`Σ_n Λ(n) n^{-1/2} (n^{1/4} + n^{-1/4}) (g(log n) + g(-log n))`. This is the
critical weighting of `−ξ'/ξ(s − 1/4) − ξ'/ξ(s + 1/4)`; no zero locations
are used. -/
noncomputable def primeSideFtheta (g : ℝ → ℝ) : ℝ :=
  ∑' n : ℕ, (Λ n / Real.sqrt n) *
    ((n : ℝ) ^ (1 / 4 : ℝ) + (n : ℝ) ^ (-(1 / 4 : ℝ))) *
      (g (Real.log n) + g (-Real.log n))

/-- The single `p = 2` kick of that pairing. -/
noncomputable def kickTwoFtheta (g : ℝ → ℝ) : ℝ :=
  (Real.log 2 / Real.sqrt 2) *
    ((2 : ℝ) ^ (1 / 4 : ℝ) + (2 : ℝ) ^ (-(1 / 4 : ℝ))) *
      (g (Real.log 2) + g (-Real.log 2))

/-- The F_θ coefficient at `n = 2` is strictly larger than zeta's. PROVED. -/
theorem ftheta_two_coeff_gt_one :
    1 < (2 : ℝ) ^ (1 / 4 : ℝ) + (2 : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have h1 : 1 < (2 : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_lt_rpow (by norm_num) (by norm_num)
  have h2 : 0 < (2 : ℝ) ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  linarith

/-- A single term of `primeSideFtheta` vanishes when `log n > L`. PROVED. -/
theorem primeSideFtheta_term_eq_zero {g : ℝ → ℝ} {L : ℝ} (hg : HasSupportIn g L)
    {n : ℕ} (hn : L < Real.log n) :
    (Λ n / Real.sqrt n) *
      ((n : ℝ) ^ (1 / 4 : ℝ) + (n : ℝ) ^ (-(1 / 4 : ℝ))) *
        (g (Real.log n) + g (-Real.log n)) = 0 := by
  have hlog : (0 : ℝ) ≤ Real.log n := Real.log_natCast_nonneg n
  have h1 : g (Real.log n) = 0 := hg _ (by rwa [abs_of_nonneg hlog])
  have h2 : g (-Real.log n) = 0 := hg _ (by rwa [abs_neg, abs_of_nonneg hlog])
  rw [h1, h2, add_zero, mul_zero]

/-- Truncation agreement for the `F_θ` pairing, same support cutoff as
`primeSide_eq_truncation`. PROVED. -/
theorem primeSideFtheta_eq_truncation {g : ℝ → ℝ} {L : ℝ} (hg : HasSupportIn g L)
    {N : ℕ} (hN : L < Real.log (N + 1)) :
    primeSideFtheta g = ∑ n ∈ Finset.range (N + 1),
      (Λ n / Real.sqrt n) *
        ((n : ℝ) ^ (1 / 4 : ℝ) + (n : ℝ) ^ (-(1 / 4 : ℝ))) *
          (g (Real.log n) + g (-Real.log n)) := by
  apply tsum_eq_sum
  intro n hn
  have hge : N + 1 ≤ n := by simpa [Finset.mem_range, not_lt] using hn
  have hlog : Real.log (N + 1) ≤ Real.log n := by
    have hcast : ((N + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hge
    have hpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    have h := (Real.log_le_log_iff hpos (by linarith)).mpr hcast
    simpa using h
  exact primeSideFtheta_term_eq_zero hg (lt_of_lt_of_le hN hlog)

/-- **Rung 1 for `F_θ`.** With support below `log 3`, the `F_θ` prime side is
its `p = 2` kick. PROVED (no zeros). -/
theorem primeSideFtheta_eq_kickTwoFtheta {g : ℝ → ℝ} {L : ℝ} (hg : HasSupportIn g L)
    (hL : L < Real.log 3) : primeSideFtheta g = kickTwoFtheta g := by
  have h3 : L < Real.log ((2 : ℕ) + 1) := by norm_num; exact hL
  rw [primeSideFtheta_eq_truncation hg h3]
  simp [Finset.sum_range_succ, vonMangoldt_apply_one,
    vonMangoldt_apply_prime Nat.prime_two, kickTwoFtheta]

/-- `c S ≠ c a S` when `c ≠ 0`, `S ≠ 0` and `1 < a`. PROVED. -/
theorem scaled_coeff_ne {c a S : ℝ} (hc : c ≠ 0) (hS : S ≠ 0) (ha : 1 < a) :
    c * S ≠ c * a * S := by
  intro h
  have h1 : S = a * S :=
    mul_left_cancel₀ hc (by convert h using 1; ring)
  have h2 : (1 : ℝ) * S = a * S := by simpa using h1
  exact ha.ne' (mul_right_cancel₀ hS h2).symm

/-- On rung 1, zeta's prime side and `F_θ`'s differ as soon as the `p = 2`
sample is visible. PROVED. -/
theorem primeSide_ne_primeSideFtheta_of_visible_two {g : ℝ → ℝ} {L : ℝ}
    (hg : HasSupportIn g L) (hL : L < Real.log 3)
    (hvis : g (Real.log 2) + g (-Real.log 2) ≠ 0) :
    primeSide g ≠ primeSideFtheta g := by
  rw [primeSide_eq_kickTwo hg hL, primeSideFtheta_eq_kickTwoFtheta hg hL]
  unfold kickTwo kickTwoFtheta
  exact scaled_coeff_ne (by positivity) hvis ftheta_two_coeff_gt_one

/-- An even compactly supported profile that sees `n = 2` and nothing at
`n ≥ 3`. (Smoothness is not required for the pairing identity.) -/
noncomputable def visibleTwoKick : ℝ → ℝ :=
  fun x => if |x| ≤ (Real.log 2 + Real.log 3) / 2 then (1 : ℝ) else 0

theorem visibleTwoKick_L : (Real.log 2 + Real.log 3) / 2 < Real.log 3 := by
  have : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  linarith

theorem visibleTwoKick_support :
    HasSupportIn visibleTwoKick ((Real.log 2 + Real.log 3) / 2) := by
  intro x hx
  unfold visibleTwoKick
  exact if_neg (not_le.mpr hx)

theorem visibleTwoKick_sees_two :
    visibleTwoKick (Real.log 2) + visibleTwoKick (-Real.log 2) = 2 := by
  have hlog : 0 ≤ Real.log 2 := Real.log_natCast_nonneg 2
  have hle : Real.log 2 ≤ (Real.log 2 + Real.log 3) / 2 := by
    have : Real.log 2 ≤ Real.log 3 :=
      (Real.log_le_log_iff (by norm_num) (by norm_num)).mpr (by norm_num)
    linarith
  unfold visibleTwoKick
  rw [if_pos (by rwa [abs_of_nonneg hlog]), if_pos (by rwa [abs_neg, abs_of_nonneg hlog])]
  norm_num

/-- Witness: the two pairings are unequal. PROVED. -/
theorem exists_datum_primeSide_ne_primeSideFtheta :
    ∃ g : ℝ → ℝ, ∃ L : ℝ, HasSupportIn g L ∧ L < Real.log 3 ∧
      primeSide g ≠ primeSideFtheta g := by
  refine ⟨visibleTwoKick, (Real.log 2 + Real.log 3) / 2,
    visibleTwoKick_support, visibleTwoKick_L, ?_⟩
  exact primeSide_ne_primeSideFtheta_of_visible_two visibleTwoKick_support
    visibleTwoKick_L (by rw [visibleTwoKick_sees_two]; norm_num)

/-! ## Windowed prime stratum, same distinction -/

/-- Windowed `F_θ` prime stratum: the same weights sampled at `W − log n`. -/
noncomputable def primeStratumFtheta (h : ℝ → ℝ) (W : ℝ) : ℝ :=
  ∑' n : ℕ, (Λ n / Real.sqrt n) *
    ((n : ℝ) ^ (1 / 4 : ℝ) + (n : ℝ) ^ (-(1 / 4 : ℝ))) * h (W - Real.log n)

/-- `2^{-1/2} = 1/√2`. PROVED. -/
theorem two_rpow_neg_half : (2 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt 2 := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_eq_rpow, inv_eq_one_div]

theorem vonMangoldt_zero : (vonMangoldt 0 : ℝ) = 0 := by
  rw [vonMangoldt_apply, if_neg]
  intro h
  have : (2 : ℕ) ≤ 0 := h.two_le
  exact Nat.not_succ_le_zero 1 this

/-- The indicator profile is even. PROVED. -/
theorem visibleTwoKick_even (u : ℝ) : visibleTwoKick (-u) = visibleTwoKick u := by
  unfold visibleTwoKick
  rw [abs_neg]

/-- Tail terms of the windowed zeta stratum vanish off a rung-1 support at `W = 0`. -/
theorem primeStratum_term_eq_zero_of_rung1 {h : ℝ → ℝ} {L : ℝ}
    (hh : HasSupportIn h L) (hL : L < Real.log 3) {n : ℕ} (hn : ¬ n ∈ Finset.range 3) :
    (vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) * h (0 - Real.log n) = 0 := by
  have hge : (3 : ℕ) ≤ n := by simpa [Finset.mem_range, not_lt] using hn
  have hlog : Real.log 3 ≤ Real.log n := by
    have hcast : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hge
    exact (Real.log_le_log_iff (by norm_num) (by linarith)).mpr hcast
  have : L < |0 - Real.log n| := by
    have hnn : (0 : ℝ) ≤ Real.log n := Real.log_natCast_nonneg n
    rw [zero_sub, abs_neg, abs_of_nonneg hnn]
    exact lt_of_lt_of_le hL hlog
  rw [hh _ this, mul_zero]

/-- Zeta's windowed prime stratum at `W = 0`, on an even rung-1 profile, is the
`p = 2` sample. PROVED. -/
theorem primeStratumTerm_eq_kick_of_even_rung1 {h : ℝ → ℝ} {L : ℝ}
    (hh : HasSupportIn h L) (hL : L < Real.log 3) (hev : ∀ u, h (-u) = h u) :
    primeStratumTerm h 0 = (Real.log 2 / Real.sqrt 2) * h (Real.log 2) := by
  unfold primeStratumTerm
  rw [tsum_eq_sum (fun n hn => primeStratum_term_eq_zero_of_rung1 hh hL hn)]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  rw [vonMangoldt_zero, vonMangoldt_apply_one, vonMangoldt_apply_prime Nat.prime_two]
  simp only [zero_mul, add_zero]
  rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num, two_rpow_neg_half, zero_sub,
    hev (Real.log 2)]
  ring

/-- Tail terms of the windowed `F_θ` stratum vanish off a rung-1 support at `W = 0`. -/
theorem primeStratumFtheta_tsum_term_eq_zero_of_rung1 {h : ℝ → ℝ} {L : ℝ}
    (hh : HasSupportIn h L) (hL : L < Real.log 3) {n : ℕ} (hn : ¬ n ∈ Finset.range 3) :
    (Λ n / Real.sqrt n) *
      ((n : ℝ) ^ (1 / 4 : ℝ) + (n : ℝ) ^ (-(1 / 4 : ℝ))) * h (0 - Real.log n) = 0 := by
  have hge : (3 : ℕ) ≤ n := by simpa [Finset.mem_range, not_lt] using hn
  have hlog : Real.log 3 ≤ Real.log n := by
    have hcast : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hge
    exact (Real.log_le_log_iff (by norm_num) (by linarith)).mpr hcast
  have : L < |0 - Real.log n| := by
    have hnn : (0 : ℝ) ≤ Real.log n := Real.log_natCast_nonneg n
    rw [zero_sub, abs_neg, abs_of_nonneg hnn]
    exact lt_of_lt_of_le hL hlog
  rw [hh _ this, mul_zero]

/-- The `F_θ` windowed prime stratum at `W = 0`, on an even rung-1 profile. PROVED. -/
theorem primeStratumFtheta_eq_kick_of_even_rung1 {h : ℝ → ℝ} {L : ℝ}
    (hh : HasSupportIn h L) (hL : L < Real.log 3) (hev : ∀ u, h (-u) = h u) :
    primeStratumFtheta h 0 =
      (Real.log 2 / Real.sqrt 2) *
        ((2 : ℝ) ^ (1 / 4 : ℝ) + (2 : ℝ) ^ (-(1 / 4 : ℝ))) * h (Real.log 2) := by
  unfold primeStratumFtheta
  rw [tsum_eq_sum (fun n hn => primeStratumFtheta_tsum_term_eq_zero_of_rung1 hh hL hn)]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  rw [show (Λ 0 : ℝ) = 0 from vonMangoldt_zero, vonMangoldt_apply_one,
    vonMangoldt_apply_prime Nat.prime_two]
  simp only [zero_div, zero_mul, add_zero]
  rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num, zero_sub, hev (Real.log 2)]
  ring

/-- On an even rung-1 profile with a visible `p = 2` sample, the windowed
prime strata of `ζ` and `F_θ` differ. PROVED. -/
theorem primeStratum_ne_primeStratumFtheta_of_rung1 {h : ℝ → ℝ} {L : ℝ}
    (hh : HasSupportIn h L) (hL : L < Real.log 3) (hev : ∀ u, h (-u) = h u)
    (hvis : h (Real.log 2) ≠ 0) :
    primeStratumTerm h 0 ≠ primeStratumFtheta h 0 := by
  rw [primeStratumTerm_eq_kick_of_even_rung1 hh hL hev,
    primeStratumFtheta_eq_kick_of_even_rung1 hh hL hev]
  exact scaled_coeff_ne (by positivity) hvis ftheta_two_coeff_gt_one

/-- A single numerical prime block cannot equal both `I ·` (zeta stratum)
and `I ·` (`F_θ` stratum) on the visible-two profile. This is the formal
content of the `ζ` vs `F_θ` hard test for any proposed (BT-Σ) clause BT3.
PROVED. -/
theorem cannot_match_zeta_and_ftheta_strata
    (block : (ℝ → ℝ) → ℝ → ℂ)
    (hζ : block visibleTwoKick 0 =
      Complex.I * (primeStratumTerm visibleTwoKick 0 : ℂ))
    (hF : block visibleTwoKick 0 =
      Complex.I * (primeStratumFtheta visibleTwoKick 0 : ℂ)) :
    False := by
  have hev : ∀ u, visibleTwoKick (-u) = visibleTwoKick u := visibleTwoKick_even
  have hvis : visibleTwoKick (Real.log 2) ≠ 0 := by
    have hsum := visibleTwoKick_sees_two
    rw [visibleTwoKick_even (Real.log 2)] at hsum
    nlinarith
  have hne := primeStratum_ne_primeStratumFtheta_of_rung1
    visibleTwoKick_support visibleTwoKick_L hev hvis
  have : (primeStratumTerm visibleTwoKick 0 : ℂ) =
      (primeStratumFtheta visibleTwoKick 0 : ℂ) :=
    mul_left_cancel₀ Complex.I_ne_zero (hζ.symm.trans hF)
  exact hne (Complex.ofReal_inj.mp this)

/-- `μ = W∞ − primeSide` is the registered Weil form. PROVED (`rfl`). -/
theorem mu_eq_weilForm (g : ℝ → ℝ) :
    poleTerm g + archimedeanTerm g - primeSide g = weilForm g :=
  rfl

#print axioms ftheta_two_coeff_gt_one
#print axioms scaled_coeff_ne
#print axioms primeSideFtheta_eq_kickTwoFtheta
#print axioms primeSide_ne_primeSideFtheta_of_visible_two
#print axioms exists_datum_primeSide_ne_primeSideFtheta
#print axioms primeStratumTerm_eq_kick_of_even_rung1
#print axioms primeStratumFtheta_eq_kick_of_even_rung1
#print axioms primeStratum_ne_primeStratumFtheta_of_rung1
#print axioms cannot_match_zeta_and_ftheta_strata
#print axioms mu_eq_weilForm

end GppFluxBoundLocalEuler
