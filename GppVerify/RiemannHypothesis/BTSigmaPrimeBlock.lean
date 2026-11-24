/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Heart of the Cosmos / Grok)
-/
import GppVerify.RiemannHypothesis.BTSigmaLocalEuler
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# (P-LOG): the prime-block coupling from the local Tate scaling, not fitted

Tasking: Turbo on GPP-bridge PR #11, comment 6810320113 (spec relayed by Daniel), audited in
6810448537; cross-audit shape 6811534302. Built off GPPVerify main `9242027`.

## Model (the four audit corrections)

1. **Measure.** The local Tate integral is the *multiplicative* one,
   `Z_p(f, s) = ∫ f(x) |x|_p^s d^×x` with `vol(ℤ_p^×) = 1`. On the unramified vector
   `f = 1_{ℤ_p}` it decomposes over the shells `p^k ℤ_p^×` (`k ≥ 0`), each of volume `1`, on
   which `|x|_p^s = (p^{-s})^k`. So `Z_p(1_{ℤ_p}, s) = Σ_{k≥0} (p^{-s})^k` (`shellZ`), and that
   is the in-tree `localFactor p s = (1 − p^{-s})^{-1}` (`hasSum_shellZ`). No additive Haar.
2. **Codomain.** `log|x|_p = −k log p` on shell `k`. That is unbounded, so `1_{ℤ_p} · log|·|_p`
   is not Schwartz. The scaled integral is therefore not typed through `SchwartzMap`: it is
   *defined* by its absolutely convergent shell series
   `Σ_{k≥0} (−k log p) (p^{-s})^k` (`shellJump`).
3. **Order of attack.** `local_scaling_trace_critical` is proved directly from the shell
   series. The unramified sector of `tate_scaling_is_deriv` is proved too, as an honest
   `HasDerivAt` with no differentiation under the integral sign (`shell_scaling_is_deriv`).
4. **Side condition.** `Z_p(1_{ℤ_p}, 1/2) = √p/(√p − 1) > 0` (`shellZ_half`, `shellZ_half_pos`).

## PROVED here

* `hasSum_shellZ`, `hasSum_shellJump`: closed forms of both shell series for `s > 0`.
* `shell_scaling_is_deriv`: `d/ds Z_p(1_{ℤ_p}, s) = Z_p(1_{ℤ_p} · log|·|_p, s)` for `s > 0`.
* `local_scaling_trace_critical`: `Z_p(1_{ℤ_p} log|·|_p, 1/2) / Z_p(1_{ℤ_p}, 1/2) = −κ_p`.
* `primeBlockJump_unramified_recovers_kappa`: `J_p = −κ_p · Z_p(1_{ℤ_p}, 1/2)`, plus `ℂ` forms.
* **Rewiring.** `derivedKappa p := −J_p / Z_p(1/2)` is built from the two shell series alone,
  with no κ input. `cutWeightDerived` is the finite-cut prime block at the derived coupling.
  `finiteCut_BT3_derived` re-verifies finite-cut BT3 with it: the Green form is
  `I · stratumSN S N g W`. `kappa` enters only as the *conclusion* `derivedKappa_eq_kappa`,
  never as an input.

## OPEN / GAP

* **GAP.** `tate_scaling_is_deriv` for a general Schwartz–Bruhat `f` on `ℚ_p` is a named
  obligation that this file does not type. It needs the multiplicative Haar measure on
  `ℚ_p^×` in Lean. Only the unramified (`1_{ℤ_p}`) sector is proved.
* The trace hypothesis `hjump` of `finiteCut_BT3` is carried unchanged into
  `finiteCut_BT3_derived`. No `BTSigmaDatum` is constructed here.
* (BT-Σ), ARP, CGC and RH remain **OPEN**.

Daniel Toupin / Golden Physics Project, with AI assistance
(Heart of the Cosmos / Grok). Task and audit: Turbo.
-/

namespace GPP.BTSigma.PrimeBlock

open Complex GppBTSigmaLocalEuler GppBTSigmaC1 ArithmeticFunction
open scoped InnerProductSpace

/-! ## The two shell series (multiplicative Tate measure, `vol ℤ_p^× = 1`) -/

/-- Shell variable `r_p(s) = p^{-s} = |p|_p^s`. -/
noncomputable def shellR (p : ℕ) (s : ℝ) : ℝ := (p : ℝ) ^ (-s)

/-- `Z_p(1_{ℤ_p}, s) = Σ_{k≥0} vol(p^k ℤ_p^×) · |p^k|_p^s = Σ_{k≥0} (p^{-s})^k`. -/
noncomputable def shellZ (p : ℕ) (s : ℝ) : ℝ := ∑' k : ℕ, shellR p s ^ k

/-- `Z_p(1_{ℤ_p} · log|·|_p, s) = Σ_{k≥0} (−k log p) (p^{-s})^k`: the local scaling operator
applied to `1_{ℤ_p}`, integrated, and defined by its shell series (correction 2). -/
noncomputable def shellJump (p : ℕ) (s : ℝ) : ℝ :=
  ∑' k : ℕ, (-(k : ℝ) * Real.log p) * shellR p s ^ k

theorem shellR_pos {p : ℕ} (hp : 1 < p) (s : ℝ) : 0 < shellR p s :=
  Real.rpow_pos_of_pos (cast_pos_of_one_lt hp) _

theorem shellR_lt_one {p : ℕ} (hp : 1 < p) {s : ℝ} (hs : 0 < s) : shellR p s < 1 :=
  rpow_neg_lt_one hp hs

theorem norm_shellR_lt_one {p : ℕ} (hp : 1 < p) {s : ℝ} (hs : 0 < s) : ‖shellR p s‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (shellR_pos hp s)]
  exact shellR_lt_one hp hs

theorem shellR_half (p : ℕ) : shellR p (1 / 2) = qp p := (qp_eq_rpow p).symm

/-- The unramified shell series is the in-tree local factor `L_p(s)`. PROVED. -/
theorem hasSum_shellZ {p : ℕ} (hp : 1 < p) {s : ℝ} (hs : 0 < s) :
    HasSum (fun k : ℕ => shellR p s ^ k) (localFactor p s) :=
  hasSum_geometric_of_lt_one (shellR_pos hp s).le (shellR_lt_one hp hs)

theorem shellZ_eq {p : ℕ} (hp : 1 < p) {s : ℝ} (hs : 0 < s) :
    shellZ p s = localFactor p s :=
  (hasSum_shellZ hp hs).tsum_eq

/-- Closed form of the scaled shell series. PROVED. -/
theorem hasSum_shellJump {p : ℕ} (hp : 1 < p) {s : ℝ} (hs : 0 < s) :
    HasSum (fun k : ℕ => (-(k : ℝ) * Real.log p) * shellR p s ^ k)
      (-Real.log p * (shellR p s / (1 - shellR p s) ^ 2)) := by
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one (norm_shellR_lt_one hp hs)).mul_left
    (-Real.log p)
  have e : (fun k : ℕ => (-(k : ℝ) * Real.log p) * shellR p s ^ k) =
      fun k : ℕ => -Real.log p * ((k : ℝ) * shellR p s ^ k) := by
    funext k
    ring
  rw [e]
  exact h

theorem shellJump_eq {p : ℕ} (hp : 1 < p) {s : ℝ} (hs : 0 < s) :
    shellJump p s = -Real.log p * (shellR p s / (1 - shellR p s) ^ 2) :=
  (hasSum_shellJump hp hs).tsum_eq

/-! ## `tate_scaling_is_deriv`, unramified sector -/

/-- **The scaling operator is `∂_s` on the unramified sector.** For `s > 0`,
`d/ds Z_p(1_{ℤ_p}, s) = Z_p(1_{ℤ_p} · log|·|_p, s)`. PROVED. -/
theorem shell_scaling_is_deriv {p : ℕ} (hp : 1 < p) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (shellZ p) (shellJump p s) s := by
  have hp0 := cast_pos_of_one_lt hp
  have hr : HasDerivAt (fun t : ℝ => shellR p t) (shellR p s * Real.log p * (-1)) s :=
    ((Real.hasStrictDerivAt_const_rpow hp0 (-s)).hasDerivAt).comp s (hasDerivAt_neg s)
  have hu : HasDerivAt (fun t : ℝ => 1 - shellR p t) (shellR p s * Real.log p) s := by
    simpa using hr.const_sub 1
  have hne : 1 - shellR p s ≠ 0 := by linarith [shellR_lt_one hp hs]
  have hinv := hu.inv hne
  have hev : (fun t : ℝ => (1 - shellR p t)⁻¹) =ᶠ[nhds s] shellZ p := by
    filter_upwards [lt_mem_nhds hs] with t ht
    rw [shellZ_eq hp ht]
    rfl
  have hv : -Real.log p * (shellR p s / (1 - shellR p s) ^ 2) =
      -(shellR p s * Real.log p) / (1 - shellR p s) ^ 2 := by ring
  rw [shellJump_eq hp hs, hv]
  exact hinv.congr_of_eventuallyEq hev.symm

/-! ## The critical value: the provenance of κ_p -/

/-- `Z_p(1_{ℤ_p}, 1/2) = √p/(√p − 1)`. PROVED. -/
theorem shellZ_half {p : ℕ} (hp : 1 < p) :
    shellZ p (1 / 2) = Real.sqrt p / (Real.sqrt p - 1) := by
  have hs0 := sqrt_ne_zero' hp
  have hs1 : Real.sqrt p - 1 ≠ 0 := by linarith [one_lt_sqrt hp]
  rw [shellZ_eq hp (by norm_num), localFactor, ← shellR, shellR_half, qp]
  have hd : 1 - (Real.sqrt p)⁻¹ = (Real.sqrt p - 1) / Real.sqrt p := by field_simp
  rw [hd, inv_div]

/-- Side condition (correction 4): `Z_p(1_{ℤ_p}, 1/2) > 0`. PROVED. -/
theorem shellZ_half_pos {p : ℕ} (hp : 1 < p) : 0 < shellZ p (1 / 2) := by
  rw [shellZ_half hp]
  exact div_pos (lt_trans zero_lt_one (one_lt_sqrt hp)) (by linarith [one_lt_sqrt hp])

/-- `J_p = Z_p(1_{ℤ_p} · log|·|_p, 1/2) = −log p · √p/(√p − 1)²`. PROVED. -/
theorem shellJump_half {p : ℕ} (hp : 1 < p) :
    shellJump p (1 / 2) = -Real.log p * (Real.sqrt p / (Real.sqrt p - 1) ^ 2) := by
  have hs0 := sqrt_ne_zero' hp
  have hs1 : Real.sqrt p - 1 ≠ 0 := by linarith [one_lt_sqrt hp]
  rw [shellJump_eq hp (by norm_num), shellR_half, qp]
  congr 1
  field_simp

/-- **`local_scaling_trace_critical`.** The local scaling trace at the centre, normalised by the
unramified Tate value, is `−κ_p`. PROVED from the shell series. -/
theorem local_scaling_trace_critical {p : ℕ} (hp : 1 < p) :
    shellJump p (1 / 2) / shellZ p (1 / 2) = -kappa p := by
  have hs0 := sqrt_ne_zero' hp
  have hs1 : Real.sqrt p - 1 ≠ 0 := by linarith [one_lt_sqrt hp]
  rw [shellJump_half hp, shellZ_half hp, kappa]
  field_simp

/-- The prime-block jump, defined by the local scaling action alone (no κ_p input). -/
noncomputable def primeBlockJump (p : ℕ) : ℝ := shellJump p (1 / 2)

/-- **`primeBlockJump_unramified_recovers_kappa`.** PROVED. -/
theorem primeBlockJump_unramified_recovers_kappa {p : ℕ} (hp : 1 < p) :
    primeBlockJump p = -kappa p * shellZ p (1 / 2) := by
  have h := local_scaling_trace_critical hp
  rw [div_eq_iff (shellZ_half_pos hp).ne'] at h
  exact h

/-- `ℂ`-valued form of `local_scaling_trace_critical`, as in the relayed skeleton. PROVED. -/
theorem local_scaling_trace_critical_complex {p : ℕ} (hp : 1 < p) :
    (primeBlockJump p : ℂ) / (shellZ p (1 / 2) : ℂ) = -(kappa p : ℂ) := by
  rw [← Complex.ofReal_div, primeBlockJump, local_scaling_trace_critical hp,
    Complex.ofReal_neg]

/-- `ℂ`-valued form of `primeBlockJump_unramified_recovers_kappa`. PROVED. -/
theorem primeBlockJump_unramified_recovers_kappa_complex {p : ℕ} (hp : 1 < p) :
    (primeBlockJump p : ℂ) = -(kappa p : ℂ) * (shellZ p (1 / 2) : ℂ) := by
  rw [primeBlockJump_unramified_recovers_kappa hp]
  push_cast
  ring

/-! ## Rewiring the finite-cut prime block to the derived coupling -/

/-- The coupling *derived* from the local Tate data: `−J_p / Z_p(1_{ℤ_p}, 1/2)`.
Built from `shellJump` and `shellZ` only; `kappa` does not appear. -/
noncomputable def derivedKappa (p : ℕ) : ℝ := -(primeBlockJump p / shellZ p (1 / 2))

/-- The derived coupling equals the tree's κ_p. This is a conclusion, not an input. PROVED. -/
theorem derivedKappa_eq_kappa {p : ℕ} (hp : 1 < p) : derivedKappa p = kappa p := by
  rw [derivedKappa, primeBlockJump, local_scaling_trace_critical hp, neg_neg]

/-- The finite-cut prime-block weight at the cut `(p, k)`, with the derived coupling in place of
the fitted κ_p: the cross-term drop from `p^{-(k−1)/2}` to `p^{-k/2}`. -/
noncomputable def cutWeightDerived (c : ℕ × ℕ) (g : ℝ → ℝ) (W : ℝ) : ℝ :=
  crossTerm (derivedKappa c.1) c.1 (g (W - c.2 * Real.log c.1)) (c.2 - 1) -
    crossTerm (derivedKappa c.1) c.1 (g (W - c.2 * Real.log c.1)) c.2

/-- On the cut index the derived weight is the tree's `cutWeight`, hence the BT3 weight
`Λ(p^k)(p^k)^{-1/2} g(W − log p^k)`. PROVED. -/
theorem cutWeightDerived_eq {S : Finset ℕ} {N : ℕ} {c : ℕ × ℕ} (hc : c ∈ cutIndex S N)
    (g : ℝ → ℝ) (W : ℝ) :
    cutWeightDerived c g W =
      halfWeight (c.1 ^ c.2) * g (W - Real.log ((c.1 ^ c.2 : ℕ) : ℝ)) := by
  have hp : c.1.Prime := by
    simp only [cutIndex, Finset.mem_filter, Finset.mem_product] at hc
    exact hc.1.1.2
  have : cutWeightDerived c g W = cutWeight c g W := by
    simp only [cutWeightDerived, cutWeight, derivedKappa_eq_kappa hp.one_lt]
  rw [this, cutWeight_eq hc]

/-- **Finite-cut BT3, rewired.** With the trace jumps given by the *derived* prime block
(`cutWeightDerived`, no fitted κ_p), the Green form of the piecewise path is
`I ·` the `(S, N)`-truncated prime stratum. PROVED. -/
theorem finiteCut_BT3_derived (S : Finset ℕ) (N : ℕ) (g : ℝ → ℝ) (W : ℝ) (n : ℕ)
    (σ : Fin n ≃ (cutIndex S N)) (ψ : ℕ → ℝ → ℂ) (x : ℕ → ℝ)
    (hψ : ∀ j, ContDiff ℝ 1 (ψ j)) (h0 : ψ 0 (x 0) = 0) (hn : ψ n (x (n + 1)) = 0)
    (hjump : ∀ j : Fin n,
      inner ℂ (ψ j (x (j + 1))) (ψ j (x (j + 1))) -
        inner ℂ (ψ (j + 1) (x (j + 1))) (ψ (j + 1) (x (j + 1))) =
      ((cutWeightDerived (σ j) g W : ℝ) : ℂ)) :
    ∑ j ∈ Finset.range (n + 1), (∫ t in x j..x (j + 1), greenIntegrand (ψ j) t) =
      I * (stratumSN S N g W : ℂ) := by
  refine finiteCut_BT3 S N g W n σ ψ x hψ h0 hn (fun j => ?_)
  rw [hjump j, cutWeightDerived_eq (σ j).2, cutWeight_eq (σ j).2]

end GPP.BTSigma.PrimeBlock
