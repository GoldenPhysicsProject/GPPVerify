/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Heart of the Cosmos / Grok)
-/
import GppVerify.RiemannHypothesis.BTSigmaCandidateC1

/-!
# (BT-Σ) local-Euler construction: skeleton

Specification: GPP-bridge `work/grok/bt-sigma-construction-spec-start-2026-11-11.md`
(commit `b71ecb7`), audited by Turbo on PR #11 (comment 6798609817, points 3, 4 and the
"next exact instruction"). Built off GPPVerify main `2e1a3ba`.

## What this file registers

1. **The valuation `ℓ²` model of the unramified Tate vector.** For a prime `p`, the
   unramified part of `L²(ℚ_p)` is modelled on valuations `v ≥ 0` with
   `ξ_p(v) = √(1 − 1/p) · p^{-v/2}` (`xi`), and `U_p` acts as the shift. With
   `q_p = p^{-1/2}` (`qp`, `qp_eq_rpow`):
   * **(E1) PROVED.** `Σ_v ξ_p(v) ξ_p(v + k) = p^{-k/2}` for every `k ≥ 0`
     (`xi_pairing`); `k = 0` is `‖ξ_p‖ = 1` (`xi_norm`), and `k < 0` is the adjoint
     (`xi_pairing_adjoint`).
   * **Unitarity fixes the centre. PROVED** (scalar form). The local scaling
     `|λ|_p^{s}` rescales the model shift by `p^{1/2 − s}`; it is norm-preserving iff
     `p^{1/2 − s} = 1` iff `s = 1/2` (`centre_forced`).

2. **(E4) PROVED.** With `L_p(s) = (1 − p^{-s})^{-1}` (`localFactor`) and
   `κ_p(s) = (log p) p^{-s} / (1 − p^{-s})` (`tateCoupling`):
   `d/ds log L_p(s) = −κ_p(s)` (`hasDerivAt_log_localFactor`), i.e.
   `κ_p(s) = −(L_p'/L_p)(s)`; at the centre `κ_p(1/2) = log p / (√p − 1)`
   (`kappa_eq_tateCoupling`). The jump `p^{-k/2} − p^{-(k+1)/2} = (√p − 1) p^{-(k+1)/2}`
   (`qp_jump`), and matching `c_{p^k} = (log p) p^{-k/2}` forces the coupling
   (`coupling_forced`).

3. **(J) PROVED, finite-cut trace form.** The multi-cut Green identity
   (`green_multi_cut`, from the merged `green_identity_interval`) telescopes the Green form
   of a piecewise-`C¹` path with vanishing outer traces to the sum of its interior trace
   jumps. If the trace jump at the cut `k log p` is the cross-term drop of the §2 test
   vector at coupling `κ_p` (the (E1) values `p^{-(k−1)/2}` before and `p^{-k/2}` after,
   `cutWeight`), the Green form is `I ·` the `(S, N)`-truncated BT3 prime stratum
   (`finiteCut_BT3`), with weights `Λ(p^k) (p^k)^{-1/2}` (`halfWeight_primePow`,
   `sum_cutWeight`).
   **Scope.** The `K ⊗ ⊕_p V_p`-valued wavefunction `ψ_{f,W}` of the spec is not built in
   Lean. That its traces have exactly these jumps is the spec's CHECKED hand computation
   (the `‖f‖²` part does not jump because `U_p` is unitary). In this file that fact is the
   hypothesis `hjump`. The domain obligation excludes `c_m² = m^{-1/2}`-type summation
   (`open_c1_full_trace_space`); only finitely many cuts occur.

4. **Guard (NC2), formal. PROVED.** `amplitude_insertion_reproduces_weights`: any
   amplitude pair with `2 Re(conj a b) = κ_p` meets the value clause of (J). So the value
   clause cannot certify provenance. This is the spec's own starting point, so (P-LOG) is
   load-bearing.

5. **Premises, named `Prop`s, not asserted.** These are the real statements the
   construction still owes. None is `True`, none is an axiom.
   * `PLogTheta`: (P-LOG) and (P-θ) as **one linked obligation** (Turbo 6798609817 §4).
     It asks for a family of genuine boundary triplets `D S N` (with Green's identity and
     surjectivity as fields) whose prime block reproduces the `(S, N)` stratum on its own
     test vectors, together with a reflection `J`, a unitary involution
     anticommuting with `T*` and acting on the test family as `W ↦ −W`. **Provenance
     clause (not typeable):** the coupling `−(L_p'/L_p)(1/2)` must come out of the vertex
     law of the extension, with `1/2` forced by `J`, not by `centre_forced` applied by
     choice. The test vectors must not carry `κ_p` in their amplitudes.
   * `PCov`: (P-COV). A unitary dilation group `S_b` with `testVec h (W + b) = S_b (testVec h W)`.
     `W` must enter through `S_W`, not through `τ_{W−u}` inside the vector.
   * `PUnit`: (P-UNIT). The unit stratum is a genuine second block whose form on test
     vectors is `−I e^{W/2} ∫ h e^{-v/2}`. With BT3 this gives
     `greenForm = I · (prime stratum − unit stratum)` (`green_testVec_of_premises`, PROVED).
   * `PLim`: (P-LIM), RH-strength. Test vectors stay uniformly bounded as `S, N` exhaust.
     No-go 2 (`two_channel_window_mass_unbounded`) obstructs this for the present
     two-channel ansatz.

No `sorry`, no `admit`, no custom axiom. `open_bt_sigma` is untouched. (BT-Σ),
(FLUX-BOUND), (SIGN), ARP, RH remain **OPEN**.

Daniel Toupin / Golden Physics Project, with AI assistance
(Heart of the Cosmos / Grok). Task and audit: Turbo.
-/

namespace GppBTSigmaLocalEuler

open Complex MeasureTheory ArithmeticFunction GppArithmeticReflection GppBTSigma GppBTSigmaC1
open scoped InnerProductSpace ContDiff

/-! ## The valuation `ℓ²` model and (E1) -/

/-- `q_p = p^{-1/2}`. -/
noncomputable def qp (p : ℕ) : ℝ := (Real.sqrt p)⁻¹

theorem cast_pos_of_one_lt {p : ℕ} (hp : 1 < p) : (0 : ℝ) < p := by
  exact_mod_cast (by omega : 0 < p)

theorem one_lt_sqrt {p : ℕ} (hp : 1 < p) : 1 < Real.sqrt p := by
  rw [Real.lt_sqrt (by norm_num)]
  simpa using (by exact_mod_cast hp : (1 : ℝ) < p)

theorem sqrt_ne_zero' {p : ℕ} (hp : 1 < p) : Real.sqrt p ≠ 0 :=
  (lt_trans zero_lt_one (one_lt_sqrt hp)).ne'

theorem qp_pos {p : ℕ} (hp : 1 < p) : 0 < qp p :=
  inv_pos.mpr (lt_trans zero_lt_one (one_lt_sqrt hp))

theorem qp_sq {p : ℕ} : qp p ^ 2 = (p : ℝ)⁻¹ := by
  unfold qp
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg p)]

theorem qp_eq_rpow (p : ℕ) : qp p = (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
  unfold qp
  rw [Real.rpow_neg (Nat.cast_nonneg p), Real.sqrt_eq_rpow]

theorem inv_lt_one' {p : ℕ} (hp : 1 < p) : (p : ℝ)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast hp)

/-- Tate's unramified vector `1_{ℤ_p}` in the valuation `ℓ²` model:
`ξ_p(v) = √(1 − 1/p) · p^{-v/2}` for `v ≥ 0`. -/
noncomputable def xi (p : ℕ) (v : ℕ) : ℝ := Real.sqrt (1 - (p : ℝ)⁻¹) * qp p ^ v

/-- **(E1).** `⟨ξ_p, U_p^k ξ_p⟩ = p^{-k/2}` for `k ≥ 0`, with `U_p` the valuation shift.
PROVED. -/
theorem xi_pairing {p : ℕ} (hp : 1 < p) (k : ℕ) :
    ∑' v : ℕ, xi p v * xi p (v + k) = qp p ^ k := by
  have h1 : 0 ≤ 1 - (p : ℝ)⁻¹ := by linarith [inv_lt_one' hp]
  have hne : 1 - (p : ℝ)⁻¹ ≠ 0 := by linarith [inv_lt_one' hp]
  have hpow : ∀ v : ℕ, ((p : ℝ)⁻¹) ^ v = (qp p ^ v) ^ 2 := by
    intro v
    rw [← qp_sq, ← pow_mul, ← pow_mul, mul_comm]
  have hterm : ∀ v : ℕ, xi p v * xi p (v + k) =
      ((1 - (p : ℝ)⁻¹) * qp p ^ k) * ((p : ℝ)⁻¹) ^ v := by
    intro v
    rw [hpow v]
    unfold xi
    rw [pow_add]
    have hs := Real.mul_self_sqrt h1
    linear_combination (qp p ^ k * (qp p ^ v) ^ 2) * hs
  rw [tsum_congr hterm, tsum_mul_left,
    tsum_geometric_of_lt_one (inv_nonneg.mpr (Nat.cast_nonneg _)) (inv_lt_one' hp)]
  rw [mul_comm (1 - (p : ℝ)⁻¹), mul_assoc, mul_inv_cancel₀ hne, mul_one]

/-- `‖ξ_p‖ = 1`: the `k = 0` case of (E1). PROVED. -/
theorem xi_norm {p : ℕ} (hp : 1 < p) : ∑' v : ℕ, xi p v * xi p v = 1 := by
  simpa using xi_pairing hp 0

/-- The `k < 0` case of (E1) is the adjoint: `⟨U_p^k ξ_p, ξ_p⟩ = p^{-k/2}`. PROVED. -/
theorem xi_pairing_adjoint {p : ℕ} (hp : 1 < p) (k : ℕ) :
    ∑' v : ℕ, xi p (v + k) * xi p v = qp p ^ k := by
  simp_rw [mul_comm (xi p (_ + k))]
  exact xi_pairing hp k

/-- **Unitarity fixes the centre** (scalar form). The local scaling `|λ|_p^{s}` rescales the
model shift by `p^{1/2 − s}`, which is norm-preserving iff `s = 1/2`. PROVED. This does not
discharge (P-θ): the obligation there is that the extension's vertex law *reads* its centre
from this unitarity (or from `J`), rather than the centre being chosen. -/
theorem centre_forced {p : ℕ} (hp : 1 < p) (s : ℝ) :
    (p : ℝ) ^ (1 / 2 - s) = 1 ↔ s = 1 / 2 := by
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  rw [Real.rpow_def_of_pos (cast_pos_of_one_lt hp), Real.exp_eq_one_iff]
  constructor
  · intro h
    have := (mul_eq_zero.mp h).resolve_left hlog.ne'
    linarith
  · intro h
    rw [h]
    simp

/-! ## (E4): the coupling is the local log-derivative at the centre -/

/-- The local Euler factor `L_p(s) = (1 − p^{-s})^{-1}`. -/
noncomputable def localFactor (p : ℕ) (s : ℝ) : ℝ := (1 - (p : ℝ) ^ (-s))⁻¹

/-- `κ_p(s) = (log p) p^{-s} / (1 − p^{-s})`. -/
noncomputable def tateCoupling (p : ℕ) (s : ℝ) : ℝ :=
  Real.log p * (p : ℝ) ^ (-s) / (1 - (p : ℝ) ^ (-s))

theorem rpow_neg_lt_one {p : ℕ} (hp : 1 < p) {s : ℝ} (hs : 0 < s) : (p : ℝ) ^ (-s) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp) (by linarith)

/-- `d/ds log(1 − p^{-s}) = κ_p(s)`. PROVED. -/
theorem hasDerivAt_log_one_sub {p : ℕ} (hp : 1 < p) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => Real.log (1 - (p : ℝ) ^ (-t))) (tateCoupling p s) s := by
  have h1 : HasDerivAt (fun t : ℝ => (p : ℝ) ^ (-t))
      ((p : ℝ) ^ (-s) * Real.log p * (-1)) s :=
    ((Real.hasStrictDerivAt_const_rpow (cast_pos_of_one_lt hp) (-s)).hasDerivAt).comp s
      (hasDerivAt_neg s)
  have h2 := h1.const_sub 1
  have hne : 1 - (p : ℝ) ^ (-s) ≠ 0 := by linarith [rpow_neg_lt_one hp hs]
  have h3 := h2.log hne
  convert h3 using 1
  unfold tateCoupling
  ring

/-- **(E4).** `d/ds log L_p(s) = −κ_p(s)`, i.e. `κ_p(s) = −(L_p'/L_p)(s)`. PROVED. -/
theorem hasDerivAt_log_localFactor {p : ℕ} (hp : 1 < p) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => Real.log (localFactor p t)) (-tateCoupling p s) s := by
  have : (fun t : ℝ => Real.log (localFactor p t)) =
      fun t : ℝ => -Real.log (1 - (p : ℝ) ^ (-t)) := by
    funext t
    simp [localFactor, Real.log_inv]
  rw [this]
  exact (hasDerivAt_log_one_sub hp hs).neg

/-- The coupling at the centre: `κ_p = log p / (√p − 1)`. -/
noncomputable def kappa (p : ℕ) : ℝ := Real.log p / (Real.sqrt p - 1)

/-- `κ_p = −(L_p'/L_p)(1/2)`. PROVED. -/
theorem kappa_eq_tateCoupling {p : ℕ} (hp : 1 < p) : kappa p = tateCoupling p (1 / 2) := by
  have hs0 := sqrt_ne_zero' hp
  have hs1 : Real.sqrt p - 1 ≠ 0 := by linarith [one_lt_sqrt hp]
  have hq : (p : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt p)⁻¹ := by rw [← qp_eq_rpow]; rfl
  unfold kappa tateCoupling
  rw [hq]
  have hd : 1 - (Real.sqrt p)⁻¹ = (Real.sqrt p - 1) / Real.sqrt p := by
    field_simp
  rw [hd]
  field_simp

theorem kappa_mul {p : ℕ} (hp : 1 < p) : kappa p * (Real.sqrt p - 1) = Real.log p := by
  have hs1 : Real.sqrt p - 1 ≠ 0 := by linarith [one_lt_sqrt hp]
  unfold kappa
  exact div_mul_cancel₀ _ hs1

/-- The jump `p^{-k/2} − p^{-(k+1)/2} = (√p − 1) p^{-(k+1)/2}`. PROVED. -/
theorem qp_jump {p : ℕ} (hp : 1 < p) (k : ℕ) :
    qp p ^ k - qp p ^ (k + 1) = (Real.sqrt p - 1) * qp p ^ (k + 1) := by
  have hq : qp p * Real.sqrt p = 1 := inv_mul_cancel₀ (sqrt_ne_zero' hp)
  rw [pow_succ]
  linear_combination (-(qp p ^ k)) * hq

/-- **Matching forces the coupling.** If a per-prime coupling `κ'` reproduces
`c_{p^{k+1}} = (log p) p^{-(k+1)/2}` at any one cut, then `κ' = κ_p`. PROVED. -/
theorem coupling_forced {p : ℕ} (hp : 1 < p) (κ' : ℝ) (k : ℕ)
    (h : κ' * (Real.sqrt p - 1) * qp p ^ (k + 1) = Real.log p * qp p ^ (k + 1)) :
    κ' = kappa p := by
  have hs1 : Real.sqrt p - 1 ≠ 0 := by linarith [one_lt_sqrt hp]
  have hq0 : qp p ^ (k + 1) ≠ 0 := pow_ne_zero _ (qp_pos hp).ne'
  have := mul_right_cancel₀ hq0 h
  exact eq_div_of_mul_eq hs1 this

/-! ## (J): finite-cut BT3 in trace form -/

/-- Cross term of the §2 test vector on the piece after `m` cuts of the `p`-channel:
`κ · p^{-m/2} · A` with `A = autocorr f (W − k log p)` (the (E1) value). -/
noncomputable def crossTerm (κ : ℝ) (p : ℕ) (A : ℝ) (m : ℕ) : ℝ := κ * qp p ^ m * A

/-- Cross-term drop across a `p`-cut. PROVED. -/
theorem crossTerm_jump {p : ℕ} (hp : 1 < p) (κ A : ℝ) (k : ℕ) :
    crossTerm κ p A k - crossTerm κ p A (k + 1) =
      κ * (Real.sqrt p - 1) * qp p ^ (k + 1) * A := by
  unfold crossTerm
  have := qp_jump hp k
  linear_combination (κ * A) * this

/-- At `κ = κ_p` the drop is exactly `(log p) p^{-(k+1)/2} A`. PROVED. -/
theorem crossTerm_jump_kappa {p : ℕ} (hp : 1 < p) (A : ℝ) (k : ℕ) :
    crossTerm (kappa p) p A k - crossTerm (kappa p) p A (k + 1) =
      Real.log p * qp p ^ (k + 1) * A := by
  rw [crossTerm_jump hp, kappa_mul hp]

/-- `Λ(p^k) (p^k)^{-1/2} = (log p) p^{-k/2}`. PROVED. -/
theorem halfWeight_primePow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    halfWeight (p ^ k) = Real.log p * qp p ^ k := by
  unfold halfWeight
  rw [vonMangoldt_apply_pow hk, vonMangoldt_apply_prime hp, qp_eq_rpow, Nat.cast_pow]
  have h0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  rw [← Real.rpow_natCast ((p : ℝ) ^ (-(1 / 2 : ℝ))) k, ← Real.rpow_mul h0,
    ← Real.rpow_natCast (p : ℝ) k, ← Real.rpow_mul h0, mul_comm (k : ℝ) (-(1 / 2 : ℝ))]

/-- Cut index of the `(S, N)` truncation: pairs `(p, k)` with `p ∈ S` prime, `k ≥ 1`,
`p^k ≤ N`. Finite, so only finitely many cuts `k log p` occur (`C1_N` setting). -/
def cutIndex (S : Finset ℕ) (N : ℕ) : Finset (ℕ × ℕ) :=
  ((S.filter Nat.Prime) ×ˢ Finset.Icc 1 N).filter (fun c => c.1 ^ c.2 ≤ N)

/-- The `(S, N)`-truncated BT3 prime stratum `Σ_{p ∈ S, p^k ≤ N} Λ(p^k)(p^k)^{-1/2} g(W − log p^k)`. -/
noncomputable def stratumSN (S : Finset ℕ) (N : ℕ) (g : ℝ → ℝ) (W : ℝ) : ℝ :=
  ∑ c ∈ cutIndex S N, halfWeight (c.1 ^ c.2) * g (W - Real.log ((c.1 ^ c.2 : ℕ) : ℝ))

/-- The trace jump that the §2 test vector produces at the cut `(p, k)`: the cross-term drop
from `p^{-(k−1)/2}` to `p^{-k/2}` at coupling `κ_p`. -/
noncomputable def cutWeight (c : ℕ × ℕ) (g : ℝ → ℝ) (W : ℝ) : ℝ :=
  crossTerm (kappa c.1) c.1 (g (W - c.2 * Real.log c.1)) (c.2 - 1) -
    crossTerm (kappa c.1) c.1 (g (W - c.2 * Real.log c.1)) c.2

theorem cutWeight_eq {S : Finset ℕ} {N : ℕ} {c : ℕ × ℕ} (hc : c ∈ cutIndex S N)
    (g : ℝ → ℝ) (W : ℝ) :
    cutWeight c g W = halfWeight (c.1 ^ c.2) * g (W - Real.log ((c.1 ^ c.2 : ℕ) : ℝ)) := by
  obtain ⟨p, k⟩ := c
  simp only [cutIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hc
  obtain ⟨⟨⟨_, hp⟩, hk1, _⟩, _⟩ := hc
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [cutWeight]
  rw [show m + 1 - 1 = m by omega, crossTerm_jump_kappa hp.one_lt,
    halfWeight_primePow hp (by omega), Nat.cast_pow, Real.log_pow]

/-- Summing the cut jumps gives the truncated stratum. PROVED. -/
theorem sum_cutWeight (S : Finset ℕ) (N : ℕ) (g : ℝ → ℝ) (W : ℝ) :
    ∑ c ∈ cutIndex S N, cutWeight c g W = stratumSN S N g W :=
  Finset.sum_congr rfl fun _ hc => cutWeight_eq hc g W

theorem telescope (e b : ℕ → ℂ) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (e j - b j) =
      e n - b 0 + ∑ j ∈ Finset.range n, (e j - b (j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

/-- The Green-form integrand of `T* = −i d/du` (as in `green_identity_interval`). -/
noncomputable def greenIntegrand (ψ : ℝ → ℂ) (t : ℝ) : ℂ :=
  inner ℂ ((-I) * deriv ψ t) (ψ t) - inner ℂ (ψ t) ((-I) * deriv ψ t)

/-- **Multi-cut Green identity, compact-support form.** For `n + 1` pieces `ψ j` on
`[x j, x (j+1)]`, each `C¹`, with vanishing outer traces, the Green form is `I` times the sum
of the `n` interior trace jumps. PROVED. -/
theorem green_multi_cut (ψ : ℕ → ℝ → ℂ) (x : ℕ → ℝ) (n : ℕ)
    (hψ : ∀ j, ContDiff ℝ 1 (ψ j)) (h0 : ψ 0 (x 0) = 0) (hn : ψ n (x (n + 1)) = 0) :
    ∑ j ∈ Finset.range (n + 1), (∫ t in x j..x (j + 1), greenIntegrand (ψ j) t) =
      I * ∑ j ∈ Finset.range n,
        (inner ℂ (ψ j (x (j + 1))) (ψ j (x (j + 1))) -
          inner ℂ (ψ (j + 1) (x (j + 1))) (ψ (j + 1) (x (j + 1)))) := by
  simp only [greenIntegrand]
  rw [Finset.sum_congr rfl (fun j _ =>
    green_identity_interval (ψ j) (ψ j) (x j) (x (j + 1)) (hψ j) (hψ j)), ← Finset.mul_sum]
  congr 1
  have ht := telescope (fun j => inner ℂ (ψ j (x (j + 1))) (ψ j (x (j + 1))))
    (fun j => inner ℂ (ψ j (x j)) (ψ j (x j))) n
  rw [ht, hn, h0]
  simp only [inner_zero_left, sub_self, zero_add]

/-- **(J) Finite-cut BT3 for the `(S, N)` truncation.** Let the `n` interior cuts be
enumerated by `σ : Fin n ≃ cutIndex S N`. If the trace jump at each cut is the §2 cross-term
drop at coupling `κ_p` (`hjump`, the spec's CHECKED trace computation from (E1) and unitarity
of `U_p`), then the Green form of the piecewise path is `I ·` the truncated prime stratum.
PROVED. -/
theorem finiteCut_BT3 (S : Finset ℕ) (N : ℕ) (g : ℝ → ℝ) (W : ℝ) (n : ℕ)
    (σ : Fin n ≃ (cutIndex S N)) (ψ : ℕ → ℝ → ℂ) (x : ℕ → ℝ)
    (hψ : ∀ j, ContDiff ℝ 1 (ψ j)) (h0 : ψ 0 (x 0) = 0) (hn : ψ n (x (n + 1)) = 0)
    (hjump : ∀ j : Fin n,
      inner ℂ (ψ j (x (j + 1))) (ψ j (x (j + 1))) -
        inner ℂ (ψ (j + 1) (x (j + 1))) (ψ (j + 1) (x (j + 1))) =
      ((cutWeight (σ j) g W : ℝ) : ℂ)) :
    ∑ j ∈ Finset.range (n + 1), (∫ t in x j..x (j + 1), greenIntegrand (ψ j) t) =
      I * (stratumSN S N g W : ℂ) := by
  rw [green_multi_cut ψ x n hψ h0 hn]
  congr 1
  rw [Finset.sum_range (fun j =>
    inner ℂ (ψ j (x (j + 1))) (ψ j (x (j + 1))) -
      inner ℂ (ψ (j + 1) (x (j + 1))) (ψ (j + 1) (x (j + 1))))]
  trans ∑ i : Fin n, ((cutWeight (σ i) g W : ℝ) : ℂ)
  · exact Finset.sum_congr rfl (fun j _ => hjump j)
  rw [Equiv.sum_comp σ (fun c => ((cutWeight (c : ℕ × ℕ) g W : ℝ) : ℂ)),
    Finset.sum_coe_sort (cutIndex S N) (fun c => ((cutWeight c g W : ℝ) : ℂ)),
    ← Complex.ofReal_sum, sum_cutWeight]

/-! ## Guard (NC2): the value clause is met by amplitude insertion -/

/-- **Guard.** Any amplitude pair `(a, b)` with `2 Re(conj a b) = κ_p`, put into the test
vector, reproduces every cut weight `c_{p^{k+1}}`. So the value clause of (J) holds for the
spec's own starting point, where `κ_p` is inserted, not produced. It therefore cannot
certify (NC2) provenance, and (P-LOG) is load-bearing. PROVED. -/
theorem amplitude_insertion_reproduces_weights {p : ℕ} (hp : 1 < p) (v : ℂ × ℂ)
    (hv : channelQ v = kappa p) (A : ℝ) (k : ℕ) :
    crossTerm (channelQ v) p A k - crossTerm (channelQ v) p A (k + 1) =
      Real.log p * qp p ^ (k + 1) * A := by
  rw [hv, crossTerm_jump_kappa hp]

/-! ## Premises still owed: (P-LOG)/(P-θ), (P-COV), (P-UNIT), (P-LIM) -/

section Premises

variable {H Gu Gp : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup Gu] [InnerProductSpace ℂ Gu]
  [NormedAddCommGroup Gp] [InnerProductSpace ℂ Gp]

/-- Finite-cut BT3 for a genuine boundary triplet `D`: on test data the prime block is
`I ·` the `(S, N)`-truncated stratum. Compare `BTSigmaTrace` (all cuts). -/
def BTSigmaTraceSN (D : BTSigmaDatum H Gu Gp) (S : Finset ℕ) (N : ℕ) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ∀ W : ℝ, 0 ≤ W →
    primeBlock D (autocorr f) W = I * (stratumSN S N (autocorr f) W : ℂ)

/-- **(P-LOG) and (P-θ), one linked obligation. GAP / OPEN, named, not asserted.** A family of
genuine boundary triplets `D S N` for the finite-cut operator (Green's identity and
surjectivity are fields of `BTSigmaDatum`) such that:
1. its prime block reproduces the `(S, N)` stratum on its own test vectors
   (`BTSigmaTraceSN`), and
2. a reflection `J`, a unitary involution with `T* J = −J T*` on the domain, acts on the test
   family as `W ↦ −W` (the BT1 reflection whose fixed point is the centre).

**Provenance clause, not typeable here; it is the audited content.** The coupling
`κ_p = −(L_p'/L_p)(1/2)` (`kappa_eq_tateCoupling`) must be produced by the vertex law of the
extension, with `1/2` forced by `J` and not chosen. The test vectors `testVec` must not carry
`κ_p` in their amplitudes. `amplitude_insertion_reproduces_weights` shows that the value
clause alone is met by insertion. -/
def PLogTheta (D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp) (J : H ≃ₗᵢ[ℂ] H) : Prop :=
  (∀ S N, BTSigmaTraceSN (D S N) S N) ∧
  (∀ x : H, J (J x) = x) ∧
  (∀ S N (x : (D S N).Tstar.domain), ∃ y : (D S N).Tstar.domain,
      (y : H) = J x ∧ (D S N).Tstar y = -J ((D S N).Tstar x)) ∧
  (∀ S N (h : ℝ → ℝ) (W : ℝ),
      (((D S N).testVec h (-W) : (D S N).Tstar.domain) : H) = J ((D S N).testVec h W))

/-- **(P-COV). OPEN, named, not asserted.** A strongly additive unitary dilation group `S_b` on
`H` that moves the window edge: `testVec h (W + b) = S_b (testVec h W)`. `W` must enter
through `S_W`, not through `τ_{W−u}` inside the test vector, as it does in the spec's
starting point. -/
def PCov (D : BTSigmaDatum H Gu Gp) (Sd : ℝ → H ≃ₗᵢ[ℂ] H) : Prop :=
  (∀ a b : ℝ, ∀ x : H, Sd (a + b) x = Sd a (Sd b x)) ∧
  (∀ (h : ℝ → ℝ) (W b : ℝ), ((D.testVec h (W + b) : D.Tstar.domain) : H) =
      Sd b (D.testVec h W))

/-- The unit-stratum block of the boundary form on a test vector. -/
noncomputable def unitBlock (D : BTSigmaDatum H Gu Gp) (h : ℝ → ℝ) (W : ℝ) : ℂ :=
  blockForm (D.Γ₀u (D.testVec h W)) (D.Γ₁u (D.testVec h W))
    (D.Γ₀u (D.testVec h W)) (D.Γ₁u (D.testVec h W))

/-- **(P-UNIT). OPEN, named, not asserted.** The unit stratum `ℂ²_∂` is a genuine second
block. On test data its form is `−I · e^{W/2} ∫ h e^{-v/2}`, the pole term that a cutoff `χ`
does not supply. -/
def PUnit (D : BTSigmaDatum H Gu Gp) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ∀ W : ℝ, 0 ≤ W →
    unitBlock D (autocorr f) W = -(I * (unitStratumTerm (autocorr f) W : ℂ))

/-- With finite-cut BT3 and (P-UNIT), the Green form on test vectors is
`I · (truncated prime stratum − unit stratum)`, the `(S, N)` flux defect. PROVED. -/
theorem green_testVec_of_premises (D : BTSigmaDatum H Gu Gp) (S : Finset ℕ) (N : ℕ)
    (hP : BTSigmaTraceSN D S N) (hU : PUnit D)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (W : ℝ) (hW : 0 ≤ W) :
    greenForm D.Tstar (D.testVec (autocorr f) W) (D.testVec (autocorr f) W) =
      I * ((stratumSN S N (autocorr f) W - unitStratumTerm (autocorr f) W : ℝ) : ℂ) := by
  rw [D.green]
  show unitBlock D (autocorr f) W + primeBlock D (autocorr f) W = _
  rw [hU f hf hc W hW, hP f hf hc W hW]
  push_cast
  ring

/-- **(P-LIM). OPEN, RH-strength, named, not asserted.** As `S, N` exhaust, the test vectors
stay uniformly bounded in `H`. For the spec's two-channel ansatz this fails: the norm grows like
`Σ_{p ∈ S} κ_p`, and no-go 2 (`two_channel_window_mass_unbounded`) obstructs it. With
`green_testVec_of_premises`, the limit is `FluxBound` (round 3 R5). -/
def PLim (D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ∀ W : ℝ, 0 ≤ W →
    ∃ C : ℝ, ∀ S N, ‖(((D S N).testVec (autocorr f) W : (D S N).Tstar.domain) : H)‖ ≤ C

end Premises

end GppBTSigmaLocalEuler
