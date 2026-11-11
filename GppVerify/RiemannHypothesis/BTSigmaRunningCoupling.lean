/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Heart of the Cosmos / Grok)
-/
import GppVerify.RiemannHypothesis.BTSigmaLocalEuler
import GppVerify.RiemannHypothesis.BTSigmaEulerSkeleton

/-!
# (BT-Σ) running coupling: real-analysis core

Specification: GPP-bridge `work/grok/running-coupling-plog-2026-11-11.md` (commit `bdc74dc`, §6),
Daniel Toupin's running-coupling ("ribosome") proposal for (P-LOG). Audited by Turbo on PR #11
(comment 6800516412: items 1–5 stand; register with conditions (a) and (b)).

## PROVED here

* **Running coupling.** `runG μ = μ/(e^{μ/2} − 1)` with `runG (log p) = κ_p`
  (`runG_log_eq_kappa`).
* **Riccati.** The occupation `runN = (e^{μ/2} − 1)⁻¹` obeys `n' = −n(n+1)/2`
  (`hasDerivAt_runN`), and `runG = μ · runN` (`runG_eq_mul_runN`).
* **Beta function.** `μ g' = g − g(g + μ)/2` (`runG_beta`, `runG_betaLaw`), and the
  occupation is logistic with rate `1/2` (`runG_logisticRate_half`).
* **Tail charge.** `tailCharge p k N` is the finite sum of
  `Λ(p^j)(p^j)^{-1/2}` over `k < j ≤ N`. Each cut drops it by exactly the next weight
  (`tail_charge_jump`). Closed form `κ_p (p^{-k/2} − p^{-(k+n)/2})` (`tailCharge_closed`),
  ratio `p^{-1/2}` per cut (`tailCharge_succ_ratio`), infinite tail `κ_p p^{-k/2}`
  (`tailCharge_hasSum`). The cut identity is `GppBTSigmaEuler.kappa_cut_jump`, imported from
  the merged `BTSigmaEulerSkeleton` (#566); Turbo 6800991395 §4(a) lifted the standalone
  condition, so no duplicate is kept here.
* **F_θ separation, local.** `runGTheta μ = μ/(e^{μ/4} − 1) + μ/(e^{3μ/4} − 1)` breaks the
  beta law at `μ = log 2` (`runGTheta_not_beta`, interval bounds). Values (mpmath, 30 digits):
  `G = runGTheta (log 2) ≈ 4.680084507606 = κ^θ_2`, actual `G' ≈ −0.885277407536`, beta-law value
  `(G − G(G + μ)/2)/μ ≈ −11.387920060206`, divided gap `≈ 10.502642652670`; undivided residual
  `μ G' − (G − G(G + μ)/2) = μ · (divided gap) ≈ 7.279877143127` (the "≈ 7.28" of earlier drafts).
* **Commutator, function level.** `[u, U_a] = a U_a` pointwise (`comm_pos_shift`).

## Named premises (OPEN), provisional statements pending Turbo's approval

`RunCommutatorCore` (domain on `K ⊗ ⊕_p V_p`, GAP), `RunCentre` (≡ (P-θ)),
`RunCriticalDamping` (CONJECTURE form of (P-θ)). `PLog_of_run` is not registered.

No `sorry`, no `admit`, no custom axiom. (P-θ), (P-LIM) ⇔ (FLUX-BOUND), (SPEC), (BT-Σ), ARP and
RH remain **OPEN**.

Daniel Toupin / Golden Physics Project (running-coupling and ribosome proposal), with AI
assistance (Heart of the Cosmos / Grok). Task and audit: Turbo.
-/

namespace GppBTSigmaRunning

open GppBTSigmaLocalEuler GppBTSigmaC1 ArithmeticFunction

/-- The running coupling `g(μ) = μ/(e^{μ/2} − 1) = 2 B(μ/2)`. -/
noncomputable def runG (μ : ℝ) : ℝ := μ / (Real.exp (μ / 2) - 1)

/-- The occupation `n(μ) = g(μ)/μ = (e^{μ/2} − 1)⁻¹`. -/
noncomputable def runN (μ : ℝ) : ℝ := (Real.exp (μ / 2) - 1)⁻¹

/-- `e^{μ/2} ≠ 1` for `μ ≠ 0`. PROVED. -/
theorem exp_half_sub_one_ne_zero {μ : ℝ} (hμ : μ ≠ 0) : Real.exp (μ / 2) - 1 ≠ 0 := by
  intro h
  have : Real.exp (μ / 2) = 1 := by linarith
  rw [Real.exp_eq_one_iff] at this
  exact hμ (by linarith)

/-- `e^{(log p)/2} = √p`. PROVED. -/
theorem exp_half_log {p : ℕ} (hp : 1 < p) : Real.exp (Real.log p / 2) = Real.sqrt p := by
  have h0 : (0 : ℝ) < p := cast_pos_of_one_lt hp
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos h0]
  ring_nf

/-- **RC1.** `g(log p) = κ_p`: one universal coupling law, read at the cut. PROVED. -/
theorem runG_log_eq_kappa {p : ℕ} (hp : 1 < p) : runG (Real.log p) = kappa p := by
  unfold runG kappa
  rw [exp_half_log hp]

/-- `g = μ · n`. PROVED. -/
theorem runG_eq_mul_runN (μ : ℝ) : runG μ = μ * runN μ := by
  unfold runG runN; rw [div_eq_mul_inv]

/-- **Riccati.** `n' = −n(n+1)/2`. PROVED. -/
theorem hasDerivAt_runN {μ : ℝ} (hμ : μ ≠ 0) :
    HasDerivAt runN (-(runN μ * (runN μ + 1)) / 2) μ := by
  have hne := exp_half_sub_one_ne_zero hμ
  have hd : HasDerivAt (fun x => Real.exp (x / 2) - 1) (Real.exp (μ / 2) * (1 / 2)) μ := by
    have := ((hasDerivAt_id μ).div_const 2).exp
    simpa using this.sub_const 1
  have h := hd.inv hne
  have hf : runN = fun x => (Real.exp (x / 2) - 1)⁻¹ := rfl
  rw [hf]
  refine h.congr_deriv ?_
  simp only
  field_simp
  ring

/-- **RC3, beta function.** `μ g' = g − g(g + μ)/2`. PROVED. -/
theorem runG_beta {μ : ℝ} (hμ : μ ≠ 0) :
    HasDerivAt runG ((runG μ - runG μ * (runG μ + μ) / 2) / μ) μ := by
  have h := (hasDerivAt_id μ).mul (hasDerivAt_runN hμ)
  have hf : runG = fun x => id x * runN x := by funext x; exact runG_eq_mul_runN x
  rw [runG_eq_mul_runN μ, hf]
  refine h.congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-! ## Tail charge, finite geometric sum -/

/-- Finite tail charge of the `p`-channel after `k` cuts, truncated at `N`. -/
noncomputable def tailCharge (p k N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico (k + 1) (N + 1), halfWeight (p ^ j)

/-- Each cut drops the tail charge by exactly the next weight. PROVED. -/
theorem tail_charge_jump (p : ℕ) {k N : ℕ} (hkN : k < N) :
    tailCharge p k N - tailCharge p (k + 1) N = halfWeight (p ^ (k + 1)) := by
  unfold tailCharge
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : k + 1 < N + 1)]
  ring

/-- Closed form of the finite tail (finite geometric sum). PROVED. -/
theorem tailCharge_closed {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∀ n : ℕ, tailCharge p k (k + n) = kappa p * (qp p ^ k - qp p ^ (k + n)) := by
  intro n
  induction n with
  | zero => simp [tailCharge]
  | succ n ih =>
    have h := tail_charge_jump p (by omega : k + n < k + n + 1)
    -- `GppBTSigmaEuler.kappa`/`qp` are the same closed forms as here (definitional).
    have hj : kappa p * (qp p ^ (k + n) - qp p ^ (k + n + 1)) =
        halfWeight (p ^ (k + n + 1)) := GppBTSigmaEuler.kappa_cut_jump hp (k + n)
    unfold tailCharge at *
    rw [← add_assoc, Finset.sum_Ico_succ_top (by omega : k + 1 ≤ k + n + 1), ih,
      ← hj]
    ring

/-- The tail value `κ_p p^{-k/2}` is multiplied by `p^{-1/2}` per cut. PROVED. -/
theorem tailCharge_succ_ratio (p k : ℕ) :
    kappa p * qp p ^ (k + 1) = qp p * (kappa p * qp p ^ k) := by ring

/-- The infinite tail is `κ_p p^{-k/2}`; `k = 0` is the Green–Kubo form of `κ_p`. PROVED. -/
theorem tailCharge_hasSum {p : ℕ} (hp : p.Prime) (k : ℕ) :
    HasSum (fun j : ℕ => halfWeight (p ^ (k + 1 + j))) (kappa p * qp p ^ k) := by
  have h1 := hp.one_lt
  have hq0 := qp_pos h1
  have hs := one_lt_sqrt h1
  have hq1 : qp p < 1 := by unfold qp; exact inv_lt_one_of_one_lt₀ hs
  have hg := (hasSum_geometric_of_lt_one hq0.le hq1).mul_left (Real.log p * qp p ^ (k + 1))
  have hf : (fun j : ℕ => halfWeight (p ^ (k + 1 + j))) =
      fun j => Real.log p * qp p ^ (k + 1) * qp p ^ j := by
    funext j
    rw [halfWeight_primePow hp (by omega), pow_add]; ring
  have hsq : qp p * Real.sqrt p = 1 := inv_mul_cancel₀ (sqrt_ne_zero' h1)
  have hne : 1 - qp p ≠ 0 := by linarith
  have hne2 : Real.sqrt p - 1 ≠ 0 := by linarith
  have hv : kappa p * qp p ^ k = Real.log p * qp p ^ (k + 1) * (1 - qp p)⁻¹ := by
    rw [show kappa p = Real.log p / (Real.sqrt p - 1) from rfl]
    field_simp
    rw [pow_succ]
    linear_combination (-(Real.log p * qp p ^ k)) * hsq
  rw [hf, hv]
  exact hg

/-! ## The F_θ coupling does not obey the beta law (at μ = log 2) -/

/-- The F_θ coupling law, read so that `runGTheta (log p) = κ^θ_p`. -/
noncomputable def runGTheta (μ : ℝ) : ℝ :=
  μ / (Real.exp (μ / 4) - 1) + μ / (Real.exp (3 * μ / 4) - 1)

/-- The beta law `μ G' = G − G(G + μ)/2` for a coupling function at `μ`. -/
def BetaLaw (G : ℝ → ℝ) (μ : ℝ) : Prop :=
  HasDerivAt G ((G μ - G μ * (G μ + μ) / 2) / μ) μ

/-- ζ's coupling obeys the beta law. PROVED. -/
theorem runG_betaLaw {μ : ℝ} (hμ : μ ≠ 0) : BetaLaw runG μ := runG_beta hμ

/-- Derivative of a single mode `μ/(e^{cμ} − 1)`. PROVED. -/
theorem hasDerivAt_mode (c μ : ℝ) (h : Real.exp (c * μ) - 1 ≠ 0) :
    HasDerivAt (fun x => x / (Real.exp (c * x) - 1))
      ((Real.exp (c * μ) - 1 - μ * (Real.exp (c * μ) * c)) / (Real.exp (c * μ) - 1) ^ 2) μ := by
  have hd : HasDerivAt (fun x => Real.exp (c * x) - 1) (Real.exp (c * μ) * c) μ := by
    have := ((hasDerivAt_id μ).const_mul c).exp
    simpa using this.sub_const 1
  have := (hasDerivAt_id μ).div hd h
  simp only [id, one_mul] at this
  exact this

/-- **F_θ breaks the beta law at `μ = log 2`.** PROVED (interval bounds:
`log 2 ∈ (0.6931471803, 0.6931471808)`, `2^{1/4} ∈ (1.1892, 1.1893)`). -/
theorem runGTheta_not_beta : ¬ BetaLaw runGTheta (Real.log 2) := by
  intro hB
  set L := Real.log 2 with hL
  set a := Real.exp (1 / 4 * L) with ha
  have hL1 := Real.log_two_gt_d9
  have hL2 := Real.log_two_lt_d9
  have ha0 : 0 < a := Real.exp_pos _
  have ha4 : a ^ 4 = 2 := by
    rw [ha, ← Real.exp_nat_mul]; push_cast
    rw [show (4 : ℝ) * (1 / 4 * L) = L by ring, hL, Real.exp_log (by norm_num)]
  have ha3 : Real.exp (3 / 4 * L) = a ^ 3 := by
    rw [ha, ← Real.exp_nat_mul]; push_cast; ring_nf
  have halo : 1.1892 < a := by
    by_contra h; push Not at h
    have : a ^ 4 ≤ 1.1892 ^ 4 := pow_le_pow_left₀ ha0.le h 4
    norm_num at this; linarith
  have hahi : a < 1.1893 := by
    by_contra h; push Not at h
    have : 1.1893 ^ 4 ≤ a ^ 4 := pow_le_pow_left₀ (by norm_num) h 4
    norm_num at this; linarith
  have hx : a - 1 ≠ 0 := by intro h; linarith
  have hy : a ^ 3 - 1 ≠ 0 := by nlinarith
  have hd1 := hasDerivAt_mode (1 / 4) L (by rw [← ha]; exact hx)
  have hd2 := hasDerivAt_mode (3 / 4) L (by rw [ha3]; exact hy)
  have hfun : runGTheta = (fun x => x / (Real.exp (1 / 4 * x) - 1)) +
      (fun x => x / (Real.exp (3 / 4 * x) - 1)) := by
    funext x; simp only [runGTheta, Pi.add_apply]; ring_nf
  have hsum := hd1.add hd2
  rw [← hfun] at hsum
  have heq := hB.unique hsum
  rw [← ha, ha3] at heq
  have hG : runGTheta L = L / (a - 1) + L / (a ^ 3 - 1) := by
    rw [hfun]; simp only [Pi.add_apply]; rw [← ha, ha3]
  rw [hG] at heq
  -- bounds on G
  have hx0 : 0 < a - 1 := by linarith
  have hy0 : 0 < a ^ 3 - 1 := by nlinarith
  have hyhi : a ^ 3 - 1 < 0.6823 := by nlinarith
  have hylo : 0.6817 < a ^ 3 - 1 := by nlinarith
  have hG1 : 3.6 < L / (a - 1) := by rw [lt_div_iff₀ hx0]; nlinarith
  have hG2 : 1 < L / (a ^ 3 - 1) := by rw [lt_div_iff₀ hy0]; nlinarith
  set G := L / (a - 1) + L / (a ^ 3 - 1) with hGdef
  have hGlo : 4.6 < G := by linarith
  -- bounds on the derivative
  have hD1 : -0.5 < (a - 1 - L * (a * (1 / 4))) / (a - 1) ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  have hD2 : -0.5 < (a ^ 3 - 1 - L * (a ^ 3 * (3 / 4))) / (a ^ 3 - 1) ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  have hL0 : 0 < L := by linarith
  have key : (G - G * (G + L) / 2) / L < -1 := by
    rw [div_lt_iff₀ hL0]; nlinarith
  linarith

/-! ## Critical damping: the occupation is logistic with rate `1/2` -/

/-- The occupation `n = G/μ` of a coupling function `G` is logistic with rate `c` at `μ`:
`n' = −c · n (1 + n)`. For `c = 1/2` this is the local (TH3) form. -/
def LogisticRate (G : ℝ → ℝ) (c μ : ℝ) : Prop :=
  HasDerivAt (fun x => G x / x) (-c * (G μ / μ) * (1 + G μ / μ)) μ

/-- ζ's running coupling is critically damped (rate `1/2`) at every `μ ≠ 0`. PROVED. -/
theorem runG_logisticRate_half {μ : ℝ} (hμ : μ ≠ 0) : LogisticRate runG (1 / 2) μ := by
  have hN := hasDerivAt_runN hμ
  have hfun : (fun x => runG x / x) =ᶠ[nhds μ] runN := by
    filter_upwards [isOpen_ne.mem_nhds hμ] with x hx
    rw [runG_eq_mul_runN]; field_simp
  have hval : runG μ / μ = runN μ := by rw [runG_eq_mul_runN]; field_simp
  unfold LogisticRate
  rw [hval]
  refine (hN.congr_of_eventuallyEq hfun).congr_deriv ?_
  ring

/-! ## The position–shift commutator, pointwise -/

/-- Translation `U_a = e^{-iaT}`, `T = −i ∂_u`: `(U_a f)(u) = f(u − a)`. -/
def shiftOp (a : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := fun u => f (u - a)

/-- Multiplication by the position `u`. -/
def posOp (f : ℝ → ℂ) : ℝ → ℂ := fun u => (u : ℂ) * f u

/-- `[u, U_a] = a U_a`, as an identity of functions (no domain is involved at this level).
PROVED. The `L²`-operator statement on `K ⊗ ⊕_p V_p`, with its domain, is part of
`RunCommutatorCore` below. -/
theorem comm_pos_shift (a : ℝ) (f : ℝ → ℂ) :
    posOp (shiftOp a f) - shiftOp a (posOp f) = fun u => (a : ℂ) * shiftOp a f u := by
  funext u
  simp only [posOp, shiftOp, Pi.sub_apply]
  push_cast
  ring

/-! ## Named premises: OPEN, provisional statements for Turbo's approval

None of these is asserted, none is `True`, none is consumed by a theorem here. The reduction
`PLog_of_run` is deliberately **not** registered (Turbo, PR #11 6800516412, condition (b)). -/

section Premises

/-- **`RunCommutatorCore`. OPEN (GAP: domain).** The operator side `s`-derivative
`P_p := [u, log L_p(½ + iT)]` supplied by a construction (`P p`) acts on the core as the cut
transport `Σ_{k ≥ 1} (log p) p^{-k/2} U_{k log p}`. Provisional statement: on bounded
profiles, pointwise. The vector-valued version on `K ⊗ ⊕_p V_p` is the GAP. -/
def RunCommutatorCore (P : ℕ → (ℝ → ℂ) → (ℝ → ℂ)) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ f : ℝ → ℂ, (∃ C, ∀ u, ‖f u‖ ≤ C) → ∀ u : ℝ,
    P p f u = ∑' k : ℕ, ((Real.log p * qp p ^ (k + 1) : ℝ) : ℂ) *
      shiftOp ((k + 1 : ℕ) * Real.log p) f u

/-- **`RunCentre`. OPEN (≡ (P-θ)).** The vertex coupling `κv` of a construction is its
operator symbol `σ p t` read at `T = 0`, forced by the operator and not chosen. -/
def RunCentre (σ : ℕ → ℝ → ℂ) (κv : ℕ → ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → (κv p : ℂ) = σ p 0

/-- **`RunCriticalDamping`. OPEN, CONJECTURE form of (P-θ) (TH3).** The vertex coupling law
`G` of a construction is critically damped at every scale. ζ's `runG` satisfies the
condition (`runG_logisticRate_half`); the conjecture is that the vertex law forces it. -/
def RunCriticalDamping (G : ℝ → ℝ) : Prop :=
  ∀ μ : ℝ, 0 < μ → LogisticRate G (1 / 2) μ

end Premises

end GppBTSigmaRunning
