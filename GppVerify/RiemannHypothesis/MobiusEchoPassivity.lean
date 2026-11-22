/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude; statements from Codex / GPT, audited by Turbo)
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Möbius echo, finite-step energy and the storage/work telescope

**Conditional telescope; nothing here proves RH.** Formalization of the packet
`work/codex/2026-11-21-mobius-passivity-lean-handoff.md` (Codex, Turbo-audited statement-by-statement),
items (1)–(3). With `a(n) = μ(n)/√n`, a free real `c` (the packet's `c = 1/ζ(1/2)` is an instance;
the identities hold for every constant), `b_k = Σ_{n≤k} a(n) − c`, `B(u) = b_{⌊e^u⌋}` and
`Q(L) = ∫₀ᴸ B(u)² du`:

1. `energy_identity`: `Q(log N) = Σ_{1≤k<N} log((k+1)/k) b_k²` (`B` is the constant `b_k` on
   `[log k, log(k+1))`).
2. `a_mul_prime` (`a(pn) = −a(n)/√p` for `p ∤ n`), `a_mul_prime_dvd` (`a(pn) = 0` for `p ∣ n`) and
   `echo_phase`/`echo_gain_gt_one`: the two-impulse multiplier `1 − p^{−1/2}e^{−iω log p}` at
   `ω = π/log p` is the positive real `1 + 1/√p > 1` — the echo **amplifies** at this phase; this is the
   regression statement against any local-contraction claim.
3. `telescope`, `energy_le_work`, `sparse_energy_bound`: for arbitrary real `stor, w` with
   `stor(k+1) − stor(k) + log((k+1)/k) b_k² ≤ w(k)`, `stor(N) + Q(log N) ≤ stor(1) + Σ_{1≤k<N} w(k)`;
   with `stor ≥ 0` and `stor(1) + Σ_{k<N_j} w(k) ≤ N_j^η` eventually for every `η > 0` (any sequence
   `N_j`, no spacing assumption), `Q(log N_j) ≤ N_j^η` eventually for every `η > 0`.

**Not built (item (4)):** the RH conclusion composes `sparse_energy_bound` with the *sparse-cutoff
criterion* (`liminf_L log(1+Q(L))/L = 0 ⇒ RH`), which is **not yet formalized in Verify** (checked
2026-11-21); per the packet it is shipped separately and named in the ledger. The arithmetic storage
law with an independently subpower-bounded work sum is open; the trivial choice `stor = 0`,
`w(k) = log((k+1)/k) b_k²` only recovers the original `Q` obligation. No `sorry`, no `axiom`.
-/


open MeasureTheory Set ArithmeticFunction

namespace GppMobiusEcho

/-- `a(n) = μ(n)/√n`. -/
noncomputable def a (n : ℕ) : ℝ := (moebius n : ℝ) / Real.sqrt n

/-- Partial sum `Σ_{n ≤ k} a(n)`. -/
noncomputable def S (k : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 k, a n

/-- `b_k = Σ_{n ≤ k} a(n) − c`. -/
noncomputable def b (c : ℝ) (k : ℕ) : ℝ := S k - c

/-- `B(u) = Σ_{n ≤ e^u} a(n) − c`. -/
noncomputable def B (c : ℝ) (u : ℝ) : ℝ := b c ⌊Real.exp u⌋₊

/-- `Q(L) = ∫₀ᴸ B(u)² du`. -/
noncomputable def Q (c : ℝ) (L : ℝ) : ℝ := ∫ u in (0 : ℝ)..L, (B c u) ^ 2

theorem B_of_mem {c : ℝ} {N : ℕ} (hN : 1 ≤ N) {u : ℝ} (h1 : Real.log N ≤ u)
    (h2 : u < Real.log (N + 1)) : B c u = b c N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  unfold B
  congr 1
  rw [Nat.floor_eq_iff (Real.exp_pos u).le]
  constructor
  · calc (N : ℝ) = Real.exp (Real.log N) := (Real.exp_log hN0).symm
      _ ≤ Real.exp u := Real.exp_le_exp.mpr h1
  · calc Real.exp u < Real.exp (Real.log (N + 1)) := Real.exp_lt_exp.mpr h2
      _ = N + 1 := Real.exp_log (by positivity)

/-- Step integral: on `[log N, log (N+1)]` the square is the constant `b_N²` (a.e.). -/
theorem step_integral (c : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    IntervalIntegrable (fun u => (B c u) ^ 2) volume (Real.log N) (Real.log (N + 1)) ∧
    ∫ u in (Real.log N)..(Real.log (N + 1)), (B c u) ^ 2
      = Real.log ((N + 1 : ℝ) / N) * (b c N) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : Real.log N ≤ Real.log (N + 1) :=
    Real.log_le_log hN0 (by linarith)
  have hae : ∀ᵐ u : ℝ, u ∈ uIoc (Real.log N) (Real.log (N + 1)) → (B c u) ^ 2 = (b c N) ^ 2 := by
    have h0 : ∀ᵐ u : ℝ, u ≠ Real.log (N + 1) := by rw [ae_iff]; simp
    filter_upwards [h0] with u hu hmem
    rw [Set.uIoc_of_le hle] at hmem
    have : u < Real.log (N + 1) := lt_of_le_of_ne hmem.2 hu
    rw [B_of_mem hN hmem.1.le this]
  have hconst : IntervalIntegrable (fun _ : ℝ => (b c N) ^ 2) volume (Real.log N) (Real.log (N + 1)) :=
    intervalIntegrable_const
  refine ⟨?_, ?_⟩
  · have h1 := intervalIntegrable_iff.mp hconst
    exact intervalIntegrable_iff.mpr (h1.congr_fun_ae
      ((ae_restrict_iff' measurableSet_uIoc).mpr (hae.mono fun u hu hmem => (hu hmem).symm)))
  · rw [intervalIntegral.integral_congr_ae hae]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    rw [Real.log_div (by positivity) hN0.ne']

/-- **Finite-step energy identity.** For every real `c` and `N ≥ 1`:
`Q(log N) = Σ_{1 ≤ k < N} log((k+1)/k) · b_k²`. -/
theorem energy_identity (c : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    IntervalIntegrable (fun u => (B c u) ^ 2) volume 0 (Real.log N) ∧
    Q c (Real.log N) = ∑ k ∈ Finset.Ico 1 N, Real.log ((k + 1 : ℝ) / k) * (b c k) ^ 2 := by
  induction N, hN using Nat.le_induction with
  | base =>
    refine ⟨by simp, ?_⟩
    simp [Q]
  | succ N hN ih =>
    obtain ⟨hi, hQ⟩ := ih
    obtain ⟨hs, hv⟩ := step_integral c hN
    have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    refine ⟨hi.trans hs, ?_⟩
    unfold Q at hQ ⊢
    rw [← intervalIntegral.integral_add_adjacent_intervals hi hs, hQ, hv,
      Finset.sum_Ico_succ_top hN]

/-! ### The prime echo -/

/-- **Prime echo.** For a prime `p` with `p ∤ n`: `a(pn) = −a(n)/√p`. -/
theorem a_mul_prime {p n : ℕ} (hp : p.Prime) (hn : ¬ p ∣ n) : a (p * n) = - a n / Real.sqrt p := by
  have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hn
  have hmu : (moebius (p * n) : ℝ) = - (moebius n : ℝ) := by
    rw [isMultiplicative_moebius.map_mul_of_coprime hcop, moebius_apply_prime hp]
    push_cast; ring
  unfold a
  rw [hmu]
  push_cast
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [Real.sqrt_mul hp0.le]
  have hsp : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr hp0).ne'
  by_cases hn0 : (n : ℝ) = 0
  · simp [hn0]
  · have : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr (lt_of_le_of_ne (Nat.cast_nonneg n) (Ne.symm hn0))).ne'
    field_simp

/-- If `p ∣ n` then `μ(pn) = 0`, so `a(pn) = 0`. -/
theorem a_mul_prime_dvd {p n : ℕ} (hp : p.Prime) (hn : p ∣ n) : a (p * n) = 0 := by
  have : moebius (p * n) = 0 := by
    apply moebius_eq_zero_of_not_squarefree
    intro hsq
    obtain ⟨m, rfl⟩ := hn
    have h1 : p * p ∣ p * (p * m) := ⟨m, by ring⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsq p h1))
  simp [a, this]

/-- **Phase test.** The two-impulse multiplier `1 − p^{−1/2} e^{−iω log p}` at `ω = π / log p`
is the positive real `1 + 1/√p`: the echo amplifies at this phase (gain `> 1`). -/
theorem echo_phase {p : ℕ} (hp : p.Prime) :
    (1 : ℂ) - ((Real.sqrt p)⁻¹ : ℝ) *
        Complex.exp (-(Complex.I * ((Real.pi / Real.log p : ℝ) : ℂ) * ((Real.log p : ℝ) : ℂ)))
      = ((1 + (Real.sqrt p)⁻¹ : ℝ) : ℂ) := by
  have hlog : Real.log p ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact (Real.log_pos this).ne'
  have hlogC : ((Real.log p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog
  have : Complex.I * ((Real.pi / Real.log p : ℝ) : ℂ) * ((Real.log p : ℝ) : ℂ) = Real.pi * Complex.I := by
    rw [mul_assoc, ← Complex.ofReal_mul, div_mul_cancel₀ _ hlog, mul_comm]
  rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]
  push_cast; ring

theorem echo_gain_gt_one {p : ℕ} (hp : p.Prime) : 1 < 1 + (Real.sqrt p)⁻¹ := by
  have : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have := Real.sqrt_pos.mpr this
  linarith [inv_pos.mpr this]

/-! ### The storage/work telescope (conditional) -/

/-- **Storage/work telescope.** For arbitrary real `stor, w` with `stor(k+1) − stor(k) +
log((k+1)/k) b_k² ≤ w(k)` for `1 ≤ k < N`:
`stor(N) + Q(log N) ≤ stor(1) + Σ_{1 ≤ k < N} w(k)`.  No storage function is chosen; this is a
finite telescope plus the energy identity.  Conditional on the stated step inequality only. -/
theorem telescope (c : ℝ) (stor w : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N)
    (hstep : ∀ k, 1 ≤ k → k < N →
      stor (k + 1) - stor k + Real.log ((k + 1 : ℝ) / k) * (b c k) ^ 2 ≤ w k) :
    stor N + Q c (Real.log N) ≤ stor 1 + ∑ k ∈ Finset.Ico 1 N, w k := by
  rw [(energy_identity c hN).2]
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    have ih' := ih (fun k hk1 hk2 => hstep k hk1 (by omega))
    rw [Finset.sum_Ico_succ_top hN, Finset.sum_Ico_succ_top hN]
    have := hstep N hN (by omega)
    linarith

/-- With nonnegative storage: `Q(log N) ≤ stor(1) + Σ_{1 ≤ k < N} w(k)`. -/
theorem energy_le_work (c : ℝ) (stor w : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) (hS : 0 ≤ stor N)
    (hstep : ∀ k, 1 ≤ k → k < N →
      stor (k + 1) - stor k + Real.log ((k + 1 : ℝ) / k) * (b c k) ^ 2 ≤ w k) :
    Q c (Real.log N) ≤ stor 1 + ∑ k ∈ Finset.Ico 1 N, w k := by
  have := telescope c stor w hN hstep
  linarith

/-- **Sparse-sequence energy bound (conditional).** Let `Nj → ∞` be any sequence of naturals
`≥ 1`, `stor ≥ 0` and the step inequality hold below every `Nj`, and suppose for every `η > 0`,
eventually `A_j := stor(1) + Σ_{1 ≤ k < Nj} w(k) ≤ Nj^η`.  Then for every `η > 0`, eventually
`Q(log Nj) ≤ Nj^η`.  No spacing assumption on `Nj`. -/
theorem sparse_energy_bound (c : ℝ) (stor w : ℕ → ℝ) (Nj : ℕ → ℕ) (hN : ∀ j, 1 ≤ Nj j)
    (hS : ∀ k, 0 ≤ stor k)
    (hstep : ∀ j k, 1 ≤ k → k < Nj j →
      stor (k + 1) - stor k + Real.log ((k + 1 : ℝ) / k) * (b c k) ^ 2 ≤ w k)
    (hwork : ∀ η : ℝ, 0 < η → ∀ᶠ j in Filter.atTop,
      stor 1 + ∑ k ∈ Finset.Ico 1 (Nj j), w k ≤ (Nj j : ℝ) ^ η) :
    ∀ η : ℝ, 0 < η → ∀ᶠ j in Filter.atTop, Q c (Real.log (Nj j)) ≤ (Nj j : ℝ) ^ η := by
  intro η hη
  filter_upwards [hwork η hη] with j hj
  exact le_trans (energy_le_work c stor w (hN j) (hS _) (hstep j)) hj

end GppMobiusEcho

#print axioms GppMobiusEcho.energy_identity
#print axioms GppMobiusEcho.a_mul_prime
#print axioms GppMobiusEcho.a_mul_prime_dvd
#print axioms GppMobiusEcho.echo_phase
#print axioms GppMobiusEcho.telescope
#print axioms GppMobiusEcho.sparse_energy_bound
