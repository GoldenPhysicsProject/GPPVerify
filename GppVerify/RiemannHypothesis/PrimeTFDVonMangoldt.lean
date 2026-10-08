import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The von Mangoldt half-density weight as a cross-sheet TFD correlator

Source: Codex's note `research/codex/2026-10-01_arithmetic_orientation_tfd_susy_heat_synthesis.md`, §2 and §4.

For a prime `p` put `q = p⁻¹` and take the canonical purification of the critical Gibbs state of
`H_p = (log p) N_p`: the diagonal vector `Ω_p = √(1−q) Σ_n q^{n/2} |n,n⟩`. This file proves, with the
amplitudes `a_n = √(1−q) q^{n/2}`:

* `amp_norm`: `Σ_n a_n² = 1` (so `Ω_p` is a unit vector);
* `tfd_correlator`: for every `m ≥ 0`, `⟨Ω_p, (S^m ⊗ S^m) Ω_p⟩ = Σ_n a_n a_{n+m} = p^{-m/2}`;
* `weight_eq`: `(log p) · p^{-m/2} = Λ(p^m)/√(p^m)` for `m ≥ 1` — the von Mangoldt half-density weight
  of the explicit formula is the modular-energy-weighted cross-sheet correlator;
* `rindler_amplitude`: with `ω_p = log p/(2π)`, the bosonic Rindler/TFD amplitude `e^{-π ω_p n}` equals
  `p^{-n/2}`.

## Scope

Exact identities for one prime. The tensor-shift is expressed through the amplitude sequence (the
diagonal inner product), not an operator on a constructed `ℓ²(ℕ)⊗ℓ²(ℕ)`. That the Rindler normalisation is
physically meaningful, and the global assembly into the explicit formula, are not claimed. No RH claim.
-/

open Real Filter Topology ArithmeticFunction

namespace GppPrimeTFD

/-- `q = p⁻¹`. -/
noncomputable def q (p : ℕ) : ℝ := (p : ℝ)⁻¹

/-- The amplitude `a_n = √(1−q) q^{n/2}`. -/
noncomputable def amp (p : ℕ) (n : ℕ) : ℝ := Real.sqrt (1 - q p) * Real.sqrt (q p) ^ n

lemma q_pos {p : ℕ} (hp : p.Prime) : 0 < q p := by
  unfold q; exact inv_pos.mpr (by exact_mod_cast hp.pos)

lemma q_lt_one {p : ℕ} (hp : p.Prime) : q p < 1 := by
  unfold q
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

lemma amp_sq {p : ℕ} (hp : p.Prime) (n : ℕ) : amp p n ^ 2 = (1 - q p) * q p ^ n := by
  have h0 := q_pos hp
  have h1 := q_lt_one hp
  unfold amp
  rw [mul_pow, Real.sq_sqrt (by linarith), ← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt h0.le]

theorem amp_norm {p : ℕ} (hp : p.Prime) : HasSum (fun n => amp p n ^ 2) 1 := by
  have h0 := q_pos hp
  have h1 := q_lt_one hp
  have hg := hasSum_geometric_of_lt_one h0.le h1
  have := hg.mul_left (1 - q p)
  have e : (1 - q p) * (1 - q p)⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
  rw [e] at this
  simpa [amp_sq hp] using this

lemma amp_mul {p : ℕ} (hp : p.Prime) (n m : ℕ) :
    amp p n * amp p (n + m) = (1 - q p) * q p ^ n * Real.sqrt (q p) ^ m := by
  have h0 := q_pos hp
  have h1 := q_lt_one hp
  have hs : Real.sqrt (1 - q p) * Real.sqrt (1 - q p) = 1 - q p := Real.mul_self_sqrt (by linarith)
  have hq : Real.sqrt (q p) * Real.sqrt (q p) = q p := Real.mul_self_sqrt h0.le
  unfold amp
  calc Real.sqrt (1 - q p) * Real.sqrt (q p) ^ n * (Real.sqrt (1 - q p) * Real.sqrt (q p) ^ (n + m))
      = (Real.sqrt (1 - q p) * Real.sqrt (1 - q p)) * ((Real.sqrt (q p) * Real.sqrt (q p)) ^ n) *
          Real.sqrt (q p) ^ m := by ring
    _ = _ := by rw [hs, hq]

theorem tfd_correlator {p : ℕ} (hp : p.Prime) (m : ℕ) :
    HasSum (fun n => amp p n * amp p (n + m)) ((Real.sqrt p)⁻¹ ^ m) := by
  have h0 := q_pos hp
  have h1 := q_lt_one hp
  have hg := hasSum_geometric_of_lt_one h0.le h1
  have := (hg.mul_left (1 - q p)).mul_right (Real.sqrt (q p) ^ m)
  have e : (1 - q p) * (1 - q p)⁻¹ * Real.sqrt (q p) ^ m = (Real.sqrt p)⁻¹ ^ m := by
    rw [mul_inv_cancel₀ (by linarith), one_mul]
    unfold q; rw [Real.sqrt_inv]
  rw [e] at this
  have hfun : (fun n => amp p n * amp p (n + m)) =
      fun i => (1 - q p) * q p ^ i * Real.sqrt (q p) ^ m := funext fun n => amp_mul hp n m
  rw [hfun]; exact this

/-- **The von Mangoldt half-density weight is the modular-energy-weighted correlator:**
`(log p)·p^{-m/2} = Λ(p^m)/√(p^m)` for `m ≥ 1`. -/
theorem weight_eq {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : m ≠ 0) :
    Real.log p * (Real.sqrt p)⁻¹ ^ m = (Λ (p ^ m)) / Real.sqrt ((p : ℝ) ^ m) := by
  have hsq : Real.sqrt ((p : ℝ) ^ m) = Real.sqrt p ^ m := by
    induction m with
    | zero => simp
    | succ k ih =>
      by_cases hk : k = 0
      · subst hk; simp
      · rw [pow_succ, Real.sqrt_mul (by positivity), ih hk, pow_succ]
  rw [vonMangoldt_apply_pow hm, vonMangoldt_apply_prime hp, hsq, inv_pow, div_eq_mul_inv]

/-- **Rindler normalisation:** with `ω_p = log p/(2π)`, `e^{-π ω_p n} = p^{-n/2}`. -/
theorem rindler_amplitude {p : ℕ} (hp : p.Prime) (n : ℕ) :
    Real.exp (-Real.pi * (Real.log p / (2 * Real.pi)) * n) = (Real.sqrt p)⁻¹ ^ n := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have e1 : -Real.pi * (Real.log p / (2 * Real.pi)) * n = -(n * (Real.log p / 2)) := by
    field_simp
  have e2 : Real.sqrt p = Real.exp (Real.log p / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp0]; congr 1; ring
  rw [e1, Real.exp_neg, Real.exp_nat_mul, e2, inv_pow]

end GppPrimeTFD
