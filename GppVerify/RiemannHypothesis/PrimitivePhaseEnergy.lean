import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# After removing the primitive harmonic, the global prime phase has finite half-derivative energy

Source: Codex, GPPDiscovery2 `research/2026-09-27_primitive_renormalized_phase_half_derivative_energy.md`,
§§1–4.

For a prime `p` with `a = p^{-1/2}`, `L = log p`, the relative Euler scattering phase has Fourier
frequencies `m log p` and amplitudes `a^m / m`. Its homogeneous half-derivative energy
`E_{1/2} = Σ |λ| |c_λ|²` is, per prime, `2 L Σ_{m≥1} p^{-m}/m`.

* `freq_injective` (§1): the frequencies `m log p` are pairwise distinct (unique factorization);
* `local_energy` (§2): `Σ_{m≥1} p^{-m}/m = −log(1 − 1/p)`, so the local energy is
  `−2 (log p) log(1 − p^{-1})`;
* `tail_energy` (§4): after removing `m = 1`, `Σ_{m≥2} p^{-m}/m = −log(1 − p^{-1}) − p^{-1}`, which
  is `≤ p^{-2}` (`tail_le`);
* `summable_tail` (§4): hence `Σ_p (log p)(−log(1 − p^{-1}) − p^{-1}) < ∞`: the primitive-renormalized
  global phase has finite half-derivative energy;
* `not_summable_primitive` (§3): whereas the raw `m = 1` contribution `Σ_p (log p)/p` diverges.

So `m = 1` is the obstruction to finite `H^{1/2}` scattering-phase energy.

## Checks and scope

All claims check. **Not formalized:** the identification of the phase `log S_p` with the stated
Fourier series (the logarithm branch), the Bohr almost-periodic Hilbert-space setting, and the
`m = 1` versus `m = 2` determinant discussion of §§5–6 (a comparison with the `det₃` threshold
already in `GppVerify`). No RH claim.
-/

open Real

namespace GppPrimitivePhaseEnergy

/-- **Frequencies are distinct.** `m log p = n log q` for primes and positive `m, n` forces
`p = q` and `m = n`. -/
theorem freq_injective {p q m n : ℕ} (hp : p.Prime) (hq : q.Prime) (hm : 0 < m)
    (h : (m : ℝ) * Real.log p = (n : ℝ) * Real.log q) : p = q ∧ m = n := by
  have hpow : (p : ℝ) ^ m = (q : ℝ) ^ n := by
    have h1 : Real.log ((p : ℝ) ^ m) = Real.log ((q : ℝ) ^ n) := by
      rw [Real.log_pow, Real.log_pow]; exact h
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr (by have := hp.pos; positivity))
      (Set.mem_Ioi.mpr (by have := hq.pos; positivity)) h1
  have hnat : p ^ m = q ^ n := by exact_mod_cast hpow
  have hpq : p ∣ q := by
    have : p ∣ q ^ n := hnat ▸ dvd_pow_self p hm.ne'
    exact hp.dvd_of_dvd_pow this
  have hpeq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
  subst hpeq
  exact ⟨rfl, Nat.pow_right_injective hp.two_le hnat⟩

/-- **The local energy series.** With `x = p^{-1}`: `Σ_{m≥1} x^m/m = −log(1 − x)`. -/
theorem local_energy (x : ℝ) (hx : |x| < 1) :
    HasSum (fun m : ℕ => x ^ (m + 1) / (m + 1)) (-Real.log (1 - x)) :=
  Real.hasSum_pow_div_log_of_abs_lt_one hx

/-- **The `m ≥ 2` tail.** -/
theorem tail_energy (x : ℝ) (hx : |x| < 1) :
    HasSum (fun m : ℕ => x ^ (m + 2) / (m + 2)) (-Real.log (1 - x) - x) := by
  have h := (hasSum_nat_add_iff' 1).mpr (local_energy x hx)
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_add, pow_one,
    div_one] at h
  have e : (fun m : ℕ => x ^ (m + 2) / (m + 2)) =
      fun n : ℕ => x ^ (n + 1 + 1) / (((n + 1 : ℕ) : ℝ) + 1) := by
    funext n; push_cast; ring_nf
  rw [e]
  exact h

/-- The tail is at most `x²` for `0 ≤ x ≤ 1/2`. -/
theorem tail_le (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : -Real.log (1 - x) - x ≤ x ^ 2 := by
  have hx1 : |x| < 1 := by rw [abs_of_nonneg hx0]; linarith
  have hT := tail_energy x hx1
  have hg : HasSum (fun m : ℕ => x ^ 2 / 2 * x ^ m) (x ^ 2 / 2 * (1 - x)⁻¹) :=
    (hasSum_geometric_of_lt_one hx0 (by linarith)).mul_left (x ^ 2 / 2)
  have hle : ∀ m : ℕ, x ^ (m + 2) / (m + 2) ≤ x ^ 2 / 2 * x ^ m := by
    intro m
    have h2 : (2 : ℝ) ≤ (m : ℝ) + 2 := by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have hpos : 0 ≤ x ^ (m + 2) := pow_nonneg hx0 _
    calc x ^ (m + 2) / (m + 2) ≤ x ^ (m + 2) / 2 :=
          div_le_div_of_nonneg_left hpos (by norm_num) h2
      _ = x ^ 2 / 2 * x ^ m := by ring
  have := hasSum_le hle hT hg
  have h1x : (1 - x)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  calc -Real.log (1 - x) - x ≤ x ^ 2 / 2 * (1 - x)⁻¹ := this
    _ ≤ x ^ 2 / 2 * 2 := by
        apply mul_le_mul_of_nonneg_left h1x (by positivity)
    _ = x ^ 2 := by ring

/-- The tail is nonnegative. -/
theorem tail_nonneg (x : ℝ) (hx0 : 0 ≤ x) (hx : x < 1) : 0 ≤ -Real.log (1 - x) - x := by
  have hx1 : |x| < 1 := by rw [abs_of_nonneg hx0]; exact hx
  exact (tail_energy x hx1).nonneg fun m => by positivity

/-- **Finite energy after primitive renormalization.** -/
theorem summable_tail :
    Summable (fun p : Nat.Primes =>
      Real.log p * (-Real.log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ))) := by
  have hs : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) (hs.mul_left 2)
  · have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.prop.two_le
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have := tail_nonneg (1 / (p : ℝ)) (by positivity) (by
      rw [div_lt_one (by linarith)]; linarith)
    exact mul_nonneg hlog this
  · have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.prop.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hlog : Real.log p ≤ (p : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
      Real.log_le_rpow_div hp0.le (by norm_num)
    have htail := tail_le (1 / (p : ℝ)) (by positivity) (by
      rw [div_le_div_iff₀ hp0 (by norm_num)]; linarith)
    have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    calc Real.log p * (-Real.log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ))
        ≤ ((p : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) * (1 / (p : ℝ)) ^ 2 :=
          mul_le_mul hlog htail (by
            have := tail_nonneg (1 / (p : ℝ)) (by positivity) (by
              rw [div_lt_one hp0]; linarith)
            exact this) (by positivity)
      _ = 2 * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
          rw [show (-(3 / 2 : ℝ)) = (1 / 2 : ℝ) + (-2 : ℝ) by norm_num,
            Real.rpow_add hp0, Real.rpow_neg hp0.le, Real.rpow_two]
          field_simp

/-- **The raw primitive channel diverges.** `Σ_p (log p)/p = ∞`. -/
theorem not_summable_primitive : ¬ Summable (fun p : Nat.Primes => Real.log p / (p : ℝ)) := by
  intro h
  apply Nat.Primes.not_summable_one_div
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) (h.mul_left (3 / 2))
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.prop.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hl : (2 / 3 : ℝ) ≤ Real.log p := by
    have h2 := Real.log_two_gt_d9
    have : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp
    linarith
  calc 1 / (p : ℝ) ≤ (3 / 2 * Real.log p) / p :=
        div_le_div_of_nonneg_right (by linarith) hp0.le
    _ = 3 / 2 * (Real.log p / (p : ℝ)) := by ring

end GppPrimitivePhaseEnergy
