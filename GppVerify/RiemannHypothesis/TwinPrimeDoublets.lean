import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Twin-prime doublets: the unique `p = 5` junction and the log-scale collision symbol

Source: Codex, `research/codex/2026-10-06_twin_prime_doublet_collision_blocks.md`, §§1–3.

* `unique_junction`: if `p − 2`, `p`, `p + 2` are all prime then `p = 5` (so the gap-2 graph on primes has
  maximum degree 1 except at `5`, whose neighbours are `3` and `7`);
* `twin_log_form`: for `μ = ½ log(p(p+2))`, `h = ½ log((p+2)/p)`: `log p = μ − h`, `log (p+2) = μ + h`,
  and `h = artanh (1/(p+1))`;
* `twin_symbol`: for the doublet `a_p D_{μ−h} + a_q D_{μ+h}` with symbol `d_y(k) = 2 − 2 cos(k y)`, the
  total symbol is `2 (a_p + a_q)(1 − cos kμ cos kh) − 2 (a_p − a_q) sin kμ sin kh`;
  `twin_symbol_equal` is the equal-weight case `4a (1 − cos kμ cos kh)`.

## Checks and scope

All claims check. The note is explicit that this is a diagnostic proposal, not an RH argument: **not
formalized** are the semilocal collision operator, its odd spectral gap, and the §5 numerical test; and
the note's own caution applies — twin primes are an additive correlation while the Euler product is
multiplicative, so nothing here implies the open global gap. No RH claim.
-/

open Real

namespace GppTwinPrime

/-- **Uniqueness of the degree-2 junction.** -/
theorem unique_junction (p : ℕ) (h0 : (p - 2).Prime) (h1 : p.Prime) (h2 : (p + 2).Prime) : p = 5 := by
  have hp2 : 2 ≤ p - 2 := h0.two_le
  have hp : 4 ≤ p := by omega
  have hmod : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hmod with h | h | h
  · have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three h1).mp hd
    omega
  · have hd : 3 ∣ p + 2 := by omega
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three h2).mp hd
    omega
  · have hd : 3 ∣ p - 2 + 0 := by omega
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three h0).mp (by simpa using hd)
    omega

/-- **Log-scale doublet.** -/
theorem twin_log_form (p : ℝ) (hp : 0 < p) :
    Real.log p = 1 / 2 * Real.log (p * (p + 2)) - 1 / 2 * Real.log ((p + 2) / p) ∧
    Real.log (p + 2) = 1 / 2 * Real.log (p * (p + 2)) + 1 / 2 * Real.log ((p + 2) / p) ∧
    1 / 2 * Real.log ((p + 2) / p) = Real.artanh (1 / (p + 1)) := by
  have hq : 0 < p + 2 := by linarith
  have hp0 : p ≠ 0 := hp.ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.log_mul hp.ne' hq.ne', Real.log_div hq.ne' hp.ne']; ring
  · rw [Real.log_mul hp.ne' hq.ne', Real.log_div hq.ne' hp.ne']; ring
  · have hm : (1 / (p + 1) : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor
      · have : 0 < 1 / (p + 1) := by positivity
        linarith
      · rw [div_le_one (by linarith)]; linarith
    rw [Real.artanh_eq_half_log hm]
    have hp1 : p + 1 ≠ 0 := by linarith
    have hr : (1 + 1 / (p + 1)) / (1 - 1 / (p + 1)) = (p + 2) / p := by
      have hne : 1 - 1 / (p + 1) ≠ 0 := by
        have e : 1 - 1 / (p + 1) = p / (p + 1) := by field_simp; ring
        rw [e]; positivity
      rw [div_eq_div_iff hne hp0]
      field_simp
      ring
    rw [hr]

/-- **Collision symbol of a twin doublet.** -/
theorem twin_symbol (ap aq k μ h : ℝ) :
    ap * (2 - 2 * Real.cos (k * (μ - h))) + aq * (2 - 2 * Real.cos (k * (μ + h))) =
      2 * (ap + aq) * (1 - Real.cos (k * μ) * Real.cos (k * h)) -
        2 * (ap - aq) * (Real.sin (k * μ) * Real.sin (k * h)) := by
  have e1 : k * (μ - h) = k * μ - k * h := by ring
  have e2 : k * (μ + h) = k * μ + k * h := by ring
  rw [e1, e2, Real.cos_sub, Real.cos_add]
  ring

theorem twin_symbol_equal (a k μ h : ℝ) :
    a * (2 - 2 * Real.cos (k * (μ - h))) + a * (2 - 2 * Real.cos (k * (μ + h))) =
      4 * a * (1 - Real.cos (k * μ) * Real.cos (k * h)) := by
  rw [twin_symbol]; ring

end GppTwinPrime
