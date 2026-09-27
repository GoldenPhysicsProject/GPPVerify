import Mathlib.Tactic

/-!
# Critical half-density resonance algebra

At the critical half-density weight, the smooth Möbius correction indexed by `n`
has continuum exponent `1/n - 3/2`, while the prime-repetition channel indexed by
`m` has exponent `-m/2`.  This file formalizes the exact algebraic resonance
condition between those two scaling degrees.

This is only a scaling identity.  It does not assert convergence, positivity, an
explicit-formula theorem, or RH.
-/

namespace GppHalfDensityResonance

/-- For nonzero real `n`, equality of the Möbius and repetition scaling exponents is
exactly the algebraic resonance equation `n * (3 - m) = 2`. -/
theorem exponent_resonance_iff {n m : ℝ} (hn : n ≠ 0) :
    1 / n - 3 / 2 = -m / 2 ↔ n * (3 - m) = 2 := by
  constructor
  · intro h
    field_simp [hn] at h
    nlinarith
  · intro h
    field_simp [hn]
    nlinarith

/-- The leading primitive channel is resonant: `(n,m) = (1,1)`. -/
theorem primitive_resonance :
    (1 : ℝ)⁻¹ - 3 / 2 = -(1 : ℝ) / 2 := by
  norm_num

/-- The prime-square channel is the nontrivial secondary resonance: `(n,m) = (2,2)`. -/
theorem square_resonance :
    (2 : ℝ)⁻¹ - 3 / 2 = -(2 : ℝ) / 2 := by
  norm_num

/-- Among positive natural-number channel labels, the resonance equation has exactly
the primitive and prime-square solutions.  This is the discrete selection statement
behind the two exceptional critical-half-density sectors. -/
theorem nat_resonance_unique {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (h : n * (3 - m) = 2) :
    (n = 1 ∧ m = 1) ∨ (n = 2 ∧ m = 2) := by
  have hn_le : n ≤ 2 := by
    exact Nat.le_of_dvd (by norm_num) ⟨3 - m, h.symm⟩
  have hm_lt : m < 3 := by
    by_contra hnot
    have h3 : 3 ≤ m := Nat.le_of_not_gt hnot
    have hz : 3 - m = 0 := Nat.sub_eq_zero_of_le h3
    rw [hz, Nat.mul_zero] at h
    norm_num at h
  have hm_le : m ≤ 2 := by omega
  interval_cases n <;> interval_cases m <;> omega

/-- Every smooth Möbius correction from `n = 3` onward has critical-half-density
power strictly below `-1`, so its continuum tail is beyond the logarithmic
integrability threshold. -/
theorem higher_mobius_exponent_lt_neg_one {n : ℕ} (hn : 3 ≤ n) :
    1 / (n : ℝ) - 3 / 2 < -1 := by
  have hn3r : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by norm_num) hn3r
  have h2n : (2 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by norm_num) hn3r
  have hfrac : (2 : ℝ) / (n : ℝ) < 1 := (div_lt_one hnpos).2 h2n
  have htwo : 2 * (1 / (n : ℝ)) < 1 := by
    rw [two_mul, one_div, ← two_mul]
    simpa [div_eq_mul_inv] using hfrac
  linarith

/-- The smooth Möbius tail has a uniform margin beyond the logarithmic threshold:
its largest post-exceptional exponent occurs at `n = 3` and equals `-7/6`. -/
theorem higher_mobius_exponent_le_neg_seven_sixths {n : ℕ} (hn : 3 ≤ n) :
    1 / (n : ℝ) - 3 / 2 ≤ -(7 : ℝ) / 6 := by
  have hn3r : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by norm_num) hn3r
  have hfrac : (1 : ℝ) / (n : ℝ) ≤ 1 / 3 := by
    rw [div_le_iff₀ hnpos]
    nlinarith
  linarith

/-- Quantitative form of the smooth-tail gap: after the exceptional sectors, the
Möbius exponent lies at least `1/6` below the logarithmic `-1` threshold. -/
theorem higher_mobius_integrability_gap_ge_one_sixth {n : ℕ} (hn : 3 ≤ n) :
    (-(1 : ℝ)) - (1 / (n : ℝ) - 3 / 2) ≥ 1 / 6 := by
  have h := higher_mobius_exponent_le_neg_seven_sixths hn
  linarith

/-- Every prime-repetition channel from `m = 3` onward also has scaling power
strictly below `-1`. -/
theorem higher_repetition_exponent_lt_neg_one {m : ℕ} (hm : 3 ≤ m) :
    -(m : ℝ) / 2 < -1 := by
  have hm3r : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  linarith

/-- The repetition tail has the sharper uniform bound `-m/2 ≤ -3/2` for `m ≥ 3`. -/
theorem higher_repetition_exponent_le_neg_three_halves {m : ℕ} (hm : 3 ≤ m) :
    -(m : ℝ) / 2 ≤ -(3 : ℝ) / 2 := by
  have hm3r : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  linarith

/-- Quantitative form of the repetition-tail gap: every `m ≥ 3` exponent lies at
least `1/2` below the logarithmic `-1` threshold. -/
theorem higher_repetition_integrability_gap_ge_one_half {m : ℕ} (hm : 3 ≤ m) :
    (-(1 : ℝ)) - (-(m : ℝ) / 2) ≥ 1 / 2 := by
  have h := higher_repetition_exponent_le_neg_three_halves hm
  linarith

end GppHalfDensityResonance

#print axioms GppHalfDensityResonance.exponent_resonance_iff
#print axioms GppHalfDensityResonance.primitive_resonance
#print axioms GppHalfDensityResonance.square_resonance
#print axioms GppHalfDensityResonance.nat_resonance_unique
#print axioms GppHalfDensityResonance.higher_mobius_exponent_lt_neg_one
#print axioms GppHalfDensityResonance.higher_mobius_exponent_le_neg_seven_sixths
#print axioms GppHalfDensityResonance.higher_mobius_integrability_gap_ge_one_sixth
#print axioms GppHalfDensityResonance.higher_repetition_exponent_lt_neg_one
#print axioms GppHalfDensityResonance.higher_repetition_exponent_le_neg_three_halves
#print axioms GppHalfDensityResonance.higher_repetition_integrability_gap_ge_one_half
