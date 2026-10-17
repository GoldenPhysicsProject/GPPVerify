import Mathlib.Tactic

/-!
# Virasoro / W₁₊∞ chiral-orientation central sewing

A pair of chiral sectors with individually NONZERO positive central
charges may have a centerless *glued* symmetry if the opposite
orientation carries mode n -> -n and c_left = c_right.

Only polynomial universal Virasoro cocycle algebra is formalized here.
The construction of actual celestial OPEs and the true W₁₊∞ quantum
vertex-algebra representation is NOT provided. Neither a vanishing
net anomaly nor the wedge central term proves RH.
-/

namespace GppWInfinityCentralSewing

/-- Virasoro central polynomial for integer mode n. -/
def central (c : ℝ) (n : ℤ) : ℝ :=
  c / 12 * ((n : ℝ) ^ 3 - (n : ℝ))

/-- The anti-oriented right sector changes the sign of the cocycle.
The conserved glued current has anomaly proportional to cL - cR. -/
theorem opposite_chiral_central (cL cR : ℝ) (n : ℤ) :
    central cL n + central cR (-n) = central (cL - cR) n := by
  simp only [central]
  push_cast
  ring

/-- Equal, even strictly positive, chiral central charges yield a
zero central term for opposite-orientation diagonal sewing. -/
theorem equal_chiral_anomaly_cancels (c : ℝ) (n : ℤ) :
    central c n + central c (-n) = 0 := by
  rw [opposite_chiral_central]
  simp [central]

/-- The Virasoro global wedge never detects the quantum central charge. -/
theorem central_wedge_neg_one (c : ℝ) :
    central c (-1 : ℤ) = 0 := by norm_num [central]

theorem central_wedge_zero (c : ℝ) :
    central c (0 : ℤ) = 0 := by norm_num [central]

theorem central_wedge_one (c : ℝ) :
    central c (1 : ℤ) = 0 := by norm_num [central]

/-- The first mode that can detect a central extension. -/
theorem central_mode_two (c : ℝ) :
    central c (2 : ℤ) = c / 2 := by norm_num [central]

/-- In a standard unitary Virasoro vacuum representation the squared
norm of the stress tensor state is c/2 (external CFT input).
This algebraic statement is the *consequence* if that formula holds. -/
theorem positive_chiral_stress_norm (c : ℝ) (hc : 0 < c) :
    0 < c / 2 := by linarith

/-- The glued anomaly vanishes at mode 2 with equal c despite
each individual mode-2 central term remaining positive. -/
theorem nontrivial_positive_anomaly_free_pair (c : ℝ) (hc : 0 < c) :
    0 < central c (2 : ℤ) ∧
    central c (2 : ℤ) + central c (-2 : ℤ) = 0 := by
  constructor
  · rw [central_mode_two]
    linarith
  · exact equal_chiral_anomaly_cancels c 2

end GppWInfinityCentralSewing
