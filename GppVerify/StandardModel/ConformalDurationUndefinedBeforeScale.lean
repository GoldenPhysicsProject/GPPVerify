import Mathlib.Tactic

/-!
# Before a conformal scale is chosen, timelike duration is not an invariant number

A weaker and mathematically cleaner alternative to a literally zero metric at the primordial
boundary is a conformal geometry: only the class `[g]` under

    g -> Omega^2 g

is physical.  Null cones are unchanged, but timelike proper durations scale by `|Omega|`.
Consequently, before a conformal scale is fixed, the same timelike conformal trajectory can
be assigned ANY positive proper duration by choosing a positive representative `Omega`.
There is therefore no invariant answer to "how long did the scale-free phase last?"

This captures the useful content of the phrase "eternal instant": neither an infinite nor a
zero elapsed physical time is selected until a clock/scale exists.  The stronger hypothesis
of a degenerate tetrad is handled separately in `TetradMetricOrderParameter.lean`.
-/

namespace GppConformalDurationUndefinedBeforeScale

/-- Scalar prototype of proper duration under a constant Weyl rescaling. -/
def scaledDuration (Omega tau : ℝ) : ℝ := |Omega| * tau

/-- Positive Weyl scaling multiplies the reference duration linearly. -/
theorem scaledDuration_of_pos (Omega tau : ℝ) (hO : 0 ≤ Omega) :
    scaledDuration Omega tau = Omega*tau := by
  simp [scaledDuration, abs_of_nonneg hO]

/-- Given any positive reference duration and any positive target duration, some positive
    conformal representative realizes exactly that target. -/
theorem any_positive_duration_representative
    (tau target : ℝ) (htau : 0 < tau) (htarget : 0 < target) :
    ∃ Omega : ℝ, 0 < Omega ∧ scaledDuration Omega tau = target := by
  refine ⟨target/tau, div_pos htarget htau, ?_⟩
  rw [scaledDuration_of_pos]
  · field_simp
  · exact (div_pos htarget htau).le

/-- Null duration is conformally invariant. -/
theorem null_duration_fixed (Omega : ℝ) : scaledDuration Omega 0 = 0 := by
  simp [scaledDuration]

/-- For a nonzero reference duration, two positive conformal factors which give the same
    duration are equal: once a duration standard is supplied, the scale is fixed. -/
theorem clock_fixes_positive_scale
    (Omega1 Omega2 tau : ℝ)
    (h1 : 0 ≤ Omega1) (h2 : 0 ≤ Omega2) (htau : tau ≠ 0)
    (hEq : scaledDuration Omega1 tau = scaledDuration Omega2 tau) :
    Omega1 = Omega2 := by
  rw [scaledDuration_of_pos Omega1 tau h1,
      scaledDuration_of_pos Omega2 tau h2] at hEq
  exact mul_right_cancel₀ htau hEq

end GppConformalDurationUndefinedBeforeScale
