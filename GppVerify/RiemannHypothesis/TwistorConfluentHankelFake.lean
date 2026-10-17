import Mathlib.Tactic

/-!
# Positive-mode arithmetic twistor: finite confluent Hankel falsifier

The rational constants below are the coefficients hₙ = (-1)^n [u^n] (f₅'/f₅)
for f₅(u) = cosh(2√u) + 5 cosh(√u). Their identification with
the analytic power series is independently reproduced with exact Fraction
formal-series division in GPPDiscovery2 (twistor_confluent_hankel_exact_falsifier.py).

This module checks only the finite rational inequalities and their explicit
negative witness. It does NOT prove RH, a positive arithmetic model,
or the analytical Loewner/Hankel equivalence.
-/

namespace GppTwistorConfluentHankelFake

private def h1 : ℚ := 13 / 48
private def h2 : ℚ := 17 / 120
private def h3 : ℚ := 6001 / 80640
private def h4 : ℚ := 56473 / 1451520
private def h5 : ℚ := 6490313 / 319334400

theorem fake_first_curvature_positive : 0 < h1 := by
  norm_num [h1]

theorem fake_consecutive_minor_positive :
    0 < h1 * h3 - h2 ^ 2 := by
  norm_num [h1, h2, h3]

theorem fake_skipped_minor_exact :
    h1 * h5 - h3 ^ 2 = -(7159067 / 214592716800 : ℚ) := by
  norm_num [h1, h3, h5]

theorem fake_skipped_minor_negative :
    h1 * h5 - h3 ^ 2 < 0 := by
  rw [fake_skipped_minor_exact]
  norm_num

theorem fake_three_by_three_det_exact :
    h1 * (h3 * h5 - h4 ^ 2)
      - h2 * (h2 * h5 - h4 * h3)
      + h3 * (h2 * h4 - h3 ^ 2)
      = -(8255485043 / 778714050723840000 : ℚ) := by
  norm_num [h1, h2, h3, h4, h5]

theorem fake_three_by_three_det_negative :
    h1 * (h3 * h5 - h4 ^ 2)
      - h2 * (h2 * h5 - h4 * h3)
      + h3 * (h2 * h4 - h3 ^ 2) < 0 := by
  rw [fake_three_by_three_det_exact]
  norm_num

theorem fake_negative_quadratic_witness :
    let x : ℚ := -(6001 / 21840)
    x ^ 2 * h1 + 2 * x * h3 + h5
      = -(7159067 / 58118860800 : ℚ) := by
  norm_num [h1, h3, h5]

end GppTwistorConfluentHankelFake
