import Mathlib.Tactic

/-!
# Horizon orientation as a branched double cover

The black-mirror radial coordinate used by Tzanavaris-Boyle-Turok has the form

    r(sigma) = 2 m [1 + (sigma/(4m))^2]
             = 2m + sigma^2/(8m),

for nonzero mass parameter `m`.  Hence the two signs `sigma` and `-sigma` represent two
lifts of the same exterior Schwarzschild radius.  The deck involution is

    D sigma = -sigma,

and the two lifts coalesce at the horizon `sigma=0`.

This is precisely the local geometry of a branched/folded double cover: away from the
horizon a base radius has two orientation lifts; at the horizon the deck involution has a
fixed point.  Any observable depending only on `r` is blind to the sheet/orientation sign.
The radial fold also has zero first derivative at the branch point, the elementary source
of the loss of invertibility in coordinates built from this folded radial variable.

The theorem is local coordinate algebra and does not identify the deck sign by itself with
the project's microscopic temporal orientation or with CPT.  It provides the geometric
carrier on which such an identification can be tested.
-/

namespace GppHorizonOrientationBranchedDoubleCover

/-- Black-mirror exterior radius in the analytic sigma coordinate. -/
def mirrorRadius (m sigma : ℝ) : ℝ :=
  2*m + sigma^2/(8*m)

/-- Sheet/orientation deck involution. -/
def sheetFlip (sigma : ℝ) : ℝ := -sigma

/-- Both sheets project to exactly the same Schwarzschild radius. -/
theorem mirrorRadius_sheetFlip (m sigma : ℝ) :
    mirrorRadius m (sheetFlip sigma) = mirrorRadius m sigma := by
  simp [mirrorRadius, sheetFlip]
  ring

/-- The only fixed point of the sheet involution is the branch/horizon coordinate. -/
theorem sheetFlip_fixed_iff (sigma : ℝ) :
    sheetFlip sigma = sigma ↔ sigma = 0 := by
  simp [sheetFlip]

/-- Away from the horizon, the two lifts are genuinely distinct. -/
theorem two_distinct_lifts_away_from_horizon (sigma : ℝ) (hs : sigma ≠ 0) :
    sheetFlip sigma ≠ sigma := by
  exact (not_congr (sheetFlip_fixed_iff sigma)).2 hs

/-- At the horizon the two lifts coalesce. -/
theorem sheets_coalesce_at_horizon : sheetFlip 0 = 0 := by
  rfl

/-- Radial distance from the horizon is a square and therefore orientation-blind. -/
theorem radius_minus_horizon (m sigma : ℝ) :
    mirrorRadius m sigma - 2*m = sigma^2/(8*m) := by
  simp [mirrorRadius]

/-- If m is positive, every point of the cover lies at or outside r=2m. -/
theorem mirrorRadius_ge_horizon (m sigma : ℝ) (hm : 0 < m) :
    2*m ≤ mirrorRadius m sigma := by
  rw [mirrorRadius]
  have hden : 0 < 8*m := mul_pos (by norm_num) hm
  have hs : 0 ≤ sigma^2 := sq_nonneg sigma
  have hq : 0 ≤ sigma^2/(8*m) := div_nonneg hs (le_of_lt hden)
  linarith

/-- Equality with the horizon occurs only at the branch point. -/
theorem mirrorRadius_eq_horizon_iff (m sigma : ℝ) (hm : 0 < m) :
    mirrorRadius m sigma = 2*m ↔ sigma = 0 := by
  rw [mirrorRadius]
  have hm0 : (8*m : ℝ) ≠ 0 := by positivity
  constructor
  · intro h
    have hs : sigma^2/(8*m) = 0 := by linarith
    have hs2 : sigma^2 = 0 := (div_eq_zero_iff).mp hs |>.1
    exact sq_eq_zero_iff.mp hs2
  · rintro rfl
    simp

/-- Algebraic first-order fold quotient: the symmetric difference of the radius vanishes
exactly, expressing zero odd/linear response under sheet exchange. -/
theorem radial_odd_difference_zero (m sigma : ℝ) :
    mirrorRadius m sigma - mirrorRadius m (-sigma) = 0 := by
  rw [mirrorRadius_sheetFlip]
  rfl

/-- Exact secant slope against the horizon: for nonzero sigma,
    `(r(sigma)-r(0))/sigma = sigma/(8m)`, which tends to zero as the branch is approached. -/
theorem horizon_secant_slope
    (m sigma : ℝ) (hm : m ≠ 0) (hs : sigma ≠ 0) :
    (mirrorRadius m sigma - mirrorRadius m 0) / sigma = sigma/(8*m) := by
  simp [mirrorRadius]
  field_simp [hm, hs]
  ring

/-- The deck-invariant base coordinate is simply sigma squared. -/
def baseSquare (sigma : ℝ) : ℝ := sigma^2

 theorem baseSquare_sheetFlip (sigma : ℝ) :
    baseSquare (sheetFlip sigma) = baseSquare sigma := by
  simp [baseSquare, sheetFlip]
  ring

/-- The fiber of the square map over a square consists exactly of the two sign lifts. -/
theorem same_square_iff_pm (sigma tau : ℝ) :
    baseSquare tau = baseSquare sigma ↔ tau = sigma ∨ tau = -sigma := by
  simp [baseSquare]
  constructor
  · intro h
    have hfac : (tau-sigma)*(tau+sigma)=0 := by
      nlinarith
    rcases mul_eq_zero.mp hfac with h1 | h2
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> ring

end GppHorizonOrientationBranchedDoubleCover
