import Mathlib.Tactic
import GppVerify.CelestialHolography.SturmDualityFixedPointGeometry
import GppVerify.StandardModel.OrientedComptonPhase

/-!
# Massless parabolic transport versus massive elliptic Compton clock

The common rank-two Sturm carrier has generator

  G_U(x,p) = (p,-U x),       G_U^2 = -U id.

Introduce a dimensionless mass/frequency parameter `mu` by

  U = mu^2.

Then

  G_(mu^2)^2 = -mu^2 id.

This gives a natural algebraic interpolation:

* `mu=0`: `U=0`, the generator is nilpotent/parabolic and produces the free null shear;
* after using a nonzero Compton scale to nondimensionalize so `|mu|=1`, `U=1` and the
  generator is the elliptic quarter-turn with square `-1`, i.e. the algebraic core of a
  periodic internal clock;
* the sign `mu -> -mu` is invisible to `U=mu^2`, matching the fact that mass magnitude is
  even while oriented phase/four-momentum can carry a separate sign.

This does NOT prove that the curved Penrose/NSF potential `P(k,k)` literally equals mass
squared.  Rather, it isolates the exact SL(2) normal form that a successful massless-to-
massive twistor deformation would have to realize.
-/

namespace GppMassiveSturmClockBridge

open GppAmbidextrousPenroseRayQuotients
open GppAmbitwistorSturmBidegrees
open GppSturmDualityFixedPointGeometry

/-- Dimensionless quadratic potential associated with a mass/frequency magnitude. -/
def massPotential (mu : ℂ) : ℂ := mu^2

/-- The normalized massive Sturm generator squares to minus mass-potential times identity. -/
theorem massiveSturm_square (mu : ℂ) (u : SturmState) :
    sturmGenerator (massPotential mu) (sturmGenerator (massPotential mu) u) =
      scaleSturmState (-(mu^2)) u := by
  simpa [massPotential] using Sturm_square_is_minus_potential (mu^2) u

/-- Mass-orientation sign is invisible to the quadratic Sturm potential. -/
theorem massPotential_even (mu : ℂ) : massPotential (-mu) = massPotential mu := by
  simp [massPotential]
  ring

/-- Hence the generator itself depends only on the mass magnitude squared. -/
theorem massiveSturm_orientation_even (mu : ℂ) (u : SturmState) :
    sturmGenerator (massPotential (-mu)) u = sturmGenerator (massPotential mu) u := by
  rw [massPotential_even]

/-- The massless limit is exactly the nilpotent/parabolic generator. -/
theorem massless_mu_zero_is_nilpotent (u : SturmState) :
    sturmGenerator (massPotential 0) (sturmGenerator (massPotential 0) u) = (0,0) := by
  simpa [massPotential] using Sturm_zero_sq_zero u

/-- Unit Compton normalization gives the elliptic complex-structure generator. -/
theorem unit_mass_normalization_is_epsilonTurn (u : SturmState) :
    sturmGenerator (massPotential 1) u = epsilonTurn u := by
  simpa [massPotential] using Sturm_at_plus_one_eq_epsilonTurn u

/-- Two normalized massive quarter-turns give the central spinor sign. -/
theorem unit_mass_two_steps_central_sign (u : SturmState) :
    sturmGenerator (massPotential 1) (sturmGenerator (massPotential 1) u) =
      scaleSturmState (-1) u := by
  simpa [massPotential] using Sturm_plus_one_sq_neg_id u

/-- Four normalized quarter-turns close. -/
theorem unit_mass_four_steps_close (u : SturmState) :
    sturmGenerator (massPotential 1)
      (sturmGenerator (massPotential 1)
        (sturmGenerator (massPotential 1)
          (sturmGenerator (massPotential 1) u))) = u := by
  simpa [massPotential, Sturm_at_plus_one_eq_epsilonTurn] using epsilonTurn_four u

end GppMassiveSturmClockBridge
