import Mathlib.Tactic

/-!
# Schwarzschild horizon orientation diagnostics

This module isolates exact, low-level statements relevant to the Shadow horizon
programme without assuming the proposed boundary-annihilation mechanism.

The key distinction is between:

* a limiting speed measured by the family of static exterior observers;
* the invariant degeneration of the stationary Killing field at the horizon;
* the future/past null branches of the maximally extended Schwarzschild horizon.

A static observer does not exist on the horizon itself, so `v -> 1` in that family
must not be used as an invariant annihilation trigger.  The invariant candidate is
instead the null condition for the horizon generator / stationary Killing field.

The Kruskal `(U,V)` statements below describe the eternal maximally extended
solution.  They do not assert that an astrophysical collapse spacetime contains a
past white-hole horizon.  Any identification of the two branches in the Shadow
framework is additional physics.
-/

namespace GppHorizonOrientationDiagnostics

/-- Schwarzschild lapse factor in units `c = 1`, with horizon radius `rs`. -/
def lapse (rs r : ℝ) : ℝ := 1 - rs / r

/-- Squared local speed of a geodesic dropped from rest at infinity, as measured by
an exterior static Schwarzschild observer: `v_static^2 = rs/r`.

This is only an exterior-frame diagnostic.  The static observer family becomes null
in the horizon limit and has no timelike member at `r = rs`. -/
def staticFrameSpeedSq (rs r : ℝ) : ℝ := rs / r

/-- Squared norm of the stationary Killing vector `K = ∂_t` in the Schwarzschild
exterior convention `(-,+,+,+)`: `g(K,K) = -(1-rs/r)`. -/
def killingNorm (rs r : ℝ) : ℝ := - lapse rs r

/-- The exterior static-frame speed tends algebraically to the light value at the
horizon radius.  This equality is a limiting diagnostic, not the velocity measured by
an observer sitting on the horizon. -/
theorem staticFrameSpeedSq_at_horizon (rs : ℝ) (hrs : rs ≠ 0) :
    staticFrameSpeedSq rs rs = 1 := by
  simp [staticFrameSpeedSq, hrs]

/-- The stationary Killing field is exactly null at the Schwarzschild horizon. -/
theorem killingNorm_at_horizon (rs : ℝ) (hrs : rs ≠ 0) :
    killingNorm rs rs = 0 := by
  simp [killingNorm, lapse, hrs]

/-- Outside the horizon the stationary Killing vector is timelike. -/
theorem killingNorm_negative_outside
    {rs r : ℝ} (hrs : 0 < rs) (hr : rs < r) :
    killingNorm rs r < 0 := by
  have hr0 : 0 < r := lt_trans hrs hr
  have hratio : rs / r < 1 := (div_lt_one hr0).2 hr
  dsimp [killingNorm, lapse]
  linarith

/-- Inside the Schwarzschild radius (for positive `r`) the same stationary Killing
vector is spacelike. -/
theorem killingNorm_positive_inside
    {rs r : ℝ} (hr : 0 < r) (hin : r < rs) :
    0 < killingNorm rs r := by
  have hratio : 1 < rs / r := (one_lt_div hr).2 hin
  dsimp [killingNorm, lapse]
  linarith

/-- Ingoing Painleve-Gullstrand / river coordinates, the radial coordinate speed of
an outgoing null ray has the standard form `1 - sqrt(rs/r)` in units `c=1`. -/
def outgoingNullRiverSpeed (rs r : ℝ) : ℝ := 1 - Real.sqrt (rs / r)

/-- An outgoing horizon generator has zero radial coordinate speed in the river
chart.  Therefore a classical outgoing photon *exactly on* the event horizon does not
move to larger Schwarzschild radius; it generates the horizon. -/
theorem outgoingNullRiverSpeed_at_horizon (rs : ℝ) (hrs : rs ≠ 0) :
    outgoingNullRiverSpeed rs rs = 0 := by
  simp [outgoingNullRiverSpeed, hrs]

/-! ## Kruskal branch structure

For the maximally extended Schwarzschild geometry, `r=rs` is the union of two null
branches.  In conventional Kruskal coordinates they are `U=0` (future black-hole
horizon) and `V=0` (past white-hole horizon).  Their intersection is the bifurcation
surface (with the angular `S^2` factors suppressed here).
-/

def onFutureHorizon (U V : ℝ) : Prop := U = 0

def onPastHorizon (U V : ℝ) : Prop := V = 0

def onBifurcationSurface (U V : ℝ) : Prop := U = 0 ∧ V = 0

/-- Future and past horizon branches meet exactly at the suppressed-coordinate
bifurcation surface. -/
theorem future_past_intersection_iff_bifurcation (U V : ℝ) :
    (onFutureHorizon U V ∧ onPastHorizon U V) ↔ onBifurcationSurface U V := by
  rfl

/-- The diagonal reversal `(U,V) -> (-U,-V)` preserves the union of the two horizon
branches.  This is a coordinate symmetry statement only; it is not identified here
with physical CPT. -/
theorem diagonal_sign_preserves_horizon_union (U V : ℝ) :
    (onFutureHorizon (-U) (-V) ∨ onPastHorizon (-U) (-V)) ↔
      (onFutureHorizon U V ∨ onPastHorizon U V) := by
  simp [onFutureHorizon, onPastHorizon]

/-- The bifurcation surface is fixed by diagonal sign reversal. -/
theorem diagonal_sign_fixes_bifurcation (U V : ℝ) :
    onBifurcationSurface (-U) (-V) ↔ onBifurcationSurface U V := by
  simp [onBifurcationSurface]

end GppHorizonOrientationDiagnostics
