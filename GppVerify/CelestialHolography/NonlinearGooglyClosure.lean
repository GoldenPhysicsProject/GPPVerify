import Mathlib.Tactic
import GppVerify.CelestialHolography.AmbientFourPenroseIntertwiner
import GppVerify.CelestialHolography.OnShellDualReconstruction

/-!
# Nonlinear googly closure criterion

This module isolates a precise nonlinear closure theorem without importing any
particular twistor action.  It combines two ingredients already separated elsewhere:

1. a Penrose duality square, sending a source twistor representative to a dual
   representative whose spacetime transform is orientation reversal of the source
   spacetime field;
2. an on-shell first-order reconstruction law, saying that the dual spacetime field
   is the connection/chiral datum determined by the geometry reconstructed from the
   source configuration.

Under those hypotheses, the dual twistor representative furnished by the duality
square is automatically on shell.  If the dual Penrose transform is injective on
physical/gauge classes, it is the unique on-shell dual representative.  If a right
inverse is available, it equals the explicit reconstructed dual field.

The theorem is intentionally conditional: the analytic/geometric work still required
for the GPP proposal is to construct the concrete ambient-epsilon/incidence transform
and prove the compatibility equation.  No nonlinear googly theorem is hidden here.
-/

namespace GppNonlinearGooglyClosure

open GppAmbientFourPenroseIntertwiner
open GppOnShellDualReconstruction

variable {Config Plus B Bulk Metric Gamma : Type*}

/-- Data tying a configuration-space Penrose description to its dual first-order
field.  `plusOf` extracts the source twistor datum from a nonlinear configuration.
`dualSquare` produces the dual twistor datum.  `reconstruction` records the geometric
first-order on-shell relation. -/
structure ClosureData where
  plusOf : Config → Plus
  penrosePlus : Plus → Bulk
  reverse : Bulk → Bulk
  dualize : Plus → B
  penroseB : B → Gamma
  metricOf : Config → Metric
  gammaOfMetric : Metric → Gamma
  bulkToGamma : Bulk → Gamma
  square : ∀ z,
    penroseB (dualize z) = bulkToGamma (reverse (penrosePlus z))
  nonlinearCompatibility : ∀ v,
    bulkToGamma (reverse (penrosePlus (plusOf v))) =
      gammaOfMetric (metricOf v)

namespace ClosureData

variable (C : ClosureData (Config:=Config) (Plus:=Plus) (B:=B)
    (Bulk:=Bulk) (Metric:=Metric) (Gamma:=Gamma))

/-- The reconstruction package underlying the dual first-order field. -/
def reconstruction : ReconstructionData
    (V:=Config) (Metric:=Metric) (B:=B) (Gamma:=Gamma) where
  metricOf := C.metricOf
  gammaOfMetric := C.gammaOfMetric
  penroseB := C.penroseB

/-- The incidence/duality-produced `B` representative is automatically on shell once
the Penrose square and nonlinear compatibility equation are both satisfied. -/
theorem dualize_plus_onShell (v : Config) :
    OnShell C.reconstruction v (C.dualize (C.plusOf v)) := by
  unfold OnShell reconstruction
  rw [C.square]
  exact C.nonlinearCompatibility v

/-- If the dual Penrose transform is injective on physical classes, the representative
produced by the duality square is the unique on-shell dual field at fixed geometry. -/
theorem dualize_plus_unique
    (hP : Function.Injective C.penroseB)
    (v : Config) (b : B)
    (hb : OnShell C.reconstruction v b) :
    b = C.dualize (C.plusOf v) := by
  exact onShell_B_unique C.reconstruction hP v b (C.dualize (C.plusOf v)) hb
    (C.dualize_plus_onShell v)

/-- If `penroseB` also has a right inverse, the duality-produced representative equals
the explicit first-order reconstruction from the nonlinear geometry. -/
theorem dualize_plus_eq_reconstructed
    (liftB : Gamma → B)
    (hRight : ∀ gamma, C.penroseB (liftB gamma) = gamma)
    (hP : Function.Injective C.penroseB)
    (v : Config) :
    C.dualize (C.plusOf v) = reconstructedB C.reconstruction liftB v := by
  exact onShell_B_eq_reconstructed C.reconstruction liftB hRight hP v
    (C.dualize (C.plusOf v)) (C.dualize_plus_onShell v)

/-- Consequently two candidate duality transforms satisfying the same Penrose/on-shell
conditions cannot disagree on physical classes when `penroseB` is injective. -/
theorem duality_transform_unique_onShell
    (hP : Function.Injective C.penroseB)
    (otherDual : Config → B)
    (hOther : ∀ v, OnShell C.reconstruction v (otherDual v))
    (v : Config) :
    otherDual v = C.dualize (C.plusOf v) := by
  exact C.dualize_plus_unique hP v (otherDual v) (hOther v)

end ClosureData

end GppNonlinearGooglyClosure
