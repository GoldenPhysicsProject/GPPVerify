import Mathlib.Tactic
import GppVerify.CelestialHolography.GrassmannianGooglyDecomposition
import GppVerify.CelestialHolography.TwistorAnnihilatorIncidence

/-!
# Epsilon duality is the canonical annihilator map on Gr(2,4)

A volume form on a four-dimensional vector space canonically identifies

  Λ²V -> Λ²V*,

because the exterior degree is the middle degree.  It does NOT identify `V` with `V*`.

In an oriented basis, the induced dual Plucker coordinates are

  (p01,p02,p03,p12,p13,p23)
    -> (p23,-p13,p12,p03,-p02,p01).

The legacy function `pluckerStar` already has exactly this coordinate formula.  When its
codomain is correctly regarded as dual Plucker space, it is epsilon dualization rather
than a metric Hodge star.

For a graph plane `[I|A]`, the result is exactly the Plucker vector of the annihilator
plane `W^0 subset V*`.  This gives the metric-free canonical bridge

  D_epsilon,2 = D_annihilator : Gr(2,V) -> Gr(2,V*).

A Hodge-star endomorphism of `Λ²V` is obtained only after separately identifying `V*`
with `V` using a metric or other polarity.
-/

namespace GppEpsilonAnnihilatorDuality

open GppGrassmannianGooglyDecomposition
open GppTwistorAnnihilatorIncidence

/-- Epsilon dual Plucker coordinates, explicitly tagged by name as a cross-space map.
The coordinate tuple is represented by the same `P6` carrier type for convenience; its
semantic codomain is `Λ²V*`. -/
def epsilonDualPlucker (p : P6) : P6 :=
  ⟨p.p23,-p.p13,p.p12,p.p03,-p.p02,p.p01⟩

/-- The legacy `pluckerStar` coordinate formula is exactly epsilon dualization. -/
theorem epsilonDualPlucker_eq_pluckerStar (p : P6) :
    epsilonDualPlucker p = pluckerStar p := by
  rfl

/-- Epsilon dualization is involutive after identifying the double dual coordinate
carrier in the canonical finite-dimensional way. -/
theorem epsilonDualPlucker_sq (p : P6) :
    epsilonDualPlucker (epsilonDualPlucker p) = p := by
  rw [epsilonDualPlucker_eq_pluckerStar,
      epsilonDualPlucker_eq_pluckerStar,
      pluckerStar_sq]

/-- Plucker coordinates of the annihilator plane spanned by
`(-a,-c,1,0)` and `(-b,-d,0,1)`. -/
def annihilatorPlucker (a b c d : ℝ) : P6 :=
  ⟨a*d-b*c,b,-a,d,-c,1⟩

/-- Direct determinant calculation of the annihilator-plane Plucker coordinates. -/
theorem annihilatorPlucker_from_basis (a b c d : ℝ) :
    annihilatorPlucker a b c d =
      ⟨(-a)*(-d)-(-c)*(-b),
        (-a)*0-1*(-b),
        (-a)*1-0*(-b),
        (-c)*0-1*(-d),
        (-c)*1-0*(-d),
        1*1-0*0⟩ := by
  apply P6.ext <;> simp [annihilatorPlucker] <;> ring

/-- Main metric-free bridge: epsilon dual of the graph-plane Plucker vector is exactly
the annihilator-plane Plucker vector. -/
theorem epsilonDual_chart_eq_annihilatorPlucker (a b c d : ℝ) :
    epsilonDualPlucker (chartPlucker (a,b,c,d)) =
      annihilatorPlucker a b c d := by
  apply P6.ext <;> simp [epsilonDualPlucker, chartPlucker,
    annihilatorPlucker, det2] <;> ring

/-- The annihilator Plucker vector is itself Klein-null, as every decomposable two-plane
must be. -/
theorem annihilatorPlucker_klein_null (a b c d : ℝ) :
    kleinQ (annihilatorPlucker a b c d) = 0 := by
  simp [annihilatorPlucker, kleinQ]
  ring

/-- Epsilon dualization preserves the Klein quadratic value. -/
theorem kleinQ_epsilonDual (p : P6) :
    kleinQ (epsilonDualPlucker p) = kleinQ p := by
  rw [epsilonDualPlucker_eq_pluckerStar]
  exact kleinQ_pluckerStar p

/-- Applying the canonical annihilator duality twice returns the original graph Plucker
point at the coordinate level, without ever choosing a metric on `V`. -/
theorem annihilator_duality_round_trip (a b c d : ℝ) :
    epsilonDualPlucker (epsilonDualPlucker (chartPlucker (a,b,c,d))) =
      chartPlucker (a,b,c,d) := by
  exact epsilonDualPlucker_sq (chartPlucker (a,b,c,d))

end GppEpsilonAnnihilatorDuality
