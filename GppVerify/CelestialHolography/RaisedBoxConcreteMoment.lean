import GppVerify.CelestialHolography.RaisedBoxPointwiseLimit
import GppVerify.CelestialHolography.RaisedBoxSimplexMajorantAlgebra
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Concrete raised-box simplex moment

For Euclidean invariants `S,T > 0`, the raised massless scalar box in
`D = 8 - 2 epsilon` has the standard Feynman-parametric moment

  J_epsilon(S,T) = integral_{Delta_3} Q^{-epsilon},
  Q = S x1 x3 + T x2 x4,
  x4 = 1 - x1 - x2 - x3.

This file introduces that exact affine nested-interval object. The subsequent
measure layer will prove `J_epsilon -> 1/6` by dominated convergence using the
already-certified pointwise limit and one-channel majorant.
-/

namespace GppRaisedBoxConcreteMoment

open scoped Interval

/-- Fourth barycentric coordinate in affine coordinates on the standard
three-simplex. -/
def x4 (x1 x2 x3 : ℝ) : ℝ := 1 - x1 - x2 - x3

/-- Euclidean four-point Symanzik polynomial on the affine simplex. -/
def Q (S T x1 x2 x3 : ℝ) : ℝ :=
  S * x1 * x3 + T * x2 * x4 x1 x2 x3

/-- Raised-box Feynman-parametric integrand. -/
noncomputable def integrand (ε S T x1 x2 x3 : ℝ) : ℝ :=
  (Q S T x1 x2 x3) ^ (-ε : ℝ)

/-- For fixed external parameters the concrete real-power integrand is Borel
measurable in the innermost affine coordinate.  This is the measure-theoretic
input needed by the first dominated-convergence step. -/
theorem integrand_measurable_x3 (ε S T x1 x2 : ℝ) :
    Measurable (fun x3 : ℝ => integrand ε S T x1 x2 x3) := by
  unfold integrand
  apply Measurable.pow_const
  unfold Q x4
  fun_prop

/-- For fixed regulator, invariants, and outer simplex coordinate, the raised-box
integrand is jointly Borel measurable in the two inner affine coordinates.
This is the product-measure input needed to replace the variable endpoint
`x3 ≤ 1 - x1 - x2` by a measurable simplex-strip indicator and invoke Fubini. -/
theorem integrand_measurable_x2_x3 (ε S T x1 : ℝ) :
    Measurable (fun p : ℝ × ℝ => integrand ε S T x1 p.1 p.2) := by
  unfold integrand
  apply Measurable.pow_const
  unfold Q x4
  fun_prop

/-- The closed affine strip representing the two inner simplex coordinates for
fixed `x1`.  Writing the variable endpoint as a measurable set is the clean
product-measure replacement for the nested bound `0 ≤ x3 ≤ 1 - x1 - x2`. -/
def innerSimplexStrip (x1 : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1 - x1}

/-- The inner simplex strip is Borel measurable. -/
theorem measurableSet_innerSimplexStrip (x1 : ℝ) :
    MeasurableSet (innerSimplexStrip x1) := by
  unfold innerSimplexStrip
  exact
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le (measurable_fst.add measurable_snd) measurable_const)

/-- Extending the two-inner-coordinate integrand by zero off the affine simplex
strip preserves Borel measurability.  This is the exact input needed by
product-measure/Fubini lemmas such as `integral_prod_right'`. -/
theorem stripIntegrand_measurable (ε S T x1 : ℝ) :
    Measurable
      ((innerSimplexStrip x1).indicator
        (fun p : ℝ × ℝ => integrand ε S T x1 p.1 p.2)) := by
  exact (integrand_measurable_x2_x3 ε S T x1).indicator
    (measurableSet_innerSimplexStrip x1)

/-- Product integration turns the jointly measurable strip integrand into a
strongly measurable function of the remaining middle coordinate.  This is the
parameter-measurability input required by the middle dominated-convergence
step, obtained without treating the variable endpoint as a primitive. -/
theorem stripInnerIntegral_stronglyMeasurable (ε S T x1 : ℝ) :
    MeasureTheory.StronglyMeasurable
      (fun x2 : ℝ =>
        ∫ x3 : ℝ,
          ((innerSimplexStrip x1).indicator
            (fun p : ℝ × ℝ => integrand ε S T x1 p.1 p.2)) (x2, x3)) := by
  exact
    (stripIntegrand_measurable ε S T x1).stronglyMeasurable.integral_prod_right'

/-- At fixed middle coordinate `x2`, the measurable two-dimensional affine strip
is exactly the closed interval `0 ≤ x3 ≤ 1 - x1 - x2` in the innermost
coordinate.  This pointwise section identity is the bridge between the Fubini
strip representation and the original variable-endpoint interval integral. -/
theorem stripIntegrand_section_eq_Icc_indicator
    (ε S T x1 x2 x3 : ℝ) :
    ((innerSimplexStrip x1).indicator
      (fun p : ℝ × ℝ => integrand ε S T x1 p.1 p.2)) (x2, x3) =
      (Set.Icc (0 : ℝ) (1 - x1 - x2)).indicator
        (fun y : ℝ => integrand ε S T x1 x2 y) x3 := by
  by_cases hstrip : (x2, x3) ∈ innerSimplexStrip x1
  · have hstrip' : 0 ≤ x3 ∧ x2 + x3 ≤ 1 - x1 := by
      simpa [innerSimplexStrip] using hstrip
    have hx3 : x3 ∈ Set.Icc (0 : ℝ) (1 - x1 - x2) := by
      constructor
      · exact hstrip'.1
      · linarith [hstrip'.2]
    simp [Set.indicator_of_mem hstrip, Set.indicator_of_mem hx3]
  · have hx3 : x3 ∉ Set.Icc (0 : ℝ) (1 - x1 - x2) := by
      intro hx3
      apply hstrip
      have hx3' : 0 ≤ x3 ∧ x3 ≤ 1 - x1 - x2 := by
        simpa only [Set.mem_Icc] using hx3
      simp only [innerSimplexStrip, Set.mem_setOf_eq]
      constructor
      · exact hx3'.1
      · linarith [hx3'.2]
    simp [Set.indicator_of_notMem hstrip, Set.indicator_of_notMem hx3]

/-- Standard affine volume of the three-simplex, written in the same iterated
coordinates used by the physical Feynman parameter integral. -/
noncomputable def simplexVolume : ℝ :=
  ∫ x1 in (0 : ℝ)..1,
    ∫ x2 in (0 : ℝ)..(1 - x1),
      ∫ _x3 in (0 : ℝ)..(1 - x1 - x2), (1 : ℝ)

/-- Concrete raised-box simplex moment. -/
noncomputable def simplexMoment (ε S T : ℝ) : ℝ :=
  ∫ x1 in (0 : ℝ)..1,
    ∫ x2 in (0 : ℝ)..(1 - x1),
      ∫ x3 in (0 : ℝ)..(1 - x1 - x2), integrand ε S T x1 x2 x3

/-- At zero regulator the Feynman integrand is identically one, including the
boundary under Lean's totalized real-power convention. -/
@[simp] theorem integrand_zero (S T x1 x2 x3 : ℝ) :
    integrand 0 S T x1 x2 x3 = 1 := by
  simp [integrand]

/-- Therefore the zero-regulator moment is exactly the affine simplex volume. -/
theorem simplexMoment_zero (S T : ℝ) :
    simplexMoment 0 S T = simplexVolume := by
  simp [simplexMoment, simplexVolume, integrand]

/-- On a strictly interior simplex point with positive Euclidean invariants, the
Symanzik polynomial used here is exactly the positive quantity required by the
pointwise regulator theorem. -/
theorem Q_pos
    {S T x1 x2 x3 : ℝ}
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx2 : 0 < x2) (hx3 : 0 < x3)
    (hxsum : x1 + x2 + x3 < 1) :
    0 < Q S T x1 x2 x3 := by
  have hx4 : 0 < x4 x1 x2 x3 := by
    unfold x4
    linarith
  unfold Q
  positivity

/-- Pointwise regulator removal at every strictly interior simplex point. -/
theorem integrand_tendsto_one
    {S T x1 x2 x3 : ℝ}
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx2 : 0 < x2) (hx3 : 0 < x3)
    (hxsum : x1 + x2 + x3 < 1) :
    Filter.Tendsto
      (fun ε : ℝ => integrand ε S T x1 x2 x3)
      (nhds 0) (nhds 1) := by
  unfold integrand
  exact GppRaisedBoxPointwiseLimit.tendsto_neg_rpow_one
    (Q_pos hS hT hx1 hx2 hx3 hxsum)

/-- The abstract one-channel estimate specializes exactly to the concrete
Feynman-parametric integrand on the affine simplex. -/
theorem integrand_le_one_channel_majorant
    {ε δ S T x1 x2 x3 : ℝ}
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx2 : 0 ≤ x2) (hx3 : 0 < x3)
    (hxsum : x1 + x2 + x3 ≤ 1)
    (hε0 : 0 ≤ ε) (hεδ : ε ≤ δ) (hδ : 0 < δ) :
    integrand ε S T x1 x2 x3 ≤
      1 + (S * x1 * x3) ^ (-δ : ℝ) := by
  have hx4 : 0 ≤ x4 x1 x2 x3 := by
    unfold x4
    linarith
  unfold integrand Q
  exact GppRaisedBoxSimplexMajorantAlgebra.symanzik_neg_eps_majorized
    hS hT.le hx1 hx2 hx3 hx4 hε0 hεδ hδ

end GppRaisedBoxConcreteMoment

#print axioms GppRaisedBoxConcreteMoment.integrand_measurable_x3
#print axioms GppRaisedBoxConcreteMoment.integrand_measurable_x2_x3
#print axioms GppRaisedBoxConcreteMoment.measurableSet_innerSimplexStrip
#print axioms GppRaisedBoxConcreteMoment.stripIntegrand_measurable
#print axioms GppRaisedBoxConcreteMoment.stripInnerIntegral_stronglyMeasurable
#print axioms GppRaisedBoxConcreteMoment.stripIntegrand_section_eq_Icc_indicator
#print axioms GppRaisedBoxConcreteMoment.simplexMoment_zero
#print axioms GppRaisedBoxConcreteMoment.Q_pos
#print axioms GppRaisedBoxConcreteMoment.integrand_tendsto_one
#print axioms GppRaisedBoxConcreteMoment.integrand_le_one_channel_majorant
