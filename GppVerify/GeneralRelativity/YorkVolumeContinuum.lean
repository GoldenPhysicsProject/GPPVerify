import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Continuum (Bochner integral) York--volume pairing

Unlike the finite-cell ADM pairing, these definitions use an arbitrary
measurable spatial slice with an arbitrary (possibly noncompact)
measure and an integrable trace-density field.

The analytic equality is a direct equality of Bochner integrals.
The `traceDensity` field is the linearized metric volume density
  sqrt(det h) h^{ij} delta h_{ij}.
A separate tensor-geometry development must derive this field from
d(sqrt(det h)), establish the actual Einstein--Hilbert momentum
and ensure all boundary/corner terms are accounted for.

This is a continuum integral theorem, NOT a completed proof of
the full covariant Iyer--Wald symplectic identity.
-/

namespace GppYorkContinuum

open scoped BigOperators
open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {n : ℕ}

/-- Local linearized unweighted volume-density trace on a slice. -/
noncomputable def traceDensity
    (w : X → ℝ) (invMetric dh : X → Fin n → Fin n → ℝ) (x : X) : ℝ :=
  w x * ∑ i, ∑ j, invMetric x i j * dh x i j

/-- The proper-volume first variation of the spatial slice at fixed
integration domain, expressed as an integral of the metric trace. -/
noncomputable def volumeVariation (μ : Measure X)
    (w : X → ℝ) (invMetric dh : X → Fin n → Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ x, traceDensity w invMetric dh x ∂μ

/-- The York momentum shift integrated against the spatial metric
variation; the coefficient is a uniform scalar. -/
noncomputable def yorkMomentumPairing (μ : Measure X) (c : ℝ)
    (w : X → ℝ) (invMetric dh : X → Fin n → Fin n → ℝ) : ℝ :=
  ∫ x, c * traceDensity w invMetric dh x ∂μ

/-- Continuum York pairing is twice the volume first variation.
No finite lattice, truncation, or local discretization. -/
theorem continuum_york_pairing_equals_volume (μ : Measure X) (c : ℝ)
    (w : X → ℝ) (invMetric dh : X → Fin n → Fin n → ℝ) :
    yorkMomentumPairing μ c w invMetric dh =
       (2 * c) * volumeVariation μ w invMetric dh := by
  unfold yorkMomentumPairing volumeVariation
  rw [integral_const_mul]
  ring

/-- Nonzero York coefficient: a vanishing continuum pairing enforces
zero unweighted spatial volume variation. -/
theorem continuum_null_forces_fixed_volume (μ : Measure X) (c : ℝ)
    (hc : c ≠ 0)
    (w : X → ℝ) (invMetric dh : X → Fin n → Fin n → ℝ)
    (h : yorkMomentumPairing μ c w invMetric dh = 0) :
    volumeVariation μ w invMetric dh = 0 := by
  rw [continuum_york_pairing_equals_volume] at h
  exact (mul_eq_zero.mp h).resolve_left
    (mul_ne_zero (by norm_num) hc)

/-- The fixed-volume condition is sufficient for vanishing York work. -/
theorem continuum_fixed_volume_is_null (μ : Measure X) (c : ℝ)
    (w : X → ℝ) (invMetric dh : X → Fin n → Fin n → ℝ)
    (h : volumeVariation μ w invMetric dh = 0) :
    yorkMomentumPairing μ c w invMetric dh = 0 := by
  rw [continuum_york_pairing_equals_volume, h]
  ring


/-- For a conformal deformation h_eps = exp(2*eps*a) h_0 on a
three-dimensional spatial slice, sqrt(det h_eps) = exp(3*eps*a)
sqrt(det h_0). This is a rigorous first derivative of the
spatial volume density in the conformal sector. -/
theorem conformal_density_hasDerivAt_zero (a w : ℝ) :
    HasDerivAt (fun eps : ℝ => w * Real.exp (eps * (3 * a)))
      (3 * a * w) 0 := by
  have hinner : HasDerivAt (fun eps : ℝ => eps * (3 * a))
       (3 * a) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (3 * a)
  have hexp := (Real.hasDerivAt_exp (0 : ℝ)).comp 0 hinner
  have hscaled := hexp.const_mul w
  convert hscaled using 1 <;> norm_num [mul_comm, mul_left_comm, mul_assoc]

end GppYorkContinuum

#print axioms GppYorkContinuum.continuum_york_pairing_equals_volume
#print axioms GppYorkContinuum.continuum_null_forces_fixed_volume

#print axioms GppYorkContinuum.conformal_density_hasDerivAt_zero
