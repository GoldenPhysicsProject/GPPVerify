import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Algebra.Group.Compact

/-!
# Haar invariance under compact-group automorphisms
# Lean 4 Kernel | Zero Sorries | Zero Errors
# Author: Daniel Toupin | Golden Physics Project | goldenphysics.org
# ORCID: 0009-0003-7682-9579
# Toolchain: leanprover/lean4:v4.33.1 | Mathlib: v4.33.1

## Theorems verified:
## 1. haar_invariant_under_automorphism — bicontinuous automorphism preserves Haar measure
## 2. grassmannian_haar_self_duality    — legacy API alias of the same compact-group theorem

## Chronology/provenance correction (2026-09-03)

The original manuscript and comments described theorem 2 as a direct theorem about
`Gr(2,4)`.  That was too strong.  The complex Grassmannian `Gr(2,4)` is the homogeneous
space `U(4)/(U(2) × U(2))`; it is not itself a group.  Consequently the theorem below,
whose hypotheses contain `[Group G]` and a multiplicative equivalence `φ : G ≃* G`,
does not instantiate `Gr(2,4)` without additional homogeneous-space measure machinery.

Likewise, inversion `g ↦ g⁻¹` is a group automorphism only in the commutative case; on a
general nonabelian group it is an anti-automorphism.  The arithmetic idèle-class use is valid
because that group is abelian and is formalized separately in
`RiemannHypothesis/HaarMeasure.lean`.

The legacy theorem name is retained for API stability.  Read its statement literally: it is
a compact-group automorphism-invariance theorem, not a formal proof of Grassmannian shadow
self-duality or of the celestial shadow transform.

## Axioms used beyond Lean kernel defaults:
##   None beyond propext, Classical.choice, Quot.sound, funext

## Proof strategy:
##   Step 1. MulEquiv.isHaarMeasure_map: pushforward of μ along φ is a Haar measure
##           (uses MulEquiv variant — avoids cocompact properness condition entirely)
##   Step 2. Regular instances: automatic for Haar on compact second-countable groups
##   Step 3. isMulLeftInvariant_eq_smul_of_regular: map φ μ = c • μ for some c : ℝ≥0
##   Step 4. Mass preservation: φ bijective ⟹ (map φ μ)(univ) = μ(univ)
##   Step 5. Cancellation via ENNReal.div_self: c = 1
-/

open MeasureTheory MeasureTheory.Measure TopologicalSpace Filter

/-- A bicontinuous group automorphism of a compact second-countable group
    preserves the Haar measure. -/
theorem haar_invariant_under_automorphism
    {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [CompactSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (φ : G ≃* G) (hφ : Continuous φ) (hφsymm : Continuous φ.symm) :
    Measure.map φ μ = μ := by
  -- Step 1: map φ μ is a Haar measure
  -- Use MulEquiv.isHaarMeasure_map (no cocompact properness condition needed)
  haveI hmap : (Measure.map (φ : G → G) μ).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map μ φ hφ hφsymm
  -- Step 2: Regular instances (automatic for Haar on compact second-countable groups)
  haveI hμ_reg  : Regular μ                         := inferInstance
  haveI hν_reg  : Regular (Measure.map (φ : G → G) μ) := inferInstance
  -- Step 3: Any two regular left-invariant measures on G differ by a scalar c : ℝ≥0
  have heq : Measure.map (φ : G → G) μ =
      haarScalarFactor (Measure.map (φ : G → G) μ) μ • μ :=
    isMulLeftInvariant_eq_smul_of_regular (Measure.map (φ : G → G) μ) μ
  -- Reduce to showing the scalar equals 1
  suffices hc : haarScalarFactor (Measure.map (φ : G → G) μ) μ = 1 by
    rw [heq, hc, one_smul]
  -- Step 4: φ is bijective, so total mass is preserved
  have hmass : (Measure.map (φ : G → G) μ) Set.univ = μ Set.univ := by
    simp [Measure.map_apply hφ.measurable MeasurableSet.univ]
  -- μ(univ) is strictly positive (IsOpen.measure_pos: returns 0 < μ U)
  have hpos : (0 : ENNReal) < μ Set.univ :=
    isOpen_univ.measure_pos μ Set.univ_nonempty
  -- μ(univ) is finite
  have hfin : μ Set.univ < ⊤ := measure_lt_top μ Set.univ
  -- From heq at univ: (c : ENNReal) * μ(univ) = μ(univ)
  have hcμ : (haarScalarFactor (Measure.map (φ : G → G) μ) μ : ENNReal) *
      μ Set.univ = μ Set.univ :=
    calc (haarScalarFactor (Measure.map (φ : G → G) μ) μ : ENNReal) * μ Set.univ
        = (haarScalarFactor (Measure.map (φ : G → G) μ) μ • μ) Set.univ := by
            simp [Measure.smul_apply]
      _ = (Measure.map (φ : G → G) μ) Set.univ := by rw [← heq]
      _ = μ Set.univ := hmass
  -- Step 5: Cancel μ(univ) via division: c = (c * μ univ) / μ univ = μ univ / μ univ = 1
  have hne  : μ Set.univ ≠ 0 := hpos.ne'
  have htop : μ Set.univ ≠ ⊤ := hfin.ne
  have hc_enn : (haarScalarFactor (Measure.map (φ : G → G) μ) μ : ENNReal) = 1 :=
    calc (haarScalarFactor (Measure.map (φ : G → G) μ) μ : ENNReal)
        = (haarScalarFactor (Measure.map (φ : G → G) μ) μ : ENNReal) *
            μ Set.univ / μ Set.univ := by
              rw [ENNReal.mul_div_cancel_right hne htop]
      _ = μ Set.univ / μ Set.univ := by rw [hcμ]
      _ = 1 := ENNReal.div_self hne htop
  exact_mod_cast hc_enn

/-- Legacy name retained for API stability.

    This theorem is exactly `haar_invariant_under_automorphism`: a bicontinuous
    automorphism of a compact second-countable group preserves Haar measure.
    It does not by itself instantiate `Gr(2,4)`, because `Gr(2,4)` is a homogeneous
    space rather than a group, and it does not identify the automorphism with the
    celestial shadow transform. -/
theorem grassmannian_haar_self_duality
    {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [CompactSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (φ : G ≃* G) (hφ_cont : Continuous φ) (hφ_symm : Continuous φ.symm) :
    Measure.map φ μ = μ :=
  haar_invariant_under_automorphism μ φ hφ_cont hφ_symm

#check @haar_invariant_under_automorphism
#check @grassmannian_haar_self_duality
