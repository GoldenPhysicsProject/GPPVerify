import GppVerify.RiemannHypothesis.IdeleQ
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Data.Complex.BigOperators
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Haar squares on the idèle class group of `ℚ` are of positive type

The idèle class group `C_ℚ = 𝔸ˣ/ℚˣ` is `GppIdeleQ.Idele ⧸ ℚˣ` with the quotient topology and
its Borel σ-algebra. For every right-invariant measure `μ` on it (in particular a Haar measure)
and every integrable bounded real `Ω`, the Haar square `P(x) = ∫ Ω(y) Ω(y x⁻¹) dμ(y)` is of
positive type: `0 ≤ Σᵢⱼ c̄ᵢ cⱼ P(xᵢ xⱼ⁻¹)` for all finite families.

`C_ℚ` is a locally compact Hausdorff group (`ℚˣ` is discrete, hence closed, in the idèles,
and `𝔸_f` is locally compact), so it carries a nonzero Haar measure `haarCQ`, to which the
theorem applies.

The argument is the multiplicative form of `GppConvolutionSquareGroup.
convolution_square_positive_type_group` (right-invariance only), stated here for any
commutative group and instantiated on `C_ℚ`.

**Scope.** Positivity of a Haar square is unconditional and is *not* Weil positivity, which
concerns the specific distribution `D_k` (see `NoGo/HaarSquareNotReflection.lean`). No claim
about RH, which remains open.

Daniel Toupin / Golden Physics Project, with AI assistance from Claude Code.

## Sources

The idele class group `C_ℚ = 𝔸ˣ/ℚˣ` and its Haar measure are Tate's setting:
J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, Ph.D.
thesis, Princeton (1950), reprinted in Cassels–Fröhlich (eds.), *Algebraic Number
Theory*, Academic Press (1967), pp. 305–347. That a Haar square
`x ↦ ∫ Ω(y) Ω(yx⁻¹) dμ(y)` is of positive type is the standard convolution-square
fact of harmonic analysis on locally compact groups.

-/

set_option autoImplicit false

open MeasureTheory Finset
open scoped ComplexOrder

namespace GppIdeleClassGroupQ

section General

variable {G : Type*} [CommGroup G] [MeasurableSpace G] [MeasurableMul G]
  {μ : Measure G} [μ.IsMulRightInvariant]

/-- Positive type on a multiplicative group: `0 ≤ Σᵢⱼ c̄ᵢ cⱼ P(xᵢ xⱼ⁻¹)` in `ℂ`. -/
def MulPositiveType (P : G → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, (starRingEnd ℂ) (c i) * c j * (P (x i * (x j)⁻¹) : ℂ)

theorem integrable_shift_mul_shift {f : G → ℝ} (hf : Integrable f μ) {C : ℝ}
    (hbdd : ∀ x, |f x| ≤ C) (a b : G) :
    Integrable (fun y => f (y * a) * f (y * b)) μ := by
  have ha : Integrable (fun y => f (y * a)) μ := hf.comp_mul_right a
  have hb : Integrable (fun y => f (y * b)) μ := hf.comp_mul_right b
  exact hb.bdd_mul (c := C) ha.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hbdd (y * a))

theorem convolution_shift {f : G → ℝ} (a b : G) :
    (∫ y, f y * f (y * (a * b⁻¹)⁻¹) ∂μ) = ∫ y, f (y * a) * f (y * b) ∂μ := by
  have h := integral_mul_right_eq_self (μ := μ) (fun y => f y * f (y * (a * b⁻¹)⁻¹)) a
  have harg : ∀ y : G, y * a * (a * b⁻¹)⁻¹ = y * b := fun y => by
    rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_comm_assoc]
  simp only [harg] at h
  exact h.symm

/-- **Haar squares are of positive type** on any commutative group with a right-invariant
measure, for integrable bounded real `f`. -/
theorem haar_square_positive_type {f : G → ℝ} (hf : Integrable f μ) {C : ℝ}
    (hbdd : ∀ x, |f x| ≤ C) :
    MulPositiveType (fun x => ∫ y, f y * f (y * x⁻¹) ∂μ) := by
  intro n x c
  have hentry : ∀ i j : Fin n,
      (((∫ y, f y * f (y * (x i * (x j)⁻¹)⁻¹) ∂μ : ℝ)) : ℂ) =
        ∫ y, (((f (y * x i) * f (y * x j) : ℝ)) : ℂ) ∂μ := by
    intro i j
    rw [convolution_shift]
    exact integral_ofReal.symm
  have hint : ∀ i j : Fin n, Integrable
      (fun y => (starRingEnd ℂ) (c i) * c j * (((f (y * x i) * f (y * x j) : ℝ)) : ℂ)) μ :=
    fun i j => ((integrable_shift_mul_shift hf hbdd (x i) (x j)).ofReal).const_mul _
  simp only [hentry]
  have hswap : ∑ i : Fin n, ∑ j : Fin n, (starRingEnd ℂ) (c i) * c j *
        ∫ y, (((f (y * x i) * f (y * x j) : ℝ)) : ℂ) ∂μ =
      ∫ y, ∑ i : Fin n, ∑ j : Fin n, (starRingEnd ℂ) (c i) * c j *
        (((f (y * x i) * f (y * x j) : ℝ)) : ℂ) ∂μ := by
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [integral_const_mul]
      · exact fun j _ => hint i j
    · exact fun i _ => integrable_finsetSum _ fun j _ => hint i j
  rw [hswap]
  have hpt : ∀ y, ∑ i : Fin n, ∑ j : Fin n, (starRingEnd ℂ) (c i) * c j *
        (((f (y * x i) * f (y * x j) : ℝ)) : ℂ) =
      ((Complex.normSq (∑ j : Fin n, c j * (f (y * x j) : ℂ)) : ℝ) : ℂ) := by
    intro y
    rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  simp only [hpt]
  rw [integral_complex_ofReal]
  exact Complex.zero_le_real.mpr (integral_nonneg fun y => Complex.normSq_nonneg _)

end General

open GppIdeleQ

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum in
instance (v : HeightOneSpectrum ℤ) : WeaklyLocallyCompactSpace (v.adicCompletion ℚ) :=
  (adicCompletion.padicEquiv v).toHomeomorph.isClosedEmbedding.weaklyLocallyCompactSpace

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum in
lemma isCompact_integers (v : HeightOneSpectrum ℤ) :
    IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  have : (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) =
      (adicCompletion.padicEquiv v).symm '' Metric.closedBall (0 : ℚ_[pr v]) 1 := by
    ext x
    simp only [SetLike.mem_coe, mem_integers_iff, Set.mem_image, Metric.mem_closedBall,
      dist_zero_right]
    constructor
    · intro hx; exact ⟨_, hx, (adicCompletion.padicEquiv v).symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩; simpa [lnorm] using hy
  rw [this]
  exact (isCompact_closedBall _ _).image (adicCompletion.padicEquiv v).symm.continuous

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in
/-- The finite adeles of `ℚ` are (weakly) locally compact. -/
instance : WeaklyLocallyCompactSpace Af :=
  RestrictedProduct.weaklyLocallyCompactSpace_of_cofinite
    (R := fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ)
    (A := fun v : HeightOneSpectrum ℤ => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
    (fun v => isOpen_integers v) (Filter.Eventually.of_forall isCompact_integers)

/-- The idèles of `ℚ` form a locally compact group. -/
instance : LocallyCompactSpace Idele := inferInstance

/-- `ℚˣ` is discrete in the idèles. -/
instance : DiscreteTopology diag.range := by
  apply discreteTopology_of_isOpen_singleton_one
  have : ({1} : Set diag.range) = (fun y : diag.range => (y : Idele)) ⁻¹' nbhdOne := by
    ext ⟨y, hy⟩
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · intro h; rw [show y = 1 from congrArg Subtype.val h]; exact one_mem_nbhdOne
    · intro h
      obtain ⟨q, rfl⟩ := hy
      have hq : q = 1 := eq_one_of_near_one q h.1 h.2
      subst hq
      apply Subtype.ext; simp
  rw [this]
  exact isOpen_nbhdOne.preimage continuous_subtype_val

/-- The idèle class group `C_ℚ = 𝔸ˣ/ℚˣ`. -/
abbrev CQ := Idele ⧸ diag.range

/-- The Borel σ-algebra on `C_ℚ`. -/
noncomputable instance : MeasurableSpace CQ := borel _

instance : BorelSpace CQ := ⟨rfl⟩

/-- `C_ℚ` is a locally compact Hausdorff group. -/
example : LocallyCompactSpace CQ := inferInstance

instance : T2Space CQ := inferInstance

/-- A Haar measure on `C_ℚ`. -/
noncomputable def haarCQ : Measure CQ := Measure.haarMeasure (Classical.arbitrary _)

instance : haarCQ.IsHaarMeasure := by unfold haarCQ; infer_instance

lemma haarCQ_ne_zero : haarCQ ≠ 0 := by
  intro h
  have := Measure.measure_pos_of_nonempty_interior haarCQ
    (Classical.arbitrary (TopologicalSpace.PositiveCompacts CQ)).interior_nonempty
  simp [h] at this

instance : haarCQ.IsMulRightInvariant :=
  ⟨fun g => by
    rw [show (· * g) = (g * ·) from funext fun x => mul_comm x g]
    exact map_mul_left_eq_self haarCQ g⟩

/-- **Haar squares on the idèle class group of `ℚ` are of positive type.** For every
right-invariant measure `μ` on `C_ℚ` and every integrable bounded real `Ω`,
`P(x) = ∫ Ω(y) Ω(y x⁻¹) dμ(y)` is of positive type. -/
theorem adelic_haar_square_positive_type (μ : Measure CQ) [μ.IsMulRightInvariant]
    {Ω : CQ → ℝ} (hΩ : Integrable Ω μ) {C : ℝ} (hbdd : ∀ x, |Ω x| ≤ C) :
    MulPositiveType (fun x => ∫ y, Ω y * Ω (y * x⁻¹) ∂μ) :=
  haar_square_positive_type hΩ hbdd

/-- The Haar-measure instance: `P = Ω^∨ * Ω` against the Haar measure `haarCQ` of `C_ℚ` is of
positive type. -/
theorem haar_square_positive_type_haarCQ {Ω : CQ → ℝ} (hΩ : Integrable Ω haarCQ) {C : ℝ}
    (hbdd : ∀ x, |Ω x| ≤ C) :
    MulPositiveType (fun x => ∫ y, Ω y * Ω (y * x⁻¹) ∂haarCQ) :=
  adelic_haar_square_positive_type haarCQ hΩ hbdd

end GppIdeleClassGroupQ
