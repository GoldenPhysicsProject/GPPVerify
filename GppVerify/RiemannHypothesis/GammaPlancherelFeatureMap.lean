import GppVerify.RiemannHypothesis.GammaPlancherelDefect
import GppVerify.RiemannHypothesis.FinitePrimeWaveFeatureMap
import Mathlib.Tactic

/-!
# Exact Gamma--Plancherel feature-map factorization

`GammaPlancherelDefect.lean` proves positivity of the real-place defect kernel by observing
that its integrand is a positive density times a rank-one feature product.  Here we sharpen
that observation to an exact norm-square identity.

For coefficients `c_i` and shifts `a_i`, the pointwise Gram form is

  density(q,x) * normSq(sum_i c_i * feature(a_i,x)),

where `feature(a,x) = 1 - exp(-a x)`.  Whenever the pairwise kernel entries are integrable,
the integrated Gamma--Plancherel Gram form is therefore exactly the integral of this
feature norm square.

This is the continuous-feature counterpart of `FinitePrimeWaveFeatureMap.lean`.  It does
not assert the frame/contraction inequality comparing the two feature systems; that is the
next analytic target.
-/

namespace GppGammaPlancherelFeatureMap

open MeasureTheory Set Finset
open GppGammaPlancherel
open GppFinitePrimeWaveFeatureMap

/-- Exact pointwise rank-one factorization of the Gamma--Plancherel Gram form. -/
theorem pointwise_gram_eq_feature_normSq
    {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) (q x : ℝ) :
    ∑ i : Fin n, ∑ j : Fin n,
      ((starRingEnd ℂ) (c i) * c j).re * defectIntegrand q (a i) (a j) x =
      density q x *
        Complex.normSq (∑ i : Fin n, c i * (feature (a i) x : ℂ)) := by
  have hfactor :
      ∑ i : Fin n, ∑ j : Fin n,
          ((starRingEnd ℂ) (c i) * c j).re * defectIntegrand q (a i) (a j) x =
        density q x *
          ∑ i : Fin n, ∑ j : Fin n,
            ((starRingEnd ℂ) (c i) * c j).re *
              (feature (a i) x * feature (a j) x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    unfold defectIntegrand
    ring
  rw [hfactor]
  congr 1
  exact gram_square_eq_normSq c (fun i => feature (a i) x)

/-- Exact integrated feature representation on an arbitrary measurable positive set,
assuming the same pairwise integrability needed by the existing Gram theorem. -/
theorem integral_gram_eq_feature_normSq
    {s : Set ℝ} (hs : MeasurableSet s) {n : ℕ}
    (c : Fin n → ℂ) (a : Fin n → ℝ) (q : ℝ)
    (hInt : ∀ i j : Fin n, IntegrableOn (defectIntegrand q (a i) (a j)) s) :
    ∑ i : Fin n, ∑ j : Fin n,
      ((starRingEnd ℂ) (c i) * c j).re *
        (∫ x : ℝ in s, defectIntegrand q (a i) (a j) x) =
      ∫ x : ℝ in s,
        density q x *
          Complex.normSq (∑ i : Fin n, c i * (feature (a i) x : ℂ)) := by
  have hint : ∀ i j : Fin n,
      IntegrableOn
        (fun x => ((starRingEnd ℂ) (c i) * c j).re *
          defectIntegrand q (a i) (a j) x) s :=
    fun i j => (hInt i j).const_mul _
  calc
    ∑ i : Fin n, ∑ j : Fin n,
        ((starRingEnd ℂ) (c i) * c j).re *
          (∫ x : ℝ in s, defectIntegrand q (a i) (a j) x)
        = ∫ x : ℝ in s, ∑ i : Fin n, ∑ j : Fin n,
            ((starRingEnd ℂ) (c i) * c j).re *
              defectIntegrand q (a i) (a j) x := by
          rw [integral_finset_sum]
          · apply Finset.sum_congr rfl
            intro i _
            rw [integral_finset_sum]
            · apply Finset.sum_congr rfl
              intro j _
              rw [integral_const_mul]
            · exact fun j _ => hint i j
          · exact fun i _ => integrable_finset_sum _ fun j _ => hint i j
    _ = ∫ x : ℝ in s,
          density q x *
            Complex.normSq (∑ i : Fin n, c i * (feature (a i) x : ℂ)) := by
          apply setIntegral_congr_fun hs
          intro x hx
          exact pointwise_gram_eq_feature_normSq c a q x

/-- On `(0,∞)`, pairwise integrability gives the exact feature representation of the full
defect kernel. -/
theorem defectKernel_gram_eq_feature_normSq
    {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) (q : ℝ)
    (hInt : ∀ i j : Fin n,
      IntegrableOn (defectIntegrand q (a i) (a j)) (Ioi (0 : ℝ))) :
    ∑ i : Fin n, ∑ j : Fin n,
      ((starRingEnd ℂ) (c i) * c j).re * defectKernel q (a i) (a j) =
      ∫ x : ℝ in Ioi (0 : ℝ),
        density q x *
          Complex.normSq (∑ i : Fin n, c i * (feature (a i) x : ℂ)) := by
  unfold defectKernel
  exact integral_gram_eq_feature_normSq measurableSet_Ioi c a q hInt

/-- Compact truncations have the exact continuous feature representation with no additional
integrability hypothesis beyond `0 < eps`. -/
theorem truncatedDefectKernel_gram_eq_feature_normSq
    {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ)
    (q eps R : ℝ) (heps : 0 < eps) :
    ∑ i : Fin n, ∑ j : Fin n,
      ((starRingEnd ℂ) (c i) * c j).re * truncatedDefectKernel q eps R (a i) (a j) =
      ∫ x : ℝ in Icc eps R,
        density q x *
          Complex.normSq (∑ i : Fin n, c i * (feature (a i) x : ℂ)) := by
  unfold truncatedDefectKernel
  apply integral_gram_eq_feature_normSq measurableSet_Icc c a q
  intro i j
  exact truncated_integrable heps q (a i) (a j)

end GppGammaPlancherelFeatureMap

#print axioms GppGammaPlancherelFeatureMap.pointwise_gram_eq_feature_normSq
#print axioms GppGammaPlancherelFeatureMap.integral_gram_eq_feature_normSq
#print axioms GppGammaPlancherelFeatureMap.defectKernel_gram_eq_feature_normSq
#print axioms GppGammaPlancherelFeatureMap.truncatedDefectKernel_gram_eq_feature_normSq
