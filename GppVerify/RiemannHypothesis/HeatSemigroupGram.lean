import GppVerify.RiemannHypothesis.HaarPositivityWeil
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Finite heat-semigroup Gram positivity

The prime–Archimedean heat-trace program studies Hankel matrices of the form

  Gᵢⱼ = K(tᵢ+tⱼ).

This file isolates the finite algebraic mechanism behind their positivity.  A
single heat mode `exp (-a t)` factors on the additive semigroup,

  exp (-a (tᵢ+tⱼ)) = exp (-a tᵢ) exp (-a tⱼ),

so its Hankel matrix is a real rank-one Gram matrix.  Every finite nonnegative
mixture of such modes is therefore positive semidefinite.

This is deliberately only the finite semigroup-Gram lemma.  It does not assert
that the arithmetic prime–Archimedean heat trace has a nonnegative heat-mode
expansion unconditionally; that identification/positivity is the RH-equivalent
boundary.
-/

namespace GppHeatSemigroupGram

open scoped BigOperators

/-- A single real heat mode. -/
noncomputable def heatMode (a t : ℝ) : ℝ := Real.exp (-a * t)

/-- A finite nonnegative mixture of heat modes. -/
noncomputable def finiteHeatMixture {m : ℕ}
    (w rate : Fin m → ℝ) (t : ℝ) : ℝ :=
  ∑ r : Fin m, w r * heatMode (rate r) t

/-- Additive-semigroup factorization of one heat mode. -/
theorem heatMode_add (a s t : ℝ) :
    heatMode a (s + t) = heatMode a s * heatMode a t := by
  unfold heatMode
  rw [show -a * (s + t) = (-a * s) + (-a * t) by ring, Real.exp_add]

/-- One heat mode gives a positive-semidefinite Hankel kernel on arbitrary
real sample times.  No sign condition on `a` or on the sample times is needed
for this finite algebraic statement. -/
theorem heatMode_hankel_nonneg {n : ℕ}
    (a : ℝ) (t : Fin n → ℝ) (c : Fin n → ℂ) :
    0 ≤
      (∑ i : Fin n, ∑ j : Fin n,
        (starRingEnd ℂ) (c i) * c j *
          ((heatMode a (t i + t j) : ℝ) : ℂ)).re := by
  have h := GppHaarPositivityWeil.sum_conj_mul_real_re_nonneg
    (Finset.univ : Finset (Fin n)) c (fun i => heatMode a (t i))
  simpa [heatMode_add] using h

/-- A nonnegative scalar multiple of one heat-mode Gram kernel is still
positive semidefinite. -/
theorem weighted_heatMode_hankel_nonneg {n : ℕ}
    {w : ℝ} (hw : 0 ≤ w) (a : ℝ) (t : Fin n → ℝ) (c : Fin n → ℂ) :
    0 ≤
      (∑ i : Fin n, ∑ j : Fin n,
        (starRingEnd ℂ) (c i) * c j *
          (((w * heatMode a (t i + t j) : ℝ) : ℂ))).re := by
  have h := heatMode_hankel_nonneg a t c
  have heq :
      (∑ i : Fin n, ∑ j : Fin n,
        (starRingEnd ℂ) (c i) * c j *
          (((w * heatMode a (t i + t j) : ℝ) : ℂ)))
        = (w : ℂ) *
          (∑ i : Fin n, ∑ j : Fin n,
            (starRingEnd ℂ) (c i) * c j *
              ((heatMode a (t i + t j) : ℝ) : ℂ)) := by
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg hw h

/-- **Finite Gaussian-semigroup Gram theorem.** Every finite nonnegative
mixture `K(t)=Σᵣ wᵣ exp(-aᵣt)` has positive-semidefinite Hankel matrices
`K(tᵢ+tⱼ)` for all finite choices of sample times and complex coefficients. -/
theorem finiteHeatMixture_hankel_nonneg {m n : ℕ}
    (w rate : Fin m → ℝ) (hw : ∀ r, 0 ≤ w r)
    (t : Fin n → ℝ) (c : Fin n → ℂ) :
    0 ≤
      (∑ i : Fin n, ∑ j : Fin n,
        (starRingEnd ℂ) (c i) * c j *
          ((finiteHeatMixture w rate (t i + t j) : ℝ) : ℂ)).re := by
  have hmode : ∀ r : Fin m,
      0 ≤
        (∑ i : Fin n, ∑ j : Fin n,
          (starRingEnd ℂ) (c i) * c j *
            (((w r * heatMode (rate r) (t i + t j) : ℝ) : ℂ))).re := by
    intro r
    exact weighted_heatMode_hankel_nonneg (hw r) (rate r) t c
  have heq :
      (∑ i : Fin n, ∑ j : Fin n,
        (starRingEnd ℂ) (c i) * c j *
          ((finiteHeatMixture w rate (t i + t j) : ℝ) : ℂ))
        = ∑ r : Fin m,
            ∑ i : Fin n, ∑ j : Fin n,
              (starRingEnd ℂ) (c i) * c j *
                (((w r * heatMode (rate r) (t i + t j) : ℝ) : ℂ)) := by
    unfold finiteHeatMixture
    push_cast
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
    ring
  rw [heq, map_sum]
  exact Finset.sum_nonneg fun r hr => hmode r

end GppHeatSemigroupGram

#print axioms GppHeatSemigroupGram.heatMode_add
#print axioms GppHeatSemigroupGram.heatMode_hankel_nonneg
#print axioms GppHeatSemigroupGram.weighted_heatMode_hankel_nonneg
#print axioms GppHeatSemigroupGram.finiteHeatMixture_hankel_nonneg
