import GppVerify.RiemannHypothesis.ConvolutionSquarePositive
import GppVerify.RiemannHypothesis.VonMangoldtCosineBridge
import Mathlib.Tactic

/-!
# Finite arithmetic wave feature map

A finite nonnegative superposition of arithmetic cosine modes has an explicit
finite-dimensional feature-map factorization.  For frequencies `omega k` and weights
`w k >= 0`, the kernel

  K(t) = sum_{k in S} w_k cos(omega_k t)

has Gram form equal to the sum, over `k`, of the cosine and sine amplitude norm squares.
This is stronger than merely proving positive type: it exhibits the concrete feature
coordinates whose Euclidean/Hermitian norm produces the kernel.

Specializing `w_n = Lambda(n) exp(-a log n)` and `omega_n = log n` gives the finite
von-Mangoldt wave sector.  No comparison with an Archimedean norm, contraction theorem,
infinite prime limit, or RH claim is made here.
-/

namespace GppFinitePrimeWaveFeatureMap

open Finset
open GppHaarPositivityWeil

/-- Exact Gram-square identity, strengthening `gram_square_nonneg` from an inequality to
an equality with the complex norm square of the feature amplitude. -/
theorem gram_square_eq_normSq {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n,
      ((starRingEnd ℂ) (c i) * c j).re * (a i * a j) =
      Complex.normSq (∑ i : Fin n, c i * (a i : ℂ)) := by
  have hkey : ∑ i : Fin n, ∑ j : Fin n,
      ((starRingEnd ℂ) (c i) * c j).re * (a i * a j) =
      (∑ i : Fin n, ∑ j : Fin n,
        (starRingEnd ℂ) (c i * (a i : ℂ)) * (c j * (a j : ℂ))).re := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hexpand :
        (starRingEnd ℂ) (c i * (a i : ℂ)) * (c j * (a j : ℂ)) =
          (starRingEnd ℂ) (c i) * c j * ((a i * a j : ℝ) : ℂ) := by
      rw [map_mul, Complex.conj_ofReal]
      push_cast
      ring
    rw [hexpand, GppHaarPositivityWeil.mul_ofReal_re]
  rw [hkey]
  have hsum : ∑ i : Fin n, ∑ j : Fin n,
      (starRingEnd ℂ) (c i * (a i : ℂ)) * (c j * (a j : ℂ)) =
      (starRingEnd ℂ) (∑ i : Fin n, c i * (a i : ℂ)) *
        (∑ i : Fin n, c i * (a i : ℂ)) := by
    rw [map_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  rw [hsum, mul_comm, Complex.mul_conj, Complex.ofReal_re]

/-- Kernel associated with a finite family of real frequencies and weights. -/
noncomputable def finiteCosineKernel
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w omega : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ S, w k * Real.cos (omega k * t)

/-- The concrete feature energy: each frequency contributes a cosine coordinate and a sine
coordinate, with the common nonnegative mode weight outside the two norm squares. -/
noncomputable def featureEnergy
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w omega : ι → ℝ)
    {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) : ℝ :=
  ∑ k ∈ S, w k *
    (Complex.normSq (∑ i : Fin n, c i * (Real.cos (omega k * x i) : ℂ)) +
     Complex.normSq (∑ i : Fin n, c i * (Real.sin (omega k * x i) : ℂ)))

/-- **Exact finite feature-map factorization.** The Gram form of a finite weighted cosine
kernel is literally the sum of the cosine/sine feature norm squares. -/
theorem finiteCosineKernel_gram_eq_featureEnergy
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w omega : ι → ℝ)
    {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) :
    ∑ i : Fin n, ∑ j : Fin n,
      ((starRingEnd ℂ) (c i) * c j).re * finiteCosineKernel S w omega (x i - x j) =
      featureEnergy S w omega x c := by
  classical
  unfold finiteCosineKernel featureEnergy
  simp_rw [Finset.mul_sum]
  let F : Fin n → Fin n → ι → ℝ := fun i j k =>
    ((starRingEnd ℂ) (c i) * c j).re *
      (w k * Real.cos (omega k * (x i - x j)))
  have hreorder :
      (∑ i : Fin n, ∑ j : Fin n, ∑ k ∈ S, F i j k) =
        ∑ k ∈ S, ∑ i : Fin n, ∑ j : Fin n, F i j k := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, ∑ k ∈ S, F i j k) =
          ∑ i : Fin n, ∑ k ∈ S, ∑ j : Fin n, F i j k := by
            refine Finset.sum_congr rfl ?_
            intro i _
            exact (Finset.sum_comm :
              (∑ j : Fin n, ∑ k ∈ S, F i j k) =
                ∑ k ∈ S, ∑ j : Fin n, F i j k)
      _ = ∑ k ∈ S, ∑ i : Fin n, ∑ j : Fin n, F i j k := by
            exact (Finset.sum_comm :
              (∑ i : Fin n, ∑ k ∈ S, ∑ j : Fin n, F i j k) =
                ∑ k ∈ S, ∑ i : Fin n, ∑ j : Fin n, F i j k)
  change (∑ i : Fin n, ∑ j : Fin n, ∑ k ∈ S, F i j k) = _
  rw [hreorder]
  apply Finset.sum_congr rfl
  intro k hk
  have hcos : ∀ i j : Fin n,
      Real.cos (omega k * (x i - x j)) =
        Real.cos (omega k * x i) * Real.cos (omega k * x j) +
        Real.sin (omega k * x i) * Real.sin (omega k * x j) := by
    intro i j
    rw [mul_sub, Real.cos_sub]
  rw [← gram_square_eq_normSq c (fun i => Real.cos (omega k * x i)),
      ← gram_square_eq_normSq c (fun i => Real.sin (omega k * x i)), mul_add]
  simp_rw [Finset.mul_sum]
  simp_rw [F, hcos, mul_add, Finset.sum_add_distrib]
  simp only [mul_assoc, mul_left_comm, mul_comm]

/-- Nonnegative weights make the explicit feature energy nonnegative. -/
theorem featureEnergy_nonneg
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w omega : ι → ℝ)
    (hw : ∀ k ∈ S, 0 ≤ w k)
    {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) :
    0 ≤ featureEnergy S w omega x c := by
  classical
  unfold featureEnergy
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (hw k hk)
    (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))

/-- The finite von-Mangoldt radial weight used by the arithmetic wave sector. -/
noncomputable def vonMangoldtWaveWeight (a : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n * a)

/-- Von-Mangoldt wave weights are nonnegative for every real radial parameter. -/
theorem vonMangoldtWaveWeight_nonneg (a : ℝ) (n : ℕ) :
    0 ≤ vonMangoldtWaveWeight a n := by
  unfold vonMangoldtWaveWeight
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le

/-- Hence every finite von-Mangoldt wave kernel has the explicit nonnegative feature
energy above. -/
theorem finite_vonMangoldt_featureEnergy_nonneg
    (S : Finset ℕ) (a : ℝ) {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) :
    0 ≤ featureEnergy S (vonMangoldtWaveWeight a) (fun m => Real.log m) x c := by
  exact featureEnergy_nonneg S _ _
    (fun k _ => vonMangoldtWaveWeight_nonneg a k) x c

end GppFinitePrimeWaveFeatureMap

#print axioms GppFinitePrimeWaveFeatureMap.gram_square_eq_normSq
#print axioms GppFinitePrimeWaveFeatureMap.finiteCosineKernel_gram_eq_featureEnergy
#print axioms GppFinitePrimeWaveFeatureMap.featureEnergy_nonneg
#print axioms GppFinitePrimeWaveFeatureMap.finite_vonMangoldt_featureEnergy_nonneg