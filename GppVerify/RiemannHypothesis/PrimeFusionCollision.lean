import GppVerify.RiemannHypothesis.PrimeFockPartition
import Mathlib.Tactic

/-!
# Prime-fusion collision invariants

This file records the exact finite algebra behind the Oct. 5 "prime Boltzmann gas"
experiment.

A prime occupation is already represented in PrimeFockPartition as a finitely supported
occupation vector. Multiplicative fusion of integer states is addition of these occupation
vectors. Every prime occupation number is therefore an exactly conserved collision invariant.

The quadratic collision form is a sum of nonnegative squares. In particular every prime
count is a null direction. This is the elementary H-theorem part of the proposed
Euler-product / collision-invariant dictionary.

No claim is made here that this collision form equals the completed Weil form, and there is
no RH claim.
-/

namespace GppPrimeFusionGas

open GppPrimeFock

/-- Fusion of two prime occupations: add every prime occupation number. -/
def fuse (f g : PrimeOccupation) : PrimeOccupation :=
  ⟨f.1 + g.1, by
    intro p hp
    by_contra hprime
    have hf0 : f.1 p = 0 := by
      by_contra h
      exact hprime (f.2 p (Finsupp.mem_support_iff.mpr h))
    have hg0 : g.1 p = 0 := by
      by_contra h
      exact hprime (g.2 p (Finsupp.mem_support_iff.mpr h))
    have hsum : (f.1 + g.1) p = 0 := by simp [hf0, hg0]
    exact (Finsupp.mem_support_iff.mp hp) hsum⟩

@[simp] theorem fuse_apply (f g : PrimeOccupation) (p : ℕ) :
    (fuse f g).1 p = f.1 p + g.1 p := by
  rfl

/-- The occupation number of a fixed prime channel. -/
def primeCount (p : ℕ) (f : PrimeOccupation) : ℕ := f.1 p

/-- **Each prime count is an exact collision invariant.** -/
theorem primeCount_fuse (p : ℕ) (f g : PrimeOccupation) :
    primeCount p (fuse f g) = primeCount p f + primeCount p g := by
  rfl

/-- Real-valued version of the conserved prime occupation. -/
def primeCountR (p : ℕ) (f : PrimeOccupation) : ℝ := (primeCount p f : ℝ)

theorem primeCountR_fuse (p : ℕ) (f g : PrimeOccupation) :
    primeCountR p (fuse f g) = primeCountR p f + primeCountR p g := by
  simp [primeCountR, primeCount, primeCount_fuse]

/-- Collision defect of an arbitrary scalar observable. -/
def collisionDefect (H : PrimeOccupation → ℝ) (f g : PrimeOccupation) : ℝ :=
  H f + H g - H (fuse f g)

/-- Prime counts have identically zero collision defect. -/
theorem primeCount_collisionDefect_zero (p : ℕ) (f g : PrimeOccupation) :
    collisionDefect (primeCountR p) f g = 0 := by
  rw [collisionDefect, primeCountR_fuse]
  ring

/-- A finite weighted collision energy: a sum of squared fusion defects. -/
def collisionEnergy
    (S : Finset (PrimeOccupation × PrimeOccupation))
    (w : PrimeOccupation × PrimeOccupation → ℝ)
    (H : PrimeOccupation → ℝ) : ℝ :=
  ∑ z ∈ S, w z * collisionDefect H z.1 z.2 ^ 2

/-- **Finite H-theorem.** Nonnegative collision rates give nonnegative energy. -/
theorem collisionEnergy_nonneg
    (S : Finset (PrimeOccupation × PrimeOccupation))
    (w : PrimeOccupation × PrimeOccupation → ℝ)
    (hw : ∀ z ∈ S, 0 ≤ w z)
    (H : PrimeOccupation → ℝ) :
    0 ≤ collisionEnergy S w H := by
  unfold collisionEnergy
  exact Finset.sum_nonneg fun z hz =>
    mul_nonneg (hw z hz) (sq_nonneg _)

/-- Every prime occupation observable is an exact null mode of every finite fusion
collision form, independently of the nonnegative collision rates. -/
theorem primeCount_collisionEnergy_zero
    (S : Finset (PrimeOccupation × PrimeOccupation))
    (w : PrimeOccupation × PrimeOccupation → ℝ)
    (p : ℕ) :
    collisionEnergy S w (primeCountR p) = 0 := by
  unfold collisionEnergy
  apply Finset.sum_eq_zero
  intro z hz
  rw [primeCount_collisionDefect_zero]
  ring

end GppPrimeFusionGas

#print axioms GppPrimeFusionGas.primeCount_fuse
#print axioms GppPrimeFusionGas.collisionEnergy_nonneg
#print axioms GppPrimeFusionGas.primeCount_collisionEnergy_zero
