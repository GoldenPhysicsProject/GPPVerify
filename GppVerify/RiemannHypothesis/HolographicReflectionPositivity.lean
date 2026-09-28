import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Holographic reflection positivity: positivity across the equator ⟺ no mirror pairs

Arithmetic holography (Daniel Toupin, Codex, 2026-09-27; this finite core formalized 2026-09-28).

The completed zeta function lives on the Riemann sphere of the spectral variable `s`. The
critical line together with `∞` is a great circle `L` (the *equator*), the fixed set of the
antiholomorphic reflection `τ(s) = 1 - s̄`, which exchanges the two hemispheres
`Re s > 1/2` and `Re s < 1/2`. By the functional equation and reality, `ξ ∘ τ = conj ∘ ξ`, so
the zero set is `τ`-invariant (in this tree: `fePartner_zero_of_strip`). A zero on `L` is
`τ`-fixed; an off-line zero comes with its mirror image as a *mirror pair*.

On the boundary side of the Mellin duality, `τ` is the inversion `x ↦ 1/x` of the multiplicative
line about its fixed point `x = 1`, and Weil's criterion says RH is equivalent to
**reflection positivity** of the explicit-formula distribution with respect to that inversion.
The spectral side of Weil's form is a sum over zeros `Σ_ρ m_ρ F(ρ) conj F(τ ρ)`.

This file proves the finite, exact core of that equivalence: for a finite set of points with an
involution `τ` and positive `τ`-invariant multiplicities `m`, the Hermitian form

  `Q(v) = Σ_z m_z v_z conj(v_{τ z})`

is real (`reflectionForm_im`) and

* `reflectionForm_nonneg_iff`: `Q ≥ 0` for every `v` **iff** `τ` fixes every point;
* `mirror_pair_indefinite`: a single mirror pair `z ≠ τ z` spans a hyperbolic plane — `Q` takes
  the value `2 m_z > 0` on `(1, 1)` and `-2 m_z < 0` on `(1, -1)`.

In holographic language: equator (boundary) modes contribute `m |v|² ≥ 0`; every bulk mirror
pair contributes one positive and one negative ("ghost") direction, so reflection positivity is
exactly the absence of bulk mirror pairs.

## Scope

Finite algebra only. Passing from this finite statement to Weil's criterion requires the
explicit formula and that the sample vectors `v_ρ = F(ρ)` be independently prescribable by test
functions, neither of which is formalized here. This file does not construct a
reflection-positive arithmetic distribution; that construction is the RH-strength step.
-/

open Finset ComplexConjugate

namespace GppHolographicRP

variable {Z : Type*} [Fintype Z] [DecidableEq Z]

/-- The reflection form `Q(v) = Σ_z m_z v_z conj(v_{τ z})`. -/
def reflectionForm (τ : Z → Z) (m : Z → ℝ) (v : Z → ℂ) : ℂ :=
  ∑ z, (m z : ℂ) * (v z * conj (v (τ z)))

omit [DecidableEq Z] in
/-- The reflection form is real when `τ` is an involution and `m` is `τ`-invariant. -/
theorem reflectionForm_im (τ : Z → Z) (hτ : ∀ z, τ (τ z) = z) (m : Z → ℝ)
    (hm : ∀ z, m (τ z) = m z) (v : Z → ℂ) : (reflectionForm τ m v).im = 0 := by
  have hbij : Function.Bijective τ :=
    Function.Involutive.bijective (fun z => hτ z)
  have hconj : conj (reflectionForm τ m v) = reflectionForm τ m v := by
    unfold reflectionForm
    rw [map_sum]
    refine (Fintype.sum_bijective τ hbij _ _ (fun z => ?_)).symm
    rw [hτ, hm]
    simp [mul_comm]
  have := congrArg Complex.im hconj
  rw [Complex.conj_im] at this
  linarith

omit [DecidableEq Z] in
/-- If `τ` fixes every point, the form is `Σ m_z |v_z|² ≥ 0`. -/
theorem reflectionForm_nonneg_of_fixed (τ : Z → Z) (hfix : ∀ z, τ z = z) (m : Z → ℝ)
    (hm0 : ∀ z, 0 ≤ m z) (v : Z → ℂ) : 0 ≤ (reflectionForm τ m v).re := by
  unfold reflectionForm
  rw [Complex.re_sum]
  refine sum_nonneg (fun z _ => ?_)
  rw [hfix z, Complex.mul_conj, ← Complex.ofReal_mul]
  simp only [Complex.ofReal_re]
  exact mul_nonneg (hm0 z) (Complex.normSq_nonneg _)

/-- **A mirror pair is a hyperbolic plane.** If `τ z ≠ z`, the vector supported on
`{z, τ z}` with values `(1, -1)` has `Q = -(m_z + m_{τ z}) < 0`, while `(1, 1)` gives
`Q = m_z + m_{τ z} > 0`. -/
theorem mirror_pair_indefinite (τ : Z → Z) (hτ : ∀ z, τ (τ z) = z) (m : Z → ℝ)
    (z : Z) (hz : τ z ≠ z) :
    reflectionForm τ m (fun w => if w = z then 1 else if w = τ z then -1 else 0) =
        -((m z : ℂ) + m (τ z)) ∧
      reflectionForm τ m (fun w => if w = z then 1 else if w = τ z then 1 else 0) =
        (m z : ℂ) + m (τ z) := by
  have hz' : z ≠ τ z := fun h => hz h.symm
  constructor <;>
  · unfold reflectionForm
    rw [← sum_subset (subset_univ {z, τ z}) (fun w _ hw => ?_), sum_pair hz']
    · simp [hτ, hz]
      try ring
    · have h1 : w ≠ z := fun h => hw (by simp [h])
      have h2 : w ≠ τ z := fun h => hw (by simp [h])
      simp [h1, h2]

/-- **Reflection positivity ⟺ no mirror pairs.** For an involution `τ` and strictly positive
`τ`-invariant multiplicities, the reflection form is nonnegative on every vector if and only
if `τ` fixes every point. -/
theorem reflectionForm_nonneg_iff (τ : Z → Z) (hτ : ∀ z, τ (τ z) = z) (m : Z → ℝ)
    (hm0 : ∀ z, 0 < m z) :
    (∀ v : Z → ℂ, 0 ≤ (reflectionForm τ m v).re) ↔ ∀ z, τ z = z := by
  constructor
  · intro hpos z
    by_contra hz
    have h := (mirror_pair_indefinite τ hτ m z hz).1
    have := hpos (fun w => if w = z then 1 else if w = τ z then -1 else 0)
    rw [h] at this
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re] at this
    linarith [hm0 z, hm0 (τ z)]
  · intro hfix v
    exact reflectionForm_nonneg_of_fixed τ hfix m (fun z => (hm0 z).le) v

end GppHolographicRP
