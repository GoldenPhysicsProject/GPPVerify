import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic

/-!
# The algebraic half of GNS, for a finite group

`HaarPositivityWeil.lean` parks `open_gns_from_positive_type`: a positive-definite function on
a group generates a Hilbert space carrying a unitary representation. Its gap label was
corrected on 2026-09-02 — Mathlib *has* the GNS construction
(`Mathlib/Analysis/CStarAlgebra/GelfandNaimarkSegal.lean`, 2025), for positive linear
functionals on C⋆-algebras. What is missing is the bridge: a C⋆-norm on the group algebra, so
that a positive-definite function on a group becomes a state.

This module does what does not need that bridge — everything about the sesquilinear form a
positive-definite `P` puts on `G → ℂ` directly, for `G` finite:

* `gramForm_translation_invariant` — the form is invariant under left translation. This is the
  content of "the regular representation acts by isometries", and it is where the group
  structure does its work: `(g y)⁻¹ * (g x) = y⁻¹ * x`, so translating both arguments leaves
  every matrix entry alone.
* `gramForm_self_nonneg` — `⟪f, f⟫ ≥ 0`, the semidefiniteness an inner product needs.
* `PositiveDefinite.conj_symm` — `P g⁻¹ = conj (P g)`, from positive-definiteness alone.
* `PositiveDefinite.norm_le` — `‖P g‖ ≤ (P 1).re`: the value at the identity dominates.

## The definition takes `ℂ`'s order, and that is not a detail

`GppHaarPositivityWeil.PositiveType` asks only that the quadratic form have nonnegative *real
part*. That is fine there, because the `P` in question is real-valued. Carried over to a
complex `P` it is too weak, and **`conj_symm` is false under it** — the compiler caught this
here on 2026-09-02, on a first draft that tried to prove it.

The counterexample is small enough to keep: `G = ℤ/2 = {1, g}`, `P 1 = 1`, `P g = I`. Then for
any `s t : ℂ`,

    Re(conj s * s * 1 + conj t * s * I + conj s * t * I + conj t * t * 1)
      = |s|² + |t|² + Re(I * 2 * Re(conj s * t))  =  |s|² + |t|² ≥ 0,

since `Re(I * r) = 0` for real `r`. So the real-part condition holds, while `P g⁻¹ = P g = I`
and `conj (P g) = -I`. Hermitian symmetry genuinely does not follow.

So `PositiveDefinite` below uses the `ComplexOrder` scoped order, under which `0 ≤ z` means
`0 ≤ z.re` **and** `z.im = 0`. That is the standard definition, and the vanishing imaginary
part is exactly what `conj_symm` consumes.

## What is deliberately not here

The Hilbert space itself. Passing from this semidefinite form to an inner-product space means
quotienting by `{f | ⟪f, f⟫ = 0}` and, in the infinite case, completing — which is the work
Mathlib's `PositiveLinearMap.PreGNS` / `.GNS` already does one level up, on a C⋆-algebra.
Rebuilding it here for `G → ℂ` would be constructing the thing the library has instead of the
bridge it lacks. The honest split: the algebra is here, the analysis is Mathlib's, and the
missing piece between them is the group C⋆-algebra.

`open_gns_from_positive_type` therefore stays open. It stands for less than it did.
-/

namespace GppFiniteGNS

open Finset
open scoped ComplexOrder

/-- `P : G → ℂ` is positive-definite: every matrix `[P (gⱼ⁻¹ * gᵢ)]` is positive semidefinite.

The inequality is in `ℂ`'s `ComplexOrder`, so it says the quadratic form is a nonnegative
**real** number. Demanding only `0 ≤ (…).re` would be strictly weaker and would not imply
Hermitian symmetry — see the module docstring for the two-element counterexample. -/
def PositiveDefinite {G : Type*} [Group G] (P : G → ℂ) : Prop :=
  ∀ (n : ℕ) (g : Fin n → G) (c : Fin n → ℂ),
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, (starRingEnd ℂ) (c j) * c i * P ((g j)⁻¹ * g i)

/-- The sesquilinear form `P` induces on functions `G → ℂ`:
`⟪f, h⟫ = ∑_{x,y} conj (h y) * f x * P (y⁻¹ x)`. -/
noncomputable def gramForm {G : Type*} [Group G] [Fintype G] (P : G → ℂ) (f h : G → ℂ) : ℂ :=
  ∑ x : G, ∑ y : G, (starRingEnd ℂ) (h y) * f x * P (y⁻¹ * x)

/-- Left translation of a function: `(translate g f) x = f (g⁻¹ x)`. -/
def translate {G : Type*} [Group G] (g : G) (f : G → ℂ) : G → ℂ := fun x => f (g⁻¹ * x)

@[simp]
theorem translate_one {G : Type*} [Group G] (f : G → ℂ) : translate (1 : G) f = f := by
  funext x; simp [translate]

/-! ### Translation invariance

The regular representation acts by isometries of `gramForm`. This is the whole reason a
positive-definite function on a *group* gives a representation and not merely a Hilbert space:
the form does not see a simultaneous shift of both arguments, because `P` is evaluated at
`y⁻¹ x`, which is invariant under `(x, y) ↦ (g x, g y)`. -/

/-- **Left translation preserves the form.** -/
theorem gramForm_translation_invariant {G : Type*} [Group G] [Fintype G]
    (P : G → ℂ) (g : G) (f h : G → ℂ) :
    gramForm P (translate g f) (translate g h) = gramForm P f h := by
  simp only [gramForm, translate]
  rw [← Equiv.sum_comp (Equiv.mulLeft g)
    (fun x : G => ∑ y : G, (starRingEnd ℂ) (h (g⁻¹ * y)) * f (g⁻¹ * x) * P (y⁻¹ * x))]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← Equiv.sum_comp (Equiv.mulLeft g)
    (fun y : G => (starRingEnd ℂ) (h (g⁻¹ * y))
      * f (g⁻¹ * ((Equiv.mulLeft g) x)) * P (y⁻¹ * ((Equiv.mulLeft g) x)))]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  simp only [Equiv.coe_mulLeft]
  rw [show g⁻¹ * (g * y) = y by group, show g⁻¹ * (g * x) = x by group,
    show (g * y)⁻¹ * (g * x) = y⁻¹ * x by group]

/-! ### Positive semidefiniteness -/

/-- **The form is positive semidefinite.** `gramForm P f f` is the quadratic form of the
definition, taken over the whole group as index set. -/
theorem gramForm_self_nonneg {G : Type*} [Group G] [Fintype G]
    {P : G → ℂ} (hP : PositiveDefinite P) (f : G → ℂ) : 0 ≤ gramForm P f f := by
  classical
  let e : G ≃ Fin (Fintype.card G) := Fintype.equivFin G
  have h := hP (Fintype.card G) (fun i => e.symm i) (fun i => f (e.symm i))
  refine le_of_le_of_eq h ?_
  simp only [gramForm]
  rw [← Equiv.sum_comp e.symm (fun x : G => ∑ y : G,
    (starRingEnd ℂ) (f y) * f x * P (y⁻¹ * x))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Equiv.sum_comp e.symm (fun y : G =>
    (starRingEnd ℂ) (f y) * f (e.symm i) * P (y⁻¹ * (e.symm i)))]

/-! ### Consequences of positive-definiteness alone

These do not mention `gramForm`; they are what the definition forces on `P` itself. -/

/-- Two-point specialisation of the definition, the workhorse below: for any `a b : G` and
coefficients `s t`, the `2 × 2` quadratic form is a nonnegative real. -/
theorem PositiveDefinite.two_point {G : Type*} [Group G] {P : G → ℂ}
    (hP : PositiveDefinite P) (a b : G) (s t : ℂ) :
    0 ≤ (starRingEnd ℂ) s * s * P (a⁻¹ * a) + (starRingEnd ℂ) t * s * P (b⁻¹ * a)
        + ((starRingEnd ℂ) s * t * P (a⁻¹ * b) + (starRingEnd ℂ) t * t * P (b⁻¹ * b)) := by
  simpa [Fin.sum_univ_two] using hP 2 ![a, b] ![s, t]

/-- The one-parameter family the two structural results both consume: the `2 × 2` form at
`(1, g)` with first coefficient `1`. -/
theorem PositiveDefinite.base {G : Type*} [Group G] {P : G → ℂ}
    (hP : PositiveDefinite P) (g : G) (t : ℂ) :
    0 ≤ P 1 + (starRingEnd ℂ) t * P g⁻¹ + (t * P g + (starRingEnd ℂ) t * t * P 1) := by
  have h := hP.two_point 1 g 1 t
  rw [show ((1 : G)⁻¹ * 1) = (1 : G) by group, show (g⁻¹ * (1 : G)) = g⁻¹ by group,
    show ((1 : G)⁻¹ * g) = g by group, show (g⁻¹ * g) = (1 : G) by group] at h
  simpa using h

/-- **`P 1` is a nonnegative real.** -/
theorem PositiveDefinite.apply_one_nonneg {G : Type*} [Group G] {P : G → ℂ}
    (hP : PositiveDefinite P) : 0 ≤ P 1 := by
  simpa using hP.base 1 0

/-- **`P g⁻¹ = conj (P g)`.**

The `2 × 2` minor at `(1, g)` is nonnegative *as a complex number*, so its imaginary part
vanishes for every test coefficient `t`. Taking `t = 0, 1, I` reads off, in turn, that `P 1` is
real, that `Im (P g⁻¹) = -Im (P g)`, and that `Re (P g⁻¹) = Re (P g)`. -/
theorem PositiveDefinite.conj_symm {G : Type*} [Group G] {P : G → ℂ}
    (hP : PositiveDefinite P) (g : G) : P g⁻¹ = (starRingEnd ℂ) (P g) := by
  have him : ∀ t : ℂ,
      (P 1 + (starRingEnd ℂ) t * P g⁻¹ + (t * P g + (starRingEnd ℂ) t * t * P 1)).im = 0 :=
    fun t => (RCLike.nonneg_iff.mp (hP.base g t)).2
  have e0 := him 0
  have e1 := him 1
  have eI := him Complex.I
  simp [Complex.add_im, Complex.mul_im] at e0 e1 eI
  apply Complex.ext
  · simp only [Complex.conj_re]; linarith
  · simp only [Complex.conj_im]; linarith

/-- **`P` is dominated by its value at the identity:** `‖P g‖ ≤ (P 1).re`.

Given `conj_symm`, the `2 × 2` minor at `(1, g)` is a genuine Hermitian PSD matrix. Testing it
against `t = -conj (P g) / ‖P g‖` — the unit direction that makes both cross terms equal
`-‖P g‖` — turns nonnegativity into exactly this bound. -/
theorem PositiveDefinite.norm_le {G : Type*} [Group G] {P : G → ℂ}
    (hP : PositiveDefinite P) (g : G) : ‖P g‖ ≤ (P 1).re := by
  rcases eq_or_ne (P g) 0 with hz | hz
  · simpa [hz] using (RCLike.nonneg_iff.mp hP.apply_one_nonneg).1
  set t : ℂ := -(starRingEnd ℂ) (P g) / (‖P g‖ : ℂ) with ht
  have hnorm : (‖P g‖ : ℂ) ≠ 0 := by simpa using (norm_ne_zero_iff.mpr hz)
  have hself : (starRingEnd ℂ) (P g) * P g = ((‖P g‖ : ℂ)) ^ 2 := by
    rw [← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_eq_norm_sq]
  have hmul : (starRingEnd ℂ) t * t = 1 := by
    rw [ht, map_div₀, map_neg, Complex.conj_conj, Complex.conj_ofReal]
    field_simp
    rw [mul_comm, hself]
  have hcross : t * P g + (starRingEnd ℂ) t * P g⁻¹ = -2 * (‖P g‖ : ℂ) := by
    rw [hP.conj_symm g, ht, map_div₀, map_neg, Complex.conj_conj, Complex.conj_ofReal]
    field_simp
    rw [hself]
    ring
  have h := (RCLike.nonneg_iff.mp (hP.base g t)).1
  have hrw : P 1 + (starRingEnd ℂ) t * P g⁻¹ + (t * P g + (starRingEnd ℂ) t * t * P 1)
      = 2 * P 1 - 2 * (‖P g‖ : ℂ) := by
    rw [hmul, one_mul,
      show P 1 + (starRingEnd ℂ) t * P g⁻¹ + (t * P g + P 1)
        = (t * P g + (starRingEnd ℂ) t * P g⁻¹) + 2 * P 1 by ring, hcross]
    ring
  rw [hrw] at h
  simp [Complex.sub_re, Complex.mul_re] at h
  linarith

end GppFiniteGNS
