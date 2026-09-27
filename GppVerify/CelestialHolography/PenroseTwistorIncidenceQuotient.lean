import Mathlib.Tactic
import Mathlib.Data.Complex.Basic

/-!
# Rank-two quotient of Penrose raywise local-twistor incidence data

Fix a nonzero primed null spinor `l`.  Along a null ray with tangent
`k = lambda tensor l`, restrict Penrose local-twistor data to the incidence subspace

  omega = f lambda.

The remaining primed component `pi` has two complex components.  The local-twistor
transport reduced in `PenroseLocalTwistorRayReduction` only sees the contraction of `pi`
with `l`.  In two-spinor coordinates the canonical contraction is the alternating bracket

  [l,pi] = l0*pi1 - l1*pi0.

Its kernel is exactly the line spanned by `l`.  Hence the three-dimensional incidence
data `(f,pi)` admit a canonical two-dimensional quotient

  (f,pi)  |->  (f,[l,pi])

modulo the gauge line `(0,c l)`.

This file proves the exact finite algebra:

* `[l,l]=0`;
* for `l != 0`, `[l,pi]=0` iff `pi` is proportional to `l`;
* the reduction map is invariant under `pi -> pi + c l`;
* it is surjective for `l != 0`;
* equal reduced data differ by exactly such a gauge shift;
* rescaling the spinor representative rescales the reduced second coordinate with the
  expected homogeneous weight.

The geometric identification of this quotient with a subquotient of Penrose's curved
local-twistor bundle and its comparison with LeBrun's Einstein bundle remain external/open.
-/

namespace GppPenroseTwistorIncidenceQuotient

abbrev Spinor2C := ℂ × ℂ
abbrev IncidenceDatum := ℂ × Spinor2C
abbrev ReducedDatum := ℂ × ℂ

/-- Canonical antisymmetric contraction of two primed two-spinors. -/
def epsBracket (x y : Spinor2C) : ℂ := x.1*y.2 - x.2*y.1

/-- Coordinate scaling of a two-spinor. -/
def scaleSpinor (c : ℂ) (x : Spinor2C) : Spinor2C := (c*x.1,c*x.2)

/-- Coordinate addition of two-spinors. -/
def addSpinor (x y : Spinor2C) : Spinor2C := (x.1+y.1,x.2+y.2)

/-- Alternating contraction vanishes on the diagonal. -/
theorem epsBracket_self (l : Spinor2C) : epsBracket l l = 0 := by
  rcases l with ⟨l0,l1⟩
  simp [epsBracket]
  ring

/-- The bracket is linear in its second slot. -/
theorem epsBracket_add_right (l x y : Spinor2C) :
    epsBracket l (addSpinor x y) = epsBracket l x + epsBracket l y := by
  rcases l with ⟨l0,l1⟩
  rcases x with ⟨x0,x1⟩
  rcases y with ⟨y0,y1⟩
  simp [epsBracket, addSpinor]
  ring

/-- Scaling in the second slot scales the bracket. -/
theorem epsBracket_scale_right (l x : Spinor2C) (c : ℂ) :
    epsBracket l (scaleSpinor c x) = c * epsBracket l x := by
  rcases l with ⟨l0,l1⟩
  rcases x with ⟨x0,x1⟩
  simp [epsBracket, scaleSpinor]
  ring

/-- Scaling the first slot also scales the bracket. -/
theorem epsBracket_scale_left (l x : Spinor2C) (c : ℂ) :
    epsBracket (scaleSpinor c l) x = c * epsBracket l x := by
  rcases l with ⟨l0,l1⟩
  rcases x with ⟨x0,x1⟩
  simp [epsBracket, scaleSpinor]
  ring

/-- For a nonzero spinor, the alternating annihilator is exactly its own line. -/
theorem epsBracket_eq_zero_iff_span
    (l pi : Spinor2C) (hl : l ≠ (0,0)) :
    epsBracket l pi = 0 ↔ ∃ c : ℂ, pi = scaleSpinor c l := by
  rcases l with ⟨l0,l1⟩
  rcases pi with ⟨p0,p1⟩
  simp only [epsBracket, scaleSpinor, Prod.mk.injEq]
  have hl' : l0 ≠ 0 ∨ l1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hl (by rw [hc.1, hc.2])
  constructor
  · intro h
    rcases hl' with hl0 | hl1
    · refine ⟨p0 / l0, (div_mul_cancel₀ p0 hl0).symm, ?_⟩
      rw [div_mul_eq_mul_div, eq_div_iff hl0]
      linear_combination h
    · refine ⟨p1 / l1, ?_, (div_mul_cancel₀ p1 hl1).symm⟩
      rw [div_mul_eq_mul_div, eq_div_iff hl1]
      linear_combination -h
  · rintro ⟨c, h0, h1⟩
    rw [h0, h1]
    ring

/-- Reduction from the three incidence coordinates to the two quotient coordinates. -/
def reduce (l : Spinor2C) (d : IncidenceDatum) : ReducedDatum :=
  (d.1, epsBracket l d.2)

/-- Gauge shift along the invisible line `(0,c l)`. -/
def gaugeShift (l : Spinor2C) (c : ℂ) (d : IncidenceDatum) : IncidenceDatum :=
  (d.1, addSpinor d.2 (scaleSpinor c l))

/-- Reduction is exactly invariant under the invisible gauge line. -/
theorem reduce_gaugeShift (l : Spinor2C) (c : ℂ) (d : IncidenceDatum) :
    reduce l (gaugeShift l c d) = reduce l d := by
  rcases l with ⟨l0,l1⟩
  rcases d with ⟨f,⟨p0,p1⟩⟩
  apply Prod.ext
  · rfl
  · simp [reduce, gaugeShift, addSpinor, scaleSpinor, epsBracket]
    ring

/-- For nonzero `l`, the quotient map is onto every reduced pair `(f,g)`. -/
theorem reduce_surjective (l : Spinor2C) (hl : l ≠ (0,0)) :
    Function.Surjective (reduce l) := by
  intro y
  rcases y with ⟨f,g⟩
  rcases l with ⟨l0,l1⟩
  have hl' : l0 ≠ 0 ∨ l1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hl (by rw [hc.1, hc.2])
  rcases hl' with hl0 | hl1
  · refine ⟨(f,(0,g/l0)), ?_⟩
    simp only [reduce, epsBracket, Prod.mk.injEq, true_and]
    field_simp
    try ring
  · refine ⟨(f,(-g/l1,0)), ?_⟩
    simp only [reduce, epsBracket, Prod.mk.injEq, true_and]
    field_simp
    try ring

/-- Equality after reduction is exactly equality modulo the one-dimensional gauge line. -/
theorem reduce_eq_iff_gauge
    (l : Spinor2C) (hl : l ≠ (0,0)) (d1 d2 : IncidenceDatum) :
    reduce l d1 = reduce l d2 ↔
      ∃ c : ℂ, d2 = gaugeShift l c d1 := by
  constructor
  · intro h
    rcases l with ⟨l0,l1⟩
    rcases d1 with ⟨f1,⟨a0,a1⟩⟩
    rcases d2 with ⟨f2,⟨b0,b1⟩⟩
    simp only [reduce, epsBracket, Prod.mk.injEq] at h
    obtain ⟨hf, hg⟩ := h
    have hdelta : epsBracket (l0,l1) (b0 - a0, b1 - a1) = 0 := by
      simp only [epsBracket]
      linear_combination -hg
    obtain ⟨c, hc⟩ := (epsBracket_eq_zero_iff_span (l0,l1) _ hl).mp hdelta
    simp only [scaleSpinor, Prod.mk.injEq] at hc
    refine ⟨c, ?_⟩
    simp only [gaugeShift, addSpinor, scaleSpinor, Prod.mk.injEq]
    exact ⟨hf.symm, by linear_combination hc.1, by linear_combination hc.2⟩
  · rintro ⟨c, rfl⟩
    exact (reduce_gaugeShift l c d1).symm

/-- If the primed spinor representative is rescaled, the bracket coordinate has the same
homogeneous weight as that rescaling. -/
theorem reduce_rescaled_spinor
    (a : ℂ) (l : Spinor2C) (d : IncidenceDatum) :
    reduce (scaleSpinor a l) d = (d.1, a * (reduce l d).2) := by
  apply Prod.ext
  · rfl
  · simp [reduce, epsBracket_scale_left]

/-- Simultaneously rescaling the first incidence coefficient by the same factor makes the
whole reduced pair scale homogeneously.  This is the algebra behind projective invariance
of the quotient pair under a compatible spin-frame rescaling. -/
def rescaleIncidenceCoefficient (a : ℂ) (d : IncidenceDatum) : IncidenceDatum :=
  (a*d.1,d.2)

/-- Homogeneous scaling package. -/
theorem reduce_homogeneous_scaling
    (a : ℂ) (l : Spinor2C) (d : IncidenceDatum) :
    reduce (scaleSpinor a l) (rescaleIncidenceCoefficient a d) =
      (a*(reduce l d).1, a*(reduce l d).2) := by
  apply Prod.ext
  · rfl
  · simp [reduce, rescaleIncidenceCoefficient, epsBracket_scale_left]

end GppPenroseTwistorIncidenceQuotient
