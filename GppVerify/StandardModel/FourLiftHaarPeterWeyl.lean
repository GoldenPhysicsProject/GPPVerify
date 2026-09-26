import Mathlib.Tactic
import GppVerify.StandardModel.FourOrientationGaugeProjection

/-!
# Finite Haar/Peter--Weyl face of the four-lift orientation carrier

The four microscopic labels form the Klein group

    V₄ = Z₂ × Z₂.

Its four one-dimensional characters are

    1, q, t, χ=q t.

The diagonal deck element D flips both signs.  Averaging over the subgroup <D> is the
normalized finite Haar projector

    P_D f(x) = (f(x) + f(Dx))/2.

This file proves directly that P_D fixes exactly the trivial and relational characters
among the four canonical V₄ characters and annihilates q and t.  More strongly, every
D-invariant function on V₄ is uniquely of the form

    a · 1 + b · χ.

Thus the D-even sector has exactly two complex amplitudes.  This is the finite compact
Peter--Weyl analogue of the project's other Haar constructions; no physical claim that
D is a gauge redundancy is assumed here.
-/

namespace GppFourLiftHaarPeterWeyl

noncomputable section

abbrev V4 := Bool × Bool

/-- Convert a binary orientation bit into the sign ±1. -/
def sgnBit (b : Bool) : ℂ := if b then -1 else 1

/-- Simultaneous reversal of both V4 factors. -/
def deckD (x : V4) : V4 := (Bool.not x.1, Bool.not x.2)

/-- The four canonical one-dimensional characters of V4. -/
def oneChar (_x : V4) : ℂ := 1
def qChar (x : V4) : ℂ := sgnBit x.1
def tChar (x : V4) : ℂ := sgnBit x.2
def chiChar (x : V4) : ℂ := qChar x * tChar x

/-- Normalized Haar average over the diagonal order-two subgroup <D>. -/
def haarD (f : V4 → ℂ) : V4 → ℂ :=
  fun x => (f x + f (deckD x)) / 2

lemma sgnBit_not (b : Bool) : sgnBit (Bool.not b) = - sgnBit b := by
  cases b <;> norm_num [sgnBit]

lemma deckD_sq (x : V4) : deckD (deckD x) = x := by
  rcases x with ⟨q,t⟩
  cases q <;> cases t <;> rfl

lemma qChar_deck (x : V4) : qChar (deckD x) = -qChar x := by
  rcases x with ⟨q,t⟩
  simp [qChar, deckD, sgnBit_not]

lemma tChar_deck (x : V4) : tChar (deckD x) = -tChar x := by
  rcases x with ⟨q,t⟩
  simp [tChar, deckD, sgnBit_not]

lemma chiChar_deck (x : V4) : chiChar (deckD x) = chiChar x := by
  rcases x with ⟨q,t⟩
  simp [chiChar, qChar, tChar, deckD, sgnBit_not]

/-- The finite Haar projector is idempotent. -/
theorem haarD_idempotent (f : V4 → ℂ) :
    haarD (haarD f) = haarD f := by
  funext x
  simp only [haarD]
  rw [deckD_sq]
  ring

/-- Haar projection fixes the trivial character. -/
theorem haarD_one : haarD oneChar = oneChar := by
  funext x
  simp [haarD, oneChar]

/-- Haar projection kills the bare q-character. -/
theorem haarD_q : haarD qChar = 0 := by
  funext x
  simp [haarD, qChar_deck]

/-- Haar projection kills the bare t-character. -/
theorem haarD_t : haarD tChar = 0 := by
  funext x
  simp [haarD, tChar_deck]

/-- Haar projection fixes the relational character χ=q t. -/
theorem haarD_chi : haarD chiChar = chiChar := by
  funext x
  simp [haarD, chiChar_deck]

/-- The canonical V4 characters therefore split under <D>-Haar projection as 2+2. -/
theorem canonical_character_projection :
    haarD oneChar = oneChar ∧
    haarD qChar = 0 ∧
    haarD tChar = 0 ∧
    haarD chiChar = chiChar := by
  exact ⟨haarD_one, haarD_q, haarD_t, haarD_chi⟩

/--
Every D-invariant function on V4 is a linear combination of the trivial character and χ.
This is the exact rank-two fixed-sector statement, expressed without matrix-rank machinery.
-/
theorem invariant_function_eq_one_plus_chi
    (f : V4 → ℂ)
    (hD : ∀ x, f (deckD x) = f x) :
    ∃ a b : ℂ, ∀ x, f x = a * oneChar x + b * chiChar x := by
  let f0 : ℂ := f (false,false)
  let f1 : ℂ := f (false,true)
  let a : ℂ := (f0 + f1) / 2
  let b : ℂ := (f0 - f1) / 2
  refine ⟨a,b,?_⟩
  intro x
  rcases x with ⟨q,t⟩
  cases q <;> cases t
  · simp [a,b,f0,f1,oneChar,chiChar,qChar,tChar,sgnBit]
    ring
  · simp [a,b,f0,f1,oneChar,chiChar,qChar,tChar,sgnBit]
    ring
  · have h := hD (false,true)
    simp [deckD] at h
    simp [a,b,f0,f1,oneChar,chiChar,qChar,tChar,sgnBit,h]
    ring
  · have h := hD (false,false)
    simp [deckD] at h
    simp [a,b,f0,f1,oneChar,chiChar,qChar,tChar,sgnBit,h]
    ring

/-- The two surviving characters are linearly independent. -/
theorem one_chi_independent
    (a b : ℂ)
    (h : ∀ x, a * oneChar x + b * chiChar x = 0) :
    a = 0 ∧ b = 0 := by
  have h0 := h (false,false)
  have h1 := h (false,true)
  norm_num [oneChar,chiChar,qChar,tChar,sgnBit] at h0 h1
  constructor <;> linear_combination h0 + h1

/--
Capstone: the finite Haar-fixed sector is exactly the two-character sector {1,χ}.
This is the finite compact face of the orientation Haar construction.
-/
theorem finite_haar_fixed_sector_capstone
    (f : V4 → ℂ)
    (hD : ∀ x, f (deckD x) = f x) :
    ∃! ab : ℂ × ℂ,
      ∀ x, f x = ab.1 * oneChar x + ab.2 * chiChar x := by
  obtain ⟨a,b,hab⟩ := invariant_function_eq_one_plus_chi f hD
  refine ⟨(a,b), ?_, ?_⟩
  · exact hab
  · intro cd hcd
    apply Prod.ext
    · have hzero : ∀ x,
          (a - cd.1) * oneChar x + (b - cd.2) * chiChar x = 0 := by
        intro x
        have ha := hab x
        have hc := hcd x
        linear_combination ha - hc
      exact sub_eq_zero.mp (one_chi_independent (a-cd.1) (b-cd.2) hzero).1
    · have hzero : ∀ x,
          (a - cd.1) * oneChar x + (b - cd.2) * chiChar x = 0 := by
        intro x
        have ha := hab x
        have hc := hcd x
        linear_combination ha - hc
      exact sub_eq_zero.mp (one_chi_independent (a-cd.1) (b-cd.2) hzero).2


end
end GppFourLiftHaarPeterWeyl

#print axioms GppFourLiftHaarPeterWeyl.canonical_character_projection
#print axioms GppFourLiftHaarPeterWeyl.finite_haar_fixed_sector_capstone
