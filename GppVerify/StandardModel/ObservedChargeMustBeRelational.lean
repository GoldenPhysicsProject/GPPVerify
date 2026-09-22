import Mathlib.Tactic
import GppVerify.StandardModel.OrientationQuotientUniversalProperty

/-!
# If diagonal reversal is gauge, an observed binary charge is forced to be relational

Assume the microscopic sign pair `(q,t)` has simultaneous reversal as a gauge/deck
identification.  Then any physical binary observable must be invariant under that diagonal
reversal and hence factor through `χ = xor q t`.

Add one experimentally motivated structural property: flipping exactly one microscopic
orientation reverses the observed binary sign.  Then the observable is forced to be either

    χ

or

    not χ,

where the latter is only the global convention for which eigenvalue is called positive.

Therefore a model in which `++` and `--` are the same physical matter state cannot also
interpret the bare first sign `q` itself as the measured electric-charge sign.  The measured
sign must be the relative alignment (up to convention), while bare q and bare t remain
microscopic lift labels.
-/

namespace GppObservedChargeMustBeRelational

open GppOrientationMassTime
open GppOrientationQuotientUniversalProperty

/-- Bare first sign is not diagonal invariant. -/
def bareQBool (x : Bool × Bool) : Bool := x.1

/-- Bare second sign is not diagonal invariant either. -/
def bareTBool (x : Bool × Bool) : Bool := x.2

 theorem bareQ_not_physical_under_diagGauge :
    ¬ (∀ x, bareQBool (diagFlip x) = bareQBool x) := by
  intro h
  have hx := h (false,false)
  decide at hx

 theorem bareT_not_physical_under_diagGauge :
    ¬ (∀ x, bareTBool (diagFlip x) = bareTBool x) := by
  intro h
  have hx := h (false,false)
  decide at hx

/-- A Boolean sign function which reverses under input negation is either identity or NOT. -/
theorem bool_odd_map_id_or_not (g : Bool → Bool)
    (hodd : ∀ c, g (!c) = !(g c)) :
    (∀ c, g c = c) ∨ (∀ c, g c = !c) := by
  cases h0 : g false
  · right
    intro c
    cases c
    · simpa using h0
    · have h := hodd false
      simp [h0] at h
      simpa using h
  · left
    intro c
    cases c
    · simpa using h0
    · have h := hodd false
      simp [h0] at h
      simpa using h

/-- Main forcing theorem: a diagonal-invariant observed sign which flips under one half-flip
is exactly the relational character, up to the overall naming convention for +/- . -/
theorem observed_sign_forced_relational_up_to_convention
    (obs : Bool × Bool → Bool)
    (hdiag : ∀ x, obs (diagFlip x) = obs x)
    (hhalf : ∀ q t, obs (!q,t) = !(obs (q,t))) :
    (∀ x, obs x = xorCharacter x) ∨
    (∀ x, obs x = !(xorCharacter x)) := by
  obtain ⟨g,hg⟩ := invariant_factors_through_xor obs hdiag
  have godd : ∀ c, g (!c) = !(g c) := by
    intro c
    have hh := hhalf false c
    have hleft := hg (true,c)
    have hright := hg (false,c)
    rw [hleft, hright] at hh
    simpa [xorCharacter] using hh
  rcases bool_odd_map_id_or_not g godd with hid | hnot
  · left
    intro x
    rw [hg x, hid (xorCharacter x)]
  · right
    intro x
    rw [hg x, hnot (xorCharacter x)]

/-- If the sign convention is fixed by declaring `++` to be positive, the ambiguity is
removed and the observed sign is exactly `χ`. -/
theorem observed_sign_eq_relational_when_pp_positive
    (obs : Bool × Bool → Bool)
    (hdiag : ∀ x, obs (diagFlip x) = obs x)
    (hhalf : ∀ q t, obs (!q,t) = !(obs (q,t)))
    (hpp : obs (false,false) = false) :
    ∀ x, obs x = xorCharacter x := by
  rcases observed_sign_forced_relational_up_to_convention obs hdiag hhalf with h | h
  · exact h
  · have hc := h (false,false)
    simp [xorCharacter, hpp] at hc

end GppObservedChargeMustBeRelational
