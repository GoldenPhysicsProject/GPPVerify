import Mathlib.Tactic

/-!
# Many-body no-go: one global diagonal Z2 does not hide per-particle orientation lifts

Suppose a matter particle with relational character `χ=+` has two kinematic lifts, `++` and
`--`.  Encode that remaining lift choice by one hidden bit `h`.

For two particles there are four lift assignments `(h1,h2)`.  If the only redundancy is ONE
global reversal

    (h1,h2) -> (!h1,!h2),

then the relative bit

    r = xor h1 h2

survives.  Thus the quotient still has two distinct sectors: aligned hidden lifts and
opposite hidden lifts.  For N particles the analogous construction would leave N-1
relative bits.

Therefore the statement "every particle can be half ++ and half -- but no local physics can
see which" cannot be implemented by a single global Z2 alone unless dynamics additionally
locks all microscopic lifts together.  To erase all per-particle hidden labels as pure
redundancy, the diagonal flip must act locally/independently enough (a Z2 gauge-type
structure), or an equivalent constraint must remove the relative bits.

This is a finite exact obstruction, not a dynamical claim.
-/

namespace GppManyBodyOrientationRedundancyNoGo

abbrev HiddenPair := Bool × Bool

/-- One global reversal of both particles' hidden lift bits. -/
def globalFlip (x : HiddenPair) : HiddenPair := (!x.1,!x.2)

/-- Relative hidden orientation between two particles. -/
def relativeHidden (x : HiddenPair) : Bool := xor x.1 x.2

/-- The relative hidden bit survives the single global reversal. -/
theorem relativeHidden_globalFlip (x : HiddenPair) :
    relativeHidden (globalFlip x) = relativeHidden x := by
  rcases x with ⟨a,b⟩
  cases a <;> cases b <;> decide

/-- Equality of the surviving relative bit is exactly membership in the global-flip orbit. -/
theorem same_relative_iff_global_orbit (x y : HiddenPair) :
    relativeHidden x = relativeHidden y ↔
      y = x ∨ y = globalFlip x := by
  rcases x with ⟨a,b⟩
  rcases y with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- Concrete obstruction: aligned and anti-aligned hidden assignments are not related by
the single global reversal. -/
theorem global_Z2_not_transitive :
    (false,true) ≠ ((false,false) : HiddenPair) ∧
    (false,true) ≠ globalFlip ((false,false) : HiddenPair) := by
  decide

/-- Independent local flip of particle 1. -/
def flipFirst (x : HiddenPair) : HiddenPair := (!x.1,x.2)

/-- Independent local flip of particle 2. -/
def flipSecond (x : HiddenPair) : HiddenPair := (x.1,!x.2)

/-- Local flips generate the global one. -/
theorem local_flips_compose_global (x : HiddenPair) :
    flipFirst (flipSecond x) = globalFlip x := by
  rcases x with ⟨a,b⟩
  rfl

/-- With independent local flips, every two-particle hidden assignment is reachable from
every other one; no relative hidden bit survives. -/
theorem local_Z2xZ2_transitive (x y : HiddenPair) :
    y = x ∨ y = flipFirst x ∨ y = flipSecond x ∨ y = globalFlip x := by
  rcases x with ⟨a,b⟩
  rcases y with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

end GppManyBodyOrientationRedundancyNoGo
