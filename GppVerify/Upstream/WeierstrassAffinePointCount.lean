/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Golden Eye)
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting affine points of a Weierstrass curve over a finite ring

Mathlib-style definitions staged for upstreaming (see `README.md`).

* `WeierstrassCurve.Affine.numAffinePoints W`: the number of `(x, y) ∈ R × R` on `W`. It is a
  `Nat.card`, so it is defined for every ring and is meaningful when `R` is finite.
* `WeierstrassCurve.Affine.numAffinePoints_eq_card_filter`: over a `Fintype` with decidable
  equality it is the cardinality of an explicit `Finset.filter`, so small cases can be settled
  by `decide`.

Over a finite field `𝔽_q`, `#W(𝔽_q) = numAffinePoints + 1` (the point at infinity), and the
trace of Frobenius is `q - numAffinePoints`.
-/

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] (W : WeierstrassCurve.Affine R)

/-- The number of affine points `(x, y) ∈ R × R` on `W`. -/
noncomputable def numAffinePoints : ℕ :=
  Nat.card {P : R × R // W.Equation P.1 P.2}

theorem numAffinePoints_eq_card_filter [Fintype R] [DecidableEq R] :
    W.numAffinePoints = (Finset.univ.filter fun P : R × R =>
      P.2 ^ 2 + W.a₁ * P.1 * P.2 + W.a₃ * P.2 =
        P.1 ^ 3 + W.a₂ * P.1 ^ 2 + W.a₄ * P.1 + W.a₆).card := by
  rw [numAffinePoints, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun P : R × R => W.equation_iff P.1 P.2)

end WeierstrassCurve.Affine
