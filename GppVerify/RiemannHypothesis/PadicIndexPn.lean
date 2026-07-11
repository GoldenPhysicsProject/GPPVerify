import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The index of `pⁿ ℤ_p` in `ℤ_p`

Real infrastructure toward Tate's-thesis p-adic zeta integral (the newly uploaded lecture
notes' Example 4.10). Combines with `HaarSubgroupIndex.lean` and `PadicHaarMeasure.lean`
to eventually give `μ(pⁿ ℤ_p) = p⁻ⁿ`. Not sourced from a specific Golden Physics Project
paper.

The key fact: `PadicInt.toZModPow n : ℤ_p →+* ZMod (pⁿ)` is surjective (proved here from
first principles: it agrees with the already-surjective canonical map `ℕ → ZMod (pⁿ)` on
the image of `ℕ → ℤ_p`, and a map whose restriction is surjective is itself surjective),
so by the first isomorphism theorem `ℤ_p ⧸ ker(toZModPow n) ≃+* ZMod (pⁿ)`. Combined with
Mathlib's `PadicInt.ker_toZModPow` (kernel = `Ideal.span {pⁿ}`), this gives
`Nat.card (ℤ_p ⧸ Ideal.span {pⁿ}) = pⁿ`.
-/

namespace GppPadicIndex

variable (p : ℕ) [Fact p.Prime]

/-- `PadicInt.toZModPow n` is surjective: it agrees with the canonical (surjective) map
    `ℕ → ZMod (pⁿ)` after precomposing with `ℕ → ℤ_p`, so it must itself be surjective. -/
theorem toZModPow_surjective (n : ℕ) :
    Function.Surjective (PadicInt.toZModPow (p := p) n) := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).pos.ne'⟩
  have hcomp : Function.Surjective
      ((PadicInt.toZModPow (p := p) n) ∘ ((↑) : ℕ → PadicInt p)) := by
    intro y
    obtain ⟨m, hm⟩ := ZMod.natCast_zmod_surjective (n := p ^ n) y
    exact ⟨m, by simp [Function.comp, map_natCast, hm]⟩
  exact hcomp.of_comp

/-- **The quotient `ℤ_p ⧸ pⁿ ℤ_p` has exactly `pⁿ` elements.** -/
theorem card_quotient_span_pow (n : ℕ) :
    Nat.card (PadicInt p ⧸ Ideal.span {(p : PadicInt p) ^ n}) = p ^ n := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).pos.ne'⟩
  have hiso :
      PadicInt p ⧸ RingHom.ker (PadicInt.toZModPow (p := p) n) ≃+* ZMod (p ^ n) :=
    RingHom.quotientKerEquivOfSurjective (toZModPow_surjective p n)
  rw [PadicInt.ker_toZModPow] at hiso
  rw [Nat.card_congr hiso.toEquiv, Nat.card_eq_fintype_card, ZMod.card]

end GppPadicIndex
