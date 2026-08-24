import Mathlib.Data.Complex.Basic

/-!
# Suzuki reflection symmetry canonically fixes the 0/π Weyl pair: the algebraic core

`formalization_queue` item `dcebf59f` ("Suzuki reflection symmetry canonically fixes the
0/π Weyl pair"), Suzuki-Herglotz thread. The item's own framing: with
`I(z) = ∫ vPlus(x) e^{izx} dx`, `A(z) = (z-i)I(z)`, `B(z) = (z+i)I(-z)`, prove `A(-z)=-B(z)`,
hence `W0 := A+B` is odd and `Wπ := A-B` is even, so `mHat(z) := -i·W0(z)/Wπ(z)` is odd
wherever defined — and its own text says "Pure symmetry/algebra portion should be
sorry-free; functional-analytic Suzuki inputs may be explicit hypotheses."

## What this file proves

Exactly that algebraic core, and it turns out to need **nothing** about the integral
transform `I`, the operator `T`, the reflection `R`, or `vPlus`/`vMinus` at all: once `A`
and `B` are both expressed through the *same* abstract function `I : ℂ → ℂ` as the item's
own formulas do, `A(-z) = -B(z)` is a one-line algebraic identity
(`(-z-i) = -(z+i)`, so `A(-z) = (-z-i)I(-z) = -(z+i)I(-z) = -B(z)`), and everything else —
`B(-z) = -A(z)`, `W0` odd, `Wπ` even, `mHat` odd — follows by the same kind of direct
substitution. This is treated abstractly for arbitrary `I : ℂ → ℂ`, since the queue item
itself separates this algebraic layer from the operator-theoretic definitions of `T`, `R`,
`vPlus`, `vMinus`, `I`.

## What this file does NOT do

Does **not** define the operator `T`, the reflection `R`, the functions `vPlus = T⁻¹eˣ`,
`vMinus = T⁻¹e⁻ˣ`, or the integral transform `I(z) = ∫ vPlus(x)e^{izx}dx` — none of that
functional-analytic machinery is built or needed for this algebraic layer. It also does
not touch the item's final claim ("combined with Suzuki/Livsic Herglotz theorem and
`mHat(i)=i`, this yields a canonical odd normalized finite Herglotz function") — that
still needs the Herglotz/Livsic representation theory confirmed absent from Mathlib in the
Weil-Semiboundedness pass. No axiom, no sorry.
-/

namespace GppWeilParity

/-- `A(z) := (z-i)·I(z)` in the queue item's notation. -/
noncomputable def suzukiA (I : ℂ → ℂ) (z : ℂ) : ℂ := (z - Complex.I) * I z

/-- `B(z) := (z+i)·I(-z)` in the queue item's notation. -/
noncomputable def suzukiB (I : ℂ → ℂ) (z : ℂ) : ℂ := (z + Complex.I) * I (-z)

/-- **`A(-z) = -B(z)`**, purely algebraic from the two definitions above. -/
theorem suzukiA_neg_eq_neg_suzukiB (I : ℂ → ℂ) (z : ℂ) :
    suzukiA I (-z) = -suzukiB I z := by
  unfold suzukiA suzukiB
  ring

/-- **`B(-z) = -A(z)`**, the symmetric companion identity. -/
theorem suzukiB_neg_eq_neg_suzukiA (I : ℂ → ℂ) (z : ℂ) :
    suzukiB I (-z) = -suzukiA I z := by
  unfold suzukiA suzukiB
  ring

/-- `W₀ := A + B` is **odd**. -/
theorem suzukiW0_odd (I : ℂ → ℂ) (z : ℂ) :
    suzukiA I (-z) + suzukiB I (-z) = -(suzukiA I z + suzukiB I z) := by
  rw [suzukiA_neg_eq_neg_suzukiB, suzukiB_neg_eq_neg_suzukiA]
  ring

/-- `Wπ := A - B` is **even**. -/
theorem suzukiWpi_even (I : ℂ → ℂ) (z : ℂ) :
    suzukiA I (-z) - suzukiB I (-z) = suzukiA I z - suzukiB I z := by
  rw [suzukiA_neg_eq_neg_suzukiB, suzukiB_neg_eq_neg_suzukiA]
  ring

/-- **`mHat(z) := -i·W₀(z)/Wπ(z)` is odd** everywhere it is defined (Lean's total division
makes this hold unconditionally as a formula; `Wπ(-z) = Wπ(z)` by `suzukiWpi_even` means
the denominator vanishing at `z` and at `-z` are the same condition, matching the item's
own "wherever defined" phrasing). -/
theorem suzuki_mHat_odd (I : ℂ → ℂ) (z : ℂ) :
    -Complex.I * (suzukiA I (-z) + suzukiB I (-z)) / (suzukiA I (-z) - suzukiB I (-z)) =
      -(-Complex.I * (suzukiA I z + suzukiB I z) / (suzukiA I z - suzukiB I z)) := by
  rw [suzukiW0_odd, suzukiWpi_even]
  ring

end GppWeilParity
