import Mathlib.Tactic

/-!
# *Which Way Is Forward?*: Majorana–Weyl rank arithmetic and the Feynman phase identity

Source: Daniel Toupin, *Which Way Is Forward?* (v26), and its check script
`verify_wwif.py`, functions `verify_compton_and_spin102_arithmetic` and
`verify_feynman_phase`. These are the arithmetic claims left over after
`OrientationCliffordCore` and `WhichWayForwardV26Gaps`:

* the Majorana–Weyl extension ranks: among `n ∈ [0, 13)`, exactly `n = 4` and
  `n = 12` satisfy `(4 + n) % 8 = 0`;
* the factorwise Majorana–Weyl checks for the two splittings of the
  `(10, 2)` parent: signature differences `1 - 1`, `9 - 1` and `2 - 2`, `8 - 0`
  are all `≡ 0 (mod 8)`;
* the Feynman phase identity (the script's Eq. `feynmanphasemonotone`): if
  `t = ±1` is the sign of both `E` and the time step `d` (that is,
  `t * E = |E|` and `t * d = |d|`), then `E * d = |E| * |d|` and the oriented
  rate `t * E` is `|E| ≥ 0`.

Scope: pure arithmetic. The Bott-periodicity reading of the mod-8 conditions
and the physical reading of the phase identity are dictionary statements and
are not asserted here.
-/

namespace GppWhichWayForwardArithmetic

/-- **Majorana–Weyl extension ranks.** Among `n < 13`, exactly `n = 4` and
`n = 12` make `(4 + n)` divisible by `8`. -/
theorem mw_extension_ranks :
    (List.range 13).filter (fun n => (4 + n) % 8 = 0) = [4, 12] := by
  decide

/-- **Factorwise check, splitting `(1,1) + (9,1)`.** Both signature
differences are divisible by `8`. -/
theorem mw_factorwise_11_91 : (1 - 1) % 8 = 0 ∧ (9 - 1) % 8 = 0 := by
  decide

/-- **Factorwise check, splitting `(2,2) + (8,0)`.** Both signature
differences are divisible by `8`. -/
theorem mw_factorwise_22_80 : (2 - 2) % 8 = 0 ∧ (8 - 0) % 8 = 0 := by
  decide

/-- **The Feynman phase identity.** With `t = ±1` the common sign of `E` and
of the step `d` (`t * E = |E|`, `t * d = |d|`), the product `E * d` is the
product of the absolute values, and the oriented rate `t * E` equals `|E|`,
in particular it is nonnegative. -/
theorem feynman_phase (t E d : ℝ) (ht : t = 1 ∨ t = -1)
    (hE : t * E = |E|) (hd : t * d = |d|) :
    E * d = |E| * |d| ∧ t * E = |E| ∧ 0 ≤ |E| := by
  have ht2 : t * t = 1 := by rcases ht with rfl | rfl <;> norm_num
  have hE' : E = t * |E| := by rw [← hE, ← mul_assoc, ht2, one_mul]
  have hd' : d = t * |d| := by rw [← hd, ← mul_assoc, ht2, one_mul]
  refine ⟨?_, hE, abs_nonneg E⟩
  conv_lhs => rw [hE', hd']
  have hring : (t * |E|) * (t * |d|) = (t * t) * (|E| * |d|) := by ring
  rw [hring, ht2, one_mul]

end GppWhichWayForwardArithmetic
