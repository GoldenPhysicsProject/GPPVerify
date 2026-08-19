import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic

/-!
# Spin-statistics ratio from the Dirichlet eta function's `p = 2` Euler factor

Source: `ONON5213.tex`, "Spin-Statistics from the Prime `p = 2`"
(Theorem `thm:spin-stats-p2`). The Dirichlet eta function
`η(s) = (1 - 2^{1-s})ζ(s)` (same convention as the `η` used implicitly in
`GppCompletedEta`, `CompletedEtaZeros.lean`) satisfies
`η(4)/ζ(4) = 1 - 2^{-3} = 7/8` — the fermion-to-boson thermal-capacity
ratio in `3+1` spacetime dimensions cited in the source. This file ties
that ratio to the actual `riemannZeta` machinery (via
`riemannZeta_ne_zero_of_one_le_re` and `riemannZeta_four`) rather than
restating it as bare rational arithmetic.

## What is proved

* `eta_div_zeta_two_mul_nat`: `η(2n)/ζ(2n) = 1 - 2^{1-2n}` for every `n ≥ 1`
  (the manuscript's general claim), unconditionally — this has genuine
  content because it requires `ζ(2n) ≠ 0`, not just algebra.
* `eta_four_div_zeta_four`: the concrete `n = 2` instance, `η(4)/ζ(4) = 7/8`.
* `eta_four_eq`: the explicit numerical value `η(4) = 7π⁴/720`, combining
  the ratio with Mathlib's `riemannZeta_four`.

## What is not claimed

Nothing about the *physical* identification of this ratio with a
fermion/boson thermal-capacity ratio is formalized here — that is a
statement about Bose–Einstein / Fermi–Dirac statistics in a QFT, well
outside what a Lean statement about `riemannZeta` can express. Only the
arithmetic content (the value of the ratio, and that it is
unconditionally the `p = 2` Euler factor of `ζ`) is claimed.
-/

namespace GppSpinStatisticsEta

open Complex

/-- The Dirichlet eta function, `η(s) = (1 - 2^{1-s})ζ(s)`. -/
noncomputable def eta (s : ℂ) : ℂ := (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s

/-- `ζ(2n) ≠ 0` for `n ≥ 1`, from Mathlib's nonvanishing of `ζ` on `Re s ≥ 1`. -/
theorem riemannZeta_two_mul_nat_ne_zero {n : ℕ} (hn : n ≠ 0) :
    riemannZeta ((2 * n : ℕ) : ℂ) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_le_re
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hre : ((2 * n : ℕ) : ℂ).re = 2 * (n : ℝ) := by
    have hcast : ((2 * n : ℕ) : ℂ) = ((2 * (n : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.ofReal_re]
  rw [hre]
  linarith

/-- **Spin-statistics from arithmetic** (`ONON5213.tex`, `thm:spin-stats-p2`,
general form): for every `n ≥ 1`, `η(2n)/ζ(2n) = 1 - 2^{1-2n}` — the `p = 2`
Euler factor removed by passing from `ζ` to `η`, at the even integer `2n`. -/
theorem eta_div_zeta_two_mul_nat {n : ℕ} (hn : n ≠ 0) :
    eta ((2 * n : ℕ) : ℂ) / riemannZeta ((2 * n : ℕ) : ℂ) =
      1 - (2 : ℂ) ^ ((1 : ℂ) - ((2 * n : ℕ) : ℂ)) := by
  unfold eta
  rw [mul_div_assoc, div_self (riemannZeta_two_mul_nat_ne_zero hn), mul_one]

/-- The exponent `1 - 4 = -3` as an integer cast, so `cpow` reduces to `zpow`. -/
private theorem exponent_four_eq : (1 : ℂ) - ((2 * 2 : ℕ) : ℂ) = ((-3 : ℤ) : ℂ) := by
  push_cast; ring

/-- **The `n = 2` instance**: `η(4)/ζ(4) = 1 - 2^{-3} = 7/8`, the specific
ratio the source ties to the fermion/boson thermal-capacity ratio in
`3+1` dimensions. -/
theorem eta_four_div_zeta_four : eta ((2 * 2 : ℕ) : ℂ) / riemannZeta ((2 * 2 : ℕ) : ℂ) = 7 / 8 := by
  rw [eta_div_zeta_two_mul_nat (n := 2) (by norm_num), exponent_four_eq,
    Complex.cpow_intCast]
  norm_num

/-- Restated at the literal numeral `4` (`(2*2 : ℕ) : ℂ = 4`), matching the
source's own indexing by spacetime dimension. -/
theorem eta_four_div_zeta_four' : eta 4 / riemannZeta 4 = 7 / 8 := by
  have h4 : ((2 * 2 : ℕ) : ℂ) = (4 : ℂ) := by norm_num
  rw [← h4]; exact eta_four_div_zeta_four

/-- The explicit numerical value `η(4) = 7π⁴/720`, combining the ratio
with Mathlib's `riemannZeta_four : ζ(4) = π⁴/90`. -/
theorem eta_four_eq : eta 4 = 7 * (Real.pi : ℂ) ^ 4 / 720 := by
  have hz4 : riemannZeta (4 : ℂ) ≠ 0 := by
    have h4 : ((2 * 2 : ℕ) : ℂ) = (4 : ℂ) := by norm_num
    rw [← h4]; exact riemannZeta_two_mul_nat_ne_zero (n := 2) (by norm_num)
  have hratio := eta_four_div_zeta_four'
  rw [div_eq_iff hz4] at hratio
  rw [hratio, riemannZeta_four]
  ring

end GppSpinStatisticsEta
