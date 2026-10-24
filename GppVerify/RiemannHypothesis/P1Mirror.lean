import GppVerify.RiemannHypothesis.LogDerivativeZeroFree

/-!
# A global mirror does not confine zeros to its fixed line: the case of `P¹_ℤ`

Source: Codex, GPP-bridge PR #11 comment 6390241157, Codex's correction of its own phrase "the
global mirror must put all zeros at its fixed centre". Daniel Toupin / Golden Physics Project,
with AI assistance from Codex (statement) and Claude Code (formalization).

With `ξ` the entire Riemann xi function (`GppLogDerivZeroFree.xi`, `ξ(1 − s) = ξ(s)`), the
completion of `ζ(P¹_ℤ, s) = ζ(s) ζ(s − 1)` is `Ξ(s) = ξ(s) ξ(s − 1)`.

* `p1Xi_mirror`: `Ξ(2 − s) = Ξ(s)`, so the whole object has one exact mirror, centred at `s = 1`.
* `differentiable_p1Xi`: `Ξ` is entire.
* `p1Xi_zeros_off_mirror`: every zero `ρ` of `ξ` with `Re ρ = 1/2` gives zeros of `Ξ` at `ρ` and
  `ρ + 1`, on `Re s = 1/2` and `Re s = 3/2`, neither on the mirror line `Re s = 1`.

So an exact global self-mirror does not by itself force zeros onto its fixed line; the
per-grade centres `1/2` (`H⁰`) and `3/2` (`H²`) carry them.

**Scope.** The existence of zeros of `ξ` on the critical line (Hardy) is not in Mathlib and is
taken as a hypothesis in `p1Xi_zeros_off_mirror`. The motivic weight grading, Tate twists and
polarization Codex specifies are not formalized. No claim about RH or BSD.
-/

open GppLogDerivZeroFree

namespace GppP1Mirror

/-- The completed zeta of `P¹_ℤ`, `Ξ(s) = ξ(s) ξ(s − 1)`. -/
noncomputable def p1Xi (s : ℂ) : ℂ := xi s * xi (s - 1)

/-- **One global mirror, centred at `s = 1`.** `Ξ(2 − s) = Ξ(s)`. -/
theorem p1Xi_mirror (s : ℂ) : p1Xi (2 - s) = p1Xi s := by
  unfold p1Xi
  have h1 : xi (2 - s) = xi (s - 1) := by
    rw [show (2 : ℂ) - s = 1 - (s - 1) by ring, xi_one_sub]
  have h2 : xi (2 - s - 1) = xi s := by
    rw [show (2 : ℂ) - s - 1 = 1 - s by ring, xi_one_sub]
  rw [h1, h2, mul_comm]

theorem differentiable_p1Xi : Differentiable ℂ p1Xi :=
  differentiable_xi.mul (differentiable_xi.comp (differentiable_id.sub_const 1))

/-- **Zeros off the mirror line.** A critical-line zero of `ξ` gives zeros of `Ξ` on
`Re s = 1/2` and `Re s = 3/2`. -/
theorem p1Xi_zeros_off_mirror {ρ : ℂ} (hρ : xi ρ = 0) (hre : ρ.re = 1 / 2) :
    p1Xi ρ = 0 ∧ p1Xi (ρ + 1) = 0 ∧ ρ.re ≠ 1 ∧ (ρ + 1).re ≠ 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [p1Xi, hρ]
  · simp [p1Xi, hρ]
  · rw [hre]; norm_num
  · rw [Complex.add_re, hre, Complex.one_re]; norm_num

end GppP1Mirror
