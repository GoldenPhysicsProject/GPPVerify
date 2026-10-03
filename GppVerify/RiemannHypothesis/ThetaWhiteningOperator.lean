import GppVerify.RiemannHypothesis.SU11PrimeBlaschke
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Subalgebra

/-!
# The local Möbius whitening operator and its symbol

Source: Codex, bridge `research/codex/2026-09-30_theta_euler_tfd_whitening.md` (the operator
identity for `W_p`; bridge copy through `59bf0a2`).

For a prime `p` put `r = p^{-1/2}` and let `U = U_{−log p}` be translation by `−log p`, a unitary
operator. The local whitening operator is `W_p = I − r U`.

* `whitening_gram`: in any `*`-ring, if `u* u = 1` (an isometry; unitary in particular) and `r` is a real
  scalar, then `W*W = (1 + r²) I − r (u + u*)`, where `W = 1 − r u`. With `u = U_{−log p}` and
  `u* = U_{log p}` this is the note's
  `W_p^* W_p = (1 + p^{-1}) I − p^{-1/2}(U_{log p} + U_{−log p})`;
* `whitening_symbol`: on the Fourier side `u` acts as `e^{it log p}`, and the symbol of `W*W` is
  `1 + r² − 2 r cos(t log p) = |1 − p^{-1/2+it}|²`; this is the same Poisson-denominator
  that appears in `GppSU11Prime.euler_factor_intensity`;
* `whitening_symbol_pos`: for `|r| < 1` the symbol is strictly positive, so `W*W` is a positive
  invertible multiplier and the whitening is nondegenerate.

## Checks

The identity is the elementary `*`-ring computation; the note's operator order is right
(`W*W` has the `(1 + r²)` diagonal and the two shift terms). No corrections.

## Scope

Abstract `*`-ring algebra and a scalar identity. **Not formalized:** the Hilbert-space action of
translations on `L²(ℝ)`, the theta kernel identity
`Φ(u − a_p) − r_p Φ(u + a_p) = Σ_{p ∤ n} φ_n(u − a_p)` (a bookkeeping identity for series over
integers coprime to `p`), the Euler-product decimation formula, and the Plancherel formula for
`‖R_P‖²`. No RH claim.
-/

open GppSU11Prime

namespace GppThetaWhitening

/-- **Whitening Gram identity.** In a `*`-algebra over `ℝ` with `u* u = 1` and a real scalar `r`,
`(1 − r u)* (1 − r u) = (1 + r²) − r (u + u*)`. -/
theorem whitening_gram {R : Type*} [Ring R] [StarRing R] [Algebra ℝ R] [StarModule ℝ R] (u : R)
    (r : ℝ)
    (hu : star u * u = 1) :
    star (1 - (r : ℝ) • u) * (1 - (r : ℝ) • u) = (1 + (r : ℝ) ^ 2) • (1 : R) - (r : ℝ) • (u + star u) := by
  simp only [star_sub, star_one, star_smul, smul_sub, sub_mul, mul_sub, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm, smul_smul, hu, star_trivial]
  module

/-- **The symbol of `W*W`.** `|1 − r e^{−iθ}|² = 1 − 2 r cos θ + r²`. -/
theorem whitening_symbol (r θ : ℝ) :
    ‖(1 : ℂ) - (r : ℂ) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)‖ ^ 2 =
      1 - 2 * r * Real.cos θ + r ^ 2 := by
  rw [Complex.sq_norm, normSq_one_sub_polar, Real.cos_neg]

/-- **The symbol is strictly positive** for `|r| < 1`. -/
theorem whitening_symbol_pos (r θ : ℝ) (hr : |r| < 1) : 0 < 1 - 2 * r * Real.cos θ + r ^ 2 :=
  den_pos r θ hr

end GppThetaWhitening
