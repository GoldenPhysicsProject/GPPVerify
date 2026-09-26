import GppVerify.RiemannHypothesis.PadicZetaIntegralClosedForm
import Mathlib.Tactic

/-!
# p-adic conformal scaling from Tate shell integrals

For a fixed prime `p`, the p-adic unit ball decomposes into valuation shells
`p^n Z_p^×`.  If the conformal/scaling weight is written as `Delta`, the Tate
integrand uses exponent `s = Delta - 1`, and the exact shell integral is

  I_n(Delta) = (1-p⁻¹) (p⁻Delta)^n.

Thus one step toward the Bruhat--Tits boundary multiplies the shell contribution
by the exact primary scaling eigenvalue `p⁻Delta`:

  I_{n+1}(Delta) = p⁻Delta I_n(Delta).

This is an exact local non-Archimedean scaling law derived from the already
formalized p-adic Haar/Tate integral.  It is compatible with the radial direction
of p-adic CFT/Bruhat--Tits constructions, but no full p-adic operator algebra or
AdS/CFT correspondence is asserted here.
-/

namespace GppPadicConformalScaling

open MeasureTheory
open scoped ENNReal
open GppPadicFullZeta

variable (p : ℕ) [Fact p.Prime]

/-- Local one-step scaling eigenvalue associated with weight `Delta`. -/
noncomputable def primaryScale (Delta : ℝ) : ℝ≥0∞ :=
  (p : ℝ≥0∞) ^ (-Delta)

/-- Tate shell contribution written in the conformal-weight convention
`s = Delta - 1`. -/
noncomputable def primaryShellIntegral (Delta : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ x in shell p n, normRpow p (Delta - 1) x ∂(GppPadicHaar.haarMeasure p)

/-- Exact closed form: each valuation shell is a geometric primary descendant. -/
theorem primaryShellIntegral_eq (Delta : ℝ) (n : ℕ) :
    primaryShellIntegral p Delta n =
      (1 - (p : ℝ≥0∞)⁻¹) * (primaryScale p Delta) ^ n := by
  unfold primaryShellIntegral primaryScale
  rw [shell_term_eq]
  congr 2
  ring_nf

/-- **Local p-adic primary scaling law.** Moving one valuation shell inward
multiplies the contribution by `p^{-Delta}` exactly. -/
theorem primaryShellIntegral_succ (Delta : ℝ) (n : ℕ) :
    primaryShellIntegral p Delta (n + 1) =
      primaryScale p Delta * primaryShellIntegral p Delta n := by
  rw [primaryShellIntegral_eq, primaryShellIntegral_eq, pow_succ]
  ac_rfl

/-- The shell ratio is independent of level whenever the current shell is a
finite nonzero `ENNReal`.  Both hypotheses are required for cancellation in
`ℝ≥0∞`; finiteness must not be silently inferred merely from nonvanishing. -/
theorem primaryShellIntegral_ratio
    (Delta : ℝ) (n : ℕ)
    (hn : primaryShellIntegral p Delta n ≠ 0)
    (hfin : primaryShellIntegral p Delta n ≠ ⊤) :
    primaryShellIntegral p Delta (n + 1) /
        primaryShellIntegral p Delta n = primaryScale p Delta := by
  rw [primaryShellIntegral_succ]
  exact ENNReal.mul_div_cancel_right hn hfin

/-- At weight zero, the local scaling eigenvalue is trivial. -/
@[simp] theorem primaryScale_zero : primaryScale p 0 = 1 := by
  simp [primaryScale]

end GppPadicConformalScaling

#print axioms GppPadicConformalScaling.primaryShellIntegral_eq
#print axioms GppPadicConformalScaling.primaryShellIntegral_succ
#print axioms GppPadicConformalScaling.primaryShellIntegral_ratio
