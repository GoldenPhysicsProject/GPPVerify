import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Casimir fold and completion boundary index

Pure algebra behind the canonical shadow-invariant RH fold.

The variable `rho * (1-rho)` is invariant under `rho ↦ 1-rho` and is the
quadratic `sl(2)`/Riemann Casimir coordinate.  For `rho = beta + i gamma`,
its imaginary part is `gamma * (1-2*beta)`, so for a nonreal zero it is real
exactly on the critical line.  Its real part is strictly positive throughout
the open critical strip.

The file also records two bookkeeping identities used by the completed
logarithmic derivative:

* the earlier fold `1-(rho-1/2)^2` is just the Casimir fold translated by
  `3/4`;
* after the change of variable `u=s(s-1)`, the two elementary completion
  terms `1/s + 1/(s-1)` collapse to the single boundary index `1/u` after
  division by `du/ds = 2s-1`.

These are unconditional algebraic identities.  No positivity theorem and no
claim of RH is made here.
-/

namespace GppCasimirFold

open Complex

/-- The shadow-invariant quadratic fold. -/
noncomputable def casimirFold (rho : ℂ) : ℂ := rho * (1 - rho)

/-- Shadow invariance of the quadratic fold. -/
theorem casimirFold_shadow (rho : ℂ) :
    casimirFold (1 - rho) = casimirFold rho := by
  unfold casimirFold
  ring

/-- Cartesian expansion of `rho(1-rho)`. -/
theorem casimirFold_cartesian (beta gamma : ℝ) :
    casimirFold ((beta : ℂ) + Complex.I * (gamma : ℂ)) =
      ((beta * (1 - beta) + gamma^2 : ℝ) : ℂ) +
        Complex.I * ((gamma * (1 - 2 * beta) : ℝ) : ℂ) := by
  unfold casimirFold
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, sq] <;>
    ring

/-- The real part of the folded parameter. -/
theorem casimirFold_re (beta gamma : ℝ) :
    (casimirFold ((beta : ℂ) + Complex.I * (gamma : ℂ))).re =
      beta * (1 - beta) + gamma^2 := by
  rw [casimirFold_cartesian]
  simp [sq]

/-- The imaginary part of the folded parameter. -/
theorem casimirFold_im (beta gamma : ℝ) :
    (casimirFold ((beta : ℂ) + Complex.I * (gamma : ℂ))).im =
      gamma * (1 - 2 * beta) := by
  rw [casimirFold_cartesian]
  simp [sq]

/-- In the open critical strip the folded parameter has strictly positive real part. -/
theorem casimirFold_re_pos {beta gamma : ℝ}
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1) :
    0 < (casimirFold ((beta : ℂ) + Complex.I * (gamma : ℂ))).re := by
  rw [casimirFold_re]
  have hprod : 0 < beta * (1 - beta) :=
    mul_pos hbeta0 (sub_pos.mpr hbeta1)
  nlinarith [sq_nonneg gamma]

/-- For a nonreal point, reality of the folded Casimir parameter is exactly the
critical-line equation `beta = 1/2`. -/
theorem casimirFold_im_eq_zero_iff {beta gamma : ℝ} (hgamma : gamma ≠ 0) :
    (casimirFold ((beta : ℂ) + Complex.I * (gamma : ℂ))).im = 0 ↔
      beta = 1 / 2 := by
  rw [casimirFold_im]
  constructor
  · intro h
    have hfac : 1 - 2 * beta = 0 := by
      rcases mul_eq_zero.mp h with hg | hb
      · exact (hgamma hg).elim
      · exact hb
    linarith
  · intro h
    rw [h]
    norm_num

/-- The earlier safe fold is the Casimir fold translated by `3/4`. -/
theorem oldFold_eq_casimirFold_add_three_quarters (rho : ℂ) :
    1 - (rho - (1 / 2 : ℂ))^2 = casimirFold rho + (3 / 4 : ℂ) := by
  unfold casimirFold
  ring

/-- Algebraic numerator identity behind the collapse of the two elementary
completion poles. -/
theorem completionPole_numerator (s : ℂ) :
    s + (s - 1) = 2 * s - 1 := by
  ring

/-- In the Casimir variable `u=s(s-1)`, the two elementary completion terms
collapse after division by `du/ds=2s-1`:

`(1/(2s-1)) * (1/s + 1/(s-1)) = 1/(s(s-1))`.
-/
theorem completionPole_collapse {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hmid : 2 * s - 1 ≠ 0) :
    (1 / (2 * s - 1)) * (1 / s + 1 / (s - 1)) =
      1 / (s * (s - 1)) := by
  field_simp [hs0, hs1, hmid]
  ring

end GppCasimirFold
