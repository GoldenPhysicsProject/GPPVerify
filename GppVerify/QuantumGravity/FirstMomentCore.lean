import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The closing third of the First Moment Theorem

`principal_series_blocks_v2.tex`, Theorem `thm:moment` (Theorem 6.1) states

  `(1/2π) ∫_ℝ P(λ) Re ψ(1/2 + iλ/2) dλ = 1/8 + (1/4) ψ(1/2)`,  `P(λ) = πλ/sinh(πλ)`.

Its proof has three inputs, and this file proves exactly one of them — the last.

1. **The Fourier pair** `(1/2π) ∫_ℝ P(λ) cos(λy) dλ = 1/(4 cosh²(y/2))`. Not proved here;
   stated precisely in the closing section, as prose rather than as a Lean declaration.
2. **Gauss's integral representation** `ψ(s) = -γ + ∫₀^∞ (e^{-t} - e^{-st})/(1 - e^{-t}) dt`,
   which turns `Re ψ(1/2 + iλ/2) - ψ(1/2)` into `∫₀^∞ e^{-t/2}[1 - cos(λt/2)]/(1 - e^{-t}) dt`.
   Not proved here; `GppDigamma` defines `ψ` as `Γ'/Γ` and proves its special values, not this.
   Also stated in the closing section.
3. **The remainder integral**, which is what produces the theorem's `1/8`:

   `∫₀^∞ (1/(2 sinh(t/2))) · (1/4)[1 - sech²(t/4)] dt = 1/8`.

   That is `remainder_integral_eq_one_eighth`, proved below with no hypotheses.

So the number `1/8` in Theorem 6.1 is now a theorem; the two analytic inputs that put the
integrand in front of it are not. **This file does not prove Theorem 6.1** and does not state
it. Everything here is unconditional real analysis: an `exp`-to-`sinh` rewrite, the
hyperbolic collapse the paper performs by hand, and one improper integral by the fundamental
theorem of calculus.

The collapse is worth stating precisely because the paper does it in a single line
("using `1/(sinh u cosh u) = sech²u/tanh u`, the integrand collapses to `tanh u sech²u`") and
that line silently carries the substitution `u = t/4`, hence a Jacobian. Written out, the
identity is `(1/(2 sinh 2u)) · (1/4)(1 - sech²u) = (1/16) tanh u sech²u`, and the `4` from
`dt = 4 du` is what turns `1/16` into the `1/4` multiplying the paper's `∫ tanh u sech²u`.
-/

namespace GppFirstMoment

open Real Set MeasureTheory Filter Topology

/-- `e^{-t/2}/(1 - e^{-t}) = 1/(2 sinh(t/2))` for `t > 0`.

The paper uses this to recognise the Gauss-representation kernel as a hyperbolic one. It
needs `t ≠ 0`: at `t = 0` the left side is `1/0` and the right side is `1/0` as well, but
only by Lean's junk convention, so the hypothesis is kept rather than leaned on. -/
theorem exp_div_one_sub_exp_eq (t : ℝ) (ht : 0 < t) :
    Real.exp (-(t / 2)) / (1 - Real.exp (-t)) = 1 / (2 * Real.sinh (t / 2)) := by
  have hsinh : 0 < Real.sinh (t / 2) := Real.sinh_pos_iff.mpr (by linarith)
  have hexp : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hne : (1 : ℝ) - Real.exp (-t) ≠ 0 := by linarith
  -- `2 sinh(t/2) = e^{t/2} - e^{-t/2}`, and multiplying through by `e^{-t/2}` gives `1 - e^{-t}`.
  have h2 : 2 * Real.sinh (t / 2) = Real.exp (t / 2) - Real.exp (-(t / 2)) := by
    rw [Real.sinh_eq]; ring
  have hden : Real.exp (t / 2) - Real.exp (-(t / 2)) ≠ 0 := by rw [← h2]; positivity
  have hmul : Real.exp (-(t / 2)) * (Real.exp (t / 2) - Real.exp (-(t / 2)))
      = 1 * (1 - Real.exp (-t)) := by
    have e1 : -(t / 2) + t / 2 = 0 := by ring
    have e2 : -(t / 2) + -(t / 2) = -t := by ring
    rw [mul_sub, ← Real.exp_add, ← Real.exp_add, e1, e2, Real.exp_zero]
    ring
  rw [h2, div_eq_div_iff hne hden]
  exact hmul

/-- The hyperbolic collapse, with the substitution's Jacobian left explicit.

The paper writes the remainder integrand as `(1/(2 sinh(t/2)))·(1/4)[1 - sech²(t/4)]` and
then says it "collapses to `tanh u sech²u`" under `u = t/4`. In that variable the identity
is the one below — note the `1/16`, not `1`: the paper's stated collapse absorbs the `4`
from `dt = 4 du` and a `1/4`. Stating it with the constant visible is what makes the final
value checkable rather than a plausible-looking chain. -/
theorem collapse (u : ℝ) :
    1 / (2 * Real.sinh (2 * u)) * ((1 - (1 / Real.cosh u) ^ 2) / 4)
      = 1 / 16 * (Real.tanh u * (1 / Real.cosh u) ^ 2) := by
  have hc : Real.cosh u ≠ 0 := (Real.cosh_pos u).ne'
  rw [Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]
  rcases eq_or_ne (Real.sinh u) 0 with hs | hs
  · rw [hs]; simp
  · field_simp
    linear_combination (16 : ℝ) * Real.cosh_sq_sub_sinh_sq u

/-- `d/du (-1/(2 cosh²u)) = tanh u · sech²u`. -/
theorem hasDerivAt_neg_inv_two_cosh_sq (u : ℝ) :
    HasDerivAt (fun v : ℝ => -(2 * Real.cosh v ^ 2)⁻¹)
      (Real.tanh u * (1 / Real.cosh u) ^ 2) u := by
  have hc : Real.cosh u ≠ 0 := (Real.cosh_pos u).ne'
  have hsq : (2 : ℝ) * Real.cosh u ^ 2 ≠ 0 := by positivity
  have hpow : HasDerivAt (fun v : ℝ => 2 * Real.cosh v ^ 2)
      (2 * (2 * Real.cosh u ^ 1 * Real.sinh u)) u :=
    ((Real.hasDerivAt_cosh u).pow 2).const_mul (2 : ℝ)
  have hinv := (hpow.inv hsq).neg
  -- `-(2·cosh²)' / (2·cosh²)² = -(4 cosh u sinh u)/(4 cosh⁴u) = sinh u / cosh³u`.
  refine hinv.congr_deriv ?_
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- `-1/(2 cosh²u) → 0` as `u → ∞`. -/
theorem tendsto_neg_inv_two_cosh_sq :
    Tendsto (fun v : ℝ => -(2 * Real.cosh v ^ 2)⁻¹) atTop (𝓝 0) := by
  have hcosh : Tendsto (fun v : ℝ => Real.cosh v) atTop atTop := by
    refine tendsto_atTop_mono (fun v => ?_) (Real.tendsto_exp_atTop.atTop_div_const two_pos)
    rw [Real.cosh_eq]
    have : 0 < Real.exp (-v) := Real.exp_pos _
    linarith
  -- `2 cosh²v ≥ cosh v` since `cosh ≥ 1`, so it too goes to `+∞`.
  have hsq : Tendsto (fun v : ℝ => 2 * Real.cosh v ^ 2) atTop atTop := by
    refine tendsto_atTop_mono (fun v => ?_) hcosh
    nlinarith [Real.one_le_cosh v]
  simpa using (hsq.inv_tendsto_atTop).neg

/-- **`∫₀^∞ tanh u · sech²u du = 1/2`.**

The paper's `[tanh²u/2]₀^∞`. Proved with the antiderivative `-1/(2 cosh²u)` instead, which
is the same function up to the constant `-1/2` and has the easier limit at `+∞`: it needs
only `cosh → ∞`, where `tanh²/2 → 1/2` needs the value of the limit as well. -/
theorem integral_tanh_mul_sech_sq :
    ∫ u in Ioi (0 : ℝ), Real.tanh u * (1 / Real.cosh u) ^ 2 = 1 / 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := fun v : ℝ => -(2 * Real.cosh v ^ 2)⁻¹)
    (g' := fun u : ℝ => Real.tanh u * (1 / Real.cosh u) ^ 2)
    (a := 0) (l := 0)
    (fun u _ => hasDerivAt_neg_inv_two_cosh_sq u)
    (fun u hu => by
      have hs : 0 ≤ Real.sinh u := Real.sinh_nonneg_iff.mpr (le_of_lt hu)
      have hc : 0 < Real.cosh u := Real.cosh_pos u
      rw [Real.tanh_eq_sinh_div_cosh]
      positivity)
    tendsto_neg_inv_two_cosh_sq
  rw [h]
  norm_num

/-- **The remainder integral of Theorem 6.1's proof equals `1/8`.**

This is the paper's step

  `∫₀^∞ (1/(2 sinh(t/2))) · (1/4)[1 - sech²(t/4)] dt = 1/4 · ∫₀^∞ tanh u sech²u du = 1/8`,

with the substitution `t = 4u` carried out explicitly. It is the source of the `1/8` in
`thm:moment`, and it is unconditional: no digamma, no Fourier transform, no exchange of
integration order enters here. -/
theorem remainder_integral_eq_one_eighth :
    ∫ t in Ioi (0 : ℝ),
        1 / (2 * Real.sinh (t / 2)) * ((1 - (1 / Real.cosh (t / 4)) ^ 2) / 4) = 1 / 8 := by
  set g : ℝ → ℝ := fun t =>
    1 / (2 * Real.sinh (t / 2)) * ((1 - (1 / Real.cosh (t / 4)) ^ 2) / 4) with hg
  have hsub : ∫ u in Ioi (0 : ℝ), g (4 * u) = (4 : ℝ)⁻¹ • ∫ t in Ioi (0 : ℝ), g t := by
    simpa using integral_comp_mul_left_Ioi g 0 (by norm_num : (0:ℝ) < 4)
  have hpoint : ∀ u : ℝ, g (4 * u) = 1 / 16 * (Real.tanh u * (1 / Real.cosh u) ^ 2) := by
    intro u
    have h2 : 4 * u / 2 = 2 * u := by ring
    have h4 : 4 * u / 4 = u := by ring
    rw [hg]
    simp only [h2, h4]
    exact collapse u
  have hleft : ∫ u in Ioi (0 : ℝ), g (4 * u) = 1 / 32 := by
    simp only [hpoint]
    rw [integral_const_mul, integral_tanh_mul_sech_sq]
    norm_num
  rw [hleft] at hsub
  have : (4 : ℝ)⁻¹ * ∫ t in Ioi (0 : ℝ), g t = 1 / 32 := by simpa using hsub.symm
  linarith

/-!
## The two inputs this file does not prove

Named so that a future session finds the boundary already drawn, rather than re-deriving it
from the paper. Both are *statements about missing mathematics*, not about missing Mathlib
vocabulary — the distinction `CLAUDE_CORRECTIONS.md` entry 12 was written about. Each is
stated here in prose only; neither is a Lean `axiom`, a `sorry`, or a `True`-valued stub, so
neither can be mistaken for something the repository has proved.

**Input 1 — the Fourier pair.**
`(1/2π) ∫_ℝ (πλ/sinh(πλ)) cos(λy) dλ = 1/(4 cosh²(y/2))` for all real `y`, equivalently
`∫_ℝ e^{iλx}/(4 cosh²(x/2)) dx = πλ/sinh(πλ)`. Used twice: at `y = 0` it gives
`(1/2π)∫_ℝ P = 1/4`, hence the `(1/4)ψ(1/2)` term; at `y = t/2` inside the exchanged double
integral it produces the remainder integrand proved above. Mathlib has the Gaussian Fourier
transform but nothing for `sech²`; the classical routes are a residue sum over the poles of
`1/sinh`, or the geometric expansion `1/sinh(πλ) = 2 Σ_{k≥0} e^{-(2k+1)πλ}` followed by the
partial-fraction expansion of `sech²`. The second route is elementary and self-contained and
is the one to try first.

**Input 2 — Gauss's integral representation of `ψ`.**
`ψ(s) = -γ + ∫₀^∞ (e^{-t} - e^{-st})/(1 - e^{-t}) dt` for `Re s > 0`, and the consequence
`Re ψ(1/2 + iλ/2) - ψ(1/2) = ∫₀^∞ e^{-t/2}[1 - cos(λt/2)]/(1 - e^{-t}) dt`. `GppDigamma`
defines `ψ = Γ'/Γ` on the reals and proves `ψ(1)`, `ψ(1/2)`, `ψ(n+1)` and the functional
equation from Mathlib's `GammaDeriv`; it proves no integral representation, and the complex
digamma along `Re s = 1/2` that the moment integrand needs is a separate extension again.
This is the harder of the two.

The exchange of integration order between them is Tonelli on a positive integrand, which is
routine once both are available.
-/

#print axioms GppFirstMoment.remainder_integral_eq_one_eighth
#print axioms GppFirstMoment.integral_tanh_mul_sech_sq
#print axioms GppFirstMoment.exp_div_one_sub_exp_eq
#print axioms GppFirstMoment.collapse

end GppFirstMoment
