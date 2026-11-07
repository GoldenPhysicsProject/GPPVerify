import GppVerify.RiemannHypothesis.ArithmeticReflectionPositivity

/-!
# Step 0: the Weil distribution in the multiplicative variable, equal to `weilForm`

Step 0 of the full-construction brief (Daniel Toupin, via Turbo, 2026-11-06): the
prime-side Weil distribution on test functions of `x ∈ (0, ∞)`. The tree already has
the log-variable form `GppArithmeticReflection.weilForm` (normalization checked
against the zeta zeros). This module writes the multiplicative form and proves the
two are **the same distribution** under `x = e^u`, so the tree has one Weil
distribution, not two.

Convention (half-density, centered at `w = 1/2`): for `h : (0,∞) → ℝ`,

  `multPrime h = Σ Λ(n)/√n · (h(n) + h(1/n))`,
  `multPole h  = ∫_{x>0} h(x) (x^{-1/2} + x^{-3/2}) dx`   ( = M[x^{-1/2}h](1) + M[x^{-1/2}h](0) ),

and the archimedean term is the validated `archimedeanTerm` of the pullback
`u ↦ h(e^u)`.

* `multPrime_eq_primeSide`: `multPrime h = primeSide (h ∘ exp)`, term by term.
* `multPole_eq_poleTerm`: `multPole h = poleTerm (h ∘ exp)` (substitution `x = e^u`,
  `integral_comp_exp_univ`).
* `multWeil_eq_weilForm`: the whole form agrees.

**Convention correction to the Step-0 spec** (bridge note
`turbo-note-2026-11-06-step0-weil-distribution-spec.md`): the spec pairs the
half-density prime weight `Λ(n)/√n · (F(n) + F(1/n))` with the *uncentered* pole
terms `∫F + ∫F/x`. Those belong to different normalizations of the test function
(`h` vs `f = x^{-1/2} h`). Numerically (cos² bump, primes 2, 3, 4 visible), the
consistent forms give `1.7100715e-4` against the zero sum `1.7100734e-4`, while the
spec as written gives `-2.04e-3` (with `F = f`) or `+8.96e-3` (with `F = h`). The
consistent uncentered form is `Σ Λ(n)(f(n) + f(1/n)/n)` with poles `∫f + ∫f/x`; the
half-density form is the one here.

Scope: real-valued test functions; the complex-valued involution `conj h(1/x)` and
the multiplicative autocorrelation class are not yet transported. No claim about RH.

Daniel Toupin / Golden Physics Project, with AI assistance from Turbo (spec) and
Claude Code (Lean, correction).
-/

namespace GppWeilMultiplicative

open MeasureTheory Set ArithmeticFunction GppWeilLadder GppArchimedeanFloor
  GppArithmeticReflection

/-- Substitution `y = e^x` over the whole line. -/
theorem integral_comp_exp_univ (G : ℝ → ℝ) :
    ∫ x : ℝ, Real.exp x * G (Real.exp x) = ∫ y in Ioi (0 : ℝ), G y := by
  have h := integral_image_eq_integral_abs_deriv_smul (MeasurableSet.univ (α := ℝ))
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x _ y _ hxy => Real.exp_injective hxy) G
  rw [Set.image_univ, Real.range_exp, setIntegral_univ] at h
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [abs_of_pos (Real.exp_pos x)]

/-- Pullback of a multiplicative test function to the log variable. -/
noncomputable def logPullback (h : ℝ → ℝ) : ℝ → ℝ := fun u => h (Real.exp u)

/-- Prime side, half-density convention. -/
noncomputable def multPrime (h : ℝ → ℝ) : ℝ :=
  ∑' n : ℕ, (Λ n / Real.sqrt n) * (h n + h (n : ℝ)⁻¹)

/-- Pole terms `∫_{x>0} h(x) (x^{-1/2} + x^{-3/2}) dx`. -/
noncomputable def multPole (h : ℝ → ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), h x * (x ^ (-(1 / 2) : ℝ) + x ^ (-(3 / 2) : ℝ))

/-- The multiplicative Weil form. -/
noncomputable def multWeil (h : ℝ → ℝ) : ℝ :=
  multPole h + archimedeanTerm (logPullback h) - multPrime h

theorem multPrime_eq_primeSide (h : ℝ → ℝ) : multPrime h = primeSide (logPullback h) := by
  unfold multPrime primeSide logPullback
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.exp_log hpos, Real.exp_neg, Real.exp_log hpos]

theorem multPole_eq_poleTerm (h : ℝ → ℝ) : multPole h = poleTerm (logPullback h) := by
  unfold multPole poleTerm logPullback
  rw [← integral_comp_exp_univ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [← Real.exp_mul, ← Real.exp_mul, Real.cosh_eq]
  have e1 : Real.exp u * Real.exp (u * -(1 / 2)) = Real.exp (u / 2) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp u * Real.exp (u * -(3 / 2)) = Real.exp (-(u / 2)) := by
    rw [← Real.exp_add]; ring_nf
  calc Real.exp u * (h (Real.exp u) * (Real.exp (u * -(1 / 2)) + Real.exp (u * -(3 / 2))))
      = h (Real.exp u) * (Real.exp u * Real.exp (u * -(1 / 2)) +
          Real.exp u * Real.exp (u * -(3 / 2))) := by ring
    _ = h (Real.exp u) * (2 * ((Real.exp (u / 2) + Real.exp (-(u / 2))) / 2)) := by
          rw [e1, e2]; ring

/-- **Step 0: one Weil distribution.** The multiplicative form is `weilForm` of the pullback. -/
theorem multWeil_eq_weilForm (h : ℝ → ℝ) : multWeil h = weilForm (logPullback h) := by
  unfold multWeil weilForm
  rw [multPole_eq_poleTerm, multPrime_eq_primeSide]

end GppWeilMultiplicative

#print axioms GppWeilMultiplicative.multWeil_eq_weilForm
