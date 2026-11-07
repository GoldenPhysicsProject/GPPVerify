import GppVerify.RiemannHypothesis.WeilSupportLadder
import GppVerify.RiemannHypothesis.ArchimedeanFloor
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The physical premise, zero-free: arithmetic reflection positivity

Daniel Toupin's formulation (2026-11-06): xi is built from physical states of a
one-dimensional conformal theory with the celestial structure, so it must obey
the physical axioms. The axiom that reaches the zeros is Osterwalder-Schrader
reflection positivity (inversion `x ↦ 1/x` is Euclidean time reversal in
`t = log x`, `GppArithmeticOS`). Transported to arithmetic it is positivity of
the Weil form, assembled here from **primes, the gamma factor and the pole
only**; no zero of any L-function is mentioned:

  `W(g) = pole(g) + A∞(g) - primeSide(g)`,
  `pole(g) = ∫ g(u) · 2 cosh(u/2) du`, `A∞ = GppArchimedeanFloor.archimedeanTerm`,
  `primeSide(g) = Σ Λ(n)/√n · (g(log n) + g(-log n))`  (`GppWeilLadder.primeSide`),

on autocorrelations `g = f ⋆ f̃`, `g(x) = ∫ f(y) f(y - x) dy`.

* `ArithmeticReflectionPositivity` is the named physical premise
  `∀ f` smooth with compact support, `0 ≤ W(f ⋆ f̃)`. It is **not asserted**.
* `weilForm_rung_zero`: for `f` supported in `[-L/2, L/2]` with `L < log 2`,
  `W = pole + A∞` exactly (no prime visible).
* `weilForm_eq_truncation`: on support `L < log(N+1)` the prime side is the
  finite sum over `n ≤ N`, so the premise restricted to each rung is one finite
  domination inequality: pole + gamma dominates the visible prime kicks.

Normalization check (numerical, not a Lean proof; script
`discovery/weil_normalization_check.py`): for `f = cos²(π x/1.2)` on
`[-0.6, 0.6]` (primes 2, 3, 4 visible), `pole - prime + A∞ = 1.7100715e-4`
against `Σ_γ ĝ(γ) = 1.7100734e-4` over the first 599 zeta zeros, agreement
~1e-12 with the digamma form of the gamma term and ~1e-9 with `archimedeanTerm`.

**What is not here.** Weil's theorem (1952; Bombieri, Rend. Lincei 2000) that
this premise is equivalent to RH goes through the explicit formula, which is not
in Mathlib; it is classical mathematics still to be formalized, not a conjecture.
The premise itself is open: it is RH-strength. Davenport-Heilbronn and the
theta-weight deformation violate their analogues at small primes, so any
argument for it must use a xi-specific prime-side input. No claim about RH.

Daniel Toupin / Golden Physics Project, with AI assistance from Claude Code.

## Sources

Reflection positivity is the Osterwalder–Schrader axiom: K. Osterwalder and
R. Schrader, "Axioms for Euclidean Green's functions", *Comm. Math. Phys.* 31
(1973), 83–112, and Part II, *Comm. Math. Phys.* 42 (1975), 281–305. That
positivity of the Weil form on autocorrelations is equivalent to RH is Weil's
theorem (A. Weil, *Comm. Sém. Math. Univ. Lund*, Tome Supplémentaire (1952),
pp. 252–265; E. Bombieri, Clay Mathematics Institute (2000)).

-/

namespace GppArithmeticReflection

open MeasureTheory GppWeilLadder GppArchimedeanFloor
open scoped ContDiff

/-- Autocorrelation `g(x) = ∫ f(y) f(y - x) dy` (the Weil test class `f ⋆ f̃`). -/
noncomputable def autocorr (f : ℝ → ℝ) : ℝ → ℝ := fun x => ∫ y : ℝ, f y * f (y - x)

/-- The pole term `ĝ(i/2) + ĝ(-i/2) = ∫ g(u) · 2 cosh(u/2) du`. -/
noncomputable def poleTerm (g : ℝ → ℝ) : ℝ := ∫ u : ℝ, g u * (2 * Real.cosh (u / 2))

/-- The Weil form assembled from pole, gamma factor and primes only. -/
noncomputable def weilForm (g : ℝ → ℝ) : ℝ := poleTerm g + archimedeanTerm g - primeSide g

/-- **The physical premise (named, not asserted):** arithmetic reflection
positivity on smooth compactly supported test functions.

Correction 2026-11-07: this was first stated with `ContDiff ℝ ⊤`, which in current Mathlib
is the *analytic* class `ω`. An analytic function on `ℝ` with compact support is zero, so
the premise quantified over `f = 0` only and was vacuously true. It is now `C^∞`
(`ContDiff ℝ ∞`); `exists_test_function_ne_zero` exhibits a nonzero member. -/
def ArithmeticReflectionPositivity : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → 0 ≤ weilForm (autocorr f)

/-- **Non-vacuity of the test class:** a smooth bump with compact support and value 1 at 0. -/
theorem exists_test_function_ne_zero :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ f 0 = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  exact ⟨b, b.contDiff, b.hasCompactSupport, b.one_of_mem_closedBall (by simpa using b.rIn_pos.le)⟩

/-- The premise restricted to test functions supported in `[-L/2, L/2]` (rung `L`). -/
def ReflectionPositiveOnRung (L : ℝ) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
    (∀ y : ℝ, L / 2 < |y| → f y = 0) → 0 ≤ weilForm (autocorr f)

/-- The full premise gives every rung. -/
theorem rung_of_reflectionPositivity (h : ArithmeticReflectionPositivity) (L : ℝ) :
    ReflectionPositiveOnRung L :=
  fun f hf hc _ => h f hf hc

/-- Support doubling for the test class. -/
theorem autocorr_hasSupportIn {f : ℝ → ℝ} {L : ℝ}
    (hsupp : ∀ y : ℝ, L / 2 < |y| → f y = 0) : HasSupportIn (autocorr f) L :=
  convolution_hasSupportIn hsupp

/-- **Rung 0:** below `log 2` no prime is visible; the Weil form is pole plus gamma. -/
theorem weilForm_rung_zero {f : ℝ → ℝ} {L : ℝ} (hsupp : ∀ y : ℝ, L / 2 < |y| → f y = 0)
    (hL : L < Real.log 2) :
    weilForm (autocorr f) = poleTerm (autocorr f) + archimedeanTerm (autocorr f) := by
  rw [weilForm, primeSide_eq_zero_of_support_lt_log_two (autocorr_hasSupportIn hsupp) hL,
    sub_zero]

/-- **Every rung is finite:** below `log (N+1)` the prime side is the sum over `n ≤ N`. -/
theorem weilForm_eq_truncation {f : ℝ → ℝ} {L : ℝ} (hsupp : ∀ y : ℝ, L / 2 < |y| → f y = 0)
    {N : ℕ} (hN : L < Real.log (N + 1)) :
    weilForm (autocorr f) = poleTerm (autocorr f) + archimedeanTerm (autocorr f) -
      ∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        (autocorr f (Real.log n) + autocorr f (-(Real.log n))) := by
  rw [weilForm, primeSide_eq_truncation (autocorr_hasSupportIn hsupp) hN]

/-- **Rung positivity is a finite domination inequality.** -/
theorem rung_positivity_iff_domination {f : ℝ → ℝ} {L : ℝ}
    (hsupp : ∀ y : ℝ, L / 2 < |y| → f y = 0) {N : ℕ} (hN : L < Real.log (N + 1)) :
    0 ≤ weilForm (autocorr f) ↔
      ∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        (autocorr f (Real.log n) + autocorr f (-(Real.log n))) ≤
        poleTerm (autocorr f) + archimedeanTerm (autocorr f) := by
  rw [weilForm_eq_truncation hsupp hN, sub_nonneg]

end GppArithmeticReflection

#print axioms GppArithmeticReflection.weilForm_rung_zero
#print axioms GppArithmeticReflection.rung_positivity_iff_domination
