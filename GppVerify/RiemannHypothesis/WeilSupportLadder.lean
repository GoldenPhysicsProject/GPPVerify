import GppVerify.RiemannHypothesis.CauchyKernelPositive
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# The support ladder of the Weil functional: rungs, truncation, and the ε-dictionary

Thread L of `docs/FORMALIZATION_PLAN.md`, after Connes–Consani (arXiv:2106.01715, §2.2):
the prime side of the Weil explicit-formula functional is a sum over prime powers `p^k`
weighted at the points `±log(p^k)`, so a test function supported in `[−L, L]` only ever
meets the finitely many rungs with `log(p^k) ≤ L` — and below the first rung `log 2` it
meets none at all. This file makes that ladder kernel-checked:

* `convolution_hasSupportIn` — support doubling: if `g` is supported in `[−L/2, L/2]`,
  its convolution square `x ↦ ∫ g(y)·g(y−x) dy` is supported in `[−L, L]` (so the Weil
  test class `f = g ⋆ g~` obeys the ladder with `L` twice the half-support of `g`);
* `primeSide` — the prime side `Σ_n Λ(n)/√n · (f(log n) + f(−log n))` with Mathlib's
  von Mangoldt function;
* `primeSide_term_eq_zero` / `primeSide_eq_truncation` — every term with `log n > L`
  vanishes identically, so the full prime side agrees with its finite truncation to
  `n ≤ N` as soon as `L < log(N+1)`: the truncated and full Weil forms agree on the
  supported class, **exactly**;
* `primeSide_eq_zero_of_support_lt_log_two` — **rung 0**: with support strictly below
  `log 2` the entire prime side vanishes (every prime power is `≥ 2`), so the Weil form
  equals its archimedean part on the nose;
* `weil_nonneg_of_arch_nonneg_rung_zero` — rung-0 positivity **conditional on the named
  hypothesis** `0 ≤ arch`: the positivity of the archimedean part is the analytic
  content of Connes–Consani's rung-0 theorem and is NOT proved here — this theorem
  records precisely what remains once it is granted (namely: nothing);
* `integral_exp_neg_abs_mul_cos` — **the ε-dictionary**: the full-line Fourier pairing
  `∫_ℝ e^{−ε|u|}·cos(xu) du = 2ε/(ε²+x²)` — the Yakaboylu cutoff `κ_ε(t) = e^{−ε|log t|}`
  (in the log variable) has Fourier transform exactly twice the Cauchy kernel proved
  positive-type in `CauchyKernelPositive.lean`. This is the computational content of the
  dictionary between ε-regularization and growing-support truncation.

**What is deliberately NOT claimed**: the equivalence "ε-uniform positivity ⟺ positivity
on every rung of the support ladder" as ε → 0 / L → ∞. Each side quantifies over an
infinite family, the bridge is the explicit formula itself, and by
`rh_iff_weil_pairedForm_nonneg` the uniform statement is equivalent to RH. It stays
open and named, as always.
-/

namespace GppWeilLadder

open MeasureTheory Set ArithmeticFunction

/-- `f` is supported in `[−L, L]`: it vanishes wherever `|x| > L`. -/
def HasSupportIn (f : ℝ → ℝ) (L : ℝ) : Prop := ∀ x : ℝ, L < |x| → f x = 0

/-! ## L1: convolution squares double the support -/

/-- **Support doubling**: if `g` vanishes outside `[−L/2, L/2]`, the convolution square
    `x ↦ ∫ g(y)·g(y−x) dy` vanishes outside `[−L, L]` — pointwise, the integrand is
    identically zero there, by the triangle inequality. -/
theorem convolution_hasSupportIn {g : ℝ → ℝ} {L : ℝ}
    (hsupp : ∀ y : ℝ, L/2 < |y| → g y = 0) :
    HasSupportIn (fun x => ∫ y : ℝ, g y * g (y - x)) L := by
  intro x hx
  show (∫ y : ℝ, g y * g (y - x)) = 0
  have hzero : ∀ y : ℝ, g y * g (y - x) = 0 := by
    intro y
    rcases le_or_lt |y| (L/2) with h1 | h1
    · have h3 : |x| - |y| ≤ |y - x| := by
        have h4 := abs_sub_abs_le_abs_sub x y
        rwa [abs_sub_comm] at h4
      have h2 : L/2 < |y - x| := by linarith
      rw [hsupp _ h2, mul_zero]
    · rw [hsupp _ h1, zero_mul]
  simp only [hzero, integral_zero]

/-! ## L2: the prime side and its rung structure -/

/-- The prime side of the Weil functional: `Σ_n Λ(n)/√n · (f(log n) + f(−log n))`,
    with `Λ` Mathlib's von Mangoldt function (supported exactly on prime powers). -/
noncomputable def primeSide (f : ℝ → ℝ) : ℝ :=
  ∑' n : ℕ, (Λ n / Real.sqrt n) * (f (Real.log n) + f (-(Real.log n)))

/-- Any single term with `log n > L` vanishes identically on the supported class. -/
theorem primeSide_term_eq_zero {f : ℝ → ℝ} {L : ℝ} (hf : HasSupportIn f L)
    {n : ℕ} (hn : L < Real.log n) :
    (Λ n / Real.sqrt n) * (f (Real.log n) + f (-(Real.log n))) = 0 := by
  have hlog : (0:ℝ) ≤ Real.log n := Real.log_natCast_nonneg n
  have h1 : f (Real.log n) = 0 := hf _ (by rwa [abs_of_nonneg hlog])
  have h2 : f (-(Real.log n)) = 0 := hf _ (by rwa [abs_neg, abs_of_nonneg hlog])
  rw [h1, h2, add_zero, mul_zero]

/-- **Truncation agreement**: on test functions supported in `[−L, L]` with
    `L < log(N+1)`, the full prime side IS its finite truncation to `n ≤ N` —
    the infinite tail vanishes term by term, not merely in the limit. -/
theorem primeSide_eq_truncation {f : ℝ → ℝ} {L : ℝ} (hf : HasSupportIn f L)
    {N : ℕ} (hN : L < Real.log (N+1)) :
    primeSide f = ∑ n ∈ Finset.range (N+1),
      (Λ n / Real.sqrt n) * (f (Real.log n) + f (-(Real.log n))) := by
  apply tsum_eq_sum
  intro n hn
  have hge : N+1 ≤ n := by simpa [Finset.mem_range, not_lt] using hn
  have hlog : Real.log (N+1) ≤ Real.log n := by
    have hcast : ((N+1 : ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast hge
    have hpos : (0:ℝ) < ((N+1 : ℕ):ℝ) := by positivity
    have h := (Real.log_le_log_iff hpos (by linarith)).mpr hcast
    simpa using h
  exact primeSide_term_eq_zero hf (lt_of_lt_of_le hN hlog)

/-- **Rung 0**: with support strictly below the first rung `log 2`, the entire prime
    side vanishes — every prime power is `≥ 2`, so no prime enters the Weil form. -/
theorem primeSide_eq_zero_of_support_lt_log_two {f : ℝ → ℝ} {L : ℝ}
    (hf : HasSupportIn f L) (hL : L < Real.log 2) :
    primeSide f = 0 := by
  have hterm : ∀ n : ℕ,
      (Λ n / Real.sqrt n) * (f (Real.log n) + f (-(Real.log n))) = 0 := by
    intro n
    rcases eq_or_ne (Λ n) 0 with h0 | h0
    · rw [h0, zero_div, zero_mul]
    · have hpp : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h0
      have h2n : (2:ℕ) ≤ n := hpp.two_le
      have hlog : Real.log 2 ≤ Real.log n := by
        have hcast : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast h2n
        exact (Real.log_le_log_iff (by norm_num) (by linarith)).mpr hcast
      exact primeSide_term_eq_zero hf (lt_of_lt_of_le hL hlog)
  show (∑' n : ℕ, (Λ n / Real.sqrt n) * (f (Real.log n) + f (-(Real.log n)))) = 0
  rw [tsum_congr hterm]
  exact tsum_zero

/-- **Conditional rung-0 positivity.** The hypothesis `0 ≤ arch` — positivity of the
    archimedean part of the Weil form on the rung-0 class — is the analytic content of
    Connes–Consani's rung-0 theorem (arXiv:2106.01715 §2.2) and is **not proved here**;
    it is carried as a named hypothesis. Granting it, nothing remains: below `log 2`
    the Weil form `arch − primeSide f` is the archimedean part on the nose. -/
theorem weil_nonneg_of_arch_nonneg_rung_zero {f : ℝ → ℝ} {L arch : ℝ}
    (harch : 0 ≤ arch) (hf : HasSupportIn f L) (hL : L < Real.log 2) :
    0 ≤ arch - primeSide f := by
  rw [primeSide_eq_zero_of_support_lt_log_two hf hL, sub_zero]
  exact harch

/-! ## L3: the ε-dictionary -/

/-- **The Fourier pairing of the ε-cutoff with the Cauchy kernel**: for `ε > 0`,
    `∫_ℝ e^{−ε|u|}·cos(xu) du = 2ε/(ε²+x²)` — the Yakaboylu regularizer
    `κ_ε(t) = e^{−ε|log t|}`, written in the log variable `u = log t`, has Fourier
    transform exactly twice the Cauchy kernel of `CauchyKernelPositive.lean`. The
    ε-regularization and the growing-support truncation are two coordinates on the
    same object; the uniformity of either limit over the zero configuration is the
    open input (equivalent to RH via `rh_iff_weil_pairedForm_nonneg`), not claimed. -/
theorem integral_exp_neg_abs_mul_cos {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    ∫ u : ℝ, Real.exp (-ε*|u|) * Real.cos (x*u) = 2 * (ε / (ε^2 + x^2)) := by
  have hdouble :
      (∫ u : ℝ, Real.exp (-ε*|u|) * Real.cos (x*|u|)) =
        2 * ∫ t in Ioi (0:ℝ), Real.exp (-ε*t) * Real.cos (x*t) :=
    integral_comp_abs (f := fun t : ℝ => Real.exp (-ε*t) * Real.cos (x*t))
  have hpt : ∀ u : ℝ, Real.exp (-ε*|u|) * Real.cos (x*u) =
      Real.exp (-ε*|u|) * Real.cos (x*|u|) := by
    intro u
    rcases abs_cases u with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]
    · rw [h1, show x * -u = -(x*u) by ring, Real.cos_neg]
  calc ∫ u : ℝ, Real.exp (-ε*|u|) * Real.cos (x*u)
      = ∫ u : ℝ, Real.exp (-ε*|u|) * Real.cos (x*|u|) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpt
    _ = 2 * ∫ t in Ioi (0:ℝ), Real.exp (-ε*t) * Real.cos (x*t) := hdouble
    _ = 2 * (ε / (ε^2 + x^2)) := by
        rw [GppCauchyKernel.integral_exp_neg_mul_cos hε x]

end GppWeilLadder
