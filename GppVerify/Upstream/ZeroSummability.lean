/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import GppVerify.Upstream.DyadicSummability
import GppVerify.Upstream.ZeroCounting
import GppVerify.Upstream.WeierstrassProduct

/-!
# The zeros of an entire function of finite order are summable beyond that order

`Complex.HasOrderLE.sum_divisor_le` bounds the zero-counting function of an entire `f` of
order at most `ρ`:

  `n(r) ≤ A + B * r ^ (ρ + ε)`  for every `ε > 0`.

`Complex.weierstrassProduct` consumes a sequence `a : ℕ → ℂ` of nonzero points together with
`Summable fun n => ‖a n‖⁻¹ ^ (p + 1)`. This file connects the two: a sequence whose counting
function is dominated by `f`'s is summable at every natural exponent strictly above `ρ`.

The analytic work is `Real.summable_inv_pow_of_counting_le`. All that happens here is the
choice `ε = (m - ρ)/2`, which is the standard trick and is available precisely because the
counting bound holds for *every* positive `ε`: the conclusion needs `ρ + ε < m`, and
`ρ + (m - ρ)/2 = (ρ + m)/2 < m`.

## What this does and does not do

It does not construct the enumeration. The hypothesis `hcard` says that `a` lists points no
more densely than `f`'s zeros, which is what an enumeration of the zero divisor (with
multiplicity, in any order) satisfies with equality. Producing such an `a` from
`MeromorphicOn.divisor` is a separate and purely combinatorial task: the divisor is a
finitely supported `ℤ`-valued function on each closed ball, and turning the increasing family
of those into one `ℕ`-indexed sequence is the remaining step before Hadamard's theorem can be
stated for `ξ` with its zeros derived rather than assumed.

Stating the summability against a hypothesised enumeration rather than a constructed one is
deliberate and is how the rest of this chain is arranged: `weierstrassProduct` also takes its
sequence as given. The two halves meet without either of them constructing anything.

## Main results

* `Complex.HasOrderLE.summable_inv_pow` : `Summable fun n => ‖a n‖⁻¹ ^ m` for `ρ < m`.
* `Complex.HasOrderLE.differentiable_weierstrassProduct` and
  `Complex.HasOrderLE.weierstrassProduct_eq_zero_iff` : the consequence, and the point of the
  whole chain. From nothing but *`f` is entire of order at most `ρ`, `f 0 ≠ 0`, and `a`
  enumerates its zeros*, the Weierstrass product of genus `p` over `a` is entire and vanishes
  exactly on `a`, for any `p` with `ρ < p + 1`. No summability hypothesis is left for the
  caller to discharge: that was the gap, and these two theorems are what it being closed
  looks like from outside.
-/

open Real Metric MeromorphicOn Set

namespace Complex

variable {f : ℂ → ℂ} {ρ : ℝ}

/-- **A sequence no denser than the zeros of an entire function of order `≤ ρ` is summable at
every natural exponent above `ρ`.**

This is the hypothesis `Complex.weierstrassProduct` takes, derived from Jensen's counting
bound. `hcard` asks that the number of `a n` in the closed ball of radius `r` be at most the
number of zeros of `f` there, counted with multiplicity, which is exactly what an enumeration
of the zero divisor satisfies. -/
theorem HasOrderLE.summable_inv_pow (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hord : HasOrderLE f ρ) (hρ : 0 ≤ ρ) {a : ℕ → ℂ} (ha : ∀ n, a n ≠ 0)
    (hfin : ∀ r : ℝ, {n | ‖a n‖ ≤ r}.Finite)
    (hcard : ∀ r : ℝ, 0 < r → (((hfin r).toFinset.card : ℕ) : ℝ)
      ≤ ((∑ᶠ u, divisor f (closedBall (0 : ℂ) r) u : ℤ) : ℝ))
    {m : ℕ} (hm : ρ < m) :
    Summable fun n => ‖a n‖⁻¹ ^ m := by
  -- `ε` chosen so that the Jensen exponent `ρ + ε` is still strictly below `m`
  set ε : ℝ := (m - ρ) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hρε : ρ + ε < m := by rw [hεdef]; linarith
  obtain ⟨A, B, hB, hbound⟩ := hord.sum_divisor_le hf h0 hε
  -- `A` is pinned only by the counting hypothesis, which is supplied last, so name the
  -- implicit arguments rather than leaving elaboration to guess a real number from a hole.
  refine Real.summable_inv_pow_of_counting_le (a := fun n => ‖a n‖) (A := A) (B := B)
    (ρ := ρ + ε) (m := m) (fun n => norm_pos_iff.2 (ha n)) hfin hB (by linarith) hρε ?_
  intro r hr
  exact (hcard r hr).trans (hbound r hr)

/-- **The Weierstrass product over the zeros of an entire function of finite order is
entire.** Genus `p` works as soon as `ρ < p + 1`, and the summability hypothesis of
`Complex.differentiable_weierstrassProduct` is now discharged from the order alone. -/
theorem HasOrderLE.differentiable_weierstrassProduct (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hord : HasOrderLE f ρ) (hρ : 0 ≤ ρ) {a : ℕ → ℂ} (ha : ∀ n, a n ≠ 0)
    (hfin : ∀ r : ℝ, {n | ‖a n‖ ≤ r}.Finite)
    (hcard : ∀ r : ℝ, 0 < r → (((hfin r).toFinset.card : ℕ) : ℝ)
      ≤ ((∑ᶠ u, divisor f (closedBall (0 : ℂ) r) u : ℤ) : ℝ))
    {p : ℕ} (hp : ρ < p + 1) :
    Differentiable ℂ (weierstrassProduct p a) :=
  -- fully qualified: inside `namespace Complex` the bare name now resolves to the theorem
  -- being defined, not to the one in `Upstream.WeierstrassProduct`
  _root_.Complex.differentiable_weierstrassProduct ha
    (hord.summable_inv_pow hf h0 hρ ha hfin hcard (m := p + 1) (by exact_mod_cast hp))

/-- **And it vanishes exactly on the prescribed zeros.** Together with
`Complex.HasOrderLE.differentiable_weierstrassProduct` this is the constructive half of
Hadamard factorisation, with the zero density supplied by Jensen rather than assumed. -/
theorem HasOrderLE.weierstrassProduct_eq_zero_iff (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hord : HasOrderLE f ρ) (hρ : 0 ≤ ρ) {a : ℕ → ℂ} (ha : ∀ n, a n ≠ 0)
    (hfin : ∀ r : ℝ, {n | ‖a n‖ ≤ r}.Finite)
    (hcard : ∀ r : ℝ, 0 < r → (((hfin r).toFinset.card : ℕ) : ℝ)
      ≤ ((∑ᶠ u, divisor f (closedBall (0 : ℂ) r) u : ℤ) : ℝ))
    {p : ℕ} (hp : ρ < p + 1) {z : ℂ} :
    weierstrassProduct p a z = 0 ↔ ∃ n, a n = z :=
  _root_.Complex.weierstrassProduct_eq_zero_iff ha
    (hord.summable_inv_pow hf h0 hρ ha hfin hcard (m := p + 1) (by exact_mod_cast hp))

end Complex
