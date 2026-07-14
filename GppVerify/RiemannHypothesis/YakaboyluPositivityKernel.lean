import Mathlib.Data.Complex.BigOperators

/-!
# The arithmetic kernel of Yakaboylu's positivity argument (Theorem 5.1, eq. (67))

The final step of Yakaboylu, *Nontrivial Riemann Zeros as Spectrum* (arXiv:2408.15135v14,
Theorem 5.1) — reproduced as Theorem 4.2 of the companion Abel-Cesàro paper
(`rh_cesaro_v2.tex`) — derives `Re(ρ) = 1/2` from `Ŵ ≥ 0` by a two-line quadratic-form
computation: the form `⟨φ|Ŵ|φ⟩ = Σ_ρ c̄_{1-ρ̄} c_ρ` evaluated on the test vector
`c_{ρ₀} = 1, c_{1-ρ̄₀} = -1` (all other coefficients zero) equals `-2 < 0` whenever
`1 - ρ̄₀ ≠ ρ₀`, contradicting positivity; conversely, when every zero is self-dual
(`1 - ρ̄ = ρ`, i.e. `Re ρ = 1/2`), the form collapses to `Σ_ρ |c_ρ|² ≥ 0`.

This file formalizes exactly that arithmetic — the part of Theorem 5.1 that is finite
linear algebra over `ℂ`:

* `swap_test_vector_exists` — for distinct `ρ₀ ≠ σ₀` (in the paper, `σ₀ = 1 - ρ̄₀`,
  distinct from `ρ₀` exactly when `Re ρ₀ ≠ 1/2`) a coefficient vector with
  `c ρ₀ = 1, c σ₀ = -1` exists;
* `swap_test_vector_value` — on any such vector the paired form is exactly `-2 < 0`;
* `diagonal_form_nonneg` — the self-dual (diagonal) form is a sum of `|c_ρ|²`, hence has
  nonnegative real part, over any finite set of zeros.

The genuinely deep content of Theorem 5.1 — that `Ŵ` is well defined and positive
semidefinite (via the regularized `V̂_{R,ε} > 0` of eq. (46), whose matrix-element value
is `GppYakaboylu.regularized_matrix_element`, compressed through the oblique projections
of Corollary 4.6) — is unbounded operator theory on rigged Hilbert spaces and is *not*
formalized; these lemmas are the honest boundary of what the elementary layer provides.
-/

namespace GppYakaboylu

/-- For distinct pairing partners `ρ₀ ≠ σ₀` the two-point test vector of Theorem 5.1's
    contradiction exists: some `c : ℂ → ℂ` with `c ρ₀ = 1` and `c σ₀ = -1`. -/
open Classical in
theorem swap_test_vector_exists {ρ₀ σ₀ : ℂ} (hne : ρ₀ ≠ σ₀) :
    ∃ c : ℂ → ℂ, c ρ₀ = 1 ∧ c σ₀ = -1 :=
  ⟨fun s => if s = ρ₀ then 1 else if s = σ₀ then -1 else 0, by simp, by simp [Ne.symm hne]⟩

/-- **The off-critical test vector pairs to `-2`** (Theorem 5.1, eq. (67)): any
    coefficient vector with `c ρ₀ = 1` and `c σ₀ = -1` gives
    `c̄_{σ₀}·c_{ρ₀} + c̄_{ρ₀}·c_{σ₀} = -2 < 0` — the two surviving terms of the paired
    quadratic form when the pairing swaps `ρ₀ ↔ σ₀` instead of fixing them. This is the
    entire arithmetic content of the contradiction forcing `Re ρ = 1/2` from `Ŵ ≥ 0`. -/
theorem swap_test_vector_value {c : ℂ → ℂ} {ρ₀ σ₀ : ℂ}
    (h1 : c ρ₀ = 1) (h2 : c σ₀ = -1) :
    (starRingEnd ℂ) (c σ₀) * c ρ₀ + (starRingEnd ℂ) (c ρ₀) * c σ₀ = -2 := by
  rw [h1, h2, map_neg, map_one]
  ring

/-- **The self-dual (diagonal) form is nonnegative**: when every zero pairs with itself,
    the quadratic form is `Σ_ρ c̄_ρ c_ρ = Σ_ρ |c_ρ|²`, with nonnegative real part over any
    finite set of zeros — positivity holds automatically on the critical line, which is
    why `Ŵ ≥ 0` singles it out. -/
theorem diagonal_form_nonneg (S : Finset ℂ) (c : ℂ → ℂ) :
    0 ≤ (∑ ρ ∈ S, (starRingEnd ℂ) (c ρ) * c ρ).re := by
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro ρ _
  rw [mul_comm, Complex.mul_conj]
  simp only [Complex.ofReal_re]
  exact Complex.normSq_nonneg (c ρ)

end GppYakaboylu
