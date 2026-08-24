import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic

/-!
# The squarefree-density Euler product `∏_p (1 - p⁻²) = 6/π²`

Source: `ONON5213.tex`, "The Squarefree Coupling: `α/π²`" (Theorem
`thm:squarefree`). The manuscript's identity
`α/π² = (α/6)·∏_p(1 - p⁻²)` reduces, after cancelling the physical
coupling `α`, to the purely arithmetic statement `∏_p(1 - p⁻²) = 6/π²`,
i.e. the reciprocal of the Euler product for `ζ(2)`. This is genuine,
classical number theory (the density of squarefree integers), tied here
to Mathlib's actual `riemannZeta` Euler-product machinery
(`riemannZeta_eulerProduct`) and the closed form `riemannZeta 2 = π²/6`,
rather than restated as a numerically-checked truncated product.

## What is proved

* `squarefree_density_partial_products_tendsto`: the partial products
  `∏_{p < n} (1 - p⁻²)` converge to `(ζ(2))⁻¹` as `n → ∞`, obtained by
  inverting Mathlib's `riemannZeta_eulerProduct` convergence statement
  for `∏_{p<n} (1 - p⁻²)⁻¹ → ζ(2)`.
* `squarefree_density_partial_products_tendsto_six_div_pi_sq`: the same
  statement with the limit made numerically explicit, `6/π²`, via
  `riemannZeta_two`.

## What is not claimed

The physical identification `α/π² = (α/6)·∏_p(1-p⁻²)` as a statement
about the fine-structure constant, and the two-loop QED coefficient
remark (`ζ(2)/2` appearing in the anomalous magnetic moment), are not
formalized — only the underlying arithmetic identity `∏_p(1-p⁻²) = 6/π²`
that both rest on.
-/

namespace GppSquarefreeDensity

open Filter Topology Nat

/-- **The squarefree-density Euler product, convergence form**: the partial
products `∏_{p < n} (1 - p⁻²)` over primes `p < n` converge, as
`n → ∞`, to `(ζ(2))⁻¹` — obtained by inverting Mathlib's convergent
Euler product `∏_{p<n} (1-p⁻²)⁻¹ → ζ(2)` (`riemannZeta_eulerProduct`)
term-by-term. -/
theorem squarefree_density_partial_products_tendsto :
    Tendsto (fun n : ℕ => ∏ p ∈ primesBelow n, (1 - (p : ℂ) ^ (-(2 : ℂ)))) atTop
      (𝓝 (riemannZeta 2)⁻¹) := by
  have h1 : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have htendsto := riemannZeta_eulerProduct h1
  have hzeta_ne : riemannZeta (2 : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h1
  have hinv := htendsto.inv₀ hzeta_ne
  simpa [Finset.prod_inv_distrib] using hinv

/-- **The squarefree-density Euler product, explicit value**: the same
convergence, with the limit evaluated to the closed form `6/π²` via
`riemannZeta_two : ζ(2) = π²/6`. This is `∏_p(1 - p⁻²) = 6/π²`, the
arithmetic content of `thm:squarefree`. -/
theorem squarefree_density_partial_products_tendsto_six_div_pi_sq :
    Tendsto (fun n : ℕ => ∏ p ∈ primesBelow n, (1 - (p : ℂ) ^ (-(2 : ℂ)))) atTop
      (𝓝 (6 / (Real.pi : ℂ) ^ 2)) := by
  have h := squarefree_density_partial_products_tendsto
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hval : (riemannZeta 2)⁻¹ = 6 / (Real.pi : ℂ) ^ 2 := by
    rw [riemannZeta_two]
    field_simp
  rwa [hval] at h

end GppSquarefreeDensity
