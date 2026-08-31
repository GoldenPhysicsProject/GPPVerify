import Mathlib.Analysis.Complex.Exponential
import GppVerify.QuantumGravity.StefanBoltzmannFamily
import GppVerify.QuantumGravity.SinhWeierstrassProduct

/-!
# The spectral weight `P(λ) = πλ/sinh(πλ)`: Planck form and the reciprocal product

From Toupin, "The Spectral Weight π λ / sinh π λ" and "Modular Thermality of the Celestial
Spectral Weight" (2026): `P(λ)` is the two-particle massless phase-space weight of a
celestial unitarity cut, `Γ(1+iλ)Γ(1-iλ)` on the shadow locus (`GammaModulusIdentity.lean`).
This file records two further identities it satisfies.

* `planck_form`: `P` written as a difference of two Bose occupation numbers at spacings
  `πλ` and `2πλ`, a genuine Planck-form identity with the zero-point energies of the two
  terms cancelling exactly.
* `one_div_P_tendsto_tprod`: the reciprocal `1/P(λ)` is the Weierstrass product
  `∏ₙ(1+λ²/n²)` as a `Tendsto` statement, an immediate restatement of
  `GppSinhWeierstrass.tendsto_prod_one_add_sq_div` for `λ ≠ 0`.
-/

namespace GppSpectralWeight

open GppStefanBoltzmann Filter Topology Real

/-- The Bose occupation number `1/(exp y - 1)`. -/
noncomputable def bose (y : ℝ) : ℝ := 1 / (Real.exp y - 1)

/-- **Planck form**: for `λ > 0`, `P(λ)` is `2πλ` times the difference of Bose occupation
    numbers at spacings `πλ` and `2πλ`. The zero-point energies of the two Bose terms
    (`πλ/2` and `2πλ/2`) cancel identically, which is why no additive constant survives. -/
theorem planck_form {lam : ℝ} (hlam : 0 < lam) :
    P lam = 2 * π * lam * (bose (π * lam) - bose (2 * π * lam)) := by
  have hpl : 0 < π * lam := by positivity
  have ha1 : (1:ℝ) < Real.exp (π * lam) := by
    have h := Real.exp_lt_exp.mpr hpl
    rwa [Real.exp_zero] at h
  have hexp2m1 : Real.exp (2 * π * lam) - 1
      = (Real.exp (π * lam) - 1) * (Real.exp (π * lam) + 1) := by
    rw [show 2 * π * lam = π * lam + π * lam by ring, Real.exp_add]; ring
  have hexpneg : Real.exp (-(π * lam)) = (Real.exp (π * lam))⁻¹ := Real.exp_neg _
  have ha0 : Real.exp (π * lam) ≠ 0 := (Real.exp_pos _).ne'
  have haM1 : Real.exp (π * lam) - 1 ≠ 0 := by linarith
  have haP1 : Real.exp (π * lam) + 1 ≠ 0 := by linarith
  -- Each auxiliary identity below has denominators that are only ever the plain atoms
  -- `Real.exp (π*lam)`, `Real.exp (π*lam) - 1`, `Real.exp (π*lam) + 1` — never their
  -- product re-expanded to `a^2 - 1`, which `field_simp` cannot relate back to `haM1`/`haP1`
  -- once its internal `ring_nf` normalization re-expands the product.
  have hA : Real.exp (π * lam) - (Real.exp (π * lam))⁻¹
      = (Real.exp (π * lam) - 1) * (Real.exp (π * lam) + 1) / Real.exp (π * lam) := by
    field_simp
    ring
  have hB : (1:ℝ) / (Real.exp (π * lam) - 1)
      - 1 / ((Real.exp (π * lam) - 1) * (Real.exp (π * lam) + 1))
      = Real.exp (π * lam) / ((Real.exp (π * lam) - 1) * (Real.exp (π * lam) + 1)) := by
    field_simp
    ring
  unfold P bose
  rw [Real.sinh_eq, hexpneg, hexp2m1, hA, hB]
  field_simp
  ring

/-- **The reciprocal is the Weierstrass product**: for `λ ≠ 0`, the partial products of
    `1 + λ²/n²` converge to `1/P(λ)`. -/
theorem one_div_P_tendsto_tprod {lam : ℝ} (hlam : lam ≠ 0) :
    Filter.Tendsto (fun n : ℕ => ∏ j ∈ Finset.range n, ((1:ℝ) + lam ^ 2 / ((j:ℝ) + 1) ^ 2))
      Filter.atTop (𝓝 (1 / P lam)) := by
  have h := GppSinhWeierstrass.tendsto_prod_one_add_sq_div lam
  have hpine : (π * lam) ≠ 0 := mul_ne_zero Real.pi_ne_zero hlam
  have hval : (1:ℝ) / P lam = Real.sinh (π * lam) / (π * lam) := by
    unfold P
    rw [one_div, inv_div]
  have hdiv := h.div_const (π * lam)
  have heq : (fun n : ℕ =>
        (π * lam * ∏ j ∈ Finset.range n, ((1:ℝ) + lam ^ 2 / ((j:ℝ) + 1) ^ 2)) / (π * lam))
      = (fun n : ℕ => ∏ j ∈ Finset.range n, ((1:ℝ) + lam ^ 2 / ((j:ℝ) + 1) ^ 2)) := by
    funext n
    rw [mul_comm (π * lam), mul_div_assoc, div_self hpine, mul_one]
  rw [heq] at hdiv
  rwa [hval]

end GppSpectralWeight
