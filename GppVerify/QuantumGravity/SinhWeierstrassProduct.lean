import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Data.Complex.Trigonometric

/-!
# The Weierstrass product for `sinh`: `sinh(πλ) = πλ ∏ₙ(1+λ²/n²)`

From `blackbody_law_qg_dtoupin_v1.tex`, Test T4 of `verify_blackbody_capstone.py`
("Weierstrass / determinant face"): `sinh(πλ)/(πλ) = ∏_{n≥1}(1+λ²/n²)`. The paper's own
numerical certification truncates the product at `N = 2000` and bounds the tail by a
Hurwitz-zeta remainder; here the identity is proved in full as a genuine infinite product
(a `Tendsto` statement for the partial products, unconditional on `λ`), directly from
Mathlib's Euler product for `sin` (`Complex.tendsto_euler_sin_prod`) via the substitution
`z = iλ`: `sin(πiλ) = iλπ∏(1-(iλ)²/n²) = iλπ∏(1+λ²/n²)`, and `sin(x·i) = sinh(x)·i`
(`Complex.sin_mul_I`) turns the left side into `i·sinh(πλ)`.
-/

namespace GppSinhWeierstrass

open Filter Topology

/-- **The Weierstrass product for `sinh`**, as a genuine infinite product (not a truncated
    numerical bound): for every real `λ`, the partial products of `1+λ²/n²` converge to
    `sinh(πλ)/(πλ)`. -/
theorem tendsto_prod_one_add_sq_div (lam : ℝ) :
    Filter.Tendsto (fun n : ℕ => Real.pi * lam *
        ∏ j ∈ Finset.range n, ((1:ℝ) + lam ^ 2 / ((j:ℝ) + 1) ^ 2))
      Filter.atTop (𝓝 (Real.sinh (Real.pi * lam))) := by
  have hC := Complex.tendsto_euler_sin_prod ((lam:ℂ) * Complex.I)
  have hterm : ∀ j : ℕ, (1:ℂ) + (lam:ℂ) ^ 2 / ((j:ℂ) + 1) ^ 2
      = (1:ℂ) - ((lam:ℂ) * Complex.I) ^ 2 / ((j:ℂ) + 1) ^ 2 := by
    intro j
    have hsq : ((lam:ℂ) * Complex.I) ^ 2 = -(lam:ℂ) ^ 2 := by rw [mul_pow, Complex.I_sq]; ring
    rw [hsq]; ring
  have hprodeq : ∀ n : ℕ,
      ((∏ j ∈ Finset.range n, ((1:ℝ) + lam ^ 2 / ((j:ℝ) + 1) ^ 2) : ℝ) : ℂ)
        = ∏ j ∈ Finset.range n, ((1:ℂ) - ((lam:ℂ) * Complex.I) ^ 2 / ((j:ℂ) + 1) ^ 2) := by
    intro n
    push_cast
    exact Finset.prod_congr rfl (fun j _ => hterm j)
  have hkey : ∀ n : ℕ, Complex.I *
      (((Real.pi * lam * ∏ j ∈ Finset.range n, ((1:ℝ) + lam ^ 2 / ((j:ℝ) + 1) ^ 2)) : ℝ) : ℂ)
      = (Real.pi:ℂ) * ((lam:ℂ) * Complex.I) *
          ∏ j ∈ Finset.range n, ((1:ℂ) - ((lam:ℂ) * Complex.I) ^ 2 / ((j:ℂ) + 1) ^ 2) := by
    intro n
    rw [show (((Real.pi * lam *
          ∏ j ∈ Finset.range n, ((1:ℝ) + lam ^ 2 / ((j:ℝ) + 1) ^ 2)) : ℝ) : ℂ)
        = (Real.pi:ℂ) * (lam:ℂ) *
            ((∏ j ∈ Finset.range n, ((1:ℝ) + lam ^ 2 / ((j:ℝ) + 1) ^ 2) : ℝ) : ℂ) by
      push_cast; ring, hprodeq n]
    ring
  have hsin_eq : Complex.sin ((Real.pi:ℂ) * ((lam:ℂ) * Complex.I))
      = Complex.I * ((Real.sinh (Real.pi * lam) : ℝ) : ℂ) := by
    rw [show ((Real.pi:ℂ) * ((lam:ℂ) * Complex.I)) = ((Real.pi * lam : ℝ):ℂ) * Complex.I by
        push_cast; ring,
      Complex.sin_mul_I, Complex.ofReal_sinh, mul_comm]
  rw [hsin_eq] at hC
  have hC2 : Filter.Tendsto
      (fun n : ℕ => Complex.I *
        (((Real.pi * lam * ∏ j ∈ Finset.range n, ((1:ℝ) + lam ^ 2 / ((j:ℝ) + 1) ^ 2)) : ℝ) : ℂ))
      Filter.atTop (𝓝 (Complex.I * ((Real.sinh (Real.pi * lam) : ℝ) : ℂ))) := by
    simp_rw [hkey]
    exact hC
  have hC3 : Filter.Tendsto
      (fun n : ℕ =>
        ((Real.pi * lam * ∏ j ∈ Finset.range n, ((1:ℝ) + lam ^ 2 / ((j:ℝ) + 1) ^ 2) : ℝ) : ℂ))
      Filter.atTop (𝓝 (((Real.sinh (Real.pi * lam) : ℝ)) : ℂ)) := by
    have h := hC2.const_mul (Complex.I)⁻¹
    have hfun : ∀ n : ℕ, (Complex.I)⁻¹ * (Complex.I *
        (((Real.pi * lam * ∏ j ∈ Finset.range n, ((1:ℝ) + lam ^ 2 / ((j:ℝ) + 1) ^ 2)) : ℝ) : ℂ))
        = ((Real.pi * lam * ∏ j ∈ Finset.range n, ((1:ℝ) + lam ^ 2 / ((j:ℝ) + 1) ^ 2) : ℝ) : ℂ) := by
      intro n
      rw [← mul_assoc, inv_mul_cancel₀ Complex.I_ne_zero, one_mul]
    have hlim : (Complex.I)⁻¹ * (Complex.I * ((Real.sinh (Real.pi * lam) : ℝ) : ℂ))
        = ((Real.sinh (Real.pi * lam) : ℝ) : ℂ) := by
      rw [← mul_assoc, inv_mul_cancel₀ Complex.I_ne_zero, one_mul]
    simp_rw [hfun] at h
    rwa [hlim] at h
  have hC4 : Filter.Tendsto
      (fun n : ℕ => Complex.re
        (((Real.pi * lam * ∏ j ∈ Finset.range n, ((1:ℝ) + lam ^ 2 / ((j:ℝ) + 1) ^ 2) : ℝ) : ℂ)))
      Filter.atTop (𝓝 (Complex.re (((Real.sinh (Real.pi * lam) : ℝ)) : ℂ))) :=
    (Complex.continuous_re.tendsto _).comp hC3
  simp only [Complex.ofReal_re] at hC4
  exact hC4

end GppSinhWeierstrass
