import GppVerify.RiemannHypothesis.ArithmeticHardySpace
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Euler factorization of the coherent vectors

Unique factorization makes the coherent vector `e_z(n) = n^{-1/2-z}` of `ArithmeticHardySpace`
*completely multiplicative*, and its squared norm an Euler product of local norms:

* `coh_mul`: `e_z(m n) = e_z(m) e_z(n)` (the vector is a character of the multiplicative monoid, i.e. a
  product vector for the factorization `ℓ²(ℕ₊) ≅ ⊗_p ℓ²(ℕ₀)`);
* `local_norm_sq`: the single-prime coherent vector `Σ_k (p^{-1/2-z})^k |k⟩` has squared norm
  `Σ_k |p^{-1/2-z}|^{2k} = (1 − p^{-1-2σ})⁻¹`, `σ = Re z`;
* `norm_sq_euler`: `‖e_z‖² = ∏_p (1 − p^{-1-2σ})⁻¹` — the global norm is the product of the local norms.

At `z → 0⁺` each local state tends to the critical TFD state `√(1−1/p) Σ_k p^{-k/2}|k⟩` (a unit vector),
while the product of local norms diverges like `ζ(1+2σ) ~ 1/(2σ)`: the global coherent state does not
converge in `ℓ²` — the normalized family becomes orthogonal (see `ZetaCoherentBoundary`).

## Checks and scope

All claims check. **Not formalized:** the isometric isomorphism `ℓ²(ℕ₊) ≅ ⊗'_p ℓ²(ℕ₀)` as an infinite
tensor product (only the norm identity it implies), and the identification of the local factors with the
TFD Fock space beyond the radius `r_p = p^{-1/2}` at `z = 0`. No RH claim.
-/

open Complex ComplexConjugate GppArithmeticHardy

namespace GppEulerFactorization

/-- **Complete multiplicativity of the coherent vector.** -/
theorem coh_mul (z : ℂ) (m n : ℕ) : coh z (m * n) = coh z m * coh z n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [coh_zero]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [coh_zero]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold coh logC
  rw [Nat.cast_mul, Real.log_mul hm0.ne' hn0.ne', Real.sqrt_mul hm0.le, mul_inv,
    Complex.ofReal_mul, Complex.ofReal_add, mul_add, Complex.exp_add]
  ring

/-- **The local norm of the single-prime coherent vector.** -/
theorem local_norm_sq (p : ℕ) (hp : 1 < p) (z : ℂ) (hz : 0 < z.re) :
    HasSum (fun k : ℕ => ‖(p : ℂ) ^ (-(1 + 2 * z.re : ℂ))‖ ^ k) (1 - (p : ℝ) ^ (-(1 + 2 * z.re)))⁻¹ := by
  have hp0 : (1 : ℝ) < p := by exact_mod_cast hp
  have hn : ‖(p : ℂ) ^ (-(1 + 2 * z.re : ℂ))‖ = (p : ℝ) ^ (-(1 + 2 * z.re)) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    congr 1
    simp
  rw [hn]
  have h1 : (p : ℝ) ^ (-(1 + 2 * z.re)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp0 (by linarith)
  have h0 : 0 ≤ (p : ℝ) ^ (-(1 + 2 * z.re)) := by positivity
  exact hasSum_geometric_of_lt_one h0 h1

/-- **The global squared norm is the Euler product of the local norms.** -/
theorem norm_sq_euler (z : ℂ) (hz : 0 < z.re) :
    (((‖cohLp z hz‖ ^ 2 : ℝ)) : ℂ) =
      ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-(1 + 2 * (z.re : ℂ))))⁻¹ := by
  have h := coherent_inner z z hz hz
  rw [inner_self_eq_norm_sq_to_K] at h
  have e : (1 + z + conj z : ℂ) = 1 + 2 * (z.re : ℂ) := by
    apply Complex.ext
    · simp; ring
    · simp
  rw [e] at h
  have hre : 1 < (1 + 2 * (z.re : ℂ)).re := by simp; linarith
  have hE := riemannZeta_eulerProduct_tprod hre
  have hneg : -(1 + 2 * (z.re : ℂ)) = -(1 + 2 * z.re : ℂ) := rfl
  rw [← hE] at h
  simpa [← Complex.ofReal_pow] using h

end GppEulerFactorization
