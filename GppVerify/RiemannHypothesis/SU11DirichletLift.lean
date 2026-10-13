import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The Euler logarithm is the Dirichlet-space lift of the prime SU(1,1) coherent state

Source: Codex, GPPDiscovery2 `research/2026-09-27_euler_log_as_dirichlet_lift_of_su11_tfd.md`.

On the compact basis `e_m` of the `k = ½` SU(1,1) module, the coherent vector is `h_z = Σ zᵐ eₘ`.
Its half-integrated non-vacuum part is `v(z) = N^{−1/2}(h_z − e₀) = Σ_{m≥1} zᵐ/√m · eₘ`, with
coefficients `vCoef z m`. This file proves:
* `inner_hasSum`: the ℓ² inner product `Σ_m conj(vₘ(z)) vₘ(w) = −log(1 − z̄w)` for `|z|, |w| < 1`.
  The logarithmic kernel is the `N^{−1/2}` (Dirichlet) lift of the coherent kernel `1/(1 − z̄w)`.
* `free_energy`: for a prime mode `z = p^{−β/2}` with `β > 0`, the norm `Σ_{m≥1} p^{−mβ}/m` equals
  `−log(1 − p^{−β}) = log ζ_p(β)`.
* `fock_kernel`: for `Re u > 1`, **`exp(Σ_p Σ_{m≥1} p^{−mu}/m) = ζ(u)`**. With `u = s̄ + w` this is
  the exponential-vector kernel `⟨ε(v_s), ε(v_w)⟩ = exp⟨v_s, v_w⟩ = ζ(s̄ + w)`.
* `radial_derivative`: `x · d/dx[−log(1 − x)] = x/(1 − x)`, the SU(1,1) forward-null excess.
  Weighted by `log p` and summed over primes this gives `−ζ'/ζ`.

The infinite-dimensional Fock space and the divergence `‖v_s‖² = log ζ(2 Re s) → ∞` as
`Re s ↓ ½` are not formalized here. **No RH claim.**
-/

namespace GppSU11DirichletLift

open Complex

/-- Coefficient of `v(z)` on `e_{m+1}`: `z^{m+1}/√(m+1)`. -/
noncomputable def vCoef (z : ℂ) (m : ℕ) : ℂ := z ^ (m + 1) / (Real.sqrt (m + 1) : ℂ)

theorem conj_vCoef_mul (z w : ℂ) (m : ℕ) :
    (starRingEnd ℂ) (vCoef z m) * vCoef w m = (starRingEnd ℂ z * w) ^ (m + 1) / (m + 1) := by
  have hs : (Real.sqrt ((m : ℝ) + 1) : ℂ) * (Real.sqrt ((m : ℝ) + 1) : ℂ) = (m : ℂ) + 1 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]; push_cast; ring
  have hne : (Real.sqrt ((m : ℝ) + 1) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  unfold vCoef
  rw [map_div₀, map_pow, Complex.conj_ofReal, mul_pow]
  rw [div_mul_div_comm, hs]

/-- **The Dirichlet lift of the coherent kernel**: `⟨v(z), v(w)⟩ = −log(1 − z̄w)`. -/
theorem inner_hasSum {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    HasSum (fun m => (starRingEnd ℂ) (vCoef z m) * vCoef w m)
      (-log (1 - starRingEnd ℂ z * w)) := by
  have h1 : ‖starRingEnd ℂ z * w‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖z‖ * ‖w‖ ≤ ‖z‖ * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hz
  have := hasSum_taylorSeries_neg_log' h1
  simp_rw [conj_vCoef_mul]
  convert this using 2 with m

/-- **Local free energy**: for a prime-mode amplitude `x = p^{−β} ∈ [0, 1)`,
`Σ_{m≥1} xᵐ/m = −log(1 − x)`. -/
theorem free_energy {p : ℕ} (hp : 1 < p) {β : ℝ} (hβ : 0 < β) :
    HasSum (fun m : ℕ => ((p : ℝ) ^ (-β)) ^ (m + 1) / (m + 1))
      (-Real.log (1 - (p : ℝ) ^ (-β))) := by
  have hx0 : 0 ≤ (p : ℝ) ^ (-β) := by positivity
  have hx1 : (p : ℝ) ^ (-β) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp) (by linarith)
  have := Real.hasSum_pow_div_log_of_abs_lt_one (x := (p : ℝ) ^ (-β))
    (by rw [abs_of_nonneg hx0]; exact hx1)
  convert this using 1

theorem norm_prime_cpow_lt_one {u : ℂ} (hu : 1 < u.re) (p : Nat.Primes) :
    ‖(p : ℂ) ^ (-u)‖ < 1 := by
  have hp : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.one_lt
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos, Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)

/-- **The prime Fock kernel**: for `Re u > 1`, `exp(Σ_p Σ_{m≥1} p^{−mu}/m) = ζ(u)`. -/
theorem fock_kernel {u : ℂ} (hu : 1 < u.re) :
    exp (∑' p : Nat.Primes, ∑' m : ℕ, ((p : ℂ) ^ (-u)) ^ (m + 1) / (m + 1)) = riemannZeta u := by
  have hinner : ∀ p : Nat.Primes,
      ∑' m : ℕ, ((p : ℂ) ^ (-u)) ^ (m + 1) / (m + 1) = -log (1 - (p : ℂ) ^ (-u)) := by
    intro p
    have := hasSum_taylorSeries_neg_log' (norm_prime_cpow_lt_one hu p)
    rw [← this.tsum_eq]
  simp_rw [hinner]
  exact riemannZeta_eulerProduct_exp_log hu

/-- **Radial derivative**: `x · d/dx[−log(1 − x)] = x/(1 − x)` for `x < 1`. -/
theorem radial_derivative {x : ℝ} (hx : x < 1) :
    HasDerivAt (fun y => -Real.log (1 - y)) (1 / (1 - x)) x ∧
      x * (1 / (1 - x)) = x / (1 - x) := by
  refine ⟨?_, by ring⟩
  have h1 : (1 : ℝ) - x ≠ 0 := by linarith
  have h : HasDerivAt (fun y => Real.log (1 - y)) (-1 / (1 - x)) x := by
    simpa using ((hasDerivAt_id x).const_sub 1).log h1
  exact h.neg.congr_deriv (by ring)

end GppSU11DirichletLift
