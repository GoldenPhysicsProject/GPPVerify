import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

/-!
# Arithmetic Poisson bulk: the logarithmic Hamiltonian as a Dirichlet-to-Neumann operator

Source: Codex / Discovery2, `research/2026-09-27_arithmetic_poisson_bulk_dtn_hamiltonian.md` §§2, 3
and 8. Daniel Toupin / Golden Physics Project, with AI assistance from Codex (statements) and Claude
Code (formalization).

For boundary data `f = Σ a_n |n⟩` the bulk extension is `Φ_f(r, t) = Σ a_n n^{−(r+it)}`. Termwise,
with `L = log n` and `u(r,t) = a · exp(−(r + it) L)`:

* `bulk_eq_cpow`: `a · n^{−(r+it)} = a · exp(−(r+it) log n)` for `n ≥ 1`.
* `bulk_hasDerivAt_r`, `bulk_hasDerivAt_t`: `∂_r u = −L u`, `∂_t u = −iL u`.
* `bulk_cauchy_riemann`: `(∂_r + i ∂_t) u = 0` (the positive-frequency Hardy/harmonic condition).
* `bulk_second_r`, `bulk_second_t`, `bulk_laplace`: `∂_r² u = L² u`, `∂_t² u = −L² u`, hence
  `∂_r² u + ∂_t² u = 0`.
* `dtn_eigen`: at `r = 0` and `t = 0`, `−∂_r u = L · a`, so the outward normal derivative acts as
  `H|n⟩ = (log n)|n⟩`.
* `vonMangoldt_projection`: `Σ_{d ≥ 2} Λ(d) [d ∣ n] = log n`, the decomposition
  `H = Σ_{d≥2} Λ(d) P_d` on the basis `|n⟩`.

**Scope.** Termwise identities for one basis vector. The summation over `n`, convergence of the
Dirichlet series, the Hardy-space interpretation, the thermal partition function `Tr e^{−βH} = ζ(β)`
and the coherent-state norm `‖k_s‖² = ζ(2σ)` are not formalized here. No claim about RH.
-/

set_option autoImplicit false

open Complex

namespace GppArithmeticPoissonBulk

/-- Termwise bulk field `a · exp(−(r + it) L)`, `L = log n`. -/
noncomputable def bulk (L : ℝ) (a : ℂ) (r t : ℝ) : ℂ :=
  a * Complex.exp (-(((r : ℂ) + (t : ℂ) * I)) * (L : ℂ))

/-- `a · n^{−(r+it)} = a · exp(−(r+it) log n)` for `n ≥ 1`. -/
theorem bulk_eq_cpow (n : ℕ) (hn : 1 ≤ n) (a : ℂ) (r t : ℝ) :
    a * (n : ℂ) ^ (-(((r : ℂ) + (t : ℂ) * I))) = bulk (Real.log n) a r t := by
  have hn0 : (n : ℂ) ≠ 0 := by
    have : (n : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  unfold bulk
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (by positivity)]
  push_cast
  ring_nf

/-- `∂_r u = −L u`. -/
theorem bulk_hasDerivAt_r (L : ℝ) (a : ℂ) (r t : ℝ) :
    HasDerivAt (fun r : ℝ => bulk L a r t) (-(L : ℂ) * bulk L a r t) r := by
  have h1 : HasDerivAt (fun r : ℝ => ((r : ℝ) : ℂ)) 1 r := (hasDerivAt_id r).ofReal_comp
  have h2 : HasDerivAt (fun r : ℝ => -(((r : ℂ) + (t : ℂ) * I)) * (L : ℂ)) (-(L : ℂ)) r := by
    have := ((h1.add_const ((t : ℂ) * I)).neg).mul_const (L : ℂ)
    simpa using this
  have h3 := (h2.cexp).const_mul a
  unfold bulk
  exact h3.congr_deriv (by ring)

/-- `∂_t u = −iL u`. -/
theorem bulk_hasDerivAt_t (L : ℝ) (a : ℂ) (r t : ℝ) :
    HasDerivAt (fun t : ℝ => bulk L a r t) (-(I * (L : ℂ)) * bulk L a r t) t := by
  have h1 : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
  have h2 : HasDerivAt (fun t : ℝ => -(((r : ℂ) + (t : ℂ) * I)) * (L : ℂ))
      (-(I * (L : ℂ))) t := by
    have := (((h1.mul_const I).const_add (r : ℂ)).neg).mul_const (L : ℂ)
    simpa using this
  have h3 := (h2.cexp).const_mul a
  unfold bulk
  exact h3.congr_deriv (by ring)

/-- **Cauchy–Riemann / positive-frequency condition**: `(∂_r + i ∂_t) u = 0`. -/
theorem bulk_cauchy_riemann (L : ℝ) (a : ℂ) (r t : ℝ) :
    (-(L : ℂ) * bulk L a r t) + I * (-(I * (L : ℂ)) * bulk L a r t) = 0 := by
  ring_nf
  simp [Complex.I_sq]

/-- **DtN eigenvalue**: at the boundary `r = 0`, `t = 0`, `−∂_r u = L · a`. -/
theorem dtn_eigen (L : ℝ) (a : ℂ) :
    -(-(L : ℂ) * bulk L a 0 0) = (L : ℂ) * a := by
  unfold bulk
  simp

/-- `H = Σ_{d ≥ 2} Λ(d) P_d` on the basis: `Σ_{d ≥ 2, d ∣ n} Λ(d) = log n` for `n ≥ 1`. -/
theorem vonMangoldt_projection (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ Finset.Icc 2 n, (if d ∣ n then ArithmeticFunction.vonMangoldt d else 0) =
      Real.log n := by
  have h := ArithmeticFunction.vonMangoldt_sum (n := n)
  rw [← h]
  have hdiv : ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d =
      ∑ d ∈ Finset.Icc 1 n, (if d ∣ n then ArithmeticFunction.vonMangoldt d else 0) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hd, hn0⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn, Nat.le_of_dvd hn hd⟩, hd⟩
    · rintro ⟨_, hd⟩
      exact ⟨hd, by omega⟩
  rw [hdiv]
  have hI : Finset.Icc 1 n = insert 1 (Finset.Icc 2 n) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hI, Finset.sum_insert (by simp)]
  simp

/-- Second radial derivative: `∂_r(∂_r u) = L² u`. -/
theorem bulk_second_r (L : ℝ) (a : ℂ) (r t : ℝ) :
    HasDerivAt (fun r : ℝ => -(L : ℂ) * bulk L a r t)
      (-(L : ℂ) * (-(L : ℂ) * bulk L a r t)) r :=
  (bulk_hasDerivAt_r L a r t).const_mul _

/-- Second time derivative: `∂_t(∂_t u) = −L² u`. -/
theorem bulk_second_t (L : ℝ) (a : ℂ) (r t : ℝ) :
    HasDerivAt (fun t : ℝ => -(I * (L : ℂ)) * bulk L a r t)
      (-(I * (L : ℂ)) * (-(I * (L : ℂ)) * bulk L a r t)) t :=
  (bulk_hasDerivAt_t L a r t).const_mul _

/-- **Harmonic**: `∂_r² u + ∂_t² u = 0`. -/
theorem bulk_laplace (L : ℝ) (a : ℂ) (r t : ℝ) :
    (-(L : ℂ) * (-(L : ℂ) * bulk L a r t)) +
      (-(I * (L : ℂ)) * (-(I * (L : ℂ)) * bulk L a r t)) = 0 := by
  ring_nf
  simp [Complex.I_sq]

end GppArithmeticPoissonBulk
