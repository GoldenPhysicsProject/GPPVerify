import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

/-!
# Prime square roots: the Möbius fermion state and the half-density threshold

Source: Codex, 2026-09-29, "Prime square roots: multiquadratic hypercube, Möbius parity, and the
half-density principal-series boundary" (GPPDiscovery2
`research/2026-09-29_prime_square_root_hypercube_principal_series.md`, §§3, 4 and 6).

For a finite set `P` of primes, the product state `⊗_{p∈P} (|0⟩ − p^{−s}|1⟩)` has, on the
basis vector labelled by `S ⊆ P` (the squarefree divisor `d_S = ∏_{p∈S} p`), the coefficient
`∏_{p∈S} (−p^{−s})`. This file certifies the following.

* `coeff_eq_moebius`: that coefficient equals `μ(d_S) d_S^{−s}`, so the state is
  `Σ_{d | ∏P} μ(d) d^{−s} |d⟩`. Möbius parity is the global fermion sign.
* `normSq_eq_prod`: `Σ_{S⊆P} |coeff_S|² = ∏_{p∈P} (1 + p^{−2σ})` with `σ = Re s`. The phase
  `t = Im s` drops out.
* `fock_threshold`: `Σ_p p^{−2σ} < ∞ ⇔ σ > 1/2`. The infinite state is square-summable
  exactly to the right of the half-density line.
* `D_det`, `D_eig_minus`, `D_eig_plus`: the trace-energy block
  `D_p = (1/(2(p−1)))·[[p+1, −2√p], [−2√p, p+1]]` has `det D_p = 1/4`. Its eigenvectors are
  `(1, 1)` and `(1, −1)`, with eigenvalues `β/2` and `1/(2β)`, where
  `β = (√p − 1)/(√p + 1)`.
* `beta_eq_tanh`: `β = tanh(log p / 4)`. `beta_inv`: `p ↦ 1/p` sends `β ↦ −β`.
  `beta_five`: `β₅ = φ⁻²`.

Scope: these are exact finite identities. The note's §7–8 RH programme (a zero-survival map on
the hypercube) is a target, not a theorem. The infinite-product/sum equivalence for the norm is
standard and is not formalized here. No RH claim.
-/

namespace GppPrimeSqrtHypercube

open Finset ArithmeticFunction Real

/-- Möbius on a product of distinct primes. -/
lemma moebius_prod_primes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    moebius (∏ p ∈ S, p) = (-1) ^ S.card := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert q S hq ih =>
    have hS' : ∀ p ∈ S, p.Prime := fun p hp => hS p (mem_insert_of_mem hp)
    have hqP : q.Prime := hS q (mem_insert_self q S)
    have hcop : Nat.Coprime q (∏ p ∈ S, p) := by
      refine Nat.Coprime.prod_right fun p hp => ?_
      exact (Nat.coprime_primes hqP (hS' p hp)).mpr (fun h => hq (h ▸ hp))
    rw [prod_insert hq, isMultiplicative_moebius.map_mul_of_coprime hcop, ih hS',
      moebius_apply_prime hqP, card_insert_of_notMem hq, pow_succ]
    ring

/-- The cpow of a product of positive naturals splits. -/
lemma natProd_cpow (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p) (s : ℂ) :
    ((∏ p ∈ S, p : ℕ) : ℂ) ^ s = ∏ p ∈ S, (p : ℂ) ^ s := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert q S hq ih =>
    rw [prod_insert hq, prod_insert hq, Nat.cast_mul, Complex.natCast_mul_natCast_cpow,
      ih fun p hp => hS p (mem_insert_of_mem hp)]

/-- **The Möbius fermion state.** The coefficient of `|d_S⟩` in `⊗(|0⟩ − p^{−s}|1⟩)` is
`μ(d_S) d_S^{−s}`. -/
theorem coeff_eq_moebius (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (s : ℂ) :
    ∏ p ∈ S, (-(p : ℂ) ^ (-s)) = (moebius (∏ p ∈ S, p) : ℂ) * ((∏ p ∈ S, p : ℕ) : ℂ) ^ (-s) := by
  rw [moebius_prod_primes S hS, natProd_cpow S (fun p hp => (hS p hp).pos)]
  rw [prod_neg]
  push_cast
  ring

/-- **The norm.** `Σ_{S⊆P} |coeff_S|² = ∏_{p∈P}(1 + p^{−2σ})`. The phase drops out. -/
theorem normSq_eq_prod (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (s : ℂ) :
    ∑ S ∈ P.powerset, ‖∏ p ∈ S, (-(p : ℂ) ^ (-s))‖ ^ 2 =
      ∏ p ∈ P, (1 + (p : ℝ) ^ (-2 * s.re)) := by
  have hterm : ∀ p ∈ P, ‖-(p : ℂ) ^ (-s)‖ ^ 2 = (p : ℝ) ^ (-2 * s.re) := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    rw [norm_neg, Complex.norm_natCast_cpow_of_pos (hP p hp).pos, Complex.neg_re,
      ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    norm_num
    ring_nf
  rw [prod_one_add]
  refine sum_congr rfl fun S hS => ?_
  rw [norm_prod, ← prod_pow]
  exact prod_congr rfl fun p hp => hterm p (mem_powerset.mp hS hp)

/-- **The half-density threshold.** The infinite prime fermion state is square-summable
exactly when `σ > 1/2`. -/
theorem fock_threshold (σ : ℝ) :
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-2 * σ)) ↔ 1 / 2 < σ := by
  rw [Nat.Primes.summable_rpow]
  constructor <;> intro h <;> linarith

/-- The Cayley variable `β_p = (√p − 1)/(√p + 1)`. -/
noncomputable def beta (p : ℝ) : ℝ := (sqrt p - 1) / (sqrt p + 1)

/-- The trace-energy block `D_p`, as its diagonal entry `a` and off-diagonal entry `b`. -/
noncomputable def Da (p : ℝ) : ℝ := (p + 1) / (2 * (p - 1))
noncomputable def Db (p : ℝ) : ℝ := -2 * sqrt p / (2 * (p - 1))

/-- `det D_p = 1/4` for every `p > 1`. -/
theorem D_det {p : ℝ} (hp : 1 < p) : Da p * Da p - Db p * Db p = 1 / 4 := by
  have h1 : p - 1 ≠ 0 := by linarith
  have hs : sqrt p ^ 2 = p := sq_sqrt (by linarith)
  unfold Da Db
  field_simp
  nlinarith [hs]

/-- On `(1, 1)` the eigenvalue is `a + b = β/2`. -/
theorem D_eig_minus {p : ℝ} (hp : 1 < p) : Da p + Db p = beta p / 2 := by
  have hs : sqrt p ^ 2 = p := sq_sqrt (by linarith)
  have hs1 : 1 < sqrt p := by rw [show (1 : ℝ) = sqrt 1 by simp]; exact sqrt_lt_sqrt (by norm_num) hp
  have h1 : p - 1 ≠ 0 := by linarith
  have h2 : sqrt p + 1 ≠ 0 := by linarith
  unfold Da Db beta
  field_simp
  nlinarith [hs]

/-- On `(1, −1)` the eigenvalue is `a − b = 1/(2β)`. -/
theorem D_eig_plus {p : ℝ} (hp : 1 < p) : Da p - Db p = 1 / (2 * beta p) := by
  have hs : sqrt p ^ 2 = p := sq_sqrt (by linarith)
  have hs1 : 1 < sqrt p := by rw [show (1 : ℝ) = sqrt 1 by simp]; exact sqrt_lt_sqrt (by norm_num) hp
  have h1 : p - 1 ≠ 0 := by linarith
  have h2 : sqrt p - 1 ≠ 0 := by linarith
  have h3 : sqrt p + 1 ≠ 0 := by linarith
  unfold Da Db beta
  field_simp
  nlinarith [hs]

/-- `β_p = tanh(log p / 4)`. -/
theorem beta_eq_tanh {p : ℝ} (hp : 0 < p) : beta p = tanh (log p / 4) := by
  have hsq : sqrt p = exp (log p / 4) ^ 2 := by
    rw [← exp_nat_mul, sqrt_eq_rpow, rpow_def_of_pos hp]; congr 1; push_cast; ring
  have he : 0 < exp (log p / 4) := exp_pos _
  rw [tanh_eq_sinh_div_cosh, sinh_eq, cosh_eq, beta, hsq, exp_neg]
  field_simp

/-- Inversion `p ↦ 1/p` flips the sign of `β`. -/
theorem beta_inv {p : ℝ} (hp : 0 < p) : beta p⁻¹ = -beta p := by
  have hs : 0 < sqrt p := sqrt_pos.mpr hp
  rw [beta, beta, sqrt_inv]
  field_simp
  ring

/-- `β₅ = φ⁻²`, a special identity of the prime `5` (no claim that all primes organise by φ). -/
theorem beta_five : beta 5 = goldenRatio⁻¹ ^ 2 := by
  have h5 : sqrt 5 ^ 2 = 5 := sq_sqrt (by norm_num)
  have hpos : 0 < sqrt 5 := by positivity
  rw [beta, goldenRatio]
  field_simp
  nlinarith [h5]

end GppPrimeSqrtHypercube
