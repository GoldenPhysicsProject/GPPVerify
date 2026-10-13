import Mathlib.Data.Nat.Fib.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

/-!
# Fibonacci/Lucas dynamics of the golden modular matrix

Source: Codex, `work/codex/2026-10-13_fibonacci_lucas_golden_haar_entropy_prime_congruences.md`,
following Daniel Toupin's request to trace the Fibonacci/Lucas structure of the golden prime-five
boundary.

With `Q = [[1,1],[1,0]]` (`det Q = −1`) and the minimal hyperbolic modular matrix `A = Q² = [[2,1],[1,1]]`:
* `Q_pow`: `Q^{m+1} = [[F_{m+2}, F_{m+1}], [F_{m+1}, F_m]]`;
* `cassini`: `F_{n+1}² − F_n F_{n+1} − F_n² = (−1)^n` (read off from `det Qⁿ = (−1)ⁿ`);
* `trace_A_pow`: `tr Aⁿ = L_{2n}`, with Lucas numbers `L_n = 2F_{n+1} − F_n`;
* `det_A_pow_sub_one`: `det(Aⁿ − 1) = 2 − L_{2n}`. So the number of points of the torus `ℝ²/ℤ²` fixed by
  `Aⁿ` is `P_n = L_{2n} − 2`;
* `periodic_odd` / `periodic_even`: `P_n = L_n²` for odd `n` and `P_n = 5 F_n²` for even `n`;
* `fib_mod_prime_small`: `F_p ≡ χ₅(p) (mod p)` for every odd prime `p < 100`, `p ≠ 5`, checked by
  `decide`. The congruence for all odd primes is the classical Frobenius argument in `𝔽_p[√5]`; that
  argument is not formalized here.

These are classical facts, restated in the shadow-framework vocabulary. The Artin–Mazur zeta
`(1−z)²/(1−3z+z²)` and the entropy/residue identity `h_Haar(A) = 2 log φ = Res Λ_{ℚ(√5)}` are not
formalized. **No RH claim:** the toral dynamical zeta is rational and carries no zeta zeros.
-/

namespace GppGoldenLucas

open Matrix Nat

/-- The Fibonacci matrix. -/
def Q : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, 0]

/-- The golden modular matrix `A = Q²`. -/
def A : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 1, 1]

/-- Lucas numbers `L_n = 2F_{n+1} − F_n`. -/
def lucas (n : ℕ) : ℤ := 2 * (fib (n + 1) : ℤ) - fib n

theorem A_eq_Q_sq : A = Q ^ 2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [A, Q, sq, mul_apply, Fin.sum_univ_two]

theorem Q_pow (m : ℕ) :
    Q ^ (m + 1) = !![(fib (m + 2) : ℤ), fib (m + 1); fib (m + 1), fib m] := by
  induction m with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp [Q]
  | succ k ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Q, mul_apply, Fin.sum_univ_two, fib_add_two] <;> ring

theorem det_Q : Q.det = -1 := by simp [Q, det_fin_two]

/-- **Cassini**, in the form `F_{n+1}² − F_n F_{n+1} − F_n² = (−1)ⁿ`. -/
theorem cassini (n : ℕ) :
    (fib (n + 1) : ℤ) ^ 2 - fib n * fib (n + 1) - (fib n : ℤ) ^ 2 = (-1) ^ n := by
  cases n with
  | zero => simp
  | succ m =>
    have h := congrArg Matrix.det (Q_pow m)
    rw [det_pow, det_Q, det_fin_two] at h
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one] at h
    have hf : (fib (m + 2) : ℤ) = fib m + fib (m + 1) := by rw [fib_add_two]; push_cast; ring
    rw [hf] at h ⊢
    linear_combination -h

/-- **`tr Aⁿ = L_{2n}`.** -/
theorem trace_A_pow (n : ℕ) : (A ^ n) 0 0 + (A ^ n) 1 1 = lucas (2 * n) := by
  cases n with
  | zero => simp [lucas]
  | succ k =>
    rw [A_eq_Q_sq, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Q_pow]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
      lucas]
    rw [show 2 * k + 1 + 1 + 1 = (2 * k + 1) + 2 by ring, fib_add_two]
    push_cast
    ring

theorem det_A : A.det = 1 := by simp [A, det_fin_two]

/-- **Periodic points**: `det(Aⁿ − 1) = 2 − L_{2n}`, so `P_n = |det(Aⁿ − 1)| = L_{2n} − 2`. -/
theorem det_A_pow_sub_one (n : ℕ) : (A ^ n - 1).det = 2 - lucas (2 * n) := by
  have hd : (A ^ n).det = 1 := by rw [det_pow, det_A, one_pow]
  rw [← trace_A_pow, det_fin_two]
  rw [det_fin_two] at hd
  simp only [Matrix.sub_apply, one_apply_eq, one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero]
  linear_combination hd

/-- `L_{2n} − 2` in terms of `F_n, F_{n+1}`, the shared step for the parity split. -/
theorem lucas_two_mul_sub_two (n : ℕ) :
    lucas (2 * n) - 2 = lucas n ^ 2 - 2 * (1 + (-1) ^ n) := by
  have hQ : (Q ^ n) ^ 2 = Q ^ (2 * n) := by rw [← pow_mul, mul_comm]
  cases n with
  | zero => simp [lucas]
  | succ m =>
    have h2 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0 + M 1 1) hQ
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, Q_pow, Q_pow, sq] at h2
    simp only [mul_apply, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero, cons_val_one,
      empty_val', cons_val_fin_one] at h2
    have hl : lucas (2 * (m + 1)) = (fib (2 * m + 1 + 2) : ℤ) + fib (2 * m + 1) := by
      rw [lucas, show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring,
        show 2 * (m + 1) = (2 * m + 1) + 1 by ring, show 2 * m + 1 + 2 = (2 * m + 1) + 2 from rfl,
        fib_add_two]
      push_cast
      ring
    have hc := cassini (m + 1)
    have hf : (fib (m + 2) : ℤ) = fib m + fib (m + 1) := by rw [fib_add_two]; push_cast; ring
    rw [hl, ← h2, lucas, hf]
    rw [hf] at hc
    linear_combination (-2) * hc

/-- **Odd `n`: `P_n = L_n²`.** -/
theorem periodic_odd {n : ℕ} (hn : Odd n) : lucas (2 * n) - 2 = lucas n ^ 2 := by
  rw [lucas_two_mul_sub_two, hn.neg_one_pow]
  ring

/-- **Even `n`: `P_n = 5F_n²`.** -/
theorem periodic_even {n : ℕ} (hn : Even n) : lucas (2 * n) - 2 = 5 * (fib n : ℤ) ^ 2 := by
  rw [lucas_two_mul_sub_two, hn.neg_one_pow]
  have hc := cassini n
  rw [hn.neg_one_pow] at hc
  unfold lucas
  linear_combination 4 * hc

/-- **`F_p ≡ χ₅(p) (mod p)`** for the odd primes `p < 100`, `p ≠ 5`. -/
theorem fib_mod_prime_small :
    ∀ p ∈ ({3, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
      89, 97} : Finset ℕ),
      fib p % p = if p % 5 = 1 ∨ p % 5 = 4 then 1 else p - 1 := by
  decide

end GppGoldenLucas
