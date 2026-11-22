/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude; task text from Claude, claude.ai seat)
-/
import GppVerify.RiemannHypothesis.MobiusEchoPassivity

/-!
# Mode decomposition of the Möbius gcd form

**Unconditional finite identity; nothing here proves RH.** With `μ` the Möbius function, put

* `J m = Σ_{k ∣ m} μ(m/k) √k` (the Dirichlet convolution `μ ∗ √·`),
* `T y m = Σ_{d ≤ y, m ∣ d} μ(d)/√d`,
* `F y = Σ_{d,e ≤ y} μ(d) μ(e) √(gcd d e) / √(d e)`.

Results, all for every `y`:

* (a) `sqrt_eq_sum_J`, `sqrt_gcd_eq_sum_J`: `√n = Σ_{m ∣ n} J m` (Möbius inversion), hence
  `√(gcd d e) = Σ_{m ∣ gcd d e} J m`.
* (b) `mode_decomposition`: `F y = Σ_{m ≤ y} J m (T y m)²`.
* (c) `T_one`: `T y 1 = GppMobiusEcho.S y`.
* (d) `J_prime`: `J p = √p − 1`; `J_one`; `J_nonneg`: `0 ≤ J m` for **every** `m`, not only squarefree
  `m` (checked at `m = p²`: `J(p²) = p − √p`, and in general `J(p^k) = p^{k/2} − p^{(k−1)/2}`);
  `T_eq_zero_of_not_squarefree`: `T y m = 0` unless `m` is squarefree.
* (e) `S_sq_le_F`: `(GppMobiusEcho.S y)² ≤ F y`, from (b), (c) and (d).

**What (e) does and does not give.** The bound `S² ≤ F` is lossy. Numerically (a Python check of the
identity and of the constant for `y ≤ 1600`; the full-range check is a separate discovery job, not
part of this file) `F(y)/√y ≈ 0.39` while `S(y)²` stays of order one, so positivity of the modes loses
about `√y`. Even `F ≪ y^{1/2+ε}` would give only `S(y) ≪ y^{1/4+ε}`, hence by partial summation
`M(x) ≪ x^{3/4+ε}`, which is not known. The proof of (a) and (b) uses only Möbius inversion of
`√` along divisibility, so the same identity holds for Beurling generalized integers, and it cannot by
itself force RH. No `sorry`, no `axiom`.
-/

open Finset ArithmeticFunction

namespace GppMobiusModes

/-- `J m = Σ_{k ∣ m} μ(m/k) √k`. -/
noncomputable def J (m : ℕ) : ℝ :=
  ∑ k ∈ m.divisors, (moebius (m / k) : ℝ) * Real.sqrt k

/-- `T y m = Σ_{d ∈ [1,y], m ∣ d} μ(d)/√d`. -/
noncomputable def T (y m : ℕ) : ℝ :=
  ∑ d ∈ (Icc 1 y).filter (fun d => m ∣ d), (moebius d : ℝ) / Real.sqrt d

/-- `F y = Σ_{d,e ∈ [1,y]} μ(d) μ(e) √(gcd d e) / √(d e)`. -/
noncomputable def F (y : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 y, ∑ e ∈ Icc 1 y,
    (moebius d : ℝ) * (moebius e : ℝ) * Real.sqrt (Nat.gcd d e) / Real.sqrt ((d * e : ℕ) : ℝ)

/-- The real square root as an arithmetic function (completely multiplicative). -/
noncomputable def sqrtFn : ArithmeticFunction ℝ :=
  ⟨fun n => Real.sqrt n, by simp⟩

@[simp] theorem sqrtFn_apply (n : ℕ) : sqrtFn n = Real.sqrt n := rfl

theorem sqrtFn_isMultiplicative : sqrtFn.IsMultiplicative := by
  refine ⟨by simp, fun {m n} _ => ?_⟩
  simp only [sqrtFn_apply]
  push_cast
  exact Real.sqrt_mul (Nat.cast_nonneg m) n

/-- `J` as a Dirichlet convolution. -/
theorem J_eq_convolution (m : ℕ) :
    J m = (((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) * sqrtFn) m := by
  rw [ArithmeticFunction.mul_apply, J]
  rw [Nat.sum_divisorsAntidiagonal' (fun x y => (((moebius : ArithmeticFunction ℤ) :
    ArithmeticFunction ℝ) x) * sqrtFn y)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [ArithmeticFunction.intCoe_apply]

theorem J_isMultiplicative : (((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) *
    sqrtFn).IsMultiplicative :=
  (isMultiplicative_moebius.intCast).mul sqrtFn_isMultiplicative

/-- (a) Möbius inversion: `√n = Σ_{m ∣ n} J m` for `n ≥ 1`. -/
theorem sqrt_eq_sum_J {n : ℕ} (hn : 0 < n) : Real.sqrt n = ∑ m ∈ n.divisors, J m := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℝ)
    (f := fun m => J m) (g := fun n => Real.sqrt n)).2 ?_ n hn
  · exact h.symm
  · intro m hm
    rw [J, Nat.sum_divisorsAntidiagonal' (fun x y => (moebius x : ℝ) * Real.sqrt y)]

/-- (a), gcd form: `√(gcd d e) = Σ_{m ∣ gcd d e} J m` for `d, e ≥ 1`. -/
theorem sqrt_gcd_eq_sum_J {d e : ℕ} (hd : 0 < d) (_he : 0 < e) :
    Real.sqrt (Nat.gcd d e) = ∑ m ∈ (Nat.gcd d e).divisors, J m :=
  sqrt_eq_sum_J (Nat.gcd_pos_of_pos_left e hd)

/-- The summand of `T`, written with an indicator. -/
noncomputable def A (m d : ℕ) : ℝ := if m ∣ d then (moebius d : ℝ) / Real.sqrt d else 0

theorem T_eq_sum_A (y m : ℕ) : T y m = ∑ d ∈ Icc 1 y, A m d := by
  rw [T, Finset.sum_filter]
  rfl

theorem term_eq_sum_J {y d e : ℕ} (hd : d ∈ Icc 1 y) (he : e ∈ Icc 1 y) :
    (moebius d : ℝ) * (moebius e : ℝ) * Real.sqrt (Nat.gcd d e) / Real.sqrt ((d * e : ℕ) : ℝ) =
      ∑ m ∈ Icc 1 y, J m * (A m d * A m e) := by
  rw [Finset.mem_Icc] at hd he
  have hd0 : 0 < d := hd.1
  have he0 : 0 < e := he.1
  have hset : (Nat.gcd d e).divisors = (Icc 1 y).filter (fun m => m ∣ d ∧ m ∣ e) := by
    ext m
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨h, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos h.1 hd0, (Nat.le_of_dvd hd0 h.1).trans hd.2⟩, h⟩
    · rintro ⟨_, h⟩
      exact ⟨h, (Nat.gcd_pos_of_pos_left e hd0).ne'⟩
  have hsum : ∑ m ∈ Icc 1 y, J m * (A m d * A m e) =
      (∑ m ∈ (Nat.gcd d e).divisors, J m) * ((moebius d : ℝ) / Real.sqrt d *
        ((moebius e : ℝ) / Real.sqrt e)) := by
    rw [hset, Finset.sum_mul, Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases h1 : m ∣ d <;> by_cases h2 : m ∣ e <;> simp [A, h1, h2]
  rw [hsum, ← sqrt_gcd_eq_sum_J hd0 he0, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg d)]
  ring

/-- (b) The mode decomposition: `F y = Σ_{m ≤ y} J m (T y m)²`. -/
theorem mode_decomposition (y : ℕ) : F y = ∑ m ∈ Icc 1 y, J m * (T y m) ^ 2 := by
  calc F y = ∑ d ∈ Icc 1 y, ∑ e ∈ Icc 1 y, ∑ m ∈ Icc 1 y, J m * (A m d * A m e) := by
        unfold F
        exact Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun e he =>
          term_eq_sum_J hd he
    _ = ∑ m ∈ Icc 1 y, ∑ d ∈ Icc 1 y, ∑ e ∈ Icc 1 y, J m * (A m d * A m e) := by
        calc _ = ∑ d ∈ Icc 1 y, ∑ m ∈ Icc 1 y, ∑ e ∈ Icc 1 y, J m * (A m d * A m e) :=
              Finset.sum_congr rfl fun d _ => Finset.sum_comm
          _ = _ := Finset.sum_comm
    _ = ∑ m ∈ Icc 1 y, J m * (T y m) ^ 2 := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [T_eq_sum_A, sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum]

/-- (c) `T y 1 = S y`. -/
theorem T_one (y : ℕ) : T y 1 = GppMobiusEcho.S y := by
  simp [T, GppMobiusEcho.S, GppMobiusEcho.a]

theorem J_one : J 1 = 1 := by simp [J]

theorem J_zero : J 0 = 0 := by simp [J]

/-- (d) `J p = √p − 1` for a prime `p`. -/
theorem J_prime {p : ℕ} (hp : p.Prime) : J p = Real.sqrt p - 1 := by
  have h1 : (1 : ℕ) ≠ p := hp.one_lt.ne
  rw [J, hp.divisors, Finset.sum_pair h1]
  simp [moebius_apply_prime hp, Nat.div_self hp.pos]
  ring

theorem J_prime_pow_nonneg {p : ℕ} (hp : p.Prime) (k : ℕ) : 0 ≤ J (p ^ k) := by
  have key : ∀ n : ℕ, Real.sqrt ((p ^ n : ℕ) : ℝ) = ∑ i ∈ Finset.range (n + 1), J (p ^ i) := by
    intro n
    rw [sqrt_eq_sum_J (pow_pos hp.pos n), Nat.sum_divisors_prime_pow hp]
  cases k with
  | zero => simp [J_one]
  | succ k =>
    have h := key (k + 1)
    rw [Finset.sum_range_succ, ← key k] at h
    have hle : Real.sqrt ((p ^ k : ℕ) : ℝ) ≤ Real.sqrt ((p ^ (k + 1) : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.pow_le_pow_right hp.pos (Nat.le_succ k))
    linarith

/-- (d) `J m ≥ 0` for every `m` (not only squarefree `m`). -/
theorem J_nonneg (m : ℕ) : 0 ≤ J m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [J_zero]
  · rw [J_eq_convolution, J_isMultiplicative.multiplicative_factorization _ hm.ne']
    refine Finset.prod_nonneg fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
    simpa only [J_eq_convolution] using J_prime_pow_nonneg hpp (m.factorization p)

/-- (d) `T y m = 0` unless `m` is squarefree. -/
theorem T_eq_zero_of_not_squarefree (y : ℕ) {m : ℕ} (hm : ¬ Squarefree m) : T y m = 0 := by
  unfold T
  refine Finset.sum_eq_zero fun d hd => ?_
  have hdm : m ∣ d := (Finset.mem_filter.1 hd).2
  have hd' : ¬ Squarefree d := fun h => hm (h.squarefree_of_dvd hdm)
  simp [moebius_eq_zero_of_not_squarefree hd']

/-- (e) `S(y)² ≤ F(y)`, from the mode decomposition, `T y 1 = S y` and `J ≥ 0`. -/
theorem S_sq_le_F (y : ℕ) : (GppMobiusEcho.S y) ^ 2 ≤ F y := by
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp [F, GppMobiusEcho.S]
  · rw [mode_decomposition]
    have h := Finset.single_le_sum (f := fun m => J m * (T y m) ^ 2)
      (fun m _ => mul_nonneg (J_nonneg m) (sq_nonneg _)) (Finset.mem_Icc.2 ⟨le_refl 1, hy⟩)
    simpa [J_one, T_one] using h

end GppMobiusModes

#print axioms GppMobiusModes.sqrt_eq_sum_J
#print axioms GppMobiusModes.sqrt_gcd_eq_sum_J
#print axioms GppMobiusModes.mode_decomposition
#print axioms GppMobiusModes.T_one
#print axioms GppMobiusModes.J_prime
#print axioms GppMobiusModes.J_nonneg
#print axioms GppMobiusModes.T_eq_zero_of_not_squarefree
#print axioms GppMobiusModes.S_sq_le_F
