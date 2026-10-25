import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-!
# Legendre's sieve for rough integers: the count is `c t + O(1)`

Source: Codex, `work/codex/2026-10-25_rough_source_pole_subtraction_tempered_escape.md` (PR #11
comment 6394699459), the inclusion–exclusion step `A_y(t) − c_y t = O_y(1)`. Daniel Toupin /
Golden Physics Project, with AI assistance from Codex (statement) and Claude Code (formalization).

For a modulus `P ≥ 1` let `A_P(N) = #{1 ≤ n ≤ N : gcd(n, P) = 1}`. With `P = ∏_{p ≤ y} p` these
are Codex's `y`-rough integers, those with no prime factor `≤ y`.

* `sum_moebius_divisors`: `Σ_{d ∣ m} μ(d) = [m = 1]` for `m ≥ 1`.
* `legendre`: `A_P(N) = Σ_{d ∣ P} μ(d) ⌊N/d⌋`.
* `abs_count_sub_le`: `|A_P(N) − c_P N| ≤ τ(P)` with `c_P = Σ_{d ∣ P} μ(d)/d` and `τ(P)` the
  number of divisors. This is `A_y(t) − c_y t = O_y(1)` with the explicit constant `τ(P) = 2^{π(y)}`
  for the primorial.

**Scope.** `c_P = Σ_{d∣P} μ(d)/d` is the inclusion–exclusion form; its equality with
`∏_{p ∣ P}(1 − 1/p) = φ(P)/P` is classical and not restated here. The Laplace reconstruction
`R_y(s) − c_y/(s − 1) = s∫ e^{−sx} B_y(x) dx`, the tempered-escape no-go (which needs Mertens'
theorem `c_y ~ e^{−γ}/log y`), and real `t` in place of integer `N` are not formalized. No claim about
RH.
-/

set_option autoImplicit false

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace GppRoughSieve

/-- `A_P(N) = #{1 ≤ n ≤ N : gcd(n, P) = 1}`. -/
def A (P N : ℕ) : ℕ := #{n ∈ Ioc 0 N | Nat.Coprime n P}

/-- `Σ_{d ∣ m} μ(d) = [m = 1]`. -/
theorem sum_moebius_divisors (m : ℕ) :
    ∑ d ∈ m.divisors, (μ d : ℤ) = if m = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f m) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply] at h
  rw [h, one_apply]

lemma divisors_gcd {n P : ℕ} (hP : P ≠ 0) :
    (Nat.gcd n P).divisors = P.divisors.filter (· ∣ n) := by
  ext d
  have hg : Nat.gcd n P ≠ 0 := Nat.gcd_ne_zero_right hP
  simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨⟨h2, hP⟩, h1⟩
  · rintro ⟨⟨h2, -⟩, h1⟩; exact ⟨⟨h1, h2⟩, hg⟩

/-- **Legendre's identity.** `A_P(N) = Σ_{d ∣ P} μ(d) ⌊N/d⌋`. -/
theorem legendre {P : ℕ} (hP : P ≠ 0) (N : ℕ) :
    (A P N : ℤ) = ∑ d ∈ P.divisors, (μ d : ℤ) * ((N / d : ℕ) : ℤ) := by
  have h1 : (A P N : ℤ) = ∑ n ∈ Ioc 0 N, if Nat.Coprime n P then (1 : ℤ) else 0 := by
    rw [A, card_filter]; push_cast; rfl
  have h2 : ∀ n ∈ Ioc 0 N, (if Nat.Coprime n P then (1 : ℤ) else 0) =
      ∑ d ∈ P.divisors, if d ∣ n then (μ d : ℤ) else 0 := by
    intro n _
    rw [← sum_filter, ← divisors_gcd hP, sum_moebius_divisors]
  rw [h1, sum_congr rfl h2, sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [← sum_filter, sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul, mul_comm]

/-- The inclusion–exclusion density `c_P = Σ_{d ∣ P} μ(d)/d`. -/
noncomputable def c (P : ℕ) : ℝ := ∑ d ∈ P.divisors, (μ d : ℝ) / d

/-- **`A_P(N) = c_P N + O(τ(P))`.** -/
theorem abs_count_sub_le {P : ℕ} (hP : P ≠ 0) (N : ℕ) :
    |(A P N : ℝ) - c P * N| ≤ P.divisors.card := by
  have hA : (A P N : ℝ) = ∑ d ∈ P.divisors, (μ d : ℝ) * ((N / d : ℕ) : ℝ) := by
    have := congrArg (Int.cast : ℤ → ℝ) (legendre hP N)
    push_cast at this
    exact this
  have hdiff : (A P N : ℝ) - c P * N =
      ∑ d ∈ P.divisors, (μ d : ℝ) * (((N / d : ℕ) : ℝ) - (N : ℝ) / d) := by
    rw [hA, c, sum_mul, ← sum_sub_distrib]
    refine sum_congr rfl fun d _ => ?_
    ring
  rw [hdiff]
  calc |∑ d ∈ P.divisors, (μ d : ℝ) * (((N / d : ℕ) : ℝ) - (N : ℝ) / d)|
      ≤ ∑ d ∈ P.divisors, |(μ d : ℝ) * (((N / d : ℕ) : ℝ) - (N : ℝ) / d)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ P.divisors, (1 : ℝ) := by
        refine sum_le_sum fun d hd => ?_
        have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
        have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
        have hmu : |(μ d : ℝ)| ≤ 1 := by
          have := abs_moebius_le_one (n := d)
          exact_mod_cast this
        have hfl : |((N / d : ℕ) : ℝ) - (N : ℝ) / d| ≤ 1 := by
          have hdiv := Nat.div_add_mod N d
          have hmod := Nat.mod_lt N hd0
          have hN : (N : ℝ) = d * ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) := by
            exact_mod_cast hdiv.symm
          have hm0 : (0 : ℝ) ≤ ((N % d : ℕ) : ℝ) := by positivity
          have hm1 : ((N % d : ℕ) : ℝ) < d := by exact_mod_cast hmod
          have : ((N / d : ℕ) : ℝ) - (N : ℝ) / d = -(((N % d : ℕ) : ℝ) / d) := by
            rw [hN]; field_simp; ring
          rw [this, abs_neg, abs_of_nonneg (by positivity)]
          rw [div_le_one hdR]; exact hm1.le
        rw [abs_mul]
        calc |(μ d : ℝ)| * |((N / d : ℕ) : ℝ) - (N : ℝ) / d| ≤ 1 * 1 :=
            mul_le_mul hmu hfl (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    _ = P.divisors.card := by simp

end GppRoughSieve
