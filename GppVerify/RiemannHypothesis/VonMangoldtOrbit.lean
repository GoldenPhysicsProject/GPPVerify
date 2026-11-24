import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The von Mangoldt dilation orbit of `{1/x}` and the prime factorial

Companion of `MoebiusBoundaryDatum`.  With `Λ` the von Mangoldt function (supported on prime
powers) and `χ(x) = {1/x}`, the orbit `L_N(x) = Σ_{k ≤ N} Λ(k) {1/(k x)}` is the truncation of
`-ζ'/ζ`, the logarithmic derivative of the Euler product, applied to the dilation generator on
`χ`.  The exact identity on the region `x ≥ 1/N` is

  `L_N(x) = x⁻¹ · Σ_{k ≤ N} Λ(k)/k  -  log ⌊1/x⌋!`                    (`orbit_exact`),

which is Legendre's factorization of `n!` into prime powers read at scale `1/x`:

  `Σ_{k ≤ n} Λ(k) ⌊n/k⌋ = log n!`                                       (`vonMangoldt_floor_nat`).

Primes enter through `Λ` and nothing else; no zero of `ζ` is used.  The two constants that the
explicit formula pairs with the prime sum, the Euler constant in `Σ_{k ≤ N} Λ(k)/k = log N - γ +
o(1)` and the Stirling term `½ log (2π n)` in `log n!`, are the archimedean data of the doubled
picture.
-/

open ArithmeticFunction Finset

namespace GppVonMangoldtOrbit

/-- `Σ_{m ≤ n} log m`, the logarithm of `n!`. -/
noncomputable def logFact (n : ℕ) : ℝ := ∑ m ∈ Ioc 0 n, Real.log m

theorem logFact_eq (n : ℕ) : logFact n = Real.log (n.factorial : ℝ) := by
  induction n with
  | zero => simp [logFact]
  | succ n ih =>
    rw [logFact, Finset.sum_Ioc_succ_top (Nat.zero_le n), ← logFact, ih, Nat.factorial_succ]
    push_cast
    rw [Real.log_mul (by positivity) (by exact_mod_cast (Nat.factorial_pos n).ne'), add_comm]

/-- **Chebyshev–Legendre.** `Σ_{k ≤ n} Λ(k) ⌊n/k⌋ = log n!`. -/
theorem vonMangoldt_floor_nat (n : ℕ) :
    ∑ k ∈ Ioc 0 n, vonMangoldt k * ((n / k : ℕ) : ℝ) = logFact n := by
  have h := sum_Ioc_mul_zeta_eq_sum (vonMangoldt : ArithmeticFunction ℝ) n
  rw [vonMangoldt_mul_zeta] at h
  rw [← h]
  unfold logFact
  refine sum_congr rfl (fun m hm => ?_)
  simp [ArithmeticFunction.log_apply]

/-- The prime sum `Σ_{k ≤ N} Λ(k)/k`. -/
noncomputable def lamSum (N : ℕ) : ℝ := ∑ k ∈ Ioc 0 N, vonMangoldt k / k

/-- The von Mangoldt dilation orbit `L_N(x) = Σ_{k ≤ N} Λ(k) {1/(k x)}` of the profile `{1/x}`. -/
noncomputable def orbit (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Ioc 0 N, vonMangoldt k * Int.fract (1 / ((k : ℝ) * x))

/-- Real form: for `y ≥ 0` and `⌊y⌋ ≤ N`, `Σ_{k ≤ N} Λ(k) ⌊y/k⌋ = log ⌊y⌋!`. -/
theorem vonMangoldt_floor_real {y : ℝ} (hy : 0 ≤ y) {N : ℕ} (hN : ⌊y⌋₊ ≤ N) :
    ∑ k ∈ Ioc 0 N, vonMangoldt k * (⌊y / (k : ℝ)⌋ : ℝ) = logFact ⌊y⌋₊ := by
  have key : ∀ k ∈ Ioc 0 N, (⌊y / (k : ℝ)⌋ : ℤ) = ((⌊y⌋₊ / k : ℕ) : ℤ) := by
    intro k hk
    have hnn : 0 ≤ y / (k : ℝ) := by positivity
    rw [← Int.natCast_floor_eq_floor hnn, Nat.floor_div_natCast]
  have h1 : ∑ k ∈ Ioc 0 N, vonMangoldt k * (⌊y / (k : ℝ)⌋ : ℝ) =
      ∑ k ∈ Ioc 0 N, vonMangoldt k * (((⌊y⌋₊ / k : ℕ) : ℤ) : ℝ) := by
    refine sum_congr rfl (fun k hk => ?_)
    rw [key k hk]
  rw [h1]
  have h2 : ∑ k ∈ Ioc 0 N, vonMangoldt k * (((⌊y⌋₊ / k : ℕ) : ℤ) : ℝ) =
      ∑ k ∈ Ioc 0 ⌊y⌋₊, vonMangoldt k * (((⌊y⌋₊ / k : ℕ) : ℤ) : ℝ) := by
    symm
    refine sum_subset (Ioc_subset_Ioc_right hN) (fun k hk hk' => ?_)
    have : ⌊y⌋₊ < k := by
      simp only [mem_Ioc, not_and, not_le] at hk'
      exact hk' (mem_Ioc.1 hk).1
    simp [Nat.div_eq_of_lt this]
  rw [h2]
  have h3 := vonMangoldt_floor_nat ⌊y⌋₊
  simp only [Int.cast_natCast]
  exact h3

/-- **The exact von Mangoldt orbit.** For `0 < x ≤ 1` and `1/x ≤ N`:
`L_N(x) = x⁻¹ · Σ_{k ≤ N} Λ(k)/k - log ⌊1/x⌋!`. -/
theorem orbit_exact {x : ℝ} (hx0 : 0 < x) {N : ℕ} (hN : 1 / x ≤ N) :
    orbit N x = (1 / x) * lamSum N - logFact ⌊1 / x⌋₊ := by
  have hy : 0 ≤ 1 / x := by positivity
  have hfl : ⌊1 / x⌋₊ ≤ N := Nat.floor_le_of_le hN
  have hF := vonMangoldt_floor_real hy hfl
  unfold orbit lamSum
  have hterm : ∀ k ∈ Ioc 0 N, vonMangoldt k * Int.fract (1 / ((k : ℝ) * x)) =
      (1 / x) * (vonMangoldt k / k) - vonMangoldt k * (⌊1 / x / (k : ℝ)⌋ : ℝ) := by
    intro k hk
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (mem_Ioc.1 hk).1.ne'
    rw [Int.fract]
    have : 1 / ((k : ℝ) * x) = 1 / x / (k : ℝ) := by field_simp
    rw [this]
    field_simp
  rw [sum_congr rfl hterm, sum_sub_distrib, hF, ← mul_sum]

end GppVonMangoldtOrbit

#print axioms GppVonMangoldtOrbit.logFact_eq
#print axioms GppVonMangoldtOrbit.vonMangoldt_floor_nat
#print axioms GppVonMangoldtOrbit.orbit_exact
