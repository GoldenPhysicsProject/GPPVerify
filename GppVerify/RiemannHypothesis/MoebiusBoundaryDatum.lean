import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Floor.Ring

/-!
# The Möbius dilation orbit of `{1/x}` and the boundary datum at `x → 0`

Let `χ(x) = {1/x}` and `(U_k χ)(x) = χ(k x) = {1/(k x)}`.  The Möbius-weighted dilation orbit
`S_N(x) = -Σ_{k ≤ N} μ(k) {1/(k x)}` is the truncation of the Dirichlet inverse `1/ζ` applied to
the dilation generator.  This module proves its exact form on the region `x ≥ 1/N`:

  `S_N(x) = 1 - M_N · x⁻¹`,   `M_N = Σ_{k ≤ N} μ(k)/k`        (`orbit_exact`).

In the logarithmic variable `t = log x` this is the pair of exponentials `e^{0·t}` and `e^{-t}`,
the states `x^{ρ-1}` at `ρ = 1` and `ρ = 0`, which are exchanged by the shadow `ρ ↔ 1 - ρ`.
The coefficient of the second state is the Mertens-type sum `M_N`.

* `moebius_floor_nat`: `Σ_{k ≤ n} μ(k) ⌊n/k⌋ = 1` for `n ≥ 1`, from `μ * ζ = 1`.
* `orbit_exact`: the closed form above, for `0 < x ≤ 1` and `1/x ≤ N`.
* `orbit_tendsto_iff`: at each fixed `x ∈ (0,1]`, `S_N(x) → 1` iff `M_N → 0`.
* `l2_defect`: the `L²` defect of `S_N` against `1` on `[1/N, 1]` is exactly `M_N² (N - 1)`.

The Euler content is the choice of coefficients: `μ` is the Dirichlet inverse of the all-ones
function, the coefficient sequence of `ζ`.  The same orbit built from another Dirichlet series
has a different closed form.
-/

open ArithmeticFunction Finset MeasureTheory Filter Topology
open scoped ArithmeticFunction.Moebius

namespace GppMoebiusBoundary

/-- **Möbius–floor identity.** For `n ≥ 1`, `Σ_{k = 1}^n μ(k) ⌊n/k⌋ = 1`. -/
theorem moebius_floor_nat {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Ioc 0 n, (μ k : ℤ) * ((n / k : ℕ) : ℤ) = 1 := by
  have h := sum_Ioc_mul_zeta_eq_sum (μ : ArithmeticFunction ℤ) n
  rw [moebius_mul_coe_zeta] at h
  rw [← h]
  simp only [ArithmeticFunction.one_apply]
  rw [Finset.sum_ite_eq' (Ioc 0 n) 1]
  simp [hn]

/-- The Mertens-type sum `M_N = Σ_{k ≤ N} μ(k)/k`. -/
noncomputable def mertens (N : ℕ) : ℝ := ∑ k ∈ Ioc 0 N, (μ k : ℝ) / k

/-- The Möbius dilation orbit `S_N(x) = -Σ_{k ≤ N} μ(k) {1/(k x)}` of the profile `{1/x}`. -/
noncomputable def orbit (N : ℕ) (x : ℝ) : ℝ :=
  -∑ k ∈ Ioc 0 N, (μ k : ℝ) * Int.fract (1 / ((k : ℝ) * x))

/-- Real form of the Möbius–floor identity: for `y ≥ 1` and `⌊y⌋ ≤ N`,
`Σ_{k ≤ N} μ(k) ⌊y/k⌋ = 1`. -/
theorem moebius_floor_real {y : ℝ} (hy : 1 ≤ y) {N : ℕ} (hN : ⌊y⌋₊ ≤ N) :
    ∑ k ∈ Ioc 0 N, (μ k : ℝ) * (⌊y / (k : ℝ)⌋ : ℝ) = 1 := by
  have hn : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by simpa using hy)
  have key : ∀ k ∈ Ioc 0 N, (⌊y / (k : ℝ)⌋ : ℤ) = ((⌊y⌋₊ / k : ℕ) : ℤ) := by
    intro k hk
    have hk0 : 0 < k := (mem_Ioc.1 hk).1
    have hnn : 0 ≤ y / (k : ℝ) := by positivity
    rw [← Int.natCast_floor_eq_floor hnn, Nat.floor_div_natCast]
  have h1 : ∑ k ∈ Ioc 0 N, (μ k : ℝ) * (⌊y / (k : ℝ)⌋ : ℝ) =
      ∑ k ∈ Ioc 0 N, (μ k : ℝ) * (((⌊y⌋₊ / k : ℕ) : ℤ) : ℝ) := by
    refine sum_congr rfl (fun k hk => ?_)
    rw [key k hk]
  rw [h1]
  have h2 : ∑ k ∈ Ioc 0 N, (μ k : ℝ) * (((⌊y⌋₊ / k : ℕ) : ℤ) : ℝ) =
      ∑ k ∈ Ioc 0 ⌊y⌋₊, (μ k : ℝ) * (((⌊y⌋₊ / k : ℕ) : ℤ) : ℝ) := by
    symm
    refine sum_subset (Ioc_subset_Ioc_right hN) (fun k hk hk' => ?_)
    have : ⌊y⌋₊ < k := by
      simp only [mem_Ioc, not_and, not_le] at hk'
      exact hk' (mem_Ioc.1 hk).1
    simp [Nat.div_eq_of_lt this]
  rw [h2]
  have h3 := moebius_floor_nat hn
  exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h3

/-- **The exact orbit.** For `0 < x ≤ 1` and `1/x ≤ N`: `S_N(x) = 1 - M_N / x`. -/
theorem orbit_exact {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) {N : ℕ} (hN : 1 / x ≤ N) :
    orbit N x = 1 - mertens N / x := by
  have hy : 1 ≤ 1 / x := by rw [le_div_iff₀ hx0]; linarith
  have hfl : ⌊1 / x⌋₊ ≤ N := Nat.floor_le_of_le hN
  have hF := moebius_floor_real hy hfl
  unfold orbit mertens
  have hterm : ∀ k ∈ Ioc 0 N, (μ k : ℝ) * Int.fract (1 / ((k : ℝ) * x)) =
      (1 / x) * ((μ k : ℝ) / k) - (μ k : ℝ) * (⌊1 / x / (k : ℝ)⌋ : ℝ) := by
    intro k hk
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (mem_Ioc.1 hk).1.ne'
    rw [Int.fract]
    have : 1 / ((k : ℝ) * x) = 1 / x / (k : ℝ) := by field_simp
    rw [this]
    field_simp
  rw [sum_congr rfl hterm, sum_sub_distrib, hF, ← mul_sum]
  field_simp
  ring

/-- **Pointwise limit.** At each `x ∈ (0, 1]`, the orbit converges to the pole state `1` exactly
when the Mertens-type sum `M_N` tends to `0`. -/
theorem orbit_tendsto_iff {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    Tendsto (fun N : ℕ => orbit N x) atTop (𝓝 1) ↔ Tendsto mertens atTop (𝓝 0) := by
  have hev : ∀ᶠ N : ℕ in atTop, orbit N x = 1 - mertens N / x := by
    filter_upwards [eventually_ge_atTop ⌈1 / x⌉₊] with N hN
    exact orbit_exact hx0 hx1 ((Nat.le_ceil _).trans (by exact_mod_cast hN))
  constructor
  · intro h
    have h2 : Tendsto (fun N : ℕ => x * (1 - orbit N x)) atTop (𝓝 (x * (1 - 1))) :=
      (tendsto_const_nhds.sub h).const_mul x
    simp only [sub_self, mul_zero] at h2
    refine h2.congr' ?_
    filter_upwards [hev] with N hN
    rw [hN]; field_simp; ring
  · intro h
    have h2 : Tendsto (fun N : ℕ => 1 - mertens N / x) atTop (𝓝 (1 - 0 / x)) :=
      tendsto_const_nhds.sub (h.div_const x)
    simp only [zero_div, sub_zero] at h2
    exact h2.congr' (by filter_upwards [hev] with N hN; rw [hN])

/-- **The `L²` defect on `[1/N, 1]` is exact.** `∫_{1/N}^1 (S_N(x) - 1)² dx = M_N² (N - 1)`. -/
theorem l2_defect {N : ℕ} (hN : 1 ≤ N) :
    ∫ x in (1 / (N : ℝ))..1, (orbit N x - 1) ^ 2 = mertens N ^ 2 * ((N : ℝ) - 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : (1 / (N : ℝ)) ≤ 1 := by rw [div_le_one hN0]; exact_mod_cast hN
  have hcongr : ∫ x in (1 / (N : ℝ))..1, (orbit N x - 1) ^ 2 =
      ∫ x in (1 / (N : ℝ))..1, mertens N ^ 2 * x ^ (-2 : ℤ) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le hle] at hx
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx.1
    have hxN : 1 / x ≤ N := by
      rw [div_le_iff₀ hx0]
      have := hx.1
      rw [div_le_iff₀ hN0] at this
      linarith
    show (orbit N x - 1) ^ 2 = mertens N ^ 2 * x ^ (-2 : ℤ)
    rw [orbit_exact hx0 hx.2 hxN]
    have hx0' : x ≠ 0 := hx0.ne'
    have : (1 - mertens N / x - 1) ^ 2 = mertens N ^ 2 * (x ^ 2)⁻¹ := by
      field_simp
      ring
    rw [this]
    simp [zpow_neg]
  rw [hcongr, intervalIntegral.integral_const_mul, integral_zpow]
  · have : (1 / (N : ℝ)) ^ (-2 + 1 : ℤ) = (N : ℝ) := by
      rw [show (-2 + 1 : ℤ) = -1 by norm_num, zpow_neg, zpow_one, one_div, inv_inv]
    rw [this, one_zpow]
    congr 1
    norm_num
    ring
  · right
    refine ⟨by norm_num, ?_⟩
    rw [Set.uIcc_of_le hle]
    intro h
    exact absurd h.1 (not_le.2 (by positivity))

end GppMoebiusBoundary

#print axioms GppMoebiusBoundary.moebius_floor_nat
#print axioms GppMoebiusBoundary.orbit_exact
#print axioms GppMoebiusBoundary.orbit_tendsto_iff
#print axioms GppMoebiusBoundary.l2_defect
