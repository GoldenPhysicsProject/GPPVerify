import GppVerify.NumberTheory.EulerSumCapstone
import Mathlib.NumberTheory.Harmonic.Defs

/-!
# Euler's second sum `Σₙ Hₙ/n³ = π⁴/72` (retires `GppEulerSum.open_euler_sum_two_gap`)

The capstone file proved the first Euler sum by the swap symmetry of `1/(m²n²)` and parked the
second, on the ground that its summand `(1/m)(1/n³)` is not swap-symmetric. The swap trick does
apply after one change of summand. With `f(m,n) = 1/(m² n (m+n))`:

* **Swap:** `f(m,n) + f(n,m) = (m+n)/(m²n²(m+n)) = 1/(m²n²)` (`f_add_f_swap`), so
  `2 Σ f = ζ(2)²` and `Σ f = π⁴/72` (`tsum_f`).
* **Rows:** `f(m,n) = (1/m³)(1/n − 1/(n+m))`, and `Σ_{n≥1} (1/n − 1/(n+m)) = H_m` by
  telescoping (`hasSum_inner_shift`), so the row sums are `H_m/m³` (`tsum_inner`).

Hence `Σ_m H_m/m³ = π⁴/72 = (5/4)ζ(4)` (`hasSum_harmonic_div_cube`). In multiple-zeta language
this is `ζ(3,1) + ζ(4) = ζ(2)²/2`, i.e. Euler's `ζ(3,1) = π⁴/360`. With the first sum the
paper's assembly `π⁴/120 + π⁴/72 = 2ζ(4)` follows (`euler_sums_assemble`). Absolute convergence
throughout: `0 ≤ f ≤ 1/(m²n²)`.

Daniel Toupin / Golden Physics Project, with AI assistance from Claude Code.
-/

namespace GppEulerSumTwo

open Real GppEulerSum Filter Topology Finset

/-- `f(m,n) = 1/(m² n (m+n))` (zero when `m = 0` or `n = 0`, by Lean's `1/0 = 0`). -/
noncomputable def f (p : ℕ × ℕ) : ℝ := 1 / ((p.1 : ℝ) ^ 2 * p.2 * (p.1 + p.2))

theorem f_nonneg (p : ℕ × ℕ) : 0 ≤ f p := by unfold f; positivity

theorem f_le_term (p : ℕ × ℕ) : f p ≤ term p := by
  obtain ⟨m, n⟩ := p
  unfold f term
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only
  rw [div_mul_div_comm, one_mul]
  apply one_div_le_one_div_of_le (by positivity)
  have : (n : ℝ) ^ 2 ≤ n * (m + n) := by nlinarith
  calc (m : ℝ) ^ 2 * n ^ 2 ≤ (m : ℝ) ^ 2 * (n * (m + n)) := by gcongr
    _ = (m : ℝ) ^ 2 * n * (m + n) := by ring

theorem summable_f : Summable f :=
  Summable.of_nonneg_of_le f_nonneg f_le_term summable_term

/-- `f(m,n) + f(n,m) = 1/(m²n²)`. -/
theorem f_add_f_swap (p : ℕ × ℕ) : f p + f p.swap = term p := by
  obtain ⟨m, n⟩ := p
  unfold f term
  simp only [Prod.swap]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hmn : (m : ℝ) + n ≠ 0 := by positivity
  have hnm : (n : ℝ) + m ≠ 0 := by positivity
  field_simp
  ring

theorem tsum_f : ∑' p, f p = Real.pi ^ 4 / 72 := by
  have hswap : ∑' p : ℕ × ℕ, f p.swap = ∑' p, f p := (Equiv.prodComm ℕ ℕ).tsum_eq f
  have hs2 : Summable (fun p : ℕ × ℕ => f p.swap) := by
    simpa [Function.comp_def] using (Equiv.prodComm ℕ ℕ).summable_iff.mpr summable_f
  have h := summable_f.tsum_add hs2
  rw [hswap] at h
  simp_rw [f_add_f_swap] at h
  rw [tsum_term_eq] at h
  linarith

/-- `a m n = Σ_{k<m} 1/(n+1+k)`, so `a m 0 = H_m` and `a m n − a m (n+1) = 1/(n+1) − 1/(n+1+m)`. -/
noncomputable def a (m n : ℕ) : ℝ := ∑ k ∈ range m, 1 / ((n : ℝ) + 1 + k)

theorem a_zero (m : ℕ) : a m 0 = harmonic m := by
  rw [a, harmonic]
  push_cast
  refine sum_congr rfl fun k _ => ?_
  rw [one_div]; congr 1; ring

theorem a_sub (m n : ℕ) : a m n - a m (n + 1) = 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1 + m) := by
  set g : ℕ → ℝ := fun k => 1 / ((n : ℝ) + 1 + k) with hg
  have h1 : a m n = ∑ k ∈ range m, g k := rfl
  have h2 : a m (n + 1) = ∑ k ∈ range m, g (k + 1) := by
    unfold a
    refine sum_congr rfl fun k _ => ?_
    simp only [hg]
    push_cast
    ring_nf
  rw [h1, h2, ← sum_sub_distrib, sum_range_sub']
  simp [hg]

theorem tendsto_a (m : ℕ) : Tendsto (fun n => a m n) atTop (𝓝 0) := by
  unfold a
  rw [show (0 : ℝ) = ∑ k ∈ range m, (0 : ℝ) by simp]
  refine tendsto_finsetSum _ fun k _ => ?_
  simp only [one_div]
  refine Tendsto.inv_tendsto_atTop ?_
  refine tendsto_atTop_add_const_right _ _ ?_
  exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

theorem hasSum_inner_shift (m : ℕ) :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1 + m)) (harmonic m) := by
  have hnn : ∀ n : ℕ, 0 ≤ 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1 + m) := by
    intro n
    rw [sub_nonneg]
    apply one_div_le_one_div_of_le (by positivity)
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hp : ∀ N, ∑ n ∈ range N, (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1 + m)) = a m 0 - a m N := by
    intro N
    simp_rw [← a_sub]
    exact sum_range_sub' (a m) N
  simp_rw [hp, a_zero]
  simpa using (tendsto_const_nhds (x := (harmonic m : ℝ))).sub (tendsto_a m)

theorem tsum_inner (m : ℕ) : ∑' n, f (m, n) = (harmonic m : ℝ) / (m : ℝ) ^ 3 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp [f]
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hs : HasSum (fun n : ℕ => f (m, n + 1)) ((harmonic m : ℝ) / (m : ℝ) ^ 3) := by
    have h := (hasSum_inner_shift m).mul_left (1 / (m : ℝ) ^ 3)
    rw [show 1 / (m : ℝ) ^ 3 * harmonic m = (harmonic m : ℝ) / (m : ℝ) ^ 3 by ring] at h
    refine h.congr_fun fun n => ?_
    unfold f
    simp only
    push_cast
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 1 + m ≠ 0 := by positivity
    have h3 : (m : ℝ) + (n + 1) ≠ 0 := by positivity
    field_simp
    ring
  have hz := tsum_eq_zero_add' (f := fun n : ℕ => f (m, n)) hs.summable
  rw [hz, hs.tsum_eq]
  simp [f]

/-- **Euler's second sum**: `Σₙ Hₙ/n³ = π⁴/72 = (5/4) ζ(4)`. -/
theorem hasSum_harmonic_div_cube :
    HasSum (fun n : ℕ => (harmonic n : ℝ) / (n : ℝ) ^ 3) (Real.pi ^ 4 / 72) := by
  have hprod := summable_f.prod
  have h := hprod.hasSum
  rw [← summable_f.tsum_prod' (fun m => summable_f.prod_factor m), tsum_f] at h
  simpa only [tsum_inner] using h

/-- **The paper's assembly** (`haar_qg_paper_v2151.tex`, base case `L = 2`): the two Euler
sums add to `2ζ(4) = π⁴/45`, which gives `M₂ = ζ(4)/π⁴ = 1/90`. -/
theorem euler_sums_assemble :
    (∑' x : Lt, term (x : ℕ × ℕ)) + ∑' n : ℕ, (harmonic n : ℝ) / (n : ℝ) ^ 3
      = 2 * (Real.pi ^ 4 / 90) := by
  rw [euler_sum_one, hasSum_harmonic_div_cube.tsum_eq]
  ring

end GppEulerSumTwo

#print axioms GppEulerSumTwo.hasSum_harmonic_div_cube
