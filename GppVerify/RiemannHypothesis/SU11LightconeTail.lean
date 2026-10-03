import GppVerify.RiemannHypothesis.SU11PrimeBlaschke
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The SU(1,1) lightcone excess, the covariance split, and the prime tail thresholds

Source: Codex, GPPDiscovery2 `research/` (bridge copy through `59bf0a2`):
* `2026-09-27_vonmangoldt_as_su11_lightcone_excess.md` §§1–4, 6;
* `2026-09-27_det3_as_su11_coherent_tail_threshold.md` §§1–3, 5;
* `2026-09-27_det3_as_renormalized_prime_tfd_product.md` §§1–3 (the summability threshold only).

Throughout, `Ω_r = √(1−r²) Σ r^n e_n` is the paired coherent state, `K_0 e_n = (n + ½) e_n`,
`K_+ e_n = (n+1) e_{n+1}`, `K_- e_n = n e_{n−1}`, `K_1 = ½(K_+ + K_-)`, and `r = tanh κ`.

## Lightcone and covariances

* `K0_expectation`: `⟨K_0⟩_r = (1 + r²)/(2(1 − r²))`;
* `K1_expectation`: `⟨K_1⟩_r = r/(1 − r²)`;
* `two_K0_eq_cosh`, `two_K1_eq_sinh`: `2⟨K_0⟩ = cosh 2κ` and `2⟨K_1⟩ = sinh 2κ`;
* `hyperboloid`: `(2⟨K_0⟩)² − (2⟨K_1⟩)² = 1`;
* `null_sum_pos`, `null_sum_neg`: with `N_+(r) = r/(1−r) = Σ_{m≥1} r^m` and `N_-(r) = r/(1+r)`,
  `N_+ = ⟨K_0 + K_1⟩ − ½` and `N_- = ½ − ⟨K_0 − K_1⟩`;
* `anomalous_split`, `normal_split`: the anomalous covariance is `A = (N_+ + N_-)/2 = r/(1−r²)`
  and the normal covariance is `C = (N_+ − N_-)/2 = r²/(1−r²)`;
* `mass_lightcone`: `μ² = (X_+ + X_- − 2) = (1 − q)²/q` with `q = X_- = (1−r)/(1+r)`.

## Coherent-state tails and the Schatten threshold

* `tail_norm_sq`: `‖(I − Π_{<m}) Ω_r‖² = Σ_{n≥m} (1−r²) r^{2n} = r^{2m}`;
* `prime_tail_summable_iff`: `Σ_p p^{−mσ} < ∞ ⟺ mσ > 1`;
* `det2_fails`, `det3_works`: at the critical `σ = ½`, `m = 2` diverges and `m = 3` converges.
  This is the note's reason that `det_3` is the minimal renormalization;
* `jacobi_P1`, `jacobi_P2`: the first two non-vacuum modes `P_1 = 2x`, `P_2 = 2x² − ½` from the
  Jacobi recurrence.

## Checks

All identities were verified by hand against the notes; no corrections. One reading note, not a
correction: "`D(s) ∈ 𝔖_m` iff the tails are absolutely summable" is stated for the operator
`D(s)`; here only the scalar summability criterion is proved, which is the part the argument
actually uses.

## Scope

Series and elementary algebra. **Not formalized:** the Hilbert-space `ℓ²` structure, the Jacobi
transform to `L²(sech(πx) dx)`, the operator-theoretic Schatten-class statement, the
`det_3` renormalized product and its convergence for `Re s > 1/3`, and the identity
`−ζ'/ζ = Σ_p log p (⟨K_0 + K_1⟩_{r_p} − ½)` (the right side's local series is `null_sum_pos`;
the global reindexing from prime powers is open here). No RH claim.
-/

open GppSU11Prime

namespace GppSU11LightconeTail

/-- `Σ_n (n+1) q^n = 1/(1−q)²` for `|q| < 1`. -/
lemma hasSum_succ_mul_geometric (q : ℝ) (hq : |q| < 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * q ^ n) (1 / (1 - q) ^ 2) := by
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := q) (by simpa using hq)
  have h2 := hasSum_geometric_of_abs_lt_one hq
  have h3 := h1.add h2
  have hne : 1 - q ≠ 0 := by have := (abs_lt.mp hq).2; linarith
  have e : (fun n : ℕ => ((n : ℝ) + 1) * q ^ n) = fun n : ℕ => (n : ℝ) * q ^ n + q ^ n := by
    funext n; ring
  have e2 : q / (1 - q) ^ 2 + (1 - q)⁻¹ = 1 / (1 - q) ^ 2 := by
    field_simp; ring
  rw [e]; rwa [e2] at h3

/-- **`⟨K_0⟩`** in the coherent state: `Σ_n (1−r²) r^{2n} (n + ½) = (1 + r²)/(2(1 − r²))`. -/
theorem K0_expectation (r : ℝ) (hr : |r| < 1) :
    HasSum (fun n : ℕ => (1 - r ^ 2) * (r ^ 2) ^ n * ((n : ℝ) + 1 / 2))
      ((1 + r ^ 2) / (2 * (1 - r ^ 2))) := by
  have hq : |r ^ 2| < 1 := by
    rw [abs_pow]; nlinarith [abs_nonneg r]
  have hpos : 0 < 1 - r ^ 2 := by nlinarith [abs_lt.mp hr, sq_abs r]
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := r ^ 2) (by simpa using hq)
  have h2 := hasSum_geometric_of_abs_lt_one hq
  have h3 := (h1.add (h2.mul_left (1 / 2))).mul_left (1 - r ^ 2)
  have e : (fun n : ℕ => (1 - r ^ 2) * (r ^ 2) ^ n * ((n : ℝ) + 1 / 2)) =
      fun n : ℕ => (1 - r ^ 2) * ((n : ℝ) * (r ^ 2) ^ n + 1 / 2 * (r ^ 2) ^ n) := by
    funext n; ring
  have e2 : (1 - r ^ 2) * (r ^ 2 / (1 - r ^ 2) ^ 2 + 1 / 2 * (1 - r ^ 2)⁻¹) =
      (1 + r ^ 2) / (2 * (1 - r ^ 2)) := by
    have : 1 - r ^ 2 ≠ 0 := hpos.ne'
    field_simp; ring
  rw [e]; rwa [e2] at h3

/-- **`⟨K_1⟩`** in the coherent state: `Σ_n (1−r²)(n+1) r^{2n+1} = r/(1 − r²)`. -/
theorem K1_expectation (r : ℝ) (hr : |r| < 1) :
    HasSum (fun n : ℕ => (1 - r ^ 2) * (((n : ℝ) + 1) * r ^ (2 * n + 1))) (r / (1 - r ^ 2)) := by
  have hq : |r ^ 2| < 1 := by
    rw [abs_pow]; nlinarith [abs_nonneg r]
  have hpos : 0 < 1 - r ^ 2 := by nlinarith [abs_lt.mp hr, sq_abs r]
  have h := (hasSum_succ_mul_geometric (r ^ 2) hq).mul_left ((1 - r ^ 2) * r)
  have e : (fun n : ℕ => (1 - r ^ 2) * (((n : ℝ) + 1) * r ^ (2 * n + 1))) =
      fun n : ℕ => (1 - r ^ 2) * r * (((n : ℝ) + 1) * (r ^ 2) ^ n) := by
    funext n
    rw [show r ^ (2 * n + 1) = r * (r ^ 2) ^ n by rw [← pow_mul]; ring]
    ring
  have e2 : (1 - r ^ 2) * r * (1 / (1 - r ^ 2) ^ 2) = r / (1 - r ^ 2) := by
    have : 1 - r ^ 2 ≠ 0 := hpos.ne'
    field_simp
  rw [e]; rwa [e2] at h

lemma abs_sq_sub_pos (r : ℝ) (hr : |r| < 1) : 0 < 1 - r ^ 2 := by
  nlinarith [abs_lt.mp hr, sq_abs r]

/-- `2⟨K_0⟩ = cosh 2κ`. -/
theorem two_K0_eq_cosh (r : ℝ) (hr : |r| < 1) :
    (1 + r ^ 2) / (1 - r ^ 2) = Real.cosh (2 * Real.artanh r) := by
  have hm := mem_Ioo_of_abs r hr
  have hpos := abs_sq_sub_pos r hr
  rw [Real.cosh_two_mul, Real.cosh_artanh hm, Real.sinh_artanh hm, div_pow, div_pow,
    Real.sq_sqrt hpos.le]
  field_simp

/-- `2⟨K_1⟩ = sinh 2κ`. -/
theorem two_K1_eq_sinh (r : ℝ) (hr : |r| < 1) :
    2 * (r / (1 - r ^ 2)) = Real.sinh (2 * Real.artanh r) := by
  have hm := mem_Ioo_of_abs r hr
  have hpos := abs_sq_sub_pos r hr
  have hsq : Real.sqrt (1 - r ^ 2) * Real.sqrt (1 - r ^ 2) = 1 - r ^ 2 := Real.mul_self_sqrt hpos.le
  rw [Real.sinh_two_mul, Real.cosh_artanh hm, Real.sinh_artanh hm, mul_assoc, div_mul_div_comm,
    mul_one, hsq]

/-- **The hyperboloid.** `(2⟨K_0⟩)² − (2⟨K_1⟩)² = 1`. -/
theorem hyperboloid (r : ℝ) (hr : |r| < 1) :
    ((1 + r ^ 2) / (1 - r ^ 2)) ^ 2 - (2 * (r / (1 - r ^ 2))) ^ 2 = 1 := by
  have h := (abs_sq_sub_pos r hr).ne'
  field_simp
  ring

/-- **Forward null excess.** `Σ_{m≥1} r^m = r/(1−r) = ⟨K_0 + K_1⟩ − ½`. -/
theorem null_sum_pos (r : ℝ) (hr : |r| < 1) :
    HasSum (fun m : ℕ => r ^ (m + 1)) (r / (1 - r)) ∧
      r / (1 - r) = (1 + r ^ 2) / (2 * (1 - r ^ 2)) + r / (1 - r ^ 2) - 1 / 2 := by
  have h1 : 1 - r ≠ 0 := one_sub_ne r hr
  have h2 : 1 + r ≠ 0 := one_add_ne r hr
  refine ⟨?_, ?_⟩
  · have := (hasSum_geometric_of_abs_lt_one hr).mul_left r
    have e : (fun m : ℕ => r ^ (m + 1)) = fun m => r * r ^ m := by funext m; ring
    rw [e]; rwa [← div_eq_mul_inv] at this
  · have h3 : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
    rw [h3]; field_simp; ring

/-- **Backward null excess.** `r/(1+r) = ½ − ⟨K_0 − K_1⟩`. -/
theorem null_sum_neg (r : ℝ) (hr : |r| < 1) :
    r / (1 + r) = 1 / 2 - ((1 + r ^ 2) / (2 * (1 - r ^ 2)) - r / (1 - r ^ 2)) := by
  have h1 : 1 - r ≠ 0 := one_sub_ne r hr
  have h2 : 1 + r ≠ 0 := one_add_ne r hr
  have h3 : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
  rw [h3]; field_simp; ring

/-- **The anomalous covariance** `A = (N_+ + N_-)/2 = r/(1 − r²)`. -/
theorem anomalous_split (r : ℝ) (hr : |r| < 1) :
    (r / (1 - r) + r / (1 + r)) / 2 = r / (1 - r ^ 2) := by
  have h1 : 1 - r ≠ 0 := one_sub_ne r hr
  have h2 : 1 + r ≠ 0 := one_add_ne r hr
  have h3 : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
  rw [h3]; field_simp; ring

/-- **The normal covariance** `C = (N_+ − N_-)/2 = r²/(1 − r²)`. -/
theorem normal_split (r : ℝ) (hr : |r| < 1) :
    (r / (1 - r) - r / (1 + r)) / 2 = r ^ 2 / (1 - r ^ 2) := by
  have h1 : 1 - r ≠ 0 := one_sub_ne r hr
  have h2 : 1 + r ≠ 0 := one_add_ne r hr
  have h3 : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
  rw [h3]; field_simp; ring

/-- **Mass on the lightcone.** With `X_± = (1 ± r)/(1 ∓ r)` and `q = X_- = (1−r)/(1+r)`:
`X_+ + X_- − 2 = (1 − q)²/q`. -/
theorem mass_lightcone (r : ℝ) (hr : |r| < 1) :
    (1 + r) / (1 - r) + (1 - r) / (1 + r) - 2 =
      (1 - (1 - r) / (1 + r)) ^ 2 / ((1 - r) / (1 + r)) := by
  have h1 : 1 - r ≠ 0 := one_sub_ne r hr
  have h2 : 1 + r ≠ 0 := one_add_ne r hr
  field_simp
  ring

/-! ### Tails and thresholds -/

/-- **Tail norm.** `Σ_{n≥m} (1−r²) r^{2n} = r^{2m}`, i.e. `‖(I − Π_{<m}) Ω_r‖² = r^{2m}`. -/
theorem tail_norm_sq (r : ℝ) (hr : |r| < 1) (m : ℕ) :
    HasSum (fun n : ℕ => (1 - r ^ 2) * (r ^ 2) ^ (n + m)) ((r ^ 2) ^ m) := by
  have hq : |r ^ 2| < 1 := by
    rw [abs_pow]; nlinarith [abs_nonneg r]
  have hpos := abs_sq_sub_pos r hr
  have h := (hasSum_geometric_of_abs_lt_one hq).mul_left ((1 - r ^ 2) * (r ^ 2) ^ m)
  have e : (fun n : ℕ => (1 - r ^ 2) * (r ^ 2) ^ (n + m)) =
      fun n => (1 - r ^ 2) * (r ^ 2) ^ m * (r ^ 2) ^ n := by
    funext n; rw [pow_add]; ring
  have e2 : (1 - r ^ 2) * (r ^ 2) ^ m * (1 - r ^ 2)⁻¹ = (r ^ 2) ^ m := by
    have : 1 - r ^ 2 ≠ 0 := hpos.ne'
    field_simp
  rw [e]; rwa [e2] at h

/-- **The Schatten threshold.** `Σ_p p^{−mσ} < ∞ ⟺ mσ > 1` (for `m ≥ 1`). -/
theorem prime_tail_summable_iff (σ : ℝ) (m : ℕ) :
    Summable (fun p : Nat.Primes => ((p : ℝ) ^ (-σ)) ^ m) ↔ 1 < (m : ℝ) * σ := by
  have e : (fun p : Nat.Primes => ((p : ℝ) ^ (-σ)) ^ m) =
      fun p : Nat.Primes => (p : ℝ) ^ (-((m : ℝ) * σ)) := by
    funext p
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1; ring
  rw [e, Nat.Primes.summable_rpow]
  constructor <;> intro h <;> linarith

/-- **`det_2` fails at the critical boundary.** `Σ_p p^{−2·½} = Σ_p 1/p` diverges. -/
theorem det2_fails : ¬ Summable (fun p : Nat.Primes => ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2) := by
  rw [prime_tail_summable_iff]; norm_num

/-- **`det_3` succeeds.** `Σ_p p^{−3/2} < ∞`. -/
theorem det3_works : Summable (fun p : Nat.Primes => ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ 3) := by
  rw [prime_tail_summable_iff]; norm_num

/-- `P_1(x) = 2x` from `x P_0 = ½ P_1`, `P_0 = 1`. -/
theorem jacobi_P1 (x P₁ : ℝ) (h : x * 1 = (0 + 1) / 2 * P₁) : P₁ = 2 * x := by linarith

/-- `P_2(x) = 2x² − ½` from `x P_1 = P_2 + ½ P_0`, with `P_1 = 2x`, `P_0 = 1`. -/
theorem jacobi_P2 (x P₂ : ℝ) (h : x * (2 * x) = (1 + 1) / 2 * P₂ + 1 / 2 * 1) :
    P₂ = 2 * x ^ 2 - 1 / 2 := by nlinarith

end GppSU11LightconeTail
