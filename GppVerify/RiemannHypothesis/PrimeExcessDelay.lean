import GppVerify.RiemannHypothesis.SU11PrimeBlaschke

/-!
# The von Mangoldt half-density current as the excess group delay of a Blaschke channel

Source: Codex, GPPDiscovery2 `research/2026-09-27_prime_vonmangoldt_as_excess_group_delay.md`,
§§2–4.

For a prime `p` put `L = log p` and `a = p^{-1/2}`. The local channel is the Blaschke factor
`B_a`, whose boundary phase derivative is the Poisson kernel
`P_a(θ) = (1−a²)/(1 − 2a cos θ + a²)` (`GppSU11Prime.blaschke_boundary_delay`). The delay in the
spectral variable `t` (with `θ = t L`) is `τ_p(t) = L · P_a(tL)`.

* `poisson_series`: `Σ_{m ≥ 1} a^m cos(mθ) = (P_a(θ) − 1)/2` (the Fourier series of the Poisson
  kernel);
* `vonMangoldt_current`: hence `Σ_{m≥1} (log p) p^{-m/2} cos(m t log p) = (τ_p(t) − log p)/2`,
  and since `Λ(p^m) = log p` this is exactly the prime-power half-density current: the excess of
  the delay above the free baseline `log p`;
* `vonMangoldt_current_finite`: phase derivatives add, so the same holds for a finite set of
  primes, with baseline `Σ log p`;
* `delay_pos`: the raw delay is strictly positive, but
  `excess_nonneg_at_zero` / `excess_neg_at_pi` show the vacuum-subtracted excess is positive at
  `θ = 0` and **negative** at `θ = π`: positivity followed by background subtraction gives a
  sign-indefinite object.

## Checks and scope

All claims check (the sign remark in the note, `e^{±itL}`, is immaterial since the cosine is even).
**Not formalized:** the global statements (§§5–7): the infinite baseline `Σ log p` diverges, the
Archimedean background delay, the link with the oscillating zero density, and the sharpened RH
target. No RH claim.
-/

open GppSU11Prime

namespace GppPrimeExcessDelay

/-- **Fourier series of the Poisson kernel.** -/
theorem poisson_series (a θ : ℝ) (ha : |a| < 1) :
    HasSum (fun m : ℕ => a ^ (m + 1) * Real.cos (((m + 1 : ℕ) : ℝ) * θ))
      ((poisson a θ - 1) / 2) := by
  have hd := den_pos a θ ha
  set z : ℂ := (a : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) with hz
  have hnorm : ‖z‖ < 1 := by
    rw [hz, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    exact ha
  have hs := hasSum_geometric_of_norm_lt_one hnorm
  have hre := ((Complex.hasSum_iff _ _).mp hs).1
  have hterm : ∀ m : ℕ, (z ^ m).re = a ^ m * Real.cos ((m : ℝ) * θ) := by
    intro m
    rw [hz, mul_pow, ← Complex.ofReal_pow, ← Complex.exp_nat_mul]
    have : (m : ℂ) * ((θ : ℂ) * Complex.I) = (((m : ℝ) * θ : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hre' : HasSum (fun m : ℕ => a ^ m * Real.cos ((m : ℝ) * θ)) ((1 - z)⁻¹).re := by
    simpa only [Function.comp_def, hterm] using hre
  have hshift := (hasSum_nat_add_iff' 1).mpr hre'
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, Real.cos_zero,
    pow_zero, mul_one] at hshift
  -- value: Re (1 - z)⁻¹ - 1 = (P - 1)/2
  have hcz : (1 - z).re = 1 - a * Real.cos θ := by
    simp [hz, Complex.exp_ofReal_mul_I_re]
  have hsz : (1 - z).im = -(a * Real.sin θ) := by
    simp [hz, Complex.exp_ofReal_mul_I_im]
  have hnsq : Complex.normSq (1 - z) = 1 - 2 * a * Real.cos θ + a ^ 2 := by
    rw [Complex.normSq_apply, hcz, hsz]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hdne : (1 - 2 * a * Real.cos θ + a ^ 2) ≠ 0 := hd.ne'
  have hval : ((1 - z)⁻¹).re - 1 = (poisson a θ - 1) / 2 := by
    rw [Complex.inv_re, hnsq, hcz, poisson]
    generalize hD : 1 - 2 * a * Real.cos θ + a ^ 2 = D at hdne ⊢
    field_simp
    rw [← hD]
    ring
  rw [← hval]
  exact hshift

/-- **The prime-power current is the excess group delay.** With `a = p^{-1/2}`, `L = log p`,
`θ = t L`: `Σ_{m≥1} L a^m cos(m θ) = (L · P_a(θ) − L)/2`. -/
theorem vonMangoldt_current (a L θ : ℝ) (ha : |a| < 1) :
    HasSum (fun m : ℕ => L * (a ^ (m + 1) * Real.cos (((m + 1 : ℕ) : ℝ) * θ)))
      ((L * poisson a θ - L) / 2) := by
  have h := (poisson_series a θ ha).mul_left L
  have e : (L * poisson a θ - L) / 2 = L * ((poisson a θ - 1) / 2) := by ring
  rw [e]
  exact h

/-- For a prime `p > 1`, the half-density current `Σ_m (log p) p^{-m/2} cos(m t log p)` equals
`(τ_p(t) − log p)/2`, with `τ_p(t) = log p · P_{p^{-1/2}}(t log p)`. -/
theorem vonMangoldt_current_prime (p t : ℝ) (hp : 1 < p) :
    HasSum (fun m : ℕ => Real.log p * ((p ^ (-(1 / 2 : ℝ))) ^ (m + 1) *
        Real.cos (((m + 1 : ℕ) : ℝ) * (t * Real.log p))))
      ((Real.log p * poisson (p ^ (-(1 / 2 : ℝ))) (t * Real.log p) - Real.log p) / 2) := by
  refine vonMangoldt_current (p ^ (-(1 / 2 : ℝ))) (Real.log p) (t * Real.log p) ?_
  have h0 : 0 < p ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  rw [abs_of_pos h0]
  exact Real.rpow_lt_one_of_one_lt_of_neg hp (by norm_num)

/-- **Finite prime sets add.** -/
theorem vonMangoldt_current_finite (S : Finset ℝ) (hS : ∀ p ∈ S, 1 < p) (t : ℝ) :
    HasSum (fun m : ℕ => ∑ p ∈ S, Real.log p * ((p ^ (-(1 / 2 : ℝ))) ^ (m + 1) *
        Real.cos (((m + 1 : ℕ) : ℝ) * (t * Real.log p))))
      (∑ p ∈ S, (Real.log p * poisson (p ^ (-(1 / 2 : ℝ))) (t * Real.log p) - Real.log p) / 2) :=
  hasSum_sum fun p hp => vonMangoldt_current_prime p t (hS p hp)

/-- The raw delay is strictly positive. -/
theorem delay_pos (a θ L : ℝ) (ha : |a| < 1) (hL : 0 < L) : 0 < L * poisson a θ := by
  have hd := den_pos a θ ha
  have : 0 < poisson a θ := by
    unfold poisson
    have : 0 < 1 - a ^ 2 := by nlinarith [abs_lt.mp ha, sq_abs a]
    positivity
  positivity

/-- At `θ = 0` the excess `(τ − L)/2` is strictly positive (`a > 0`)... -/
theorem excess_pos_at_zero (a L : ℝ) (ha : |a| < 1) (ha0 : 0 < a) (hL : 0 < L) :
    0 < (L * poisson a 0 - L) / 2 := by
  have h1 : 0 < 1 - a := by linarith [abs_lt.mp ha]
  rw [poisson_zero a ha]
  have : (1 + a) / (1 - a) > 1 := by rw [gt_iff_lt, lt_div_iff₀ h1]; linarith
  nlinarith

/-- ... and at `θ = π` it is strictly negative: the vacuum-subtracted delay is indefinite. -/
theorem excess_neg_at_pi (a L : ℝ) (ha : |a| < 1) (ha0 : 0 < a) (hL : 0 < L) :
    (L * poisson a Real.pi - L) / 2 < 0 := by
  have h1 : 0 < 1 + a := by linarith [abs_lt.mp ha]
  rw [poisson_pi a ha]
  have : (1 - a) / (1 + a) < 1 := by rw [div_lt_one h1]; linarith
  nlinarith

end GppPrimeExcessDelay
