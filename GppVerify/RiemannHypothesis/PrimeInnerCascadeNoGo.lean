import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# No-go: the raw cascade of prime inner channels has a non-globalizable zero divisor

Source: Codex, GPPDiscovery2 `research/2026-09-27_prime_inner_cascade_zero_accumulation_nogo.md`.

For a prime `p` put `L_p = log p`, `a_p = p^{-1/2} = e^{-L_p/2}` and let
`Θ_p(z) = B_{a_p}(e^{i L_p z})` with `B_a(w) = (w − a)/(1 − a w)`, the causal prime channel on
the upper half-plane.

* `theta_eq_zero_iff`: for `Im z > 0`, `Θ_p(z) = 0` iff `z = 2πk/L_p + i/2` for some `k ∈ ℤ`
  (the exact zero lattice, all on `Im z = 1/2`);
* `theta_zero_at_half_I`: every prime channel vanishes at the same point `z = i/2` (`k = 0`);
* `zk_dist_half_I`, `tendsto_zk`: even after removing `k = 0`, the `k = 1` zeros `z_{p,1}` are
  pairwise distinct (`zk_injOn`) and accumulate at `i/2` as `p → ∞`;
* `no_analytic_with_prime_zeros`: a function analytic on a preconnected set containing `i/2` and
  vanishing at all the `z_{p,1}` is identically zero (identity theorem), so no nonzero analytic
  global transfer can have these zero lattices;
* `blaschke_term_half_I`, `not_summable_blaschke`: the Blaschke terms
  `Im z/(1+|z|²)` at the common zero `i/2` equal `2/5` for every prime, so the Blaschke sum over
  primes diverges.

## Checks and scope

All claims check. The statement "an infinite product of the `Θ_p` times nonvanishing factors
cannot converge to a nonzero analytic function" is *not* formalized as such (it needs the
Hurwitz/zero-multiplicity argument for locally uniform limits); what is formalized is the exact
zero geometry and the identity-theorem and Blaschke-divergence consequences the note derives
from it. No RH claim.
-/

open Complex Filter Topology

namespace GppPrimeInnerCascade

/-- The Blaschke factor `B_a(w) = (w − a)/(1 − a w)`. -/
noncomputable def B (a w : ℂ) : ℂ := (w - a) / (1 - a * w)

/-- The causal prime channel `Θ_p(z) = B_{e^{-L/2}}(e^{i L z})`, `L = log p`. -/
noncomputable def theta (p : ℕ) (z : ℂ) : ℂ :=
  B (Complex.exp (-(Real.log p : ℂ) / 2)) (Complex.exp (I * (Real.log p : ℂ) * z))

/-- The zero `z_{p,k} = 2πk/log p + i/2`. -/
noncomputable def zpk (p : ℕ) (k : ℤ) : ℂ := ((2 * Real.pi * k / Real.log p : ℝ) : ℂ) + I / 2

theorem zpk_re (p : ℕ) (k : ℤ) : (zpk p k).re = 2 * Real.pi * k / Real.log p := by
  simp only [zpk, Complex.add_re, Complex.ofReal_re, Complex.div_ofNat_re, Complex.I_re, zero_div,
    add_zero]

/-- `e^{-L/2}` is `p^{-1/2}`. -/
theorem exp_neg_half_log (p : ℕ) (hp : 0 < p) :
    Real.exp (-(Real.log p) / 2) = (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast hp)]
  congr 1
  ring

/-- Solving `e^{i L z} = e^{-L/2}`. -/
theorem exp_eq_iff (L : ℝ) (hL : 0 < L) (z : ℂ) :
    Complex.exp (I * (L : ℂ) * z) = Complex.exp (-(L : ℂ) / 2) ↔
      ∃ k : ℤ, z = ((2 * Real.pi * k / L : ℝ) : ℂ) + I / 2 := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have e1 : ∀ k : ℤ, I * (L : ℂ) * (2 * Real.pi * k / L) = k * (2 * Real.pi * I) := by
    intro k; field_simp
  have e2 : I * (L : ℂ) * (I / 2) = -(L : ℂ) / 2 := by
    rw [show I * (L : ℂ) * (I / 2) = (I * I) * L / 2 by ring, I_mul_I]
    ring
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    push_cast
    have h2 : I * (L : ℂ) * (z - (2 * Real.pi * k / L + I / 2)) = 0 := by
      rw [mul_sub, mul_add, e1, e2]
      linear_combination hk
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (mul_ne_zero I_ne_zero hL')
    · exact sub_eq_zero.mp h
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    push_cast
    rw [mul_add, e1, e2]
    ring

/-- For `Im z > 0` the denominator of `Θ_p` does not vanish. -/
theorem denom_ne_zero_aux (L : ℝ) (hL : 0 < L) (z : ℂ) (hz : 0 < z.im) :
    1 - Complex.exp (-(L : ℂ) / 2) * Complex.exp (I * (L : ℂ) * z) ≠ 0 := by
  intro h
  have h1 : Complex.exp (-(L : ℂ) / 2) * Complex.exp (I * (L : ℂ) * z) = 1 := by
    linear_combination -h
  have h2 := congrArg norm h1
  rw [norm_mul, Complex.norm_exp, Complex.norm_exp, norm_one, ← Real.exp_add] at h2
  have h3 : (-(L : ℂ) / 2).re = -L / 2 := by
    rw [Complex.div_ofNat_re]; simp
  have h4 : (I * (L : ℂ) * z).re = -L * z.im := by simp
  rw [h3, h4, Real.exp_eq_one_iff] at h2
  nlinarith

theorem denom_ne_zero (p : ℕ) (hp : 2 ≤ p) (z : ℂ) (hz : 0 < z.im) :
    1 - Complex.exp (-(Real.log p : ℂ) / 2) * Complex.exp (I * (Real.log p : ℂ) * z) ≠ 0 :=
  denom_ne_zero_aux _ (Real.log_pos (by exact_mod_cast hp)) z hz

/-- **Exact zero lattice** of the prime channel in the upper half-plane. -/
theorem theta_eq_zero_iff (p : ℕ) (hp : 2 ≤ p) (z : ℂ) (hz : 0 < z.im) :
    theta p z = 0 ↔ ∃ k : ℤ, z = zpk p k := by
  have hL : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have hd := denom_ne_zero p hp z hz
  unfold theta B zpk
  rw [div_eq_zero_iff, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact (exp_eq_iff _ hL z).mp h
    · exact absurd h hd
  · intro h
    exact Or.inl ((exp_eq_iff _ hL z).mpr h)

/-- **All prime channels share the zero `i/2`.** -/
theorem theta_zero_at_half_I (p : ℕ) (hp : 2 ≤ p) : theta p (I / 2) = 0 := by
  have h := (theta_eq_zero_iff p hp (I / 2) (by simp)).mpr ⟨0, by simp [zpk]⟩
  exact h

/-- Hence every finite product of prime channels vanishes at `i/2`. -/
theorem prod_theta_zero (S : Finset ℕ) (hS : S.Nonempty) (hp : ∀ p ∈ S, 2 ≤ p) :
    ∏ p ∈ S, theta p (I / 2) = 0 :=
  Finset.prod_eq_zero hS.choose_spec (theta_zero_at_half_I _ (hp _ hS.choose_spec))

/-- The `k = 1` zeros approach `i/2` at distance `2π / log p`. -/
theorem zk_dist_half_I (p : ℕ) (hp : 2 ≤ p) : ‖zpk p 1 - I / 2‖ = 2 * Real.pi / Real.log p := by
  have hL : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have : zpk p 1 - I / 2 = ((2 * Real.pi / Real.log p : ℝ) : ℂ) := by
    simp [zpk]
  rw [this, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (by positivity)

theorem zk_ne_half_I (p : ℕ) (hp : 2 ≤ p) : zpk p 1 ≠ I / 2 := by
  intro h
  have := zk_dist_half_I p hp
  rw [h, sub_self, norm_zero] at this
  have hL : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have : 0 < 2 * Real.pi / Real.log p := by positivity
  linarith

/-- The `k = 1` zeros are pairwise distinct. -/
theorem zk_injOn : Set.InjOn (fun p : ℕ => zpk p 1) {p | 2 ≤ p} := by
  intro p hp q hq h
  have hp' : 2 ≤ p := hp
  have hq' : 2 ≤ q := hq
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp')
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq')
  have h' : 2 * Real.pi * ((1 : ℤ) : ℝ) / Real.log p = 2 * Real.pi * ((1 : ℤ) : ℝ) / Real.log q := by
    have := congrArg Complex.re h
    rwa [zpk_re, zpk_re] at this
  have h3 := (div_eq_div_iff hlp.ne' hlq.ne').mp h'
  simp only [Int.cast_one, mul_one] at h3
  have h2 : Real.log p = Real.log q :=
    (mul_left_cancel₀ (by positivity : (2 * Real.pi) ≠ 0) h3).symm
  have := Real.log_injOn_pos (Set.mem_Ioi.mpr (by exact_mod_cast (by omega : 0 < p)))
    (Set.mem_Ioi.mpr (by exact_mod_cast (by omega : 0 < q))) h2
  exact_mod_cast this

/-- Along the sequence of primes the `k = 1` zeros tend to `i/2`. -/
theorem tendsto_zk : Tendsto (fun n : ℕ => zpk (Nat.nth Nat.Prime n) 1) atTop (𝓝 (I / 2)) := by
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  have h1 : Tendsto (fun n => (Nat.nth Nat.Prime n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (Nat.nth_strictMono hinf).tendsto_atTop
  have h2 : Tendsto (fun n => Real.log (Nat.nth Nat.Prime n)) atTop atTop :=
    Real.tendsto_log_atTop.comp h1
  have h3 : Tendsto (fun n => 2 * Real.pi / Real.log (Nat.nth Nat.Prime n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h2
  have h4 := ((Complex.continuous_ofReal.tendsto 0).comp h3).add
    (tendsto_const_nhds (x := I / 2))
  simpa [zpk] using h4

/-- **Identity-theorem no-go.** A function analytic on a preconnected set containing `i/2` and
vanishing at every `z_{p,1}` is identically zero there. -/
theorem no_analytic_with_prime_zeros {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hU : IsPreconnected U) (h0 : I / 2 ∈ U) (hz : ∀ p : ℕ, p.Prime → f (zpk p 1) = 0) :
    Set.EqOn f 0 U := by
  refine hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU h0 ?_
  have hmem : Tendsto (fun n : ℕ => zpk (Nat.nth Nat.Prime n) 1) atTop (𝓝[≠] (I / 2)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_zk, Eventually.of_forall fun n => ?_⟩
    exact zk_ne_half_I _ (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n).two_le
  refine hmem.frequently (Frequently.of_forall fun n => ?_)
  exact hz _ (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n)

/-- The Blaschke term `Im z / (1 + |z|²)`. -/
noncomputable def blaschkeTerm (z : ℂ) : ℝ := z.im / (1 + Complex.normSq z)

/-- At the common zero `i/2` the term is `2/5` (the note's `(1/2)/(1 + 1/4)`). -/
theorem blaschke_term_half_I : blaschkeTerm (I / 2) = 2 / 5 := by
  simp [blaschkeTerm, Complex.normSq_apply]
  norm_num

/-- **Blaschke divergence.** Summing the common-zero contributions over all primes diverges. -/
theorem not_summable_blaschke :
    ¬ Summable (fun _ : Nat.Primes => blaschkeTerm (I / 2)) := by
  have : Infinite Nat.Primes := Nat.Primes.infinite
  rw [summable_const_iff]
  rw [blaschke_term_half_I]
  norm_num

end GppPrimeInnerCascade
