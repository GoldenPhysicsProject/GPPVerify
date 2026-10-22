import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Critical GCD Gram: Euler packets collapse, so the first coefficient is unbounded for `ε ≤ 1/2`

Source: Codex, `work/codex/2026-10-21_gcd_coefficient_recovery_closability_zeta_threshold.md` §C
(GPP-bridge); audited by Grok (S86, `work/grok/2026-10-22_s86_prime_path_schur.md`). Daniel Toupin /
Golden Physics Project, with AI assistance from Codex (the theorem) and Claude Code (formalization).

The GCD Gram kernel is `K_ε(m, n) = (gcd(m, n)² / (m n))^ε` (`gcdKernel`). For a finite set `P` of
primes, the Euler packet `F_P = ∏_{p∈P}(1 − p^{−ε} χ_p)` has coefficient `(−1)^{|S|}(∏_S p)^{−ε}` on
`χ_{∏_S p}` (`coef`), which is `μ(n) n^{−ε}` (`coef_eq_moebius`).

* `double_sum_collapse`: for nonzero reals `y_p`,
  `∑_{S,T⊆P} ∏_S(−y²) ∏_T(−y²) ∏_{S∩T} y^{−2} = ∏_P(1 − y²)`. For fixed `S` the sum over `T` is
  `∏_P(1 + h_S)`, which vanishes unless `S = ∅`.
* `packet_gram`: `‖F_P‖²_{K_ε} = ∏_{p∈P}(1 − p^{−2ε})` (the case `y_p = p^{−ε}`, with
  `gcd(∏_S p, ∏_T p) = ∏_{S∩T} p`).
* `prefix_sum_lt_two`: for `1 ≤ x < 2` the prefix sum `∑_{∏_S p ≤ x} coef S` is `1`, so on
  `[0, log 2)` the prefix transfer of every packet is `e^{−t/2}`, independent of `P`.
* `coeff_one_unbounded`: for `0 < ε ≤ 1/2` and every `δ > 0` there is a packet with
  `χ₁`-coefficient `1` and `K_ε`-norm squared below `δ`, by `prod_primes_tends_small` (the
  divergence of `∑_p 1/p`, Mathlib's `not_summable_one_div_on_primes`). This is the finite core of
  Codex's nonclosability statement: the sources tend to `0` in `K_ε` while the outputs stay
  `e^{−t/2}` on `[0, min(T, log 2))`.

**Scope.** Only the finite, `ε ≤ 1/2` side is formalized. The note's `ε > 1/2` side, the exact dual
norm `‖coeff_n‖² = ζ(2ε) ∏_{p|n}(1 + p^{−2ε})` on the analytic Hardy subspace, and the operator-norm
statements are not, and neither is the Hilbert completion itself. The note itself says that `ζ(2ε)`
here is the ordinary pole at `s = 1`, not information about nontrivial zeros. No RH content.
-/

open Finset

namespace GppGcdPacketClosability

/-- **The collapse identity.** For any nonzero reals `y_p`,
`∑_{S,T ⊆ P} ∏_S(−y²) ∏_T(−y²) ∏_{S∩T} y^{−2} = ∏_P (1 − y²)`. -/
theorem double_sum_collapse (P : Finset ℕ) (y : ℕ → ℝ) (hy : ∀ p ∈ P, y p ≠ 0) :
    ∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
      (∏ p ∈ S, -(y p) ^ 2) * (∏ p ∈ T, -(y p) ^ 2) * ∏ p ∈ S ∩ T, ((y p) ^ 2)⁻¹ =
      ∏ p ∈ P, (1 - (y p) ^ 2) := by
  classical
  -- inner sum over `T`, for fixed `S ⊆ P`
  have hinner : ∀ S ∈ P.powerset, ∑ T ∈ P.powerset,
      (∏ p ∈ S, -(y p) ^ 2) * (∏ p ∈ T, -(y p) ^ 2) * ∏ p ∈ S ∩ T, ((y p) ^ 2)⁻¹ =
      (∏ p ∈ S, -(y p) ^ 2) *
        ∏ p ∈ P, (1 + (-(y p) ^ 2) * (if p ∈ S then ((y p) ^ 2)⁻¹ else 1)) := by
    intro S _
    rw [prod_one_add, mul_sum]
    refine sum_congr rfl fun T _ => ?_
    rw [mul_assoc, prod_mul_distrib, prod_ite, prod_const_one, mul_one,
      show T.filter (fun p => p ∈ S) = S ∩ T by ext; simp [and_comm]]
  rw [sum_congr rfl hinner, sum_eq_single (∅ : Finset ℕ)]
  · simp only [prod_empty, one_mul, notMem_empty, if_false, mul_one]
    exact prod_congr rfl fun p _ => by ring
  · intro S hS hne
    obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hqP : q ∈ P := mem_powerset.mp hS hq
    refine mul_eq_zero_of_right _ (prod_eq_zero hqP ?_)
    rw [if_pos hq]
    have : (y q) ^ 2 ≠ 0 := pow_ne_zero 2 (hy q hqP)
    rw [neg_mul, mul_inv_cancel₀ this]; ring
  · intro h; exact absurd (empty_mem_powerset P) h

/-- `gcd(∏_S p, ∏_T p) = ∏_{S∩T} p` for sets of primes. -/
lemma gcd_prod_primes {S T : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hT : ∀ p ∈ T, p.Prime) :
    Nat.gcd (∏ p ∈ S, p) (∏ p ∈ T, p) = ∏ p ∈ S ∩ T, p := by
  classical
  have hS' : ∏ p ∈ S, p = (∏ p ∈ S ∩ T, p) * ∏ p ∈ S \ T, p :=
    (prod_inter_mul_prod_sdiff S T _).symm
  have hT' : ∏ p ∈ T, p = (∏ p ∈ S ∩ T, p) * ∏ p ∈ T \ S, p := by
    rw [inter_comm]; exact (prod_inter_mul_prod_sdiff T S _).symm
  have hcop : Nat.Coprime (∏ p ∈ S \ T, p) (∏ p ∈ T \ S, p) := by
    refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.prod_right fun q hq => ?_
    have hp' := mem_sdiff.mp hp
    have hq' := mem_sdiff.mp hq
    refine (Nat.coprime_primes (hS p hp'.1) (hT q hq'.1)).mpr ?_
    rintro rfl; exact hp'.2 hq'.1
  rw [hS', hT', Nat.gcd_mul_left, hcop, mul_one]

/-- The GCD Gram kernel `K_ε(m, n) = (gcd(m, n)² / (m n))^ε`. -/
noncomputable def gcdKernel (ε : ℝ) (m n : ℕ) : ℝ :=
  (((Nat.gcd m n : ℕ) : ℝ) ^ 2 / ((m : ℝ) * n)) ^ ε

/-- Coefficient of the Euler packet `∏_{p ∈ P}(1 − p^{−ε} χ_p)` on `χ_{∏_S p}`. -/
noncomputable def coef (ε : ℝ) (S : Finset ℕ) : ℝ := (-1) ^ S.card * ((∏ p ∈ S, p : ℕ) : ℝ) ^ (-ε)

lemma coef_empty (ε : ℝ) : coef ε ∅ = 1 := by simp [coef]

/-- The packet coefficient is `μ(n) n^{−ε}` at `n = ∏_S p`. -/
lemma coef_eq_moebius (ε : ℝ) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    coef ε S = (ArithmeticFunction.moebius (∏ p ∈ S, p) : ℝ) * ((∏ p ∈ S, p : ℕ) : ℝ) ^ (-ε) := by
  rw [coef, ArithmeticFunction.isMultiplicative_moebius.map_prod_of_prime S hS]
  congr 1
  rw [prod_congr rfl fun p hp => ArithmeticFunction.moebius_apply_prime (hS p hp)]
  push_cast
  rw [prod_const]

private lemma cast_prod_rpow (S : Finset ℕ) (r : ℝ) :
    ((∏ p ∈ S, p : ℕ) : ℝ) ^ r = ∏ p ∈ S, ((p : ℝ) ^ r) := by
  push_cast
  exact (Real.finsetProd_rpow S _ (fun p _ => Nat.cast_nonneg p) r).symm

/-- **Gram norm of the Euler packet.** For a finite set `P` of primes,
`‖∏_{p∈P}(1 − p^{−ε} χ_p)‖²_{K_ε} = ∏_{p∈P}(1 − p^{−2ε})`. -/
theorem packet_gram (ε : ℝ) {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    ∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
      coef ε S * coef ε T * gcdKernel ε (∏ p ∈ S, p) (∏ p ∈ T, p) =
      ∏ p ∈ P, (1 - (p : ℝ) ^ (-2 * ε)) := by
  have hpos : ∀ p ∈ P, (0 : ℝ) < p := fun p hp => by exact_mod_cast (hP p hp).pos
  have hy : ∀ p ∈ P, ((p : ℝ) ^ (-ε)) ≠ 0 := fun p hp => (Real.rpow_pos_of_pos (hpos p hp) _).ne'
  have hRHS : ∏ p ∈ P, (1 - (p : ℝ) ^ (-2 * ε)) = ∏ p ∈ P, (1 - ((p : ℝ) ^ (-ε)) ^ 2) := by
    refine prod_congr rfl fun p hp => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hpos p hp).le]; ring_nf
  rw [hRHS, ← double_sum_collapse P (fun p => (p : ℝ) ^ (-ε)) hy]
  · refine sum_congr rfl fun S hS => sum_congr rfl fun T hT => ?_
    have hSP := mem_powerset.mp hS
    have hTP := mem_powerset.mp hT
    have hSp : ∀ p ∈ S, p.Prime := fun p hp => hP p (hSP hp)
    have hTp : ∀ p ∈ T, p.Prime := fun p hp => hP p (hTP hp)
    have hinv : ∀ p ∈ P, (((p : ℝ) ^ (-ε)) ^ 2)⁻¹ = (p : ℝ) ^ ε * (p : ℝ) ^ ε := by
      intro p hp
      rw [sq, mul_inv, ← Real.rpow_neg (hpos p hp).le, neg_neg]
    rw [gcdKernel, gcd_prod_primes hSp hTp,
      Real.div_rpow (by positivity) (mul_nonneg (by positivity) (by positivity)),
      Real.mul_rpow (by positivity) (by positivity),
      show ((((∏ p ∈ S ∩ T, p : ℕ) : ℝ)) ^ 2) = ((∏ p ∈ S ∩ T, p : ℕ) : ℝ) ^ (2 : ℝ) by
        rw [Real.rpow_two],
      ← Real.rpow_mul (by positivity), coef, coef]
    rw [cast_prod_rpow S, cast_prod_rpow T, cast_prod_rpow (S ∩ T), cast_prod_rpow S,
      cast_prod_rpow T]
    rw [prod_congr rfl fun p hp => hinv p (hSP (mem_inter.mp hp).1)]
    have hneg : ∀ U : Finset ℕ, (∏ p ∈ U, -((p : ℝ) ^ (-ε)) ^ 2) =
        (-1) ^ U.card * ((∏ p ∈ U, (p : ℝ) ^ (-ε)) * ∏ p ∈ U, (p : ℝ) ^ (-ε)) := by
      intro U
      rw [← prod_mul_distrib, ← prod_const, ← prod_mul_distrib]
      exact prod_congr rfl fun p _ => by ring
    rw [hneg S, hneg T]
    have hε2 : ∀ p ∈ S ∩ T, (p : ℝ) ^ (2 * ε) = (p : ℝ) ^ ε * (p : ℝ) ^ ε := fun p hp => by
      rw [← Real.rpow_add (hpos p (hSP (mem_inter.mp hp).1))]; ring_nf
    rw [prod_congr rfl hε2]
    have hdiv : ∀ (U : Finset ℕ), U ⊆ P → (∏ p ∈ U, (p : ℝ) ^ ε) =
        (∏ p ∈ U, (p : ℝ) ^ (-ε))⁻¹ := by
      intro U hU
      rw [← prod_inv_distrib]
      exact prod_congr rfl fun p hp => by rw [Real.rpow_neg (hpos p (hU hp)).le, inv_inv]
    rw [hdiv S hSP, hdiv T hTP]
    have hneS : (∏ p ∈ S, (p : ℝ) ^ (-ε)) ≠ 0 := prod_ne_zero_iff.mpr fun p hp => hy p (hSP hp)
    have hneT : (∏ p ∈ T, (p : ℝ) ^ (-ε)) ≠ 0 := prod_ne_zero_iff.mpr fun p hp => hy p (hTP hp)
    field_simp

/-- On `[0, log 2)` the prefix transfer of the packet is the constant `1`: among `∏_S p` only
`n = 1` (`S = ∅`) is below `2`. -/
lemma prefix_sum_lt_two (ε : ℝ) {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {x : ℝ}
    (hx1 : 1 ≤ x) (hx2 : x < 2) :
    ∑ S ∈ P.powerset.filter (fun S => ((∏ p ∈ S, p : ℕ) : ℝ) ≤ x), coef ε S = 1 := by
  rw [sum_eq_single (∅ : Finset ℕ)]
  · exact coef_empty ε
  · intro S hS hne
    exfalso
    obtain ⟨hSP, hle⟩ := mem_filter.mp hS
    obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hq2 : 2 ≤ q := (hP q (mem_powerset.mp hSP hq)).two_le
    have hdvd : q ∣ ∏ p ∈ S, p := dvd_prod_of_mem _ hq
    have hpos : 0 < ∏ p ∈ S, p :=
      prod_pos fun p hp => (hP p (mem_powerset.mp hSP hp)).pos
    have : (2 : ℝ) ≤ ((∏ p ∈ S, p : ℕ) : ℝ) := by
      exact_mod_cast hq2.trans (Nat.le_of_dvd hpos hdvd)
    linarith
  · intro h
    exact absurd (mem_filter.mpr ⟨empty_mem_powerset P, by simpa using hx1⟩) h

/-- For `0 < ε ≤ 1/2` the products `∏_{p<N}(1 − p^{−2ε})` become arbitrarily small. -/
theorem prod_primes_tends_small {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∏ p ∈ Nat.primesBelow N, (1 - (p : ℝ) ^ (-2 * ε)) < δ := by
  -- the partial sums of `1/p` are unbounded
  have hdiv := not_summable_one_div_on_primes
  rw [not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => Set.indicator_nonneg
    (fun n _ => by positivity) n)] at hdiv
  obtain ⟨N, hN⟩ := (hdiv.eventually_ge_atTop (-Real.log δ + 1)).exists
  refine ⟨N, ?_⟩
  have hsum : ∑ i ∈ range N, Set.indicator {p | p.Prime} (fun n : ℕ => (1 : ℝ) / n) i =
      ∑ p ∈ Nat.primesBelow N, (1 : ℝ) / p := by
    rw [Nat.primesBelow, sum_filter]
    exact sum_congr rfl fun i _ => by simp [Set.indicator]
  rw [hsum] at hN
  have hle : ∀ p ∈ Nat.primesBelow N, (1 - (p : ℝ) ^ (-2 * ε)) ≤ Real.exp (-(1 / (p : ℝ))) := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt.le
    have h1 : (p : ℝ) ^ (-1 : ℝ) ≤ (p : ℝ) ^ (-2 * ε) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    rw [Real.rpow_neg_one] at h1
    have := Real.add_one_le_exp (-(1 / (p : ℝ)))
    rw [one_div] at this ⊢
    linarith
  have hnn : ∀ p ∈ Nat.primesBelow N, 0 ≤ 1 - (p : ℝ) ^ (-2 * ε) := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt.le
    have : (p : ℝ) ^ (-2 * ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
    linarith
  calc ∏ p ∈ Nat.primesBelow N, (1 - (p : ℝ) ^ (-2 * ε))
      ≤ ∏ p ∈ Nat.primesBelow N, Real.exp (-(1 / (p : ℝ))) := prod_le_prod hnn hle
    _ = Real.exp (-∑ p ∈ Nat.primesBelow N, (1 : ℝ) / p) := by
        rw [← Real.exp_sum, sum_neg_distrib]
    _ ≤ Real.exp (Real.log δ - 1) := Real.exp_le_exp.mpr (by linarith)
    _ < Real.exp (Real.log δ) := Real.exp_lt_exp.mpr (by linarith)
    _ = δ := Real.exp_log hδ

/-- **Codex's nonclosability core.** For `0 < ε ≤ 1/2`, the coefficient-of-`χ₁` functional is
unbounded for the GCD Gram form `K_ε`: for every `δ > 0` there is a finite Euler packet whose
`χ₁`-coefficient is `1` and whose `K_ε`-norm squared is `< δ`. -/
theorem coeff_one_unbounded {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ coef ε ∅ = 1 ∧
      ∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
        coef ε S * coef ε T * gcdKernel ε (∏ p ∈ S, p) (∏ p ∈ T, p) < δ := by
  obtain ⟨N, hN⟩ := prod_primes_tends_small hε0 hε hδ
  have hP : ∀ p ∈ Nat.primesBelow N, p.Prime := fun p hp => Nat.prime_of_mem_primesBelow hp
  exact ⟨Nat.primesBelow N, hP, coef_empty ε, by rw [packet_gram ε hP]; exact hN⟩

end GppGcdPacketClosability
