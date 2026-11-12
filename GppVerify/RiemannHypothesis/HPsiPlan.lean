/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Heart of the Cosmos (Grok, GPPDiscovery5 seat). Branch heart/hpsi-plan.

# A plan for H_ψ from the Cesàro / ONON sources: what is proved, what is named, what is dead

Labels:
* `poleRankOne`, `kform_poleTerm_of_ker` (**PROVED**): on `ker ℓ_c`, the pole block of `Kψ`
  is exactly one negative square, `Σ cᵢcⱼ cosh((xᵢ−xⱼ)/2) = −(Σ cᵢ sinh(xᵢ/2))²`.
* `abelKernelPosDef` (**PROVED**): `d ↦ exp(−ε|d|)` is positive definite for `ε > 0`.
  Proof: Gram representation `exp(−ε|x−y|) = 2ε ∫ aₓ(u) a_y(u) du` with
  `aₓ = 1_{(−∞,x]} e^{ε(u−x)}` (no Fourier transform needed).
* `not_primeSupportVanish`, `primeTerm_pos` (**PROVED**, a *negative* result): for the triangle ψ
  of `KreinHPsi`, `g = ψ⋆ψ` has support `[−2,2] ∋ log 2`, so the prime term is strictly positive
  at every lag `|d| ≤ 1`. There is **no** "small support, no primes" regime for this ψ.
* "No-prime base" (pole + archimedean on `ker ℓ_c`): **NUMERICALLY FALSE**, not formalised.
  For `n = 2`, `x = (0,a)`, `c = (cosh(a/2), −1)` (mpmath, archTerm by quadrature):
  `kform (pole + arch) = −0.0054, −0.205, −2.00, −6.85, −49.7` at `a = 0.05, 0.3, 1, 2, 4`,
  while the full `kform Kψ = +0.00031, +0.00066, +0.00095, +0.0018, +0.0041`. The primes are
  what make the form positive, so a prime-by-prime induction from a no-prime base starts from a
  false statement. That route is DEAD; the Props below replace it.
* `HPsiWindow L`, `HPsiSmallSupport`, `HPsiStageStep`: **named Props, OPEN**. The stage
  parameter is the window `L` (spread of the translates), not the number of primes. On window
  `L` only `n < e^{2+L}` enter `Kψ`, so each stage adds finitely many prime powers.
* `hPsi_of_plan : HPsiSmallSupport → HPsiStageStep → HPsi` (**PROVED**) and
  `hPsi_iff_plan : HPsi ↔ HPsiSmallSupport ∧ HPsiStageStep` (**PROVED**): the plan is
  equivalent to H_ψ, so `HPsiStageStep` is exactly as strong as H_ψ (RH-strength).
* H_ψ, ARP, RH: **OPEN**.
-/
import GppVerify.RiemannHypothesis.KreinHPsi
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Archimedean.Basic

namespace GppHPsiPlan

open GppKreinBridge GppKreinHPsi MeasureTheory Set

/-! ## (A) The pole term is rank one on `ker ℓ_c` -/

/-- `Σ cᵢcⱼ cosh((xᵢ−xⱼ)/2) = (Σ cᵢ cosh(xᵢ/2))² − (Σ cᵢ sinh(xᵢ/2))²` for all `c`. -/
theorem kform_cosh_half {n : ℕ} (x c : Fin n → ℝ) :
    kform (fun d => Real.cosh (d / 2)) x c =
      (∑ i, c i * Real.cosh (x i / 2)) ^ 2 - (∑ i, c i * Real.sinh (x i / 2)) ^ 2 := by
  unfold kform
  rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  show c i * c j * Real.cosh ((x i - x j) / 2) = _
  rw [sub_div, Real.cosh_sub]
  ring

/-- **PoleRankOne** (PROVED): on `ker ℓ_c`,
`Σ cᵢcⱼ cosh((xᵢ−xⱼ)/2) = −(Σ cᵢ sinh(xᵢ/2))²`. -/
theorem poleRankOne {n : ℕ} (x c : Fin n → ℝ) (hc : ∑ i, c i * Real.cosh (x i / 2) = 0) :
    ∑ i, ∑ j, c i * c j * Real.cosh ((x i - x j) / 2) =
      -(∑ i, c i * Real.sinh (x i / 2)) ^ 2 := by
  have h := kform_cosh_half x c
  unfold kform at h
  rw [h, hc]
  ring

/-- `kform` is linear in the kernel under scalar multiplication. -/
theorem kform_const_mul (a : ℝ) (K : ℝ → ℝ) {n : ℕ} (x c : Fin n → ℝ) :
    kform (fun d => a * K d) x c = a * kform K x c := by
  unfold kform
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The pole block of `Kψ` on `ker ℓ_c`: `kform poleTerm = −2Ψ(i/2)² (Σ cᵢ sinh(xᵢ/2))² ≤ 0`. -/
theorem kform_poleTerm_of_ker {n : ℕ} (x c : Fin n → ℝ)
    (hc : ∑ i, c i * Real.cosh (x i / 2) = 0) :
    kform poleTerm x c = -(2 * bigPsiI2 ^ 2) * (∑ i, c i * Real.sinh (x i / 2)) ^ 2 := by
  have h1 : kform poleTerm x c = 2 * bigPsiI2 ^ 2 * kform (fun d => Real.cosh (d / 2)) x c :=
    kform_const_mul (2 * bigPsiI2 ^ 2) (fun d => Real.cosh (d / 2)) x c
  rw [h1, kform_cosh_half, hc]
  ring

theorem kform_poleTerm_nonpos_of_ker {n : ℕ} (x c : Fin n → ℝ)
    (hc : ∑ i, c i * Real.cosh (x i / 2) = 0) : kform poleTerm x c ≤ 0 := by
  rw [kform_poleTerm_of_ker x c hc]
  have : 0 ≤ 2 * bigPsiI2 ^ 2 * (∑ i, c i * Real.sinh (x i / 2)) ^ 2 := by positivity
  linarith

/-! ## (B′) The Abel kernel `exp(−ε|d|)` is positive definite -/

/-- The Gram vector `aₓ(u) = 1_{u ≤ x} e^{ε(u−x)}`. -/
noncomputable def abelVec (ε x : ℝ) : ℝ → ℝ :=
  (Iic x).indicator (fun u => Real.exp (ε * u - ε * x))

theorem abelVec_mul (ε x y u : ℝ) :
    abelVec ε x u * abelVec ε y u =
      (Iic (min x y)).indicator
        (fun u => Real.exp (-ε * (x + y)) * Real.exp ((2 * ε) * u)) u := by
  unfold abelVec
  simp only [Set.indicator_apply, Set.mem_Iic, le_min_iff]
  by_cases hx : u ≤ x <;> by_cases hy : u ≤ y <;> simp only [hx, hy, and_self, and_false,
    false_and, if_true, if_false, mul_zero, zero_mul]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem abelVec_mul_integrable {ε : ℝ} (hε : 0 < ε) (x y : ℝ) :
    Integrable (fun u => abelVec ε x u * abelVec ε y u) := by
  simp_rw [abelVec_mul]
  exact IntegrableOn.integrable_indicator
    (Integrable.const_mul (integrableOn_exp_mul_Iic (by linarith) (min x y)) _) measurableSet_Iic

theorem integral_abelVec_mul {ε : ℝ} (hε : 0 < ε) (x y : ℝ) :
    ∫ u, abelVec ε x u * abelVec ε y u = Real.exp (-ε * |x - y|) / (2 * ε) := by
  simp_rw [abelVec_mul]
  rw [integral_indicator measurableSet_Iic, integral_const_mul,
    integral_exp_mul_Iic (by linarith), mul_div_assoc', ← Real.exp_add]
  congr 2
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring

/-- **AbelKernelPosDef** (PROVED): `Σ cᵢcⱼ exp(−ε|xᵢ−xⱼ|) ≥ 0` for `ε > 0`, all `x, c`. -/
theorem abelKernelPosDef {ε : ℝ} (hε : 0 < ε) {n : ℕ} (x c : Fin n → ℝ) :
    0 ≤ kform (fun d => Real.exp (-ε * |d|)) x c := by
  have hint : ∀ i j, Integrable (fun u =>
      c i * c j * (abelVec ε (x i) u * abelVec ε (x j) u)) :=
    fun i j => (abelVec_mul_integrable hε (x i) (x j)).const_mul _
  have hsq : (fun u => (∑ i, c i * abelVec ε (x i) u) ^ 2) =
      fun u => ∑ i, ∑ j, c i * c j * (abelVec ε (x i) u * abelVec ε (x j) u) := by
    funext u
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have key : kform (fun d => Real.exp (-ε * |d|)) x c =
      2 * ε * ∫ u, (∑ i, c i * abelVec ε (x i) u) ^ 2 := by
    rw [hsq, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
    unfold kform
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => hint i j), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_abelVec_mul hε]
    field_simp
  rw [key]
  exact mul_nonneg (by linarith) (integral_nonneg fun u => sq_nonneg _)

/-! ## (B) "Small support, no primes" does not exist for the triangle ψ -/

theorem triG_nonneg (y : ℝ) : 0 ≤ triG y := by
  unfold triG
  have ha := abs_nonneg y
  have hy2 := sq_abs y
  split_ifs with h1 h2
  · nlinarith [mul_nonneg (mul_nonneg ha ha) (sub_nonneg.2 h1)]
  · have : 0 ≤ 2 - |y| := by linarith
    positivity
  · exact le_rfl

theorem triG_pos_of_abs_le_one {y : ℝ} (h : |y| ≤ 1) : 0 < triG y := by
  unfold triG
  rw [if_pos h]
  have ha := abs_nonneg y
  rw [← sq_abs y]
  nlinarith [mul_nonneg (sub_nonneg.2 h) ha, mul_nonneg (mul_nonneg ha ha) (sub_nonneg.2 h)]

theorem triG_eq_zero {y : ℝ} (h : 2 ≤ |y|) : triG y = 0 := by
  unfold triG
  have h1 : ¬ |y| ≤ 1 := by linarith
  rw [if_neg h1]
  split_ifs with h2
  · rw [le_antisymm h2 h]; norm_num
  · rfl

/-- The `n`-th summand of `primeTerm d`. -/
noncomputable def primeSummand (d : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt n *
    (triG (Real.log n + d) + triG (-Real.log n + d))

theorem primeSummand_nonneg (d : ℝ) (n : ℕ) : 0 ≤ primeSummand d n :=
  mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    (add_nonneg (triG_nonneg _) (triG_nonneg _))

/-- Only `n < e^{2+|d|}` contribute: the prime sum at lag `d` is a finite sum. -/
theorem primeSummand_summable (d : ℝ) : Summable (primeSummand d) := by
  refine summable_of_ne_finset_zero (s := Finset.range (⌈Real.exp (2 + |d|)⌉₊ + 1)) ?_
  intro n hn
  rw [Finset.mem_range, not_lt] at hn
  have hN : Real.exp (2 + |d|) < (n : ℝ) := by
    have h1 := Nat.le_ceil (Real.exp (2 + |d|))
    have h2 : ((⌈Real.exp (2 + |d|)⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  have hpos : (0 : ℝ) < n := lt_trans (Real.exp_pos _) hN
  have hlog : 2 + |d| < Real.log n := (Real.lt_log_iff_exp_lt hpos).2 hN
  have e1 : triG (Real.log n + d) = 0 :=
    triG_eq_zero (le_abs.2 (Or.inl (by linarith [neg_abs_le d])))
  have e2 : triG (-Real.log n + d) = 0 :=
    triG_eq_zero (le_abs.2 (Or.inr (by linarith [le_abs_self d])))
  simp [primeSummand, e1, e2]

/-- `primeTerm d > 0` for every lag `|d| ≤ 1` (the `n = 2` term alone is positive). -/
theorem primeTerm_pos {d : ℝ} (hd : |d| ≤ 1) : 0 < primeTerm d := by
  have hsum := primeSummand_summable d
  show 0 < ∑' n : ℕ, primeSummand d n
  refine hsum.tsum_pos (primeSummand_nonneg d) 2 ?_
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hd' := abs_le.1 hd
  have htri : 0 < triG (Real.log 2 + d) + triG (-Real.log 2 + d) := by
    rcases le_total 0 d with h | h
    · have := triG_pos_of_abs_le_one (y := -Real.log 2 + d) (abs_le.2 ⟨by linarith, by linarith⟩)
      linarith [triG_nonneg (Real.log 2 + d)]
    · have := triG_pos_of_abs_le_one (y := Real.log 2 + d) (abs_le.2 ⟨by linarith, by linarith⟩)
      linarith [triG_nonneg (-Real.log 2 + d)]
  unfold primeSummand
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  push_cast
  have : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  positivity

/-- **PrimeSupportVanish** (as a Prop): the prime term vanishes on some neighbourhood of lag 0,
i.e. small translates of ψ see no primes. -/
def PrimeSupportVanish : Prop := ∃ δ > 0, ∀ d : ℝ, |d| < δ → primeTerm d = 0

/-- **PROVED false** for the triangle ψ: `log 2 < 2 = half-width of supp g`. -/
theorem not_primeSupportVanish : ¬ PrimeSupportVanish := by
  rintro ⟨δ, hδ, h⟩
  have h0 := h 0 (by simpa using hδ)
  have := primeTerm_pos (d := 0) (by simp)
  linarith

/-! ## (C) Window stages and the assembly -/

/-- H_ψ restricted to configurations of spread at most `L` (**OPEN** for every `L > 0`).
On such configurations `Kψ` is evaluated only at `|d| ≤ L`, where only `n < e^{2+L}` enter. -/
def HPsiWindow (L : ℝ) : Prop :=
  ∀ (n : ℕ) (x c : Fin n → ℝ), (∀ i j, |x i - x j| ≤ L) →
    ∑ i, c i * Real.cosh (x i / 2) = 0 → 0 ≤ kform Kpsi x c

/-- **Named Prop (OPEN)**: the base case, positivity on some window of positive width.
It contains the primes `n < e^{2+L₀}` (at least `n = 2,3,4,5,7`): see `not_primeSupportVanish`. -/
def HPsiSmallSupport : Prop := ∃ L₀ > 0, HPsiWindow L₀

/-- **Named Prop (OPEN, RH-strength)**: the stage step, window doubling. Doubling `L` adds the
prime powers with `e^{2+L} ≤ n < e^{2+2L}`. -/
def HPsiStageStep : Prop := ∀ L > 0, HPsiWindow L → HPsiWindow (2 * L)

theorem hPsiWindow_mono {L L' : ℝ} (h : L ≤ L') (hw : HPsiWindow L') : HPsiWindow L :=
  fun n x c hx hc => hw n x c (fun i j => (hx i j).trans h) hc

theorem hPsiWindow_of_hPsi (h : HPsi) (L : ℝ) : HPsiWindow L :=
  fun n x c _ hc => h n x c hc

theorem hPsiWindow_pow {L₀ : ℝ} (hL₀ : 0 < L₀) (hb : HPsiWindow L₀) (hs : HPsiStageStep) :
    ∀ k : ℕ, HPsiWindow (2 ^ k * L₀) := by
  intro k
  induction k with
  | zero => simpa using hb
  | succ k ih =>
    have := hs (2 ^ k * L₀) (by positivity) ih
    rwa [pow_succ, mul_comm (2 ^ k : ℝ) 2, mul_assoc]

/-- **Assembly (PROVED)**: `HPsiSmallSupport → HPsiStageStep → HPsi`. -/
theorem hPsi_of_plan (hb : HPsiSmallSupport) (hs : HPsiStageStep) : HPsi := by
  obtain ⟨L₀, hL₀, hbase⟩ := hb
  intro n x c hc
  set S : ℝ := ∑ i, ∑ j, |x i - x j|
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (S / L₀) (one_lt_two : (1 : ℝ) < 2)
  have hSk : S ≤ 2 ^ k * L₀ := ((div_lt_iff₀ hL₀).1 hk).le
  refine hPsiWindow_pow hL₀ hbase hs k n x c (fun i j => ?_) hc
  have h1 : |x i - x j| ≤ ∑ j', |x i - x j'| :=
    Finset.single_le_sum (fun j' _ => abs_nonneg (x i - x j')) (Finset.mem_univ j)
  have h2 : ∑ j', |x i - x j'| ≤ S :=
    Finset.single_le_sum (f := fun i' => ∑ j', |x i' - x j'|)
      (fun i' _ => Finset.sum_nonneg fun j' _ => abs_nonneg _) (Finset.mem_univ i)
  linarith

/-- The plan is **equivalent** to H_ψ (PROVED): it neither weakens nor strengthens the target,
so `HPsiStageStep` carries the full strength of H_ψ. -/
theorem hPsi_iff_plan : HPsi ↔ HPsiSmallSupport ∧ HPsiStageStep :=
  ⟨fun h => ⟨⟨1, one_pos, hPsiWindow_of_hPsi h 1⟩, fun L _ _ => hPsiWindow_of_hPsi h (2 * L)⟩,
   fun h => hPsi_of_plan h.1 h.2⟩

end GppHPsiPlan

#print axioms GppHPsiPlan.poleRankOne
#print axioms GppHPsiPlan.kform_poleTerm_of_ker
#print axioms GppHPsiPlan.abelKernelPosDef
#print axioms GppHPsiPlan.primeTerm_pos
#print axioms GppHPsiPlan.not_primeSupportVanish
#print axioms GppHPsiPlan.hPsi_of_plan
#print axioms GppHPsiPlan.hPsi_iff_plan
