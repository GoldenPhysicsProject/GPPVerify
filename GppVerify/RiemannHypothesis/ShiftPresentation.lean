import GppVerify.RiemannHypothesis.ShiftSeriesNorm

/-!
# The shift presentation of the Weil form: per-prime identity (I1), regrouping (I2), and OB-6

Build order (i)–(ii) of Turbo's final-identity entry (bridge `b38417e`; note
`final-identity-candidate-2026-11-15.md`), as exact algebra over in-tree objects (`weilForm`, `autocorr`,
`poleTerm`, `archimedeanTerm`, `primeSide`, Mathlib's `vonMangoldt`).

* `phi p g = Σ_{m≥0} p^{−m/2} g(· − m log p)`, the canonical local map; `phiNormSq p g = ‖Φ_p g‖²`.
* **I1 `primeTermP_eq`** (per-prime identity). For a prime `p` and continuous compactly supported `g`,
  `Σ_{k≥1} log p · p^{−k/2}(A(k log p) + A(−k log p)) = (log p)(1 − p^{−1})‖Φ_p g‖² − (log p)‖g‖²`,
  `A = autocorr g`: a Gram form **minus a per-prime mass defect** `(log p)‖g‖²` (Meyer's minus sign,
  localised). The analytic core is `ShiftSeriesNorm.norm_sq_shiftSeries`.
* **`sum_vonMangoldt_eq_sum_primes`**: the finite prime side `Σ_{n≤N} Λ(n)/√n (…)` regrouped by primes.
* **I2 `weilForm_regrouped`**: for `g` supported in `[−L/2, L/2]` and `L < log(N+1)`,
  `weilForm(autocorr g) = poleTerm + archimedeanTerm + (Σ_{p≤N} log p)‖g‖² − Σ_{p≤N} (log p)(1−p^{−1})‖Φ_p g‖²`.
* **`OB6At L` / `OB6`** (a definition): the archimedean block plus the mass defect dominates the finite Gram
  sum, at width `L` / at every width. No appeal to `SemilocalArchDomAll`, `H_ψ`, `WeilIsGram` — none has an
  in-tree definition or an in-tree equivalence with this statement.
* **`arp_iff_ob6`**: `ArithmeticReflectionPositivity ↔ OB6`, a derivation from I2.

**What this is not.** OB-6 is *not* proved: it is `ARP` restated in the shift presentation, so it is exactly
as open as ARP. No `sorry`, no axiom.
-/

open MeasureTheory
open GppArithmeticReflection GppArchimedeanFloor
open scoped ContDiff

noncomputable section

namespace GppShiftPresentation

/-! ### The canonical local map and the per-prime term -/

/-- **The canonical local map** `Φ_p g = Σ_{m≥0} p^{−m/2} g(· − m log p)`. -/
def phi (p : ℕ) (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∑' m : ℕ, (p : ℝ) ^ (-(m : ℝ) / 2) * g (y - m * Real.log p)

/-- `‖Φ_p g‖²`. -/
def phiNormSq (p : ℕ) (g : ℝ → ℝ) : ℝ := ∫ y, (phi p g y) ^ 2

/-- The per-prime term of the prime side, for a function `A`:
`Σ_{k≥1} log p · p^{−k/2} · (A(k log p) + A(−k log p))`. -/
def primeTermP (p : ℕ) (A : ℝ → ℝ) : ℝ :=
  ∑' k : ℕ, Real.log p * (p : ℝ) ^ (-((k : ℝ) + 1) / 2) *
    (A (((k : ℝ) + 1) * Real.log p) + A (-(((k : ℝ) + 1) * Real.log p)))

/-- `q = p^{−1/2}`. -/
def qOf (p : ℕ) : ℝ := (p : ℝ) ^ (-(1 / 2 : ℝ))

theorem qOf_pos {p : ℕ} (hp : 2 ≤ p) : 0 < qOf p :=
  Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < p)) _

theorem qOf_lt_one {p : ℕ} (hp : 2 ≤ p) : qOf p < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < p)) (by norm_num)

theorem qOf_pow {p : ℕ} (hp : 2 ≤ p) (m : ℝ) :
    (p : ℝ) ^ (-m / 2) = qOf p ^ m := by
  have hp0 : (0 : ℝ) ≤ p := by positivity
  unfold qOf
  rw [← Real.rpow_mul hp0]
  congr 1; ring

theorem qOf_pow_nat {p : ℕ} (hp : 2 ≤ p) (m : ℕ) :
    (p : ℝ) ^ (-(m : ℝ) / 2) = qOf p ^ m := by
  rw [qOf_pow hp, Real.rpow_natCast]

theorem qOf_sq {p : ℕ} (hp : 2 ≤ p) : qOf p ^ 2 = 1 / (p : ℝ) := by
  have := qOf_pow_nat hp 2
  rw [← this]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  rw [show -((2 : ℕ) : ℝ) / 2 = -1 by norm_num, Real.rpow_neg_one, one_div]

theorem phi_eq {p : ℕ} (hp : 2 ≤ p) (g : ℝ → ℝ) :
    phi p g = shiftSeries (qOf p) (Real.log p) g := by
  funext y
  unfold phi shiftSeries
  exact tsum_congr fun m => by rw [qOf_pow_nat hp]

/-- **I1 (the per-prime identity).** For a prime `p` and a continuous compactly supported `g`,
`Σ_{k≥1} log p · p^{−k/2} (A(k log p) + A(−k log p)) = (log p)(1 − p^{−1}) ‖Φ_p g‖² − (log p) ‖g‖²`,
`A = autocorr g`, `‖g‖² = A(0)`. The per-prime Weil term is a Gram form minus a per-prime mass defect. -/
theorem primeTermP_eq {p : ℕ} (hp : p.Prime) {g : ℝ → ℝ} (hg : Continuous g)
    (hc : HasCompactSupport g) :
    primeTermP p (autocorr g) =
      Real.log p * (1 - 1 / (p : ℝ)) * phiNormSq p g - Real.log p * autocorr g 0 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hq0 := qOf_pos hp2
  have hq1 := qOf_lt_one hp2
  have key := norm_sq_shiftSeries (ℓ := Real.log p) hg hc hq0 hq1
  have hnorm : phiNormSq p g = ∫ y, (shiftSeries (qOf p) (Real.log p) g y) ^ 2 := by
    unfold phiNormSq; rw [phi_eq hp2]
  have hterm : ∀ k : ℕ, Real.log p * (p : ℝ) ^ (-((k : ℝ) + 1) / 2) *
      (autocorr g (((k : ℝ) + 1) * Real.log p) + autocorr g (-(((k : ℝ) + 1) * Real.log p))) =
      2 * Real.log p * (qOf p ^ (k + 1) * autocorr g (((k : ℝ) + 1) * Real.log p)) := by
    intro k
    have h1 : (p : ℝ) ^ (-((k : ℝ) + 1) / 2) = qOf p ^ (k + 1) := by
      have := qOf_pow_nat hp2 (k + 1)
      rw [← this]; push_cast; ring_nf
    rw [h1, autocorr_neg]; ring
  rw [qOf_sq hp2] at key
  unfold primeTermP
  simp_rw [hterm]
  rw [tsum_mul_left, hnorm]
  linear_combination (-Real.log p) * key

/-! ### Regrouping the prime side by primes -/

open ArithmeticFunction in
/-- The `(p, k)` term of the prime side at `n = p^{k+1}`. -/
theorem vonMangoldt_term_prime_pow {p : ℕ} (hp : p.Prime) (A : ℝ → ℝ) (k : ℕ) :
    (Λ (p ^ (k + 1)) / Real.sqrt ((p ^ (k + 1) : ℕ) : ℝ)) *
        (A (Real.log ((p ^ (k + 1) : ℕ) : ℝ)) + A (-Real.log ((p ^ (k + 1) : ℕ) : ℝ))) =
      Real.log p * (p : ℝ) ^ (-((k : ℝ) + 1) / 2) *
        (A (((k : ℝ) + 1) * Real.log p) + A (-(((k : ℝ) + 1) * Real.log p))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hΛ : Λ (p ^ (k + 1)) = Real.log p := by
    rw [vonMangoldt_apply_pow (Nat.succ_ne_zero k), vonMangoldt_apply_prime hp]
  have hsq : Real.sqrt ((p ^ (k + 1) : ℕ) : ℝ) = (p : ℝ) ^ (((k : ℝ) + 1) / 2) := by
    rw [Real.sqrt_eq_rpow, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    congr 1; push_cast; ring
  have hlog : Real.log ((p ^ (k + 1) : ℕ) : ℝ) = ((k : ℝ) + 1) * Real.log p := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
  rw [hΛ, hsq, hlog, show -((k : ℝ) + 1) / 2 = -(((k : ℝ) + 1) / 2) by ring, Real.rpow_neg hp0.le]
  ring

/-- **The prime side regrouped by primes.** If `A(log n) + A(−log n) = 0` for all `n > N`, then
`Σ_{n ≤ N} Λ(n)/√n · (A(log n) + A(−log n)) = Σ_{p ≤ N prime} Σ_{k ≥ 1} log p · p^{−k/2} · (…)`. -/
theorem sum_vonMangoldt_eq_sum_primes (A : ℝ → ℝ) (N : ℕ)
    (hvan : ∀ n : ℕ, N < n → A (Real.log n) + A (-Real.log n) = 0) :
    ∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        (A (Real.log n) + A (-Real.log n)) =
      ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, primeTermP p A := by
  classical
  set P := (Finset.range (N + 1)).filter Nat.Prime with hP
  set tt : ℕ → ℕ → ℝ := fun p k => Real.log p * (p : ℝ) ^ (-((k : ℝ) + 1) / 2) *
    (A (((k : ℝ) + 1) * Real.log p) + A (-(((k : ℝ) + 1) * Real.log p))) with htt
  have hfin : ∀ p ∈ P, primeTermP p A = ∑ k ∈ Finset.range N, tt p k := by
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    unfold primeTermP
    apply tsum_eq_sum
    intro k hk
    have hk' : N ≤ k := by simpa using hk
    have hlt : N < p ^ (k + 1) :=
      lt_of_le_of_lt hk' (lt_trans (Nat.lt_succ_self k) (Nat.lt_pow_self hpp.one_lt))
    have h1 := vonMangoldt_term_prime_pow hpp A k
    rw [Nat.cast_pow] at h1
    have h2 := hvan _ hlt
    rw [Nat.cast_pow] at h2
    rw [← h1, h2, mul_zero]
  rw [Finset.sum_congr rfl hfin, Finset.sum_sigma']
  symm
  refine Finset.sum_bij_ne_zero (fun x _ _ => x.1 ^ (x.2 + 1)) ?_ ?_ ?_ ?_
  · intro x hx hne
    obtain ⟨hxp, hxk⟩ := Finset.mem_sigma.mp hx
    have hpp : x.1.Prime := (Finset.mem_filter.mp hxp).2
    rw [Finset.mem_range]
    by_contra hcon
    have hlt : N < x.1 ^ (x.2 + 1) := by omega
    apply hne
    have h1 := vonMangoldt_term_prime_pow hpp A x.2
    rw [Nat.cast_pow] at h1
    have h2 := hvan _ hlt
    rw [Nat.cast_pow] at h2
    simp only [htt]
    rw [← h1, h2, mul_zero]
  · intro a ha _ b hb _ hab
    have hap : a.1.Prime := (Finset.mem_filter.mp (Finset.mem_sigma.mp ha).1).2
    have hbp : b.1.Prime := (Finset.mem_filter.mp (Finset.mem_sigma.mp hb).1).2
    have h1 : a.1 = b.1 := by
      have e1 : (a.1 ^ (a.2 + 1)).minFac = a.1 := hap.pow_minFac (Nat.succ_ne_zero _)
      have e2 : (b.1 ^ (b.2 + 1)).minFac = b.1 := hbp.pow_minFac (Nat.succ_ne_zero _)
      rw [← e1, ← e2, hab]
    have h2 : a.2 = b.2 := by
      have e1 : (a.1 ^ (a.2 + 1)).factorization a.1 = a.2 + 1 := by
        rw [hap.factorization_pow]; simp
      have e2 : (b.1 ^ (b.2 + 1)).factorization b.1 = b.2 + 1 := by
        rw [hbp.factorization_pow]; simp
      have := congrArg (fun n => n.factorization a.1) hab
      simp only [e1] at this
      rw [h1] at this
      omega
    exact Sigma.ext h1 (heq_of_eq h2)
  · intro n hn hne
    have hΛ : ArithmeticFunction.vonMangoldt n ≠ 0 := by
      intro h; apply hne; rw [h]; simp
    have hpp : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
    obtain ⟨p, k, hp, hk, hnk⟩ := (isPrimePow_nat_iff n).mp hpp
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    subst hnk
    have hnN : p ^ (j + 1) < N + 1 := Finset.mem_range.mp hn
    have hpN : p ≤ N := by
      have := Nat.le_self_pow (n := j + 1) (by omega) p
      omega
    have hjN : j < N := by
      have h1 : j + 1 < p ^ (j + 1) := Nat.lt_pow_self hp.one_lt
      omega
    have hmem : (⟨p, j⟩ : Σ _ : ℕ, ℕ) ∈ P.sigma (fun _ => Finset.range N) :=
      Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by show p < N + 1; omega), hp⟩,
        Finset.mem_range.mpr hjN⟩
    have h1 := vonMangoldt_term_prime_pow hp A j
    refine ⟨⟨p, j⟩, hmem, ?_, rfl⟩
    simp only [htt]
    rw [← h1]
    exact hne
  · intro x hx hne
    obtain ⟨hxp, hxk⟩ := Finset.mem_sigma.mp hx
    have hpp : x.1.Prime := (Finset.mem_filter.mp hxp).2
    have h1 := vonMangoldt_term_prime_pow hpp A x.2
    simp only [htt]
    rw [← h1]

/-! ### I2: the regrouped Weil form; OB-6 -/

/-- The primes up to `N`. -/
def primesUpTo (N : ℕ) : Finset ℕ := (Finset.range (N + 1)).filter Nat.Prime

/-- The finite Gram sum `Σ_{p ≤ N} (log p)(1 − p^{−1}) ‖Φ_p g‖²`. -/
def shiftGramSum (N : ℕ) (g : ℝ → ℝ) : ℝ :=
  ∑ p ∈ primesUpTo N, Real.log p * (1 - 1 / (p : ℝ)) * phiNormSq p g

/-- The total mass defect `(Σ_{p ≤ N} log p) ‖g‖²`. -/
def massDefectSum (N : ℕ) (g : ℝ → ℝ) : ℝ := (∑ p ∈ primesUpTo N, Real.log p) * autocorr g 0

/-- **I2 (the regrouped identity).** For a test function supported in `[−L/2, L/2]` and `N` with
`L < log(N+1)`:
`weilForm(g ⋆ g̃) = poleTerm + archimedeanTerm + (Σ_{p≤N} log p)‖g‖² − Σ_{p≤N} (log p)(1−p^{−1})‖Φ_p g‖²`.
The primes enter only as norms of explicit shift operators. -/
theorem weilForm_regrouped {g : ℝ → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) {L : ℝ}
    (hsupp : ∀ y : ℝ, L / 2 < |y| → g y = 0) {N : ℕ} (hN : L < Real.log (N + 1)) :
    weilForm (autocorr g) = poleTerm (autocorr g) + archimedeanTerm (autocorr g) +
      massDefectSum N g - shiftGramSum N g := by
  have hsupA := autocorr_hasSupportIn hsupp
  have hvan : ∀ n : ℕ, N < n → autocorr g (Real.log n) + autocorr g (-Real.log n) = 0 := by
    intro n hn
    have hn' : ((N + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : Real.log (N + 1) ≤ Real.log n := by
      have := Real.log_le_log (by positivity) hn'
      simpa using this
    have hl0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have h1 : autocorr g (Real.log n) = 0 := hsupA _ (by rw [abs_of_nonneg hl0]; linarith)
    have h2 : autocorr g (-Real.log n) = 0 := hsupA _ (by rw [abs_neg, abs_of_nonneg hl0]; linarith)
    rw [h1, h2, add_zero]
  rw [weilForm_eq_truncation hsupp hN, sum_vonMangoldt_eq_sum_primes _ N hvan]
  have hper : ∀ p ∈ primesUpTo N, primeTermP p (autocorr g) =
      Real.log p * (1 - 1 / (p : ℝ)) * phiNormSq p g - Real.log p * autocorr g 0 := fun p hp =>
    primeTermP_eq (Finset.mem_filter.mp hp).2 hg hc
  unfold primesUpTo at hper
  rw [Finset.sum_congr rfl hper, Finset.sum_sub_distrib, ← Finset.sum_mul]
  unfold massDefectSum shiftGramSum primesUpTo
  ring

/-- **OB-6 at width `L`** (shift presentation): the archimedean block (pole + gamma factor) together
with the total mass defect dominates the finite Gram sum, for every test function supported in
`[−L/2, L/2]` and every cutoff `N` with `L < log(N+1)`.
-/
def OB6At (L : ℝ) : Prop :=
  ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → (∀ y : ℝ, L / 2 < |y| → g y = 0) →
    ∀ N : ℕ, L < Real.log (N + 1) →
      shiftGramSum N g ≤ poleTerm (autocorr g) + archimedeanTerm (autocorr g) + massDefectSum N g

/-- **OB-6**: the domination at every width. -/
def OB6 : Prop := ∀ L : ℝ, OB6At L

/-- **`ARP ⇔ OB-6`.** A derivation from I2, not an assertion: positivity of the Weil form at every
width is the domination of the finite Gram sum by the archimedean block plus the mass defect.
Both sides are OPEN. -/
theorem arp_iff_ob6 : ArithmeticReflectionPositivity ↔ OB6 := by
  constructor
  · intro harp L g hg hc hsupp N hN
    have h0 := harp g hg hc
    have h2 := weilForm_regrouped hg.continuous hc hsupp hN
    linarith
  · intro hob g hg hc
    obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℝ)
    have hsupp : ∀ y : ℝ, (2 * |R|) / 2 < |y| → g y = 0 := by
      intro y hy
      by_contra hne
      have hy' : y ∈ Metric.closedBall (0 : ℝ) R := hR (subset_tsupport _ hne)
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hy'
      linarith [le_abs_self R]
    obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 * |R| < Real.log (N + 1) := by
      refine ⟨⌈Real.exp (2 * |R|)⌉₊, ?_⟩
      rw [Real.lt_log_iff_exp_lt (by positivity)]
      have := Nat.le_ceil (Real.exp (2 * |R|))
      linarith
    have h1 := hob (2 * |R|) g hg hc hsupp N hN
    have h2 := weilForm_regrouped hg.continuous hc hsupp hN
    linarith

end GppShiftPresentation

#print axioms GppShiftPresentation.primeTermP_eq
#print axioms GppShiftPresentation.sum_vonMangoldt_eq_sum_primes
#print axioms GppShiftPresentation.weilForm_regrouped
#print axioms GppShiftPresentation.arp_iff_ob6
