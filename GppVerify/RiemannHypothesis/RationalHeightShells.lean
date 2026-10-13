import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Rational height shells and integer-shell frequencies on the adelic solenoid

Source: Codex, GPP-bridge PR #11 comment 6138600589 and
`work/codex/2026-10-13_additive_adelic_solenoid_multiscale_trace.md` (Daniel Toupin's compact-`K`
idea, continued by Codex to the additive solenoid `X = 𝔸_ℚ/ℚ`, whose dual is `ℚ`).

Two exact finite statements from that note are formalized here, for the positive quadrant of `ℚ`.

**Height shells.** Put `H(a/b) = max a b` on reduced positive fractions (`reduced n` collects those
with `H ≤ n`).
* `reduced_lower`: **`36 · #reduced n ≥ 11 n²`**. The sieve bound uses
  `Σ_{d≥2} d⁻² ≤ 1/4 + 1/9 + Σ_{d≥4} 1/(d(d−1)) = 25/36` (`sum_inv_sq_le`).
* `shell_card_lower`: the dyadic shell `n < H ≤ 2n` has at least `2n²/9` elements.
* `shell_sum_lower`: each such shell contributes **`≥ 1/18`** to `Σ H⁻²`.
* `bounded_iff`: the partial sums of `Σ H^{−2σ}` are bounded **iff `σ > 1`**. Since `δ₀` has all
  Fourier coefficients `1`, this is the statement `δ₀ ∈ H_{−σ}(X) ⟺ σ > 1`, restricted to positive
  frequencies. The negative frequencies and `0` add a mirror copy and one term, so the threshold is
  unchanged; that bookkeeping is not formalized.

* `card_height_eq`: for `n ≥ 2` exactly `2φ(n)` reduced positive fractions have height `n`
  (`4φ(n)` over `ℚ`). So `Σ_q H(q)^{−s} = 4ζ(s−1)/ζ(s) − 1` and the height operator has compact
  resolvent; the Dirichlet-series identity itself is not formalized.

**Integer shells.** Every rational `q` lies in `Γ_j = (1/(j+1)!)ℤ` at level `j = q.den`
(`factorial_level`). At any level where `(j+1)! q ∈ ℤ` and `q ≠ 0`, the accelerated
frequency satisfies `|(j+1)! q| ≥ 1` (`one_le_abs_level`). So the multiscale inverse has
`|2π N_j q|⁻¹ ≤ 1/(2π)` uniformly over all of `ℚ`, with no prime cutoff (`inverse_bound`).

**Not formalized:** the solenoid itself, the shell projectors and their Parseval identity, the
Tate–Poisson periodization `Φ_a` and its norm identity, and the sign of the completed Weil form
(**OPEN**). The inverse is an auxiliary operator, not a physical Hamiltonian. **No RH claim.**
-/

namespace GppRationalHeightShells

open Finset

/-- Positive numerator/denominator pairs with both entries at most `n`. -/
def box (n : ℕ) : Finset (ℕ × ℕ) := Ioc 0 n ×ˢ Ioc 0 n

/-- Reduced positive fractions `a/b` with height `max a b ≤ n`. -/
def reduced (n : ℕ) : Finset (ℕ × ℕ) := (box n).filter (fun p => Nat.Coprime p.1 p.2)

/-- The projective height `H(a/b) = max a b`. -/
def height (p : ℕ × ℕ) : ℕ := max p.1 p.2

theorem card_box (n : ℕ) : (box n).card = n ^ 2 := by
  simp [box, card_product, sq]

theorem card_reduced_le (n : ℕ) : (reduced n).card ≤ n ^ 2 :=
  (card_filter_le _ _).trans (card_box n).le

theorem card_common_dvd (n d : ℕ) :
    ((box n).filter (fun p => d ∣ p.1 ∧ d ∣ p.2)).card = (n / d) ^ 2 := by
  rw [box, filter_product, card_product, Nat.Ioc_filter_dvd_card_eq_div, sq]

theorem nonreduced_subset (n : ℕ) :
    (box n).filter (fun p => ¬ Nat.Coprime p.1 p.2) ⊆
      (Icc 2 n).biUnion (fun d => (box n).filter (fun p => d ∣ p.1 ∧ d ∣ p.2)) := by
  intro p hp
  simp only [mem_filter, box, mem_product, mem_Ioc] at hp
  obtain ⟨⟨⟨ha0, han⟩, ⟨hb0, hbn⟩⟩, hcop⟩ := hp
  simp only [mem_biUnion, mem_Icc, mem_filter, box, mem_product, mem_Ioc]
  refine ⟨Nat.gcd p.1 p.2, ⟨?_, (Nat.gcd_le_left _ ha0).trans han⟩,
    ⟨⟨⟨ha0, han⟩, ⟨hb0, hbn⟩⟩, Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _⟩⟩
  have h0 : Nat.gcd p.1 p.2 ≠ 0 := (Nat.gcd_pos_of_pos_left _ ha0).ne'
  have h1 : Nat.gcd p.1 p.2 ≠ 1 := hcop
  omega

/-- `Σ_{2 ≤ d ≤ n} d⁻² ≤ 25/36`. -/
theorem sum_inv_sq_le (n : ℕ) : ∑ d ∈ Icc 2 n, ((d : ℝ) ^ 2)⁻¹ ≤ 25 / 36 := by
  have key : ∀ m : ℕ, ∑ d ∈ Icc 2 (m + 3), ((d : ℝ) ^ 2)⁻¹ ≤ 25 / 36 - ((m : ℝ) + 3)⁻¹ := by
    intro m
    induction m with
    | zero =>
      rw [show Icc 2 (0 + 3) = {2, 3} by decide]
      norm_num
    | succ k ih =>
      rw [show k + 1 + 3 = (k + 3) + 1 by ring, sum_Icc_succ_top (by omega)]
      have hx : (0 : ℝ) < (k : ℝ) + 3 := by positivity
      have hstep : ((((k + 3 + 1 : ℕ) : ℝ)) ^ 2)⁻¹ ≤ ((k : ℝ) + 3)⁻¹ - ((k : ℝ) + 3 + 1)⁻¹ := by
        have e : ((k : ℝ) + 3)⁻¹ - ((k : ℝ) + 3 + 1)⁻¹ = (((k : ℝ) + 3) * ((k : ℝ) + 3 + 1))⁻¹ := by
          field_simp
          ring
        rw [e]
        push_cast
        exact inv_anti₀ (by positivity) (by nlinarith)
      push_cast at ih hstep ⊢
      rw [show (k : ℝ) + 1 + 3 = (k : ℝ) + 3 + 1 by ring]
      linarith
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have := key m
    have : (0 : ℝ) ≤ ((m : ℝ) + 3)⁻¹ := by positivity
    linarith

/-- **The sieve lower bound** `36 · #reduced n ≥ 11 n²`. -/
theorem reduced_lower (n : ℕ) : 11 * (n : ℝ) ^ 2 ≤ 36 * (reduced n).card := by
  have hsplit := card_filter_add_card_filter_not (s := box n) (p := fun p => Nat.Coprime p.1 p.2)
  have hbad : (((box n).filter (fun p => ¬ Nat.Coprime p.1 p.2)).card : ℝ) ≤ 25 / 36 * n ^ 2 := by
    calc (((box n).filter (fun p => ¬ Nat.Coprime p.1 p.2)).card : ℝ)
        ≤ (((Icc 2 n).biUnion (fun d => (box n).filter (fun p => d ∣ p.1 ∧ d ∣ p.2))).card : ℝ) := by
          exact_mod_cast card_le_card (nonreduced_subset n)
      _ ≤ ∑ d ∈ Icc 2 n, (((box n).filter (fun p => d ∣ p.1 ∧ d ∣ p.2)).card : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ = ∑ d ∈ Icc 2 n, (((n / d : ℕ) : ℝ) ^ 2) := by
          simp_rw [card_common_dvd]
          push_cast
          rfl
      _ ≤ ∑ d ∈ Icc 2 n, ((n : ℝ) ^ 2 * ((d : ℝ) ^ 2)⁻¹) := by
          gcongr with d hd
          rw [← div_eq_mul_inv, ← div_pow]
          gcongr
          exact Nat.cast_div_le
      _ = (n : ℝ) ^ 2 * ∑ d ∈ Icc 2 n, ((d : ℝ) ^ 2)⁻¹ := by rw [mul_sum]
      _ ≤ (n : ℝ) ^ 2 * (25 / 36) := by gcongr; exact sum_inv_sq_le n
      _ = 25 / 36 * n ^ 2 := by ring
  have htot : ((reduced n).card : ℝ) +
      (((box n).filter (fun p => ¬ Nat.Coprime p.1 p.2)).card : ℝ) = (n : ℝ) ^ 2 := by
    rw [card_box] at hsplit
    have h' : (reduced n).card + ((box n).filter (fun p => ¬ Nat.Coprime p.1 p.2)).card = n ^ 2 :=
      hsplit
    exact_mod_cast h'
  linarith

/-- The dyadic height shell `n < H ≤ 2n`. -/
def shell (n : ℕ) : Finset (ℕ × ℕ) := (reduced (2 * n)).filter (fun p => n < height p)

theorem reduced_filter_not (n : ℕ) :
    (reduced (2 * n)).filter (fun p => ¬ n < height p) = reduced n := by
  ext ⟨a, b⟩
  simp only [reduced, box, height, mem_filter, mem_product, mem_Ioc, not_lt, max_le_iff]
  constructor
  · rintro ⟨⟨⟨⟨h1, _⟩, h3, _⟩, hc⟩, h5, h6⟩
    exact ⟨⟨⟨h1, h5⟩, h3, h6⟩, hc⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, hc⟩
    exact ⟨⟨⟨⟨h1, by omega⟩, h3, by omega⟩, hc⟩, h2, h4⟩

theorem card_shell (n : ℕ) : (shell n).card + (reduced n).card = (reduced (2 * n)).card := by
  have h := card_filter_add_card_filter_not (s := reduced (2 * n)) (p := fun p => n < height p)
  rw [reduced_filter_not] at h
  exact h

/-- **The dyadic shell count**: `9 · #shell n ≥ 2n²`. -/
theorem shell_card_lower (n : ℕ) : 2 * (n : ℝ) ^ 2 ≤ 9 * (shell n).card := by
  have h2 := reduced_lower (2 * n)
  have h1 : ((reduced n).card : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast card_reduced_le n
  have hs : ((shell n).card : ℝ) + (reduced n).card = (reduced (2 * n)).card := by
    exact_mod_cast card_shell n
  push_cast at h2
  nlinarith

/-- **Each dyadic shell contributes at least `1/18` to `Σ H⁻²`.** -/
theorem shell_sum_lower {n : ℕ} (hn : 0 < n) :
    1 / 18 ≤ ∑ p ∈ shell n, (((height p : ℕ) : ℝ) ^ 2)⁻¹ := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hterm : ∀ p ∈ shell n, ((2 * (n : ℝ)) ^ 2)⁻¹ ≤ (((height p : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro p hp
    rw [shell, mem_filter] at hp
    obtain ⟨hp, hlt⟩ := hp
    rw [reduced, mem_filter, box, mem_product, mem_Ioc, mem_Ioc] at hp
    obtain ⟨⟨⟨_, ha⟩, _, hb⟩, _⟩ := hp
    rw [height] at hlt
    have hle : ((max p.1 p.2 : ℕ) : ℝ) ≤ 2 * n := by exact_mod_cast max_le ha hb
    have hpos : (0 : ℝ) < ((max p.1 p.2 : ℕ) : ℝ) := by
      have : 0 < max p.1 p.2 := by omega
      exact_mod_cast this
    show ((2 * (n : ℝ)) ^ 2)⁻¹ ≤ (((max p.1 p.2 : ℕ) : ℝ) ^ 2)⁻¹
    exact inv_anti₀ (by positivity) (by gcongr)
  calc (1 : ℝ) / 18 ≤ (shell n).card * ((2 * (n : ℝ)) ^ 2)⁻¹ := by
        rw [show (2 * (n : ℝ)) ^ 2 = 4 * n ^ 2 by ring, ← div_eq_mul_inv,
          le_div_iff₀ (by positivity)]
        linarith [shell_card_lower n]
    _ = ∑ p ∈ shell n, ((2 * (n : ℝ)) ^ 2)⁻¹ := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := sum_le_sum hterm

/-- **Dyadic divergence**: up to height `2^k`, `Σ H⁻² ≥ k/18`. -/
theorem dyadic_sum_lower (k : ℕ) :
    (k : ℝ) / 18 ≤ ∑ p ∈ reduced (2 ^ k), (((height p : ℕ) : ℝ) ^ 2)⁻¹ := by
  induction k with
  | zero => simpa using sum_nonneg (fun p _ => by positivity)
  | succ k ih =>
    have hsplit := sum_filter_add_sum_filter_not (reduced (2 * 2 ^ k)) (fun p => 2 ^ k < height p)
      (fun p => (((height p : ℕ) : ℝ) ^ 2)⁻¹)
    rw [reduced_filter_not] at hsplit
    rw [pow_succ, mul_comm, ← hsplit]
    have := shell_sum_lower (n := 2 ^ k) (by positivity)
    rw [shell] at this
    push_cast
    linarith

/-- **At `σ = 1` the partial sums are unbounded.** -/
theorem not_bounded : ¬ ∃ C : ℝ, ∀ n, ∑ p ∈ reduced n, (((height p : ℕ) : ℝ) ^ 2)⁻¹ ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨k, hk⟩ := exists_nat_gt (18 * C)
  have := (dyadic_sum_lower k).trans (hC _)
  have : (k : ℝ) ≤ 18 * C := by linarith
  linarith

theorem bounded_of_one_lt {σ : ℝ} (hσ : 1 < σ) :
    ∃ C : ℝ, ∀ n, ∑ p ∈ reduced n, (((height p : ℕ) : ℝ) ^ (2 * σ))⁻¹ ≤ C := by
  have hs : Summable (fun a : ℕ => ((a : ℝ) ^ σ)⁻¹) := Real.summable_nat_rpow_inv.mpr hσ
  refine ⟨(∑' a : ℕ, ((a : ℝ) ^ σ)⁻¹) ^ 2, fun n => ?_⟩
  have hterm : ∀ p ∈ box n,
      (((height p : ℕ) : ℝ) ^ (2 * σ))⁻¹ ≤ ((p.1 : ℝ) ^ σ)⁻¹ * ((p.2 : ℝ) ^ σ)⁻¹ := by
    intro p hp
    simp only [box, mem_product, mem_Ioc] at hp
    have ha : (0 : ℝ) < p.1 := by exact_mod_cast hp.1.1
    have hb : (0 : ℝ) < p.2 := by exact_mod_cast hp.2.1
    have hah : (p.1 : ℝ) ≤ ((height p : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
    have hbh : (p.2 : ℝ) ≤ ((height p : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    rw [← mul_inv]
    apply inv_anti₀ (by positivity)
    rw [show 2 * σ = σ + σ by ring, Real.rpow_add (by linarith)]
    have h0 : (0 : ℝ) ≤ σ := by linarith
    exact mul_le_mul (Real.rpow_le_rpow ha.le hah h0) (Real.rpow_le_rpow hb.le hbh h0)
      (by positivity) (by positivity)
  calc ∑ p ∈ reduced n, (((height p : ℕ) : ℝ) ^ (2 * σ))⁻¹
      ≤ ∑ p ∈ box n, (((height p : ℕ) : ℝ) ^ (2 * σ))⁻¹ :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ ≤ ∑ p ∈ box n, ((p.1 : ℝ) ^ σ)⁻¹ * ((p.2 : ℝ) ^ σ)⁻¹ := sum_le_sum hterm
    _ = (∑ a ∈ Ioc 0 n, ((a : ℝ) ^ σ)⁻¹) ^ 2 := by rw [box, sum_product, sq, sum_mul_sum]
    _ ≤ (∑' a : ℕ, ((a : ℝ) ^ σ)⁻¹) ^ 2 := by
        gcongr
        · exact sum_nonneg (fun _ _ => by positivity)
        · exact hs.sum_le_tsum _ (fun _ _ => by positivity)

/-- **`δ₀ ∈ H_{−σ}` threshold** (positive frequencies): bounded partial sums iff `σ > 1`. -/
theorem bounded_iff (σ : ℝ) :
    (∃ C : ℝ, ∀ n, ∑ p ∈ reduced n, (((height p : ℕ) : ℝ) ^ (2 * σ))⁻¹ ≤ C) ↔ 1 < σ := by
  refine ⟨fun ⟨C, hC⟩ => ?_, bounded_of_one_lt⟩
  refine (le_or_gt σ 1).elim (fun hσ => ?_) id
  exfalso
  apply not_bounded
  refine ⟨C, fun n => (sum_le_sum fun p hp => ?_).trans (hC n)⟩
  simp only [reduced, box, mem_filter, mem_product, mem_Ioc] at hp
  have h1 : (1 : ℝ) ≤ ((height p : ℕ) : ℝ) := by
    have : 1 ≤ max p.1 p.2 := le_max_of_le_left hp.1.1.1
    exact_mod_cast this
  apply inv_anti₀ (by positivity)
  calc ((height p : ℕ) : ℝ) ^ (2 * σ) ≤ ((height p : ℕ) : ℝ) ^ ((2 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by push_cast; linarith)
    _ = ((height p : ℕ) : ℝ) ^ 2 := Real.rpow_natCast _ 2

theorem mem_reduced {n : ℕ} {p : ℕ × ℕ} :
    p ∈ reduced n ↔ ((0 < p.1 ∧ p.1 ≤ n) ∧ (0 < p.2 ∧ p.2 ≤ n)) ∧ Nat.Coprime p.1 p.2 := by
  rw [reduced, mem_filter, box, mem_product, mem_Ioc, mem_Ioc]

/-- **Height multiplicity** (positive quadrant): for `n ≥ 2` exactly `2φ(n)` reduced fractions
have height `n`, namely `a/n` and `n/a` with `a < n` coprime to `n`. Over all of `ℚ` the signs
double this to `4φ(n)`, as in Codex's note. -/
theorem card_height_eq {n : ℕ} (hn : 2 ≤ n) :
    ((reduced n).filter (fun p => height p = n)).card = 2 * Nat.totient n := by
  set T := (Ioc 0 n).filter (fun a => n.Coprime a) with hTdef
  have hT : T.card = Nat.totient n := by
    rw [hTdef, show Ioc 0 n = Ico 1 (1 + n) by ext x; simp; omega]
    exact Nat.filter_coprime_Ico_eq_totient n 1
  have hsplit : (reduced n).filter (fun p => height p = n) =
      T.image (fun a => (a, n)) ∪ T.image (fun b => (n, b)) := by
    ext ⟨a, b⟩
    rw [mem_union, mem_filter, mem_reduced]
    simp only [hTdef, height, mem_filter, mem_Ioc, mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨⟨ha0, han⟩, hb0, hbn⟩, hc⟩, hmax⟩
      rcases le_total a b with h | h
      · have hb : b = n := by rwa [max_eq_right h] at hmax
        exact Or.inl ⟨a, ⟨⟨ha0, han⟩, hb ▸ hc.symm⟩, rfl, hb.symm⟩
      · have ha : a = n := by rwa [max_eq_left h] at hmax
        exact Or.inr ⟨b, ⟨⟨hb0, hbn⟩, ha ▸ hc⟩, ha.symm, rfl⟩
    · rintro (⟨x, ⟨⟨hx0, hxn⟩, hc⟩, rfl, rfl⟩ | ⟨x, ⟨⟨hx0, hxn⟩, hc⟩, rfl, rfl⟩)
      · exact ⟨⟨⟨⟨hx0, hxn⟩, by omega, le_rfl⟩, hc.symm⟩, max_eq_right hxn⟩
      · exact ⟨⟨⟨⟨by omega, le_rfl⟩, hx0, hxn⟩, hc⟩, max_eq_left hxn⟩
  have hdisj : Disjoint (T.image (fun a => (a, n))) (T.image (fun b => (n, b))) := by
    rw [disjoint_left]
    rintro p hp1 hp2
    simp only [mem_image] at hp1 hp2
    obtain ⟨x, hx, rfl⟩ := hp1
    obtain ⟨y, _, hy⟩ := hp2
    simp only [Prod.mk.injEq] at hy
    rw [hTdef, mem_filter, ← hy.1] at hx
    have := (Nat.coprime_self n).mp hx.2
    omega
  rw [hsplit, card_union_of_disjoint hdisj,
    card_image_of_injective _ (fun x y h => (Prod.mk.inj h).1),
    card_image_of_injective _ (fun x y h => (Prod.mk.inj h).2), hT]
  ring

/-- Every rational appears at a factorial level: `(q.den + 1)! · q` is the integer
`((q.den + 1)! / q.den) · q.num`. -/
theorem factorial_level (q : ℚ) :
    ((q.den + 1).factorial : ℚ) * q = ((((q.den + 1).factorial / q.den : ℕ) : ℤ) * q.num : ℤ) := by
  obtain ⟨c, hc⟩ := Nat.dvd_factorial q.den_pos (Nat.le_succ q.den)
  rw [hc, Nat.mul_div_cancel_left c q.den_pos]
  push_cast
  rw [show (q.den : ℚ) * c * q = c * (q * q.den) by ring, Rat.mul_den_eq_num]

/-- **Integer-shell frequency**: a nonzero rational accelerated into `ℤ` has modulus `≥ 1`. -/
theorem one_le_abs_level {q N : ℚ} (hq : q ≠ 0) (hN : N ≠ 0) {k : ℤ} (hk : N * q = k) :
    1 ≤ |N * q| := by
  rw [hk]
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, mul_eq_zero] at hk
    tauto
  exact_mod_cast Int.one_le_abs hk0

/-- **Uniform inverse bound**: an eigenvalue `2π x` with `|x| ≥ 1` has `|2π x|⁻¹ ≤ 1/(2π)`. -/
theorem inverse_bound {x : ℝ} (hx : 1 ≤ |x|) : |2 * Real.pi * x|⁻¹ ≤ (2 * Real.pi)⁻¹ := by
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  apply inv_anti₀ (by positivity)
  nlinarith [Real.pi_pos]

/-- The multiscale inverse is uniformly bounded over every nonzero rational frequency. -/
theorem level_inverse_bound {q : ℚ} (hq : q ≠ 0) :
    |2 * Real.pi * ((((q.den + 1).factorial : ℚ) * q : ℚ) : ℝ)|⁻¹ ≤ (2 * Real.pi)⁻¹ := by
  have hk := factorial_level q
  have hN : ((q.den + 1).factorial : ℚ) ≠ 0 := by positivity
  apply inverse_bound
  have := one_le_abs_level hq hN hk
  rw [← Rat.cast_abs]
  exact_mod_cast this

end GppRationalHeightShells
