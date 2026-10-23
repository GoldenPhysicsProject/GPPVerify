import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Last-coordinate pivots: monotonicity, coercive floors, and why a constant barrier fails

Source: Astra, `work/2026-10-23_astra_pivot_floor_obstruction.md` §2–§3 (GPP-bridge), answering
Turbo's push P3 (the constant scalar barrier (SBC)). Daniel Toupin / Golden Physics Project, with
AI assistance from Astra (statements and proofs) and Claude Code (formalization).

For a quadratic form `A` on `ℝ^K` (coordinates `0, …, K−1`), its last-coordinate pivot is
`s(A) = inf { A(v) : v_{K−1} = 1 }`, the Schur/Haynsworth pivot of the bordering step.

* `pivot_le_of_le`: Loewner order passes to pivots, `A ≤ B ⇒ s(A) ≤ s(B)`.
* `le_pivot_of_coercive`: if `A(v) ≥ d ∑ v_i²` then `s(A) ≥ d`, because `v_{K−1} = 1` forces
  `∑ v_i² ≥ 1`.
* `toeplitzPivot_antitone`: for a positive semidefinite Toeplitz kernel `q(i − j)`, the pivots
  `t_K` are nonincreasing in `K`. Shifting a competitor one slot to the right gives a competitor
  at size `K + 1` with the same value. This is Astra's "shift the predictor" argument.
* `tendsto_zero_of_antitone_of_root`: if positive nonincreasing `t_j` have
  `(∏_{j<K} t_j)^{1/K} → 0`, then `t_K → 0`.
* `no_constant_barrier`: if `0 < s_K ≤ 2 t_K` with `t_K → 0`, and the comparison pivots satisfy
  `s^Δ_K ≥ d > 0`, then no fixed `c > 0` has `s_K ≥ c s^Δ_K` for all `K`.

**Scope.** Astra's spectral input is not formalized. That input is: under RH the packet kernel is
a pure-point measure, so the Ky Fan bound gives `(det Q_K)^{1/K} → 0`, with `det Q_K = ∏ t_j`.
Without it, the constant-barrier refutation here is conditional on `t_K → 0`. Nothing here rules
out a moving barrier `c_K > 0` or the all-positive-pivot route. No claim about RH.
-/

open Filter Topology Finset

namespace GppPivotFloor

/-- The last-coordinate pivot of a quadratic form `A` on `ℝ^K`, as the infimum of `A(v)` over
`v` with `v_{K−1} = 1` (coordinates outside `0, …, K−1` are ignored by `A`). -/
noncomputable def pivot (A : (ℕ → ℝ) → ℝ) (K : ℕ) : ℝ :=
  sInf (A '' {v : ℕ → ℝ | v (K - 1) = 1})

lemma competitors_nonempty (K : ℕ) : (A : (ℕ → ℝ) → ℝ) →
    (A '' {v : ℕ → ℝ | v (K - 1) = 1}).Nonempty := fun A =>
  ⟨A fun _ => 1, ⟨fun _ => 1, rfl, rfl⟩⟩

/-- **Loewner monotonicity.** If `A ≤ B` pointwise and `A` is bounded below on competitors, then
`s(A) ≤ s(B)`. -/
theorem pivot_le_of_le {A B : (ℕ → ℝ) → ℝ} (K : ℕ) (hAB : ∀ v, A v ≤ B v)
    (hA : BddBelow (A '' {v : ℕ → ℝ | v (K - 1) = 1})) : pivot A K ≤ pivot B K := by
  refine le_csInf (competitors_nonempty K B) ?_
  rintro _ ⟨v, hv, rfl⟩
  exact (csInf_le hA ⟨v, hv, rfl⟩).trans (hAB v)

/-- **Coercive floor.** If `A(v) ≥ d ∑_{i<K} v_i²` with `d ≥ 0` and `K ≥ 1`, then `s(A) ≥ d`. -/
theorem le_pivot_of_coercive {A : (ℕ → ℝ) → ℝ} {K : ℕ} (hK : 1 ≤ K) {d : ℝ} (hd : 0 ≤ d)
    (hA : ∀ v, d * ∑ i ∈ range K, v i ^ 2 ≤ A v) : d ≤ pivot A K := by
  refine le_csInf (competitors_nonempty K A) ?_
  rintro _ ⟨v, hv, rfl⟩
  have hv' : v (K - 1) = 1 := hv
  have hmem : K - 1 ∈ range K := mem_range.mpr (by omega)
  have h1 : (1 : ℝ) ≤ ∑ i ∈ range K, v i ^ 2 := by
    calc (1 : ℝ) = v (K - 1) ^ 2 := by rw [hv']; norm_num
      _ ≤ ∑ i ∈ range K, v i ^ 2 :=
        single_le_sum (f := fun i => v i ^ 2) (fun i _ => sq_nonneg _) hmem
  calc d = d * 1 := (mul_one d).symm
    _ ≤ d * ∑ i ∈ range K, v i ^ 2 := mul_le_mul_of_nonneg_left h1 hd
    _ ≤ A v := hA v

/-- The Toeplitz quadratic form `∑_{i,j<K} v_i v_j q(i − j)`. -/
def toeplitzForm (q : ℤ → ℝ) (K : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range K, ∑ j ∈ range K, v i * v j * q ((i : ℤ) - j)

/-- The Toeplitz pivots `t_K = s(Q_K)`. -/
noncomputable def toeplitzPivot (q : ℤ → ℝ) (K : ℕ) : ℝ := pivot (toeplitzForm q K) K

/-- Shift a vector one slot to the right. -/
def shift (v : ℕ → ℝ) : ℕ → ℝ := fun i => if i = 0 then 0 else v (i - 1)

lemma shift_zero (v : ℕ → ℝ) : shift v 0 = 0 := rfl

lemma shift_succ (v : ℕ → ℝ) (i : ℕ) : shift v (i + 1) = v i := by
  simp [shift]

lemma toeplitzForm_shift (q : ℤ → ℝ) (K : ℕ) (v : ℕ → ℝ) :
    toeplitzForm q (K + 1) (shift v) = toeplitzForm q K v := by
  simp only [toeplitzForm, sum_range_succ', shift_succ, shift_zero, zero_mul, mul_zero,
    sum_const_zero, add_zero]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [show ((i + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ) = (i : ℤ) - j by push_cast; ring]

/-- **Toeplitz pivots are nonincreasing.** For a positive semidefinite Toeplitz kernel and
`K ≥ 1`, `t_{K+1} ≤ t_K`. -/
theorem toeplitzPivot_succ_le (q : ℤ → ℝ) (hpsd : ∀ K v, 0 ≤ toeplitzForm q K v) {K : ℕ}
    (hK : 1 ≤ K) : toeplitzPivot q (K + 1) ≤ toeplitzPivot q K := by
  unfold toeplitzPivot pivot
  have hbdd : BddBelow (toeplitzForm q (K + 1) '' {v : ℕ → ℝ | v (K + 1 - 1) = 1}) :=
    ⟨0, by rintro _ ⟨v, _, rfl⟩; exact hpsd _ v⟩
  refine le_csInf (competitors_nonempty K _) ?_
  rintro _ ⟨v, hv, rfl⟩
  have hv' : v (K - 1) = 1 := hv
  refine csInf_le hbdd ⟨shift v, ?_, toeplitzForm_shift q K v⟩
  show shift v (K + 1 - 1) = 1
  simp only [shift, Nat.add_sub_cancel]
  rw [if_neg (by omega)]
  exact hv'

theorem toeplitzPivot_antitone (q : ℤ → ℝ) (hpsd : ∀ K v, 0 ≤ toeplitzForm q K v) :
    AntitoneOn (toeplitzPivot q) {K | 1 ≤ K} := by
  intro a ha b hb hab
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih =>
    exact (toeplitzPivot_succ_le q hpsd (le_trans ha hn)).trans (ih (le_trans ha hn))

/-- **Geometric-mean decay forces decay.** If `t_j > 0` is nonincreasing and
`(∏_{j<K} t_j)^{1/K} → 0`, then `t_K → 0`. -/
theorem tendsto_zero_of_antitone_of_root {t : ℕ → ℝ} (hpos : ∀ n, 0 < t n) (hanti : Antitone t)
    (hroot : Tendsto (fun K : ℕ => (∏ j ∈ range K, t j) ^ ((1 : ℝ) / K)) atTop (𝓝 0)) :
    Tendsto t atTop (𝓝 0) := by
  have hbdd : BddBelow (Set.range t) := ⟨0, by rintro _ ⟨n, rfl⟩; exact (hpos n).le⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ n, t n
  have hL0 : 0 ≤ L := le_ciInf fun n => (hpos n).le
  rcases hL0.lt_or_eq with hL | hL
  · exfalso
    have hge : ∀ K : ℕ, 1 ≤ K → L ≤ (∏ j ∈ range K, t j) ^ ((1 : ℝ) / K) := by
      intro K hK
      have hprod : L ^ K ≤ ∏ j ∈ range K, t j := by
        calc L ^ K = ∏ _j ∈ range K, L := by rw [prod_const, card_range]
          _ ≤ ∏ j ∈ range K, t j :=
            prod_le_prod (fun _ _ => hL0) fun j _ => ciInf_le hbdd j
      calc L = (L ^ K) ^ ((1 : ℝ) / K) := by
            rw [one_div, Real.pow_rpow_inv_natCast hL0 (by omega)]
        _ ≤ _ := Real.rpow_le_rpow (by positivity) hprod (by positivity)
    have := hroot.eventually (gt_mem_nhds hL)
    obtain ⟨K, hK⟩ := (this.and (eventually_ge_atTop 1)).exists
    exact absurd (hge K hK.2) (not_le.mpr hK.1)
  · rw [← hL] at hlim; exact hlim

/-- **No constant barrier.** If `0 < s_K ≤ 2 t_K` with `t_K → 0`, and the comparison pivots
satisfy `s^Δ_K ≥ d > 0`, then no fixed `c > 0` has `c s^Δ_K ≤ s_K` for all `K`. -/
theorem no_constant_barrier {s t sΔ : ℕ → ℝ} {d : ℝ} (hd : 0 < d)
    (hst : ∀ K, s K ≤ 2 * t K) (ht : Tendsto t atTop (𝓝 0)) (hΔ : ∀ K, d ≤ sΔ K) :
    ¬ ∃ c > 0, ∀ K, c * sΔ K ≤ s K := by
  rintro ⟨c, hc, hbar⟩
  have hpos : 0 < c * d / 2 := by positivity
  obtain ⟨K, hK⟩ := (ht.eventually (gt_mem_nhds hpos)).exists
  have h1 : c * d ≤ c * sΔ K := mul_le_mul_of_nonneg_left (hΔ K) hc.le
  have h2 := hbar K
  have h3 := hst K
  linarith

end GppPivotFloor
