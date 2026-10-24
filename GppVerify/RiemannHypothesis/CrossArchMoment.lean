import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Real.Basic

/-!
# The cross-Arch moment matrix: positive definite, with an explicit near-null direction

Source: Codex, GPP-bridge PR #11 comment 6376886553 (cross-Arch moment/rank). Daniel Toupin /
Golden Physics Project, with AI assistance from Codex (statement) and Claude Code (formalization).

The moment matrix is `M_{jk} = ∑_n c_n² r_n^{j+k}` for `j, k < K`, over finitely many nodes
`r_n` with weights `c_n`. For `v ∈ ℝ^K` write `P_v(x) = ∑_{j<K} v_j x^j`.

* `moment_form_eq`: `vᵀ M v = ∑_n c_n² P_v(r_n)²`. In particular `moment_form_nonneg`.
* `moment_form_pos`: **positive definiteness (Vandermonde).** If the nodes are distinct, every
  weight is nonzero and there are at least `K` nodes, then `vᵀ M v > 0` for every `v ≠ 0`.
* `moment_form_of_vanishing`: **Rayleigh witness.** If `P_v` vanishes at the nodes in `S`, then
  `vᵀ M v = ∑_{n ∉ S} c_n² P_v(r_n)²`. With `P_v = ∏_{m ≤ K−2}(x − r_m)` only the remaining nodes
  contribute; Codex's size estimate `λ_min ≤ e^{−X_K}/(Λ_K²(1 − e^{−7/5}))` then bounds that tail.

**Scope.** Finite algebra. The size estimate on the tail (`|P_K(r_n)| ≤ ∏ r_m`, `S(−λ) ≤ 1/(2λ)`,
the geometric sum) and the identification of `c_n, r_n` with the Arch modes are not formalized;
the continuum compactness statement stays analytic. No claim about RH.
-/

open Finset Polynomial

namespace GppCrossArchMoment

variable {K N : ℕ}

/-- `P_v(x) = ∑_{j<K} v_j x^j`. -/
def evalP (v : Fin K → ℝ) (x : ℝ) : ℝ := ∑ j, v j * x ^ (j : ℕ)

/-- The moment quadratic form `∑_{j,k} v_j v_k ∑_n c_n² r_n^{j+k}`. -/
def momentForm (c r : Fin N → ℝ) (v : Fin K → ℝ) : ℝ :=
  ∑ j, ∑ k, v j * v k * ∑ n, c n ^ 2 * r n ^ ((j : ℕ) + k)

/-- **The form is a weighted sum of squares.** `vᵀ M v = ∑_n c_n² P_v(r_n)²`. -/
theorem moment_form_eq (c r : Fin N → ℝ) (v : Fin K → ℝ) :
    momentForm c r v = ∑ n, c n ^ 2 * evalP v (r n) ^ 2 := by
  have hF : ∀ j k : Fin K, v j * v k * ∑ n, c n ^ 2 * r n ^ ((j : ℕ) + k) =
      ∑ n, c n ^ 2 * (v j * r n ^ (j : ℕ)) * (v k * r n ^ (k : ℕ)) := fun j k => by
    rw [mul_sum]; exact sum_congr rfl fun n _ => by rw [pow_add]; ring
  calc momentForm c r v
      = ∑ j, ∑ k, ∑ n, c n ^ 2 * (v j * r n ^ (j : ℕ)) * (v k * r n ^ (k : ℕ)) := by
        simp only [momentForm, hF]
    _ = ∑ j, ∑ n, ∑ k, c n ^ 2 * (v j * r n ^ (j : ℕ)) * (v k * r n ^ (k : ℕ)) :=
        sum_congr rfl fun j _ => sum_comm
    _ = ∑ n, ∑ j, ∑ k, c n ^ 2 * (v j * r n ^ (j : ℕ)) * (v k * r n ^ (k : ℕ)) := sum_comm
    _ = ∑ n, c n ^ 2 * evalP v (r n) ^ 2 := sum_congr rfl fun n _ => by
        rw [evalP, sq (∑ j, v j * r n ^ (j : ℕ)), sum_mul_sum, mul_sum]
        exact sum_congr rfl fun j _ => by rw [mul_sum]; exact sum_congr rfl fun k _ => by ring

theorem moment_form_nonneg (c r : Fin N → ℝ) (v : Fin K → ℝ) : 0 ≤ momentForm c r v := by
  rw [moment_form_eq]; exact sum_nonneg fun n _ => by positivity

/-- The polynomial with coefficient vector `v`. -/
noncomputable def poly (v : Fin K → ℝ) : ℝ[X] := ∑ j, C (v j) * X ^ (j : ℕ)

lemma eval_poly (v : Fin K → ℝ) (x : ℝ) : (poly v).eval x = evalP v x := by
  simp [poly, evalP, eval_finsetSum]

lemma coeff_poly (v : Fin K → ℝ) (j : Fin K) : (poly v).coeff j = v j := by
  simp only [poly, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  rw [sum_eq_single j (fun b _ hb => by rw [if_neg (fun h => hb (Fin.ext h).symm), mul_zero])
    (fun h => absurd (mem_univ j) h), if_pos rfl, mul_one]

/-- **Positive definiteness (Vandermonde).** Distinct nodes, nonzero weights and at least `K`
nodes make the moment form strictly positive off `0`. -/
theorem moment_form_pos {c r : Fin N → ℝ} (hr : Function.Injective r) (hc : ∀ n, c n ≠ 0)
    (hKN : K ≤ N) {v : Fin K → ℝ} (hv : v ≠ 0) : 0 < momentForm c r v := by
  refine lt_of_le_of_ne (moment_form_nonneg c r v) fun h0 => hv ?_
  rw [moment_form_eq] at h0
  have hterm := (sum_eq_zero_iff_of_nonneg fun n _ => by positivity).mp h0.symm
  have heval : ∀ n, (poly v).eval (r n) = 0 := fun n => by
    have := hterm n (mem_univ n)
    rw [eval_poly]
    have hc2 : c n ^ 2 ≠ 0 := pow_ne_zero 2 (hc n)
    exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp ((mul_eq_zero.mp this).resolve_left hc2)
  have hp : poly v = 0 := by
    by_contra hp
    refine absurd (eq_zero_of_natDegree_lt_card_of_eval_eq_zero (poly v) hr heval ?_) hp
    rw [Fintype.card_fin]
    have hdeg : (poly v).degree < K := degree_sum_fin_lt _
    exact lt_of_lt_of_le ((natDegree_lt_iff_degree_lt hp).mpr hdeg) hKN
  funext j
  rw [← coeff_poly v j, hp, coeff_zero, Pi.zero_apply]

/-- **Rayleigh witness.** If `P_v` vanishes at the nodes in `S`, only the other nodes contribute:
`vᵀ M v = ∑_{n ∉ S} c_n² P_v(r_n)²`. -/
theorem moment_form_of_vanishing (c r : Fin N → ℝ) (v : Fin K → ℝ) (S : Finset (Fin N))
    (hS : ∀ n ∈ S, evalP v (r n) = 0) :
    momentForm c r v = ∑ n ∈ univ.filter (· ∉ S), c n ^ 2 * evalP v (r n) ^ 2 := by
  rw [moment_form_eq, ← sum_filter_add_sum_filter_not univ (· ∈ S)]
  have h0 : ∑ n ∈ univ.filter (· ∈ S), c n ^ 2 * evalP v (r n) ^ 2 = 0 :=
    sum_eq_zero fun n hn => by
      rw [hS n (mem_filter.mp hn).2]; ring
  rw [h0, zero_add]

end GppCrossArchMoment
