import GppVerify.RiemannHypothesis.WeilHRhoCheck0
import GppVerify.RiemannHypothesis.WeilHRhoCheck1
import GppVerify.RiemannHypothesis.WeilHRhoCheck2
import GppVerify.RiemannHypothesis.WeilHRhoCheck3
import GppVerify.RiemannHypothesis.WeilHRhoCheck4
import GppVerify.RiemannHypothesis.WeilHRhoCheck5
import GppVerify.RiemannHypothesis.WeilHRhoCheck6
import GppVerify.RiemannHypothesis.WeilHRhoCheck7
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# (H-ρ), Gershgorin form: a ball on the normalised matrix gives `‖Ã − I‖ ≤ ρ` as quadratic-form bounds

Flint's (H-ρ) export (bridge `c3c80df`, `work/flint/hrho_gershgorin_export_2026_11_16.json`) encloses every
off-diagonal entry of the normalised `740 × 740` matrix `Ã = D^{-1/2} A D^{-1/2}` of run 16 (`A = S_Z^eff`,
`L = 0.5`, `j = 73 … 812`) in a ball, and `|Ã_jj − 1|` by `dDev_j / 2³²`. This file proves, **given those
ball hypotheses**:

  `(1 − ρ) ‖x‖² ≤ xᵀ Ã x ≤ (1 + ρ) ‖x‖²`   with   `ρ = 3632727590 / 2³² ≈ 0.84581`.

The kernel part is `rows_0 … rows_7` (eight shards of `decide +kernel` over exact integers): for **every**
`j < 740`, `dDev j + Σ_k s_jk ≤ 3632727590`. The analytic part is the row-sum (Gershgorin) lemma
`quad_ge_of_ball`, the same argument as in `OddFaceItem4Floor.lean`, in both directions.

**Scope — read before citing.** `ρ ≈ 0.846` is the *Gershgorin* value; run 16's `LDLᵀ` certificate gives the
sharper `ρ ≤ 0.34`-type bound and is **not** in Lean here. The hypotheses `hoff`, `hdiag` (that the real
run-16 matrix lies in Flint's balls) are *not* proved here — they are statements about the numerics of the
matrix `A` — and the assembly chain from `A` to the window is not in Lean. Nothing here proves ARP, RH or AKG.
No `sorry`, no axiom.
-/

open Finset

namespace GppWeilHRho

/-- **The row-sum bound, all 740 rows.** -/
theorem rowOk_all (j : ℕ) (hj : j < 740) :
    dDev j + ∑ k ∈ Finset.range 740, sSym j k ≤ rowBound := by
  have h : rowOk j = true := by
    have hc : (0 ≤ j ∧ j < 93) ∨ (93 ≤ j ∧ j < 186) ∨ (186 ≤ j ∧ j < 279) ∨ (279 ≤ j ∧ j < 372) ∨ (372 ≤ j ∧ j < 465) ∨ (465 ≤ j ∧ j < 558) ∨ (558 ≤ j ∧ j < 651) ∨ (651 ≤ j ∧ j < 740) := by omega
    rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
    · exact List.all_eq_true.mp rows_0 j (by rw [List.mem_range'_1]; omega)
    · exact List.all_eq_true.mp rows_1 j (by rw [List.mem_range'_1]; omega)
    · exact List.all_eq_true.mp rows_2 j (by rw [List.mem_range'_1]; omega)
    · exact List.all_eq_true.mp rows_3 j (by rw [List.mem_range'_1]; omega)
    · exact List.all_eq_true.mp rows_4 j (by rw [List.mem_range'_1]; omega)
    · exact List.all_eq_true.mp rows_5 j (by rw [List.mem_range'_1]; omega)
    · exact List.all_eq_true.mp rows_6 j (by rw [List.mem_range'_1]; omega)
    · exact List.all_eq_true.mp rows_7 j (by rw [List.mem_range'_1]; omega)
  simpa [rowOk] using h

/-! ### The row-sum (Gershgorin) lemma, both directions -/

theorem quad_ge_of_ball {n : ℕ} (Mt C R : Fin n → Fin n → ℝ) (hR : ∀ i j, R i j = R j i)
    (hb : ∀ i j, |Mt i j - C i j| ≤ R i j) (x : Fin n → ℝ) :
    ∑ i, ∑ j, C i j * x i * x j - ∑ i, (∑ j, R i j) * x i ^ 2 ≤ ∑ i, ∑ j, Mt i j * x i * x j := by
  have h1 : ∀ i j, -(R i j * (x i ^ 2 + x j ^ 2)) ≤ 2 * ((Mt i j - C i j) * x i * x j) := by
    intro i j
    have hRij : 0 ≤ R i j := (abs_nonneg _).trans (hb i j)
    have h2 : |(Mt i j - C i j) * x i * x j| ≤ R i j * (|x i| * |x j|) := by
      rw [abs_mul, abs_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_right (hb i j) (by positivity)
    have h3 : 2 * (|x i| * |x j|) ≤ x i ^ 2 + x j ^ 2 := by
      nlinarith [sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j)]
    have h4 : R i j * (2 * (|x i| * |x j|)) ≤ R i j * (x i ^ 2 + x j ^ 2) :=
      mul_le_mul_of_nonneg_left h3 hRij
    have := (abs_le.mp h2).1
    nlinarith
  have hT : ∑ i, ∑ j, R i j * (x i ^ 2 + x j ^ 2) = 2 * ∑ i, (∑ j, R i j) * x i ^ 2 := by
    have e1 : ∑ i, ∑ j, R i j * (x i ^ 2 + x j ^ 2)
        = ∑ i, ∑ j, R i j * x i ^ 2 + ∑ i, ∑ j, R i j * x j ^ 2 := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [← sum_add_distrib]
      exact sum_congr rfl fun j _ => by ring
    have e2 : ∑ i, ∑ j, R i j * x j ^ 2 = ∑ i, ∑ j, R i j * x i ^ 2 := by
      rw [sum_comm]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      rw [hR i j]
    have e3 : ∑ i, ∑ j, R i j * x i ^ 2 = ∑ i, (∑ j, R i j) * x i ^ 2 :=
      sum_congr rfl fun i _ => by rw [sum_mul]
    rw [e1, e2, e3]; ring
  have h6 : ∑ i, ∑ j, -(R i j * (x i ^ 2 + x j ^ 2))
      ≤ ∑ i, ∑ j, 2 * ((Mt i j - C i j) * x i * x j) :=
    sum_le_sum fun i _ => sum_le_sum fun j _ => h1 i j
  have h7 : ∑ i, ∑ j, 2 * ((Mt i j - C i j) * x i * x j)
      = 2 * (∑ i, ∑ j, Mt i j * x i * x j - ∑ i, ∑ j, C i j * x i * x j) := by
    have e : ∀ i j, 2 * ((Mt i j - C i j) * x i * x j)
        = 2 * (Mt i j * x i * x j) - 2 * (C i j * x i * x j) := fun i j => by ring
    simp_rw [e]
    simp only [sum_sub_distrib, ← mul_sum]
    ring
  have h8 : ∑ i, ∑ j, -(R i j * (x i ^ 2 + x j ^ 2)) = -(2 * ∑ i, (∑ j, R i j) * x i ^ 2) := by
    rw [← hT]
    simp only [sum_neg_distrib]
  linarith

theorem quad_le_of_ball {n : ℕ} (Mt C R : Fin n → Fin n → ℝ) (hR : ∀ i j, R i j = R j i)
    (hb : ∀ i j, |Mt i j - C i j| ≤ R i j) (x : Fin n → ℝ) :
    ∑ i, ∑ j, Mt i j * x i * x j ≤ ∑ i, ∑ j, C i j * x i * x j + ∑ i, (∑ j, R i j) * x i ^ 2 := by
  have h := quad_ge_of_ball (fun i j => -Mt i j) (fun i j => -C i j) R hR
    (fun i j => by rw [show -Mt i j - -C i j = -(Mt i j - C i j) by ring, abs_neg]; exact hb i j) x
  simp only [neg_mul, sum_neg_distrib] at h
  linarith

/-! ### The Gershgorin theorem for the exported balls -/

/-- `ρ = 3632727590 / 2³²`. -/
noncomputable def rho : ℝ := (rowBound : ℝ) / 2 ^ 32

theorem rho_lt_one : rho < 1 := by
  unfold rho rowBound; norm_num

/-- **(H-ρ), Gershgorin form.** If a real `740 × 740` matrix lies in the exported entry balls
(`hoff`: off-diagonal, `hdiag`: `|M_jj − 1|`), then `(1 − ρ)‖x‖² ≤ xᵀ M x ≤ (1 + ρ)‖x‖²` for
`ρ = 3632727590 / 2³² ≈ 0.8458`. The ball hypotheses are *not* proved here. -/
theorem gershgorin_quadForm (M : Fin 740 → Fin 740 → ℝ)
    (hoff : ∀ i j : Fin 740, i ≠ j → |M i j| ≤ (sSym i j : ℝ) / 2 ^ 32)
    (hdiag : ∀ i : Fin 740, |M i i - 1| ≤ (dDev i : ℝ) / 2 ^ 32) (x : Fin 740 → ℝ) :
    (1 - rho) * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, M i j * x i * x j ∧
      ∑ i, ∑ j, M i j * x i * x j ≤ (1 + rho) * ∑ i, x i ^ 2 := by
  set C : Fin 740 → Fin 740 → ℝ := fun i j => if i = j then 1 else 0 with hC
  set R : Fin 740 → Fin 740 → ℝ :=
    fun i j => ((sSym i j : ℝ) + if i = j then (dDev i : ℝ) else 0) / 2 ^ 32 with hR
  have hRsymm : ∀ i j, R i j = R j i := by
    intro i j
    simp only [hR]
    by_cases hij : i = j
    · subst hij; rfl
    · have : ¬ (j = i) := fun h => hij h.symm
      simp [hij, this, sSym_comm (i : ℕ) (j : ℕ)]
  have hb : ∀ i j, |M i j - C i j| ≤ R i j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have := hdiag i
      simp only [hC, hR, if_true, sSym_self, Nat.cast_zero, zero_add]
      simpa using this
    · have h0 := hoff i j hij
      simp only [hC, hR, hij, if_false, sub_zero, add_zero]
      exact h0
  have hrow : ∀ i, ∑ j, R i j ≤ rho := by
    intro i
    have hs : ∑ j : Fin 740, ((sSym i j : ℕ) : ℝ) = ((∑ k ∈ Finset.range 740, sSym i k : ℕ) : ℝ) := by
      push_cast
      exact Fin.sum_univ_eq_sum_range (fun k => ((sSym i k : ℕ) : ℝ)) 740
    have e : ∑ j, R i j = (((∑ k ∈ Finset.range 740, sSym i k : ℕ) : ℝ) + (dDev i : ℝ)) / 2 ^ 32 := by
      simp only [hR, div_eq_mul_inv]
      have h2 : ∑ j : Fin 740, (if i = j then (dDev i : ℝ) else 0) = dDev i := by
        rw [Finset.sum_ite_eq]; simp only [Finset.mem_univ, if_true]
      rw [← Finset.sum_mul, Finset.sum_add_distrib, hs, h2]
    rw [e]
    have hk := rowOk_all i i.2
    have hk' : (((∑ k ∈ Finset.range 740, sSym i k : ℕ) : ℝ) + (dDev i : ℝ)) ≤ (rowBound : ℝ) := by
      exact_mod_cast (by omega : (∑ k ∈ Finset.range 740, sSym i k) + dDev i ≤ rowBound)
    unfold rho
    exact div_le_div_of_nonneg_right hk' (by positivity)
  have hsum : ∑ i, (∑ j, R i j) * x i ^ 2 ≤ rho * ∑ i, x i ^ 2 := by
    rw [mul_sum]
    exact sum_le_sum fun i _ => by
      exact mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
  have hCsum : ∑ i, ∑ j, C i j * x i * x j = ∑ i, x i ^ 2 := by
    refine sum_congr rfl fun i _ => ?_
    simp [hC, sq]
  have h1 := quad_ge_of_ball M C R hRsymm hb x
  have h2 := quad_le_of_ball M C R hRsymm hb x
  rw [hCsum] at h1 h2
  constructor <;> nlinarith [hsum]

end GppWeilHRho

#print axioms GppWeilHRho.rowOk_all
#print axioms GppWeilHRho.gershgorin_quadForm
