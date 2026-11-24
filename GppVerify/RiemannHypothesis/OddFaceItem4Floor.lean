import GppVerify.RiemannHypothesis.OddFaceItem4Core
import GppVerify.RiemannHypothesis.OddFaceItem4Check0
import GppVerify.RiemannHypothesis.OddFaceItem4Check1
import GppVerify.RiemannHypothesis.OddFaceItem4Check2
import GppVerify.RiemannHypothesis.OddFaceItem4Check3
import GppVerify.RiemannHypothesis.OddFaceItem4Check4
import GppVerify.RiemannHypothesis.OddFaceItem4Check5
import GppVerify.RiemannHypothesis.OddFaceItem4Check6
import GppVerify.RiemannHypothesis.OddFaceItem4Check7
import GppVerify.Upstream.QuadraticFormLDL

/-!
# OddFace(0.5), item 4: the bordered floor `β₂ = 1.3e-8`, kernel-checked, conditional on the entry balls

Flint's run 15 certifies, by a 600-bit Arb `LDLᵀ`, that the scaled bordered matrix
`Mt = A_{X'} − CCᵀ/λ_Z` (`λ_Z = 5.24628`, certificate order `ψ₁₃..ψ₇₂, δ, φ₁..φ₁₂`) satisfies
`Schur_{E₁₂}(Mt) ≥ β₂`. Turbo reran it byte-identically and audited the dyadic export (bridge `df1ec9d`,
`b086cf4`). This file moves the **finite arithmetic** of that certificate into the Lean kernel.

**`item4_floor`.** Let `Mt` be any real `73 × 73` matrix whose entries lie in the exported balls
`|Mt_ij − C_ij/2¹⁰⁰| ≤ R_ij/2¹⁰⁰`. Then for every `x`,

  `(13/10) Σ_{i ≥ 61} x_i² ≤ Σ_{i,j} Mt_ij x_i x_j`,

i.e. `Mt − 1.3 P ⪰ 0` with `P` the indicator of the `E₁₂` block.

**`item4_floor_unscaled`** undoes the diagonal scaling: for any positive scaling `s` with
`s_i = 1/10⁴` on `E₁₂`, a matrix `M` whose scaled entries `M_ij/(s_i s_j)` lie in the balls satisfies
`β₂ Σ_{i ≥ 61} y_i² ≤ Σ M_ij y_i y_j` with `β₂ = 13/10⁹ = 1.3e-8`. (Any positive `s` works; the
scaling vector's own values enter only through the ball hypothesis.)

**Proof.** (1) `quad_ge_of_ball`: an entrywise ball with symmetric radii costs at most the row sum
`r_i = Σ_j R_ij` on the diagonal. (2) `Matrix.le_quadForm_of_ldl_residual` applied to
`Nm = C − diag(r) − (13/10)P` and the integer factors `L, D` of `Nm − 2⁻⁶⁰ I`, with the residual bound
`EE` checked entrywise by `decide +kernel` over the eight shard files, gives `Σ Nm x x ≥ (δ − 73 ε) Σ x²
≥ 0`, as `73·EE < δ`-scale (`marginOk`).

**What is and is not proved.** PROVED here: the implication *entry balls ⇒ floor*, on exactly
Flint's exported data, with the kernel checking all `73 × 73` residuals. NOT proved here: that the
true `A_{X'}` and `CCᵀ/λ_Z` entries lie in the balls (those are interval-certified numerics — Arb
enclosures of the kernel integrals — not Lean theorems), and the sine-mode/arch-form identification of
`Mt`. So this upgrades the 600-bit `LDLᵀ` step of item 4 from interval-certified to kernel-checked and
leaves the integrals as the named hypothesis. OddFace(0.5) is NUMERICAL; proof-grade OPEN on (H-A),
(H-ρ). H_ψ, WeilIsGram, ARP, RH: OPEN. No `sorry`, no axioms.
-/

namespace GppOddFaceItem4

open Finset

/-! ### The kernel checks, assembled -/

theorem rowsAll : ∀ i, i < 73 → rowOk i = true := by
  intro i hi
  have key : ∀ (a c : ℕ), (List.range' a c).all rowOk = true → a ≤ i → i < a + c →
      rowOk i = true := fun a c h h1 h2 => by
    rw [List.all_eq_true] at h
    exact h i (List.mem_range'.2 ⟨i - a, by omega, by omega⟩)
  rcases (by omega : i < 10 ∨ (10 ≤ i ∧ i < 19) ∨ (19 ≤ i ∧ i < 28) ∨ (28 ≤ i ∧ i < 37) ∨
      (37 ≤ i ∧ i < 46) ∨ (46 ≤ i ∧ i < 55) ∨ (55 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 73)) with
    h | h | h | h | h | h | h | h
  · exact key 0 10 rows_0 (by omega) (by omega)
  · exact key 10 9 rows_1 h.1 (by omega)
  · exact key 19 9 rows_2 h.1 (by omega)
  · exact key 28 9 rows_3 h.1 (by omega)
  · exact key 37 9 rows_4 h.1 (by omega)
  · exact key 46 9 rows_5 h.1 (by omega)
  · exact key 55 9 rows_6 h.1 (by omega)
  · exact key 64 9 rows_7 h.1 (by omega)

theorem dOk_true : dOk = true := by decide +kernel
theorem marginOk_true : marginOk = true := by decide +kernel

/-- Radii symmetric (a finite check on the data). -/
def radSymmOk : Bool :=
  (List.range 73).all fun i => (List.range 73).all fun j => decide (ent radD i j = ent radD j i)

theorem radSymmOk_true : radSymmOk = true := by decide +kernel

/-! ### The entry-ball lemma (row-sum / Gershgorin form) -/

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

/-! ### The real-number data -/

noncomputable def cenR (i j : ℕ) : ℝ := (ent cenD i j : ℝ) / 2 ^ 100
noncomputable def radR (i j : ℕ) : ℝ := (ent radD i j : ℝ) / 2 ^ 100

theorem radR_symm (i j : Fin 73) : radR i j = radR j i := by
  have h := radSymmOk_true
  unfold radSymmOk at h
  rw [List.all_eq_true] at h
  have := h i (List.mem_range.2 i.2)
  rw [List.all_eq_true] at this
  have := of_decide_eq_true (this j (List.mem_range.2 j.2))
  unfold radR
  rw [this]

/-- The charge on the `E₁₂` block: `13/10` for positions `≥ 61`. -/
noncomputable def chg (i : ℕ) : ℝ := if 61 ≤ i then 13 / 10 else 0

theorem Nmr_eq (i j : Fin 73) :
    Nmr i j = cenR i j - (if i = j then (∑ k : Fin 73, radR i k) + chg i else 0) := by
  by_cases hij : i = j
  · subst hij
    have hr : (rsum i : ℝ) = (∑ k : Fin 73, (ent radD i k : ℝ)) := by
      unfold rsum
      rw [ssum_eq]
      push_cast
      exact (Fin.sum_univ_eq_sum_range (fun k => (ent radD i k : ℝ)) 73).symm
    have hs : (∑ k : Fin 73, radR i k) = (rsum i : ℝ) / 2 ^ 100 := by
      unfold radR
      rw [← Finset.sum_div, ← hr]
    simp only [if_true]
    rw [hs]
    unfold Nmr Nnum cenR chg Qq chargeNum
    by_cases h61 : 61 ≤ (i : ℕ)
    · simp only [h61, if_true]
      push_cast
      field_simp
      ring
    · simp only [h61, if_false]
      push_cast
      field_simp
      ring
  · have hne : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    simp only [hij, if_false]
    unfold Nmr Nnum cenR Qq
    simp only [hne, if_false]
    push_cast
    field_simp
    ring

/-! ### Nonnegativity of `Nm` from the `LDLᵀ` certificate -/

theorem Nm_quad_nonneg (x : Fin 73 → ℝ) :
    0 ≤ ∑ i : Fin 73, ∑ j : Fin 73, Nmr i j * x i * x j := by
  have hD : ∀ k : Fin 73, 0 ≤ Dr k := by
    intro k
    have h := dOk_true
    unfold dOk at h
    rw [List.all_eq_true] at h
    have := of_decide_eq_true (h k (List.mem_range.2 k.2))
    unfold Dr
    positivity
  have hM : ∀ i j : Fin 73, |Nmr i j - ((if i = j then δr else 0) + ∑ k : Fin 73, Lr i k * Dr k * Lr j k)|
      ≤ εr := by
    intro i j
    have h := check_real (rowsAll i i.2) j.2
    rw [Fin.sum_univ_eq_sum_range (fun k => Lr i k * Dr k * Lr j k) 73]
    have hij : (i : ℕ) = j ↔ i = j := ⟨Fin.ext, fun h => by rw [h]⟩
    simpa only [hij] using h
  have key := Matrix.le_quadForm_of_ldl_residual (fun i j : Fin 73 => Nmr i j)
    (fun i k : Fin 73 => Lr i k) (fun k : Fin 73 => Dr k) δr εr hM hD x
  have hmargin : 0 < δr - 73 * εr := by
    have h := marginOk_true
    unfold marginOk at h
    have h' : 73 * EE < Qq * twoPow324 := of_decide_eq_true h
    have h'' : (73 : ℝ) * (EE : ℝ) < (Qq : ℝ) * (twoPow324 : ℝ) := by exact_mod_cast h'
    unfold δr εr
    have hQ := Qq_pos
    have hT := twoPow384_pos
    have hT2 : (0 : ℝ) < (twoPow324 : ℝ) := by unfold twoPow324; norm_num
    rw [twoPow324_eq]
    rw [show (1 : ℝ) / 2 ^ 60 - 73 * ((EE : ℝ) / ((Qq : ℝ) * ((twoPow324 : ℝ) * 2 ^ 60)))
        = ((Qq : ℝ) * (twoPow324 : ℝ) - 73 * (EE : ℝ)) / ((Qq : ℝ) * (twoPow324 : ℝ) * 2 ^ 60) by
      field_simp]
    apply div_pos (by linarith) (by positivity)
  have hsq : 0 ≤ ∑ i : Fin 73, x i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  have := mul_nonneg hmargin.le hsq
  push_cast at key
  linarith

/-! ### The floor -/

/-- **Item 4, scaled basis.** Entry balls ⇒ `Mt − 1.3 P ⪰ 0`. -/
theorem item4_floor (Mt : Fin 73 → Fin 73 → ℝ)
    (hball : ∀ i j : Fin 73, |Mt i j - cenR i j| ≤ radR i j) (x : Fin 73 → ℝ) :
    (13 / 10 : ℝ) * ∑ i : Fin 73, (if 61 ≤ (i : ℕ) then x i ^ 2 else 0)
      ≤ ∑ i : Fin 73, ∑ j : Fin 73, Mt i j * x i * x j := by
  have hA := quad_ge_of_ball Mt (fun i j => cenR i j) (fun i j => radR i j) radR_symm hball x
  have hN := Nm_quad_nonneg x
  -- `Σ Nm x x = Σ C x x − Σ (r_i + chg_i) x_i²`
  have hexp : ∑ i : Fin 73, ∑ j : Fin 73, Nmr i j * x i * x j
      = ∑ i : Fin 73, ∑ j : Fin 73, cenR i j * x i * x j
        - ∑ i : Fin 73, ((∑ k : Fin 73, radR i k) + chg i) * x i ^ 2 := by
    have e : ∀ i j : Fin 73, Nmr i j * x i * x j
        = cenR i j * x i * x j
          - (if i = j then ((∑ k : Fin 73, radR i k) + chg i) * x i ^ 2 else 0) := by
      intro i j
      rw [Nmr_eq]
      by_cases hij : i = j
      · subst hij; simp only [if_true]; ring
      · simp only [hij, if_false]; ring
    simp_rw [e]
    rw [show (∑ i : Fin 73, ∑ j : Fin 73,
        (cenR i j * x i * x j - (if i = j then ((∑ k : Fin 73, radR i k) + chg i) * x i ^ 2 else 0)))
      = ∑ i : Fin 73, ∑ j : Fin 73, cenR i j * x i * x j
        - ∑ i : Fin 73, ∑ j : Fin 73,
            (if i = j then ((∑ k : Fin 73, radR i k) + chg i) * x i ^ 2 else 0) by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [← sum_sub_distrib]]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    simp
  have hsplit : ∑ i : Fin 73, ((∑ k : Fin 73, radR i k) + chg i) * x i ^ 2
      = ∑ i : Fin 73, (∑ k : Fin 73, radR i k) * x i ^ 2 + ∑ i : Fin 73, chg i * x i ^ 2 := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  have hchg : ∑ i : Fin 73, chg i * x i ^ 2
      = (13 / 10 : ℝ) * ∑ i : Fin 73, (if 61 ≤ (i : ℕ) then x i ^ 2 else 0) := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    unfold chg
    split_ifs <;> ring
  linarith

/-! ### Undoing the scaling -/

/-- **Item 4, unscaled basis.** For any positive scaling `s` that is `1/10⁴` on the `E₁₂` block, a matrix
`M` whose scaled entries `M_ij/(s_i s_j)` lie in the exported balls satisfies
`β₂ Σ_{i ≥ 61} y_i² ≤ Σ M_ij y_i y_j`, `β₂ = 13/10⁹ = 1.3e-8`. -/
theorem item4_floor_unscaled (M : Fin 73 → Fin 73 → ℝ) (s : Fin 73 → ℝ) (hs : ∀ i, 0 < s i)
    (hE : ∀ i : Fin 73, 61 ≤ (i : ℕ) → s i = 1 / 10 ^ 4)
    (hball : ∀ i j : Fin 73, |M i j / (s i * s j) - cenR i j| ≤ radR i j) (y : Fin 73 → ℝ) :
    (13 / 10 ^ 9 : ℝ) * ∑ i : Fin 73, (if 61 ≤ (i : ℕ) then y i ^ 2 else 0)
      ≤ ∑ i : Fin 73, ∑ j : Fin 73, M i j * y i * y j := by
  have h := item4_floor (fun i j => M i j / (s i * s j)) hball (fun i => s i * y i)
  have e1 : ∀ i j : Fin 73, M i j / (s i * s j) * (s i * y i) * (s j * y j) = M i j * y i * y j := by
    intro i j
    have := (hs i).ne'; have := (hs j).ne'
    field_simp
  have e2 : ∀ i : Fin 73, (if 61 ≤ (i : ℕ) then (s i * y i) ^ 2 else 0)
      = (1 / 10 ^ 8 : ℝ) * (if 61 ≤ (i : ℕ) then y i ^ 2 else 0) := by
    intro i
    by_cases h61 : 61 ≤ (i : ℕ)
    · simp only [h61, if_true, hE i h61]
      ring
    · simp [h61]
  simp_rw [e1, e2] at h
  rw [← mul_sum, ← mul_assoc] at h
  have : (13 / 10 : ℝ) * (1 / 10 ^ 8) = 13 / 10 ^ 9 := by norm_num
  rw [this] at h
  exact h

end GppOddFaceItem4

#print axioms GppOddFaceItem4.rowsAll
#print axioms GppOddFaceItem4.Nm_quad_nonneg
#print axioms GppOddFaceItem4.item4_floor
#print axioms GppOddFaceItem4.item4_floor_unscaled
