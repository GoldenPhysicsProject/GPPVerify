import GppVerify.RiemannHypothesis.Phat6RectangularFactor
import Mathlib.Algebra.Order.Chebyshev

/-!
# A quantitative margin for Turbo's `P̂₆`, and its transfer to nearby real matrices

Source: Codex, GPP-bridge PR #11 comment 6376664595 (2026-10-23), with private proof in
`work/codex/2026-10-23_phat6_exact_shifted_ldl_robust_interval_gate.md`. It builds on Turbo's `P̂₆`
data (`MuseResearch/Phat6Data.lean`, bridge `feedac1`) and `GppPhat6.phat6_eq` (#424). Daniel
Toupin / Golden Physics Project, with AI assistance from Codex (statement) and Claude Code (shifted
`LDLᵀ` data, independently recomputed, and formalization).

* `phat6_shift_ldl`: `P̂₆ − c·I = L D Lᵀ` over `ℚ` with `c = 1/5000000`, for an explicit unit lower
  triangular `L` and diagonal `D`.
* `dvec_pos`: all six pivots of `D` are positive.
* `phat6_margin`: `c ‖x‖² ≤ xᵀ P̂₆ x` for every real `x`, i.e. `P̂₆ ⪰ 2·10⁻⁷ I`.
* `margin_of_entrywise`: if any real `A` satisfies `|A_ij − P̂₆_ij| ≤ δ` for all
  `i, j`, then `(c − 6δ) ‖x‖² ≤ xᵀ A x`. With `δ ≤ 10⁻⁸` this gives `A ⪰ 1.4·10⁻⁷ I`.

**Scope.** The entrywise bound `δ` for the arithmetic matrix `P̂₆` was rounded from is **not**
supplied here. That is the open interval-enclosure obligation Codex names. Finite `K = 6` only. No
claim about RH.
-/

open Matrix

namespace GppPhat6

/-- The unit lower triangular factor of `P̂₆ − c·I`. -/
def Lmat : Matrix (Fin 6) (Fin 6) ℚ :=
  Matrix.of ![
    ![(1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)],
    ![(-77767283/215056684 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)],
    ![(-55647157/107528342 : ℚ), (-840367034122010/858153135313607 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)],
    ![(70505260/53764171 : ℚ), (4226576034095720/7723378217822463 : ℚ), (-1604004801145800476391/827241904051944275686 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ)],
    ![(-90899753/53764171 : ℚ), (-663662136462980/1103339745403209 : ℚ), (961356135754162226953/827241904051944275686 : ℚ), (-5656156744101995720100261737/2314232690614577589284833511 : ℚ), (1 : ℚ), (0 : ℚ)],
    ![(81977899/53764171 : ℚ), (10268601864325664/7723378217822463 : ℚ), (-518111140643321314471/413620952025972137843 : ℚ), (40979752309946947832330678374/11571163453072887946424167555 : ℚ), (-1260469505830672407771170887025165/2315801992471564593667712277895501 : ℚ), (1 : ℚ)]
  ]

/-- The pivots of `P̂₆ − c·I`. -/
def dvec : Fin 6 → ℚ := ![(53764171/250000000000 : ℚ), (7723378217822463/215056684000000000000 : ℚ), (413620952025972137843/429076567656803500000000000 : ℚ), (2314232690614577589284833511/1489035427293499696234800000000000 : ℚ), (2315801992471564593667712277895501/2314232690614577589284833511000000000000 : ℚ), (29561268842949225829542223682959650634721/11579009962357822968338561389477505000000000000 : ℚ)]

/-- The shift `c = 1/5000000`. -/
def shift : ℚ := 1 / 5000000

theorem phat6_shift_ldl :
    Phat6 = Lmat * diagonal dvec * Lmatᵀ + diagonal (fun _ => shift) := by
  ext i j
  rw [Matrix.add_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Phat6, Lmat, dvec, shift, Fin.sum_univ_succ] <;> norm_num

theorem dvec_pos (i : Fin 6) : 0 < dvec i := by
  fin_cases i <;> simp [dvec]

/-- `P̂₆` cast to `ℝ`. -/
noncomputable def PhatR : Matrix (Fin 6) (Fin 6) ℝ := Phat6.map (Rat.cast : ℚ → ℝ)

lemma phatR_eq : PhatR = (Lmat.map (Rat.cast : ℚ → ℝ)) * diagonal (fun i => (dvec i : ℝ)) *
    (Lmat.map (Rat.cast : ℚ → ℝ))ᵀ + diagonal (fun _ => ((shift : ℚ) : ℝ)) := by
  have h := congrArg (Rat.castHom ℝ).mapMatrix phat6_shift_ldl
  simp only [map_add, map_mul, RingHom.mapMatrix_apply, Rat.coe_castHom] at h
  rw [PhatR, h, transpose_map, diagonal_map (by simp), diagonal_map (by simp)]

/-- **The margin** `P̂₆ ⪰ c·I`: `c ‖x‖² ≤ xᵀ P̂₆ x`. -/
theorem phat6_margin (x : Fin 6 → ℝ) : ((shift : ℚ) : ℝ) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (PhatR *ᵥ x) := by
  set LR := Lmat.map (Rat.cast : ℚ → ℝ)
  set y := LRᵀ *ᵥ x
  have hq : x ⬝ᵥ ((LR * diagonal (fun i => (dvec i : ℝ)) * LRᵀ) *ᵥ x)
      = ∑ i, (dvec i : ℝ) * (y i * y i) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
    simp only [dotProduct, mulVec_diagonal, y]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hnn : 0 ≤ ∑ i, (dvec i : ℝ) * (y i * y i) :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (by exact_mod_cast (dvec_pos i).le) (mul_self_nonneg _)
  have hs : x ⬝ᵥ (diagonal (fun _ => ((shift : ℚ) : ℝ)) *ᵥ x) = ((shift : ℚ) : ℝ) * (x ⬝ᵥ x) := by
    simp only [dotProduct, mulVec_diagonal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [phatR_eq, add_mulVec, dotProduct_add, hq, hs]
  linarith

/-- **Transfer to a nearby matrix.** An entrywise error `δ` costs at most `6δ` of margin. -/
theorem margin_of_entrywise (A : Matrix (Fin 6) (Fin 6) ℝ) {δ : ℝ}
    (hA : ∀ i j, |A i j - PhatR i j| ≤ δ) (x : Fin 6 → ℝ) :
    (((shift : ℚ) : ℝ) - 6 * δ) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (hA 0 0)
  set E := A - PhatR
  have hsplit : x ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (PhatR *ᵥ x) + x ⬝ᵥ (E *ᵥ x) := by
    rw [← dotProduct_add, ← add_mulVec]; simp [E]
  have hE : |x ⬝ᵥ (E *ᵥ x)| ≤ δ * (∑ i, |x i|) ^ 2 := by
    simp only [dotProduct, mulVec]
    calc |∑ i, x i * ∑ j, E i j * x j|
        ≤ ∑ i, |x i| * ∑ j, δ * |x j| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hA i j) (abs_nonneg _)
      _ = δ * (∑ i, |x i|) ^ 2 := by
          have hi : ∀ i, |x i| * ∑ j, δ * |x j| = δ * (∑ j, |x j|) * |x i| := fun i => by
            rw [← Finset.mul_sum]; ring
          simp_rw [hi, ← Finset.mul_sum]
          ring
  have hcs : (∑ i, |x i|) ^ 2 ≤ 6 * (x ⬝ᵥ x) := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |x i|)
    simpa [dotProduct, sq_abs, ← sq] using this
  have hm := phat6_margin x
  have := neg_abs_le (x ⬝ᵥ (E *ᵥ x))
  nlinarith [mul_le_mul_of_nonneg_left hcs hδ]

end GppPhat6
