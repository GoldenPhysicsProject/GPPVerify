import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.QuadraticDiscriminant
import GppVerify.RiemannHypothesis.RadicalPoleThreshold
import Mathlib.Tactic

/-!
# Finite-dimensional core of the Mestre-type analytic-rank bound

Galerkin setting for the elliptic Weil form `Q_L^E` (GPP-bridge `GOLDEN_EYE_NOTES.md`):
`Q` is the real symmetric matrix of the explicit-formula quadratic form on a finite test-function
basis, and `v` is the vector of `f̂(0)` values. Under GRH(E), each zero contributes `|f̂(γ)|² ≥ 0`
and the central zero contributes `r · (v ⬝ᵥ x)²`. So `Q = Q' + r • vecMulVec v v` with `Q' ⪰ 0`.

Proved here, with no analytic input:

* `sub_rankOne_posSemidef`: that decomposition gives `Q - r • vvᵀ ⪰ 0`.
* `rankOne_lower`: `r · (v ⬝ᵥ x)² ≤ xᵀ Q x` for every `x`.
* `rank_le_ratio`: hence `r ≤ xᵀQx / (v ⬝ᵥ x)²` for every test vector with `v ⬝ᵥ x ≠ 0`.
  This is the form the Arb certificate uses, with one float-chosen `x`.
* `sq_dot_le_mul_invForm`: Cauchy–Schwarz, `(v ⬝ᵥ x)² ≤ (xᵀQx) (vᵀQ⁻¹v)` for `Q ≻ 0`.
* `rank_le_inv_invForm`: `r ≤ 1 / (vᵀ Q⁻¹ v)` for `Q ≻ 0` and `v ≠ 0`. The bound is attained at
  `x = Q⁻¹ v` (`invForm_attained`), so `1/(vᵀQ⁻¹v)` is the minimum of the ratio.

Honest boundary. Nothing here touches L-functions, GRH(E), the explicit formula, or BSD.
The decomposition hypothesis `Q = Q' + r • vvᵀ, Q' ⪰ 0` is exactly where GRH(E) and the
explicit formula enter. It is an assumption in these theorems, not a result.
Carrier search (rule 3): `GppWeilParity.rankOne_sub_nonneg_iff` (scalar `ℓ²/2` pole channel) and
`GppRadicalPoleThreshold.rankOne_mulVec` (reused below) were the nearest existing carriers.
-/

namespace GppMestreRankBound

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The quadratic form `xᵀ Q x`. -/
def qf (Q : Matrix n n ℝ) (x : n → ℝ) : ℝ := x ⬝ᵥ (Q *ᵥ x)

omit [DecidableEq n] in
theorem qf_add_rankOne (Q' : Matrix n n ℝ) (r : ℝ) (v x : n → ℝ) :
    qf (Q' + r • vecMulVec v v) x = qf Q' x + r * (v ⬝ᵥ x) ^ 2 := by
  unfold qf
  rw [add_mulVec, smul_mulVec, GppRadicalPoleThreshold.rankOne_mulVec, dotProduct_add,
    dotProduct_smul, dotProduct_smul, dotProduct_comm x v]
  simp only [smul_eq_mul]
  ring

omit [Fintype n] [DecidableEq n] in
/-- GRH-shaped decomposition ⇒ `Q - r vvᵀ ⪰ 0`. -/
theorem sub_rankOne_posSemidef {Q Q' : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (hQ' : Q'.PosSemidef) (h : Q = Q' + r • vecMulVec v v) :
    (Q - r • vecMulVec v v).PosSemidef := by
  subst h
  simpa using hQ'

omit [DecidableEq n] in
/-- GRH-shaped decomposition ⇒ `r (v ⬝ x)² ≤ xᵀQx` for all `x`. -/
theorem rankOne_lower {Q Q' : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (hQ' : Q'.PosSemidef) (h : Q = Q' + r • vecMulVec v v) (x : n → ℝ) :
    r * (v ⬝ᵥ x) ^ 2 ≤ qf Q x := by
  have h0 : 0 ≤ qf Q' x := by
    have := (posSemidef_iff_dotProduct_mulVec.mp hQ').2 x
    simpa [qf] using this
  rw [h, qf_add_rankOne]
  linarith

omit [DecidableEq n] in
/-- Any single test vector bounds the central multiplicity. -/
theorem rank_le_ratio {Q : Matrix n n ℝ} {r : ℝ} {v x : n → ℝ}
    (H : ∀ y, r * (v ⬝ᵥ y) ^ 2 ≤ qf Q y) (hx : v ⬝ᵥ x ≠ 0) :
    r ≤ qf Q x / (v ⬝ᵥ x) ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  exact H x

omit [DecidableEq n] in
theorem dotProduct_mulVec_symm {Q : Matrix n n ℝ} (hsym : Qᵀ = Q) (x y : n → ℝ) :
    x ⬝ᵥ (Q *ᵥ y) = y ⬝ᵥ (Q *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hsym, dotProduct_comm]

theorem mulVec_inv_mulVec {Q : Matrix n n ℝ} (hQ : Q.PosDef) (v : n → ℝ) :
    Q *ᵥ (Q⁻¹ *ᵥ v) = v := by
  have hu : IsUnit Q.det := (isUnit_iff_isUnit_det Q).mp hQ.isUnit
  rw [mulVec_mulVec, mul_nonsing_inv Q hu, one_mulVec]

theorem invForm_pos {Q : Matrix n n ℝ} (hQ : Q.PosDef) {v : n → ℝ} (hv : v ≠ 0) :
    0 < v ⬝ᵥ (Q⁻¹ *ᵥ v) := by
  simpa using hQ.inv.dotProduct_mulVec_pos hv

omit [Fintype n] [DecidableEq n] in
theorem posDef_symm {Q : Matrix n n ℝ} (hQ : Q.PosDef) : Qᵀ = Q := by
  have h := hQ.isHermitian
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h
  exact h

/-- At `x = Q⁻¹v` both `xᵀQx` and `v ⬝ x` equal `vᵀQ⁻¹v`. -/
theorem invForm_attained {Q : Matrix n n ℝ} (hQ : Q.PosDef) (v : n → ℝ) :
    qf Q (Q⁻¹ *ᵥ v) = v ⬝ᵥ (Q⁻¹ *ᵥ v) := by
  unfold qf
  rw [mulVec_inv_mulVec hQ, dotProduct_comm]

/-- Cauchy–Schwarz for `Q ≻ 0`: `(v ⬝ x)² ≤ (xᵀQx)(vᵀQ⁻¹v)`. -/
theorem sq_dot_le_mul_invForm {Q : Matrix n n ℝ} (hQ : Q.PosDef) (v x : n → ℝ) :
    (v ⬝ᵥ x) ^ 2 ≤ qf Q x * (v ⬝ᵥ (Q⁻¹ *ᵥ v)) := by
  set y := Q⁻¹ *ᵥ v with hy
  have hsym := posDef_symm hQ
  have hB : v ⬝ᵥ x = x ⬝ᵥ (Q *ᵥ y) := by
    rw [hy, mulVec_inv_mulVec hQ, dotProduct_comm]
  have hc : v ⬝ᵥ y = qf Q y := (invForm_attained hQ v).symm
  have hpsd := (posSemidef_iff_dotProduct_mulVec.mp hQ.posSemidef).2
  have key : ∀ t : ℝ, 0 ≤ qf Q y * (t * t) + (2 * (x ⬝ᵥ (Q *ᵥ y))) * t + qf Q x := by
    intro t
    have h1 := hpsd (x + t • y)
    simp only [star_trivial] at h1
    have hs := dotProduct_mulVec_symm hsym x y
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul] at h1
    rw [← hs] at h1
    unfold qf
    have e : y ⬝ᵥ (Q *ᵥ y) * (t * t) + 2 * (x ⬝ᵥ (Q *ᵥ y)) * t + x ⬝ᵥ (Q *ᵥ x) =
        x ⬝ᵥ (Q *ᵥ x) + t * (x ⬝ᵥ (Q *ᵥ y)) + t * (x ⬝ᵥ (Q *ᵥ y) + t * (y ⬝ᵥ (Q *ᵥ y))) := by
      ring
    rw [e]; exact h1
  have hd := discrim_le_zero key
  unfold discrim at hd
  rw [hB, hc]
  nlinarith [hd]

/-- Mestre-type bound in inverse-form shape: `r ≤ 1/(vᵀQ⁻¹v)`. -/
theorem rank_le_inv_invForm {Q : Matrix n n ℝ} {r : ℝ} {v : n → ℝ} (hQ : Q.PosDef)
    (hv : v ≠ 0) (H : ∀ y, r * (v ⬝ᵥ y) ^ 2 ≤ qf Q y) :
    r ≤ 1 / (v ⬝ᵥ (Q⁻¹ *ᵥ v)) := by
  have hc := invForm_pos hQ hv
  have h := H (Q⁻¹ *ᵥ v)
  rw [invForm_attained hQ v] at h
  rw [le_div_iff₀ hc]
  nlinarith [h, hc]

/-- End-to-end finite statement: decomposition with `Q' ⪰ 0`, `Q ≻ 0`, `v ≠ 0` ⇒
`r ≤ 1/(vᵀQ⁻¹v)`. In the application, `r` is the analytic rank and the decomposition is GRH(E). -/
theorem mestre_rank_bound {Q Q' : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (hQ : Q.PosDef) (hQ' : Q'.PosSemidef) (h : Q = Q' + r • vecMulVec v v) (hv : v ≠ 0) :
    r ≤ 1 / (v ⬝ᵥ (Q⁻¹ *ᵥ v)) :=
  rank_le_inv_invForm hQ hv (rankOne_lower hQ' h)

end GppMestreRankBound
