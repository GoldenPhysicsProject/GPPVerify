import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.RCLike.Basic

/-!
# Thread Weil-Parity — cross-resolvent / parity-crossing core

From `public.formalization_queue` (Supabase project `dunrgpupddbmzffntwph`), section
"A. WEIL-PARITY CORE". These are abstract, hypothesis-explicit finite-dimensional linear
algebra facts about generic parity-decomposed operators. They are proved here exactly as
stated in the queue, following the explicit instruction to attempt every queued item
directly in Lean rather than pre-filtering by hand.

**Read `research_notes` before trusting anything about the actual arithmetic instance.**
Row `35a9efdc…` records a stress-test counterexample: the finite CCM (Connes–Consani)
prime–Archimedean Gram matrix does *not* have a universally positive commuting metric —
the top residue at `c=13,N=6` is negative. So the positivity hypotheses these theorems
need (`c_j > 0` for all `j`, or `f(z) > 0` below the ground) are **not** established for
the actual arithmetic object globally; only a weaker "positive below the ground" target
survives. These theorems are real and unconditional as stated — abstract implications —
but nothing here proves anything about the real Weil operator's spectrum, and nothing
here is a step toward RH by itself.
-/

open Matrix

section CrossResolventDeterminant

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Formalization-queue item `3ebed50a`, "Parity displacement cross-resolvent determinant
identity", coordinate form. The even block `A` is given in `Unit ⊕ n` block form with
scalar `α`, row `p`, column `β`, and `n × n` block `E`; the odd block
`B := E - β η'ᵀ` is exactly the shape the Sylvester relation `C A - B C = β η'ᵀ` forces
when `C : Unit ⊕ n → n` is the coordinate projection and `e0`/`η = (1, η')` are the
standard basis vector / functional of the `Unit` summand. This is the reduction of the
abstract statement (arbitrary `V`, `W`, surjective `C` with `ker C = span{e0}`) to
coordinates adapted to `ker C`; choosing such a basis is exactly what the abstract
hypotheses force, so this coordinate form carries the full mathematical content.

Claim: `det(B - zI) = det(A - zI) · η ((A-zI)⁻¹ e0)`. Proved via the Schur complement
(`Matrix.det_fromBlocks₂₂`) for `det(A-zI)` and the Matrix determinant lemma
(`Matrix.det_add_mul`) for `det(B-zI)` as a rank-one update of the same Schur block. -/
theorem cross_resolvent_det_identity
    (α : ℂ) (p β η' : n → ℂ) (E : Matrix n n ℂ) (z : ℂ)
    (hD : Invertible (E - z • (1 : Matrix n n ℂ))) :
    let A : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ :=
      Matrix.fromBlocks (fun (_ : Unit) (_ : Unit) => α) (fun (_ : Unit) j => p j)
        (fun i (_ : Unit) => β i) E
    let B : Matrix n n ℂ := E - Matrix.vecMulVec β η'
    let e0 : Unit ⊕ n → ℂ := Sum.elim (fun _ => (1 : ℂ)) 0
    let η : Unit ⊕ n → ℂ := Sum.elim (fun _ => (1 : ℂ)) η'
    ∀ hA : Invertible (A - z • (1 : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ)),
      det (B - z • (1 : Matrix n n ℂ))
        = det (A - z • (1 : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ))
            * (η ⬝ᵥ ((A - z • (1 : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ))⁻¹ *ᵥ e0)) := by
  intro A B e0 η hA
  set D : Matrix n n ℂ := E - z • (1 : Matrix n n ℂ) with hDdef
  set AzI : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ := A - z • (1 : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ)
    with hAzIdef
  have hAdef : A = Matrix.fromBlocks (fun (_ : Unit) (_ : Unit) => α) (fun (_ : Unit) j => p j)
      (fun i (_ : Unit) => β i) E := rfl
  -- Step 1: block form of `A - zI`.
  have hblock : AzI = Matrix.fromBlocks (fun (_ : Unit) (_ : Unit) => α - z)
      (fun (_ : Unit) j => p j) (fun i (_ : Unit) => β i) D := by
    rw [hAzIdef, hDdef, hAdef]
    ext (i | i) (j | j) <;>
      simp [Matrix.fromBlocks, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  -- Step 2: Schur complement scalar `s`.
  set s : ℂ := (α - z) - p ⬝ᵥ (D⁻¹ *ᵥ β) with hsdef
  have hdetA : det AzI = det D * s := by
    rw [hblock, det_fromBlocks₂₂ _ _ _ _]
    congr 1
    rw [det_unique, Matrix.invOf_eq_nonsing_inv, hsdef]
    show (α - z) - (Matrix.of (fun (_ : Unit) j => p j) * D⁻¹ *
      Matrix.of (fun i (_ : Unit) => β i)) default default = (α - z) - p ⬝ᵥ (D⁻¹ *ᵥ β)
    congr 1
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.mulVec, dotProduct]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum, mul_assoc]
  -- Step 3: det(B - zI) via the Matrix determinant lemma (rank-one update of `D`).
  have hBzI : B - z • (1 : Matrix n n ℂ)
      = D + Matrix.of (fun i (_ : Unit) => -β i) * Matrix.of (fun (_ : Unit) j => η' j) := by
    show E - Matrix.vecMulVec β η' - z • (1 : Matrix n n ℂ) = D + _
    rw [hDdef]
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
    ring
  have hdetB : det (B - z • (1 : Matrix n n ℂ)) = det D * (1 - η' ⬝ᵥ (D⁻¹ *ᵥ β)) := by
    rw [hBzI, det_add_mul _ _ (isUnit_det_of_invertible (A := D))]
    congr 1
    rw [det_unique]
    show 1 + (Matrix.of (fun (_ : Unit) j => η' j) * D⁻¹ *
      Matrix.of (fun i (_ : Unit) => -β i)) default default = 1 - η' ⬝ᵥ (D⁻¹ *ᵥ β)
    rw [sub_eq_add_neg]
    congr 1
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.mulVec, dotProduct]
    simp_rw [Finset.sum_mul, mul_neg, Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum, mul_assoc]
  -- `s ≠ 0`: `AzI` and `D` are both invertible, and `det AzI = det D * s`.
  have hDdet_ne : D.det ≠ 0 := (isUnit_det_of_invertible (A := D)).ne_zero
  have hAdet_ne : AzI.det ≠ 0 := (isUnit_det_of_invertible (A := AzI)).ne_zero
  have hs_ne : s ≠ 0 := by
    intro h
    rw [h, mul_zero] at hdetA
    exact hAdet_ne hdetA
  -- Step 4: exhibit `AzI⁻¹ *ᵥ e0` explicitly.
  set x0 : ℂ := s⁻¹ with hx0def
  set x' : n → ℂ := -x0 • (D⁻¹ *ᵥ β) with hx'def
  set x : Unit ⊕ n → ℂ := Sum.elim (fun _ => x0) x' with hxdef
  have hxeq : AzI *ᵥ x = e0 := by
    rw [hblock]
    ext (i | i)
    · show ∑ j : Unit ⊕ n, (Matrix.fromBlocks (fun (_ : Unit) (_ : Unit) => α - z)
          (fun (_ : Unit) j => p j) (fun i (_ : Unit) => β i) D) (Sum.inl i) j * x j = e0 (Sum.inl i)
      rw [Fintype.sum_sum_type]
      simp only [hxdef, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Finset.sum_const, Finset.card_univ, Fintype.card_unit,
        one_smul, Matrix.mulVec, dotProduct]
      show (α - z) * x0 + ∑ j, p j * x' j = 1
      rw [hx'def]
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
      show (α - z) * x0 + ∑ j, p j * (-x0 * ∑ k, D⁻¹ j k * β k) = 1
      have : ∑ j, p j * (-x0 * ∑ k, D⁻¹ j k * β k) = -x0 * (p ⬝ᵥ (D⁻¹ *ᵥ β)) := by
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.mul_sum]
        congr 1
        ext j
        ring
      rw [this, hx0def]
      have hstep : (α - z) * s⁻¹ + -s⁻¹ * (p ⬝ᵥ (D⁻¹ *ᵥ β)) = s * s⁻¹ := by
        rw [hsdef]; ring
      rw [hstep, mul_inv_cancel₀ hs_ne]
    · show ∑ j : Unit ⊕ n, (Matrix.fromBlocks (fun (_ : Unit) (_ : Unit) => α - z)
          (fun (_ : Unit) j => p j) (fun i (_ : Unit) => β i) D) (Sum.inr i) j * x j = e0 (Sum.inr i)
      rw [Fintype.sum_sum_type]
      simp only [hxdef, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂]
      show ∑ _j : Unit, β i * x0 + ∑ j, D i j * x' j = e0 (Sum.inr i)
      show ∑ _j : Unit, β i * x0 + ∑ j, D i j * x' j = (0 : n → ℂ) i
      simp only [Pi.zero_apply, Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul,
        smul_eq_mul]
      rw [hx'def]
      simp only [Pi.smul_apply, smul_eq_mul]
      show β i * x0 + ∑ j, D i j * (-x0 * (D⁻¹ *ᵥ β) j) = 0
      have hcol : ∑ j, D i j * (-x0 * (D⁻¹ *ᵥ β) j) = -x0 * (D *ᵥ (D⁻¹ *ᵥ β)) i := by
        show ∑ j, D i j * (-x0 * (D⁻¹ *ᵥ β) j) = -x0 * ∑ j, D i j * (D⁻¹ *ᵥ β) j
        rw [Finset.mul_sum]
        congr 1
        ext j
        ring
      rw [hcol, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_of_invertible (A := D))]
      simp only [Matrix.one_mulVec]
      show β i * x0 + -x0 * β i = 0
      ring
  -- Step 5: `x = AzI⁻¹ *ᵥ e0`, and compute `η ⬝ᵥ x`.
  have hxinv : x = AzI⁻¹ *ᵥ e0 := by
    rw [← hxeq, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_det_of_invertible (A := AzI)), Matrix.one_mulVec]
  have hetax : η ⬝ᵥ x = x0 * (1 - η' ⬝ᵥ (D⁻¹ *ᵥ β)) := by
    show ∑ j : Unit ⊕ n, η j * x j = x0 * (1 - η' ⬝ᵥ (D⁻¹ *ᵥ β))
    rw [Fintype.sum_sum_type]
    simp only [hxdef, Sum.elim_inl, Sum.elim_inr]
    show ∑ _j : Unit, (1 : ℂ) * x0 + ∑ j, η' j * x' j = x0 * (1 - η' ⬝ᵥ (D⁻¹ *ᵥ β))
    simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul]
    rw [hx'def]
    have : ∑ j, η' j * (-x0 • (D⁻¹ *ᵥ β)) j = -x0 * (η' ⬝ᵥ (D⁻¹ *ᵥ β)) := by
      show ∑ j, η' j * (-x0 * (D⁻¹ *ᵥ β) j) = -x0 * ∑ j, η' j * (D⁻¹ *ᵥ β) j
      rw [Finset.mul_sum]
      congr 1
      ext j
      ring
    rw [this]
    ring
  -- Step 6: assemble.
  rw [hdetB, hdetA, ← hxinv, hetax, hx0def]
  field_simp

end CrossResolventDeterminant

section ParityCrossingObstruction

open scoped ComplexOrder

variable {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

/-- The outer product `w vᴴ` sends `x ↦ (v ⬝ᵥ x) • w`. -/
theorem vecMulVec_mulVec (w : q → ℂ) (v : p → ℂ) (x : p → ℂ) :
    (Matrix.vecMulVec w v) *ᵥ x = (v ⬝ᵥ x) • w := by
  funext i
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul]
  calc ∑ j, w i * v j * x j = ∑ j, v j * x j * w i := by
        apply Finset.sum_congr rfl; intro j _; ring
    _ = (∑ j, v j * x j) * w i := by rw [Finset.sum_mul]

/-- Self-adjoint pairing identity: for Hermitian `M` with `M *ᵥ x = μ • x`,
`⟪x, M v⟫ = conj(μ) · ⟪x, v⟫` for every `v`. -/
theorem hermitian_dotProduct_mulVec {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.IsHermitian) (mu : ℂ) (x v : n → ℂ)
    (hx : M *ᵥ x = mu • x) :
    star x ⬝ᵥ (M *ᵥ v) = star mu * (star x ⬝ᵥ v) := by
  have h1 : star x ⬝ᵥ (M *ᵥ v) = (star x ᵥ* M) ⬝ᵥ v := (Matrix.dotProduct_mulVec _ _ _)
  have h2 : star x ᵥ* M = star (Mᴴ *ᵥ x) := by
    rw [Matrix.star_mulVec]
    simp
  rw [h1, h2, hM.eq, hx]
  simp [Matrix.dotProduct_smul]

/-- Formalization-queue item `0cf9aebf`, "Parity crossing obstruction from rank-one
Sylvester displacement". If `C Aplus - Aminus C = β ηᴴ` and `lam` is a common eigenvalue
of the Hermitian odd block `Aminus` (nonzero eigenvector `o`) and the even block `Aplus`
(eigenvector `e`), then `⟪o,β⟫ · ⟪η,e⟫ = 0`. Only `Aminus` needs to be Hermitian for this
argument (kept as a hypothesis for fidelity to the queue item's physical setup, even
though the proof does not use `hAplus`). -/
theorem parity_crossing_obstruction
    (Aplus : Matrix p p ℂ) (Aminus : Matrix q q ℂ)
    (hAplus : Aplus.IsHermitian) (hAminus : Aminus.IsHermitian)
    (C : Matrix q p ℂ) (β : q → ℂ) (η : p → ℂ)
    (hsyl : C * Aplus - Aminus * C = Matrix.vecMulVec β (star η))
    (lam : ℂ) (e : p → ℂ) (o : q → ℂ) (ho : o ≠ 0)
    (he_eig : Aplus *ᵥ e = lam • e) (ho_eig : Aminus *ᵥ o = lam • o) :
    (star o ⬝ᵥ β) * (star η ⬝ᵥ e) = 0 := by
  have hoo_ne : star o ⬝ᵥ o ≠ 0 := by
    rw [Ne, dotProduct_star_self_eq_zero]
    exact ho
  have hreal : star lam = lam := by
    have h1 : star o ⬝ᵥ (Aminus *ᵥ o) = lam * (star o ⬝ᵥ o) := by
      rw [ho_eig, dotProduct_smul, smul_eq_mul]
    have h2 : star o ⬝ᵥ (Aminus *ᵥ o) = star lam * (star o ⬝ᵥ o) :=
      hermitian_dotProduct_mulVec Aminus hAminus lam o o ho_eig
    have heq := h1.symm.trans h2
    exact mul_right_cancel₀ hoo_ne heq.symm
  have hkey : C *ᵥ (Aplus *ᵥ e) - Aminus *ᵥ (C *ᵥ e) = (star η ⬝ᵥ e) • β := by
    have hlhs : (C * Aplus - Aminus * C) *ᵥ e = C *ᵥ (Aplus *ᵥ e) - Aminus *ᵥ (C *ᵥ e) := by
      rw [Matrix.sub_mulVec, mulVec_mulVec e C Aplus, mulVec_mulVec e Aminus C]
    have hrhs : (Matrix.vecMulVec β (star η)) *ᵥ e = (star η ⬝ᵥ e) • β :=
      vecMulVec_mulVec β (star η) e
    rw [← hlhs, hsyl, hrhs]
  -- Pair `hkey` against `o` using `hermitian_dotProduct_mulVec` on the `Aminus` term.
  have hpair : star o ⬝ᵥ (C *ᵥ (Aplus *ᵥ e)) - star o ⬝ᵥ (Aminus *ᵥ (C *ᵥ e))
      = (star η ⬝ᵥ e) * (star o ⬝ᵥ β) := by
    have := congrArg (fun v => star o ⬝ᵥ v) hkey
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul] at this
    linear_combination this
  have hA_term : star o ⬝ᵥ (Aminus *ᵥ (C *ᵥ e)) = lam * (star o ⬝ᵥ (C *ᵥ e)) := by
    rw [hermitian_dotProduct_mulVec Aminus hAminus lam o (C *ᵥ e) ho_eig, hreal]
  have hA_pos_term : star o ⬝ᵥ (C *ᵥ (Aplus *ᵥ e)) = lam * (star o ⬝ᵥ (C *ᵥ e)) := by
    rw [he_eig, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  rw [hA_pos_term, hA_term, sub_self] at hpair
  linear_combination -hpair

end ParityCrossingObstruction
