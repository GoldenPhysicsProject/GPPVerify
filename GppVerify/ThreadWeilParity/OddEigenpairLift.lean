import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.RCLike.Basic

/-!
# Thread Weil-Parity — odd eigenpair canonical lift and the Schur-Rayleigh defect

From `public.formalization_queue` (Supabase project `dunrgpupddbmzffntwph`), item
`c0c96bbc-3dcc-44a3-9408-cc8d523cf5c6`, "Odd eigenpair canonical lift and Schur-Rayleigh
defect identity". Builds directly on `ThreadWeilParity/CrossResolvent.lean`'s block
structure and Schur-complement scalar (there called `s`, here `phiSchur`).

Setup: `Aplus = [[a, bᴴ], [b, E]]` on `Unit ⊕ n`, `Aminus` on `n`, `D : n → n` invertible,
`C = (0, D)`, `η = (1, η1)`, and the Sylvester relation `C Aplus - Aminus C = (Db) ηᴴ`.
Given an `Aminus`-eigenpair `(λ, y)`, set `x1 := D⁻¹y`.

* `odd_eigenpair_defect_step1`: `(E - λI) x1 = s • b`, where `s := η1ᴴ x1` — PROVED, direct
  from the Sylvester relation applied at `(0, x1)`.
* `odd_eigenpair_defect_step2`: if `E - λI` is invertible, `x1 = s • (E-λI)⁻¹b` — PROVED,
  by applying `(E-λI)⁻¹` to step 1.
* `odd_eigenpair_canonical_lift`: the canonical lift `x := s • (-1, (E-λI)⁻¹b)` satisfies
  `η* x = 0` and `(Aplus - λI) x = -s·φ(λ)·e0`, where `φ(λ) := a - λ - bᴴ(E-λI)⁻¹b` is
  exactly the Schur complement scalar from the cross-resolvent identity — PROVED, but
  **note the extra hypothesis `hw1 : η1ᴴ((E-λI)⁻¹b) = 1`**. This is not a free-standing
  fact about arbitrary `b`, `η1`, `E`, `λ`: combining step 1 and step 2 forces it
  automatically whenever `s ≠ 0` (dividing `s = η1ᴴx1 = η1ᴴ(s•(E-λI)⁻¹b) = s·(η1ᴴ(E-λI)⁻¹b)`
  by `s` gives `η1ᴴ(E-λI)⁻¹b = 1`) — it is a genuine solvability/quantization condition on
  `λ`, not an independent assumption, so it is stated here explicitly rather than smuggled
  in. The consequence `⟪x,(Aplus-λI)x⟫ = |s|²φ(λ)` (the item's closing Rayleigh-quotient
  remark) follows immediately from the second conjunct plus `η*x=0`/`x`'s explicit form,
  and is not separately restated as its own theorem here — it is definitionally the same
  content as `(Aplus - λI) x = -s·φ(λ)·e0` paired against `x` itself.

As with `CrossResolvent.lean`: these are abstract, unconditional facts about *any*
`(Aplus, Aminus, C, D)` satisfying the stated relations. See that file's header for the
standing warning about the real arithmetic CCM matrix's positivity hypotheses.
-/

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The coordinate projection `C = (0, D) : Unit ⊕ n → n`. -/
def CProj (D : Matrix n n ℂ) : Matrix n (Unit ⊕ n) ℂ :=
  Matrix.of (fun i => Sum.elim (fun (_ : Unit) => (0 : ℂ)) (fun j => D i j))

/-- The even block `Aplus = [[a, bᴴ], [b, E]]` on `Unit ⊕ n`. -/
def AplusBlock (a : ℂ) (b : n → ℂ) (E : Matrix n n ℂ) : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ :=
  Matrix.fromBlocks (Matrix.of fun (_ : Unit) (_ : Unit) => a) (Matrix.of fun (_ : Unit) j => star (b j))
    (Matrix.of fun i (_ : Unit) => b i) E

/-- The functional `η = (1, η1)` on `Unit ⊕ n`. -/
def etaVec (η1 : n → ℂ) : Unit ⊕ n → ℂ := Sum.elim (fun (_ : Unit) => (1 : ℂ)) η1

/-- `(fromBlocks P Q R S) *ᵥ (Sum.elim 0 v) = Sum.elim (Q *ᵥ v) (S *ᵥ v)`. -/
theorem fromBlocks_mulVec_inr {l m n' o : Type*} [Fintype l] [Fintype m]
    (P : Matrix n' l ℂ) (Q : Matrix n' m ℂ) (R : Matrix o l ℂ) (S : Matrix o m ℂ) (v : m → ℂ) :
    (Matrix.fromBlocks P Q R S) *ᵥ (Sum.elim (0 : l → ℂ) v) = Sum.elim (Q *ᵥ v) (S *ᵥ v) := by
  ext (i | i) <;> simp [Matrix.mulVec, Matrix.fromBlocks, dotProduct, Fintype.sum_sum_type]

/-- `(fromBlocks P Q R S) *ᵥ (Sum.elim u v) = Sum.elim (P*ᵥu + Q*ᵥv) (R*ᵥu + S*ᵥv)`. -/
theorem fromBlocks_mulVec_gen {l m n' o : Type*} [Fintype l] [Fintype m]
    (P : Matrix n' l ℂ) (Q : Matrix n' m ℂ) (R : Matrix o l ℂ) (S : Matrix o m ℂ)
    (u : l → ℂ) (v : m → ℂ) :
    (Matrix.fromBlocks P Q R S) *ᵥ (Sum.elim u v) = Sum.elim (P *ᵥ u + Q *ᵥ v) (R *ᵥ u + S *ᵥ v) := by
  ext (i | i) <;> simp [Matrix.mulVec, Matrix.fromBlocks, dotProduct, Fintype.sum_sum_type,
    Finset.sum_add_distrib]

/-- The outer product `w vᴴ` sends `x ↦ (v ⬝ᵥ x) • w`. -/
theorem vecMulVec_mulVec' {p q : Type*} [Fintype p] (w : q → ℂ) (v : p → ℂ) (x : p → ℂ) :
    (Matrix.vecMulVec w v) *ᵥ x = (v ⬝ᵥ x) • w := by
  funext i
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul]
  calc ∑ j, w i * v j * x j = ∑ j, v j * x j * w i := by
        apply Finset.sum_congr rfl; intro j _; ring
    _ = (∑ j, v j * x j) * w i := by rw [Finset.sum_mul]

theorem odd_eigenpair_defect_step1
    (a : ℂ) (b η1 : n → ℂ) (E : Matrix n n ℂ) (Aminus : Matrix n n ℂ)
    (D : Matrix n n ℂ) (hD : Invertible D)
    (hsyl : CProj D * AplusBlock a b E - Aminus * CProj D
      = Matrix.vecMulVec (D *ᵥ b) (star (etaVec η1)))
    (lam : ℂ) (y : n → ℂ) (hy : Aminus *ᵥ y = lam • y) :
    (E - lam • (1 : Matrix n n ℂ)) *ᵥ (D⁻¹ *ᵥ y) = (star η1 ⬝ᵥ (D⁻¹ *ᵥ y)) • b := by
  set x1 : n → ℂ := D⁻¹ *ᵥ y with hx1def
  set v : Unit ⊕ n → ℂ := Sum.elim (0 : Unit → ℂ) x1 with hvdef
  have hDx1 : D *ᵥ x1 = y := by
    rw [hx1def, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_of_invertible (A := D)),
      Matrix.one_mulVec]
  have hCproj0 : CProj D *ᵥ v = D *ᵥ x1 := by
    funext i
    show ∑ j : Unit ⊕ n, (Sum.elim (fun (_ : Unit) => (0 : ℂ)) (fun j => D i j)) j * v j
        = (D *ᵥ x1) i
    rw [hvdef, Fintype.sum_sum_type]
    simp [Matrix.mulVec, dotProduct]
  have hApv : AplusBlock a b E *ᵥ v = Sum.elim (fun (_ : Unit) => star b ⬝ᵥ x1) (E *ᵥ x1) := by
    have hthis := fromBlocks_mulVec_inr (Matrix.of fun (_ : Unit) (_ : Unit) => a)
      (Matrix.of fun (_ : Unit) j => star (b j)) (Matrix.of fun i (_ : Unit) => b i) E x1
    have hunfold : AplusBlock a b E *ᵥ v = (Matrix.fromBlocks
        (Matrix.of fun (_ : Unit) (_ : Unit) => a) (Matrix.of fun (_ : Unit) j => star (b j))
        (Matrix.of fun i (_ : Unit) => b i) E) *ᵥ (Sum.elim (0 : Unit → ℂ) x1) := by
      rw [hvdef]; rfl
    rw [hunfold, hthis]
    congr 1
  have hCApv : CProj D *ᵥ (AplusBlock a b E *ᵥ v) = D *ᵥ (E *ᵥ x1) := by
    rw [hApv]
    funext i
    show ∑ j : Unit ⊕ n, (Sum.elim (fun (_ : Unit) => (0 : ℂ)) (fun j => D i j)) j
        * (Sum.elim (fun (_ : Unit) => star b ⬝ᵥ x1) (E *ᵥ x1)) j = (D *ᵥ (E *ᵥ x1)) i
    rw [Fintype.sum_sum_type]
    simp [Matrix.mulVec, dotProduct]
  have hy' : Aminus *ᵥ (D *ᵥ x1) = lam • (D *ᵥ x1) := by rw [hDx1]; exact hy
  have hlhs : (CProj D * AplusBlock a b E - Aminus * CProj D) *ᵥ v
      = D *ᵥ ((E - lam • (1 : Matrix n n ℂ)) *ᵥ x1) := by
    have step1 : (CProj D * AplusBlock a b E - Aminus * CProj D) *ᵥ v
        = (CProj D * AplusBlock a b E) *ᵥ v - (Aminus * CProj D) *ᵥ v := Matrix.sub_mulVec _ _ _
    have step2 : (CProj D * AplusBlock a b E) *ᵥ v = CProj D *ᵥ (AplusBlock a b E *ᵥ v) :=
      (Matrix.mulVec_mulVec v (CProj D) (AplusBlock a b E)).symm
    have step3 : (Aminus * CProj D) *ᵥ v = Aminus *ᵥ (CProj D *ᵥ v) :=
      (Matrix.mulVec_mulVec v Aminus (CProj D)).symm
    have step4 : D *ᵥ ((E - lam • (1 : Matrix n n ℂ)) *ᵥ x1)
        = D *ᵥ (E *ᵥ x1) - lam • (D *ᵥ x1) := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
        Matrix.mulVec_smul]
    rw [step1, step2, step3, hCApv, hCproj0, hy', step4]
  have hrhs : (Matrix.vecMulVec (D *ᵥ b) (star (etaVec η1))) *ᵥ v
      = D *ᵥ ((star η1 ⬝ᵥ x1) • b) := by
    have hstep := vecMulVec_mulVec' (D *ᵥ b) (star (etaVec η1)) v
    have hdp : star (etaVec η1) ⬝ᵥ v = star η1 ⬝ᵥ x1 := by
      show ∑ j : Unit ⊕ n, star (etaVec η1 j) * v j = star η1 ⬝ᵥ x1
      rw [hvdef, Fintype.sum_sum_type]
      simp [etaVec, dotProduct]
    rw [hstep, hdp, Matrix.mulVec_smul]
  have heq : D *ᵥ ((E - lam • (1 : Matrix n n ℂ)) *ᵥ x1) = D *ᵥ ((star η1 ⬝ᵥ x1) • b) := by
    rw [← hlhs, hsyl, hrhs]
  exact Matrix.mulVec_injective_of_invertible D heq

theorem odd_eigenpair_defect_step2
    (a : ℂ) (b η1 : n → ℂ) (E : Matrix n n ℂ) (Aminus : Matrix n n ℂ)
    (D : Matrix n n ℂ) (hD : Invertible D)
    (hsyl : CProj D * AplusBlock a b E - Aminus * CProj D
      = Matrix.vecMulVec (D *ᵥ b) (star (etaVec η1)))
    (lam : ℂ) (y : n → ℂ) (hy : Aminus *ᵥ y = lam • y)
    (hEinv : Invertible (E - lam • (1 : Matrix n n ℂ))) :
    D⁻¹ *ᵥ y = (star η1 ⬝ᵥ (D⁻¹ *ᵥ y)) • ((E - lam • (1 : Matrix n n ℂ))⁻¹ *ᵥ b) := by
  have h1 := odd_eigenpair_defect_step1 a b η1 E Aminus D hD hsyl lam y hy
  have h2 := congrArg (fun v => (E - lam • (1 : Matrix n n ℂ))⁻¹ *ᵥ v) h1
  rw [Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_det_of_invertible (A := E - lam • (1 : Matrix n n ℂ))),
    Matrix.one_mulVec, Matrix.mulVec_smul] at h2
  exact h2

/-- The Schur complement scalar `φ(λ) = a − λ − bᴴ(E−λI)⁻¹b`. -/
noncomputable def phiSchur (a : ℂ) (b : n → ℂ) (E : Matrix n n ℂ) (lam : ℂ) : ℂ :=
  a - lam - star b ⬝ᵥ ((E - lam • (1 : Matrix n n ℂ))⁻¹ *ᵥ b)

theorem odd_eigenpair_canonical_lift
    (a : ℂ) (b η1 : n → ℂ) (E : Matrix n n ℂ) (lam s : ℂ)
    (hEinv : Invertible (E - lam • (1 : Matrix n n ℂ)))
    (hw1 : star η1 ⬝ᵥ ((E - lam • (1 : Matrix n n ℂ))⁻¹ *ᵥ b) = 1) :
    let w : n → ℂ := (E - lam • (1 : Matrix n n ℂ))⁻¹ *ᵥ b
    let x : Unit ⊕ n → ℂ := s • Sum.elim (fun (_ : Unit) => (-1 : ℂ)) w
    star (etaVec η1) ⬝ᵥ x = 0
      ∧ (AplusBlock a b E - lam • (1 : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ)) *ᵥ x
          = (-s * phiSchur a b E lam) • (Sum.elim (fun (_ : Unit) => (1 : ℂ)) 0) := by
  intro w x
  have hEw : (E - lam • (1 : Matrix n n ℂ)) *ᵥ w = b := by
    show (E - lam • (1 : Matrix n n ℂ)) *ᵥ ((E - lam • (1 : Matrix n n ℂ))⁻¹ *ᵥ b) = b
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_det_of_invertible (A := E - lam • (1 : Matrix n n ℂ))),
      Matrix.one_mulVec]
  constructor
  · -- `η* x = 0` — uses the solvability constraint `hw1`.
    have hcore : star (etaVec η1) ⬝ᵥ (Sum.elim (fun (_ : Unit) => (-1 : ℂ)) w) = 0 := by
      show (star (Sum.elim (fun (_ : Unit) => (1 : ℂ)) η1))
        ⬝ᵥ (Sum.elim (fun (_ : Unit) => (-1 : ℂ)) w) = 0
      have heq : (star (Sum.elim (fun (_ : Unit) => (1 : ℂ)) η1))
          = Sum.elim (fun (_ : Unit) => (1 : ℂ)) (star η1) := by
        ext (i | i) <;> simp
      rw [heq]
      show ∑ j : Unit ⊕ n,
          (Sum.elim (fun (_ : Unit) => (1 : ℂ)) (star η1)) j
            * (Sum.elim (fun (_ : Unit) => (-1 : ℂ)) w) j = 0
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      have hunit : ∑ _j : Unit, (1 : ℂ) * (-1 : ℂ) = -1 := by simp
      rw [hunit]
      have hw' : ∑ j, star η1 j * w j = 1 := hw1
      rw [hw']
      ring
    show star (etaVec η1) ⬝ᵥ x = 0
    show star (etaVec η1) ⬝ᵥ (s • Sum.elim (fun (_ : Unit) => (-1 : ℂ)) w) = 0
    rw [dotProduct_smul, hcore, smul_eq_mul, mul_zero]
  · -- `(Aplus - λI) x = -s·φ(λ)·e0`.
    have hblock : AplusBlock a b E - lam • (1 : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ)
        = Matrix.fromBlocks (Matrix.of fun (_ : Unit) (_ : Unit) => a - lam) (Matrix.of fun (_ : Unit) j => star (b j))
            (Matrix.of fun i (_ : Unit) => b i) (E - lam • (1 : Matrix n n ℂ)) := by
      show Matrix.fromBlocks (Matrix.of fun (_ : Unit) (_ : Unit) => a) (Matrix.of fun (_ : Unit) j => star (b j))
          (Matrix.of fun i (_ : Unit) => b i) E - lam • (1 : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ) = _
      ext (i | i) (j | j) <;>
        simp [Matrix.fromBlocks, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
    have hcore : (Matrix.fromBlocks (Matrix.of fun (_ : Unit) (_ : Unit) => a - lam)
        (Matrix.of fun (_ : Unit) j => star (b j)) (Matrix.of fun i (_ : Unit) => b i)
        (E - lam • (1 : Matrix n n ℂ))) *ᵥ (Sum.elim (fun (_ : Unit) => (-1 : ℂ)) w)
        = Sum.elim (fun (_ : Unit) => -phiSchur a b E lam) 0 := by
      rw [fromBlocks_mulVec_gen]
      have hnpart : (Matrix.of fun i (_ : Unit) => b i : Matrix n Unit ℂ) *ᵥ (fun (_ : Unit) => (-1 : ℂ))
          + (E - lam • (1 : Matrix n n ℂ)) *ᵥ w = 0 := by
        have h1 : (Matrix.of fun i (_ : Unit) => b i : Matrix n Unit ℂ) *ᵥ (fun (_ : Unit) => (-1 : ℂ)) = -b := by
          funext i
          show ∑ _j : Unit, b i * (-1 : ℂ) = -b i
          simp
        rw [h1, hEw]
        ring_nf
      have hupart : (Matrix.of fun (_ : Unit) (_ : Unit) => a - lam : Matrix Unit Unit ℂ) *ᵥ
          (fun (_ : Unit) => (-1 : ℂ)) + (Matrix.of fun (_ : Unit) j => star (b j) : Matrix Unit n ℂ) *ᵥ w
          = fun (_ : Unit) => -phiSchur a b E lam := by
        funext _
        show ∑ _j : Unit, (a - lam) * (-1 : ℂ) + ∑ j, star (b j) * w j = -phiSchur a b E lam
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul, smul_eq_mul]
        show (a - lam) * (-1 : ℂ) + star b ⬝ᵥ w = -phiSchur a b E lam
        rw [phiSchur]
        ring
      rw [hupart, hnpart]
    show (AplusBlock a b E - lam • (1 : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ)) *ᵥ x
      = (-s * phiSchur a b E lam) • (Sum.elim (fun (_ : Unit) => (1 : ℂ)) 0)
    show (AplusBlock a b E - lam • (1 : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ))
      *ᵥ (s • Sum.elim (fun (_ : Unit) => (-1 : ℂ)) w)
      = (-s * phiSchur a b E lam) • (Sum.elim (fun (_ : Unit) => (1 : ℂ)) 0)
    rw [Matrix.mulVec_smul, hblock, hcore]
    ext (i | i) <;> simp [smul_eq_mul]
