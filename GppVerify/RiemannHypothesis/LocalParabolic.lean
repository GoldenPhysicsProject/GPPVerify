import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.Matrix.Block

/-!
# The parabolic subgroup of `GL_n` attached to a block decomposition, and its Levi projection

Conventions: vectors are columns, `g : GL_n(k)` acts on `n → k` by `Matrix.mulVec`. For a block
decomposition `e : a ⊕ b ≃ n`, the coordinate subspace `S_e` is the set of vectors vanishing on the
`b`-coordinates, so the parabolic `parab e` is block upper-triangular in the `e`-ordering, `a` first.

* `coordSub e`: the subspace `S_e`. `isoA e : S_e ≃ₗ (a → k)` and `isoB e : (n → k) ⧸ S_e ≃ₗ (b → k)`
  are the identifications with the `a`-block and the `b`-block.
* `glEquiv : GL_n(k) →* ((n → k) ≃ₗ (n → k))`, with `glEquiv_apply : glEquiv g v = g *ᵥ v`.
* `parab e`: the stabilizer of `S_e` pulled back along `glEquiv`; `mem_parab_iff` is membership by
  equality of submodules, `S_e.map (glEquiv g) = S_e`.
* `leviProj e : parab e →* GL_a(k) × GL_b(k)`: the induced action on `S_e` (the `a`-block, along
  `isoA`) and on the quotient `(n → k) ⧸ S_e` (the `b`-block, along `isoB`); a monoid homomorphism
  by the functoriality of `LinearEquiv.ofSubmodules` and `Submodule.Quotient.equiv`.
* `leviEmb e : GL_a(k) × GL_b(k) →* GL_n(k)`: the block-diagonal embedding, with
  `leviEmb_mulVec_inl` / `leviEmb_mulVec_inr` (the action on the two coordinate blocks),
  `leviEmb_mem_parab`, and `leviProj_leviEmb : leviProj e ⟨leviEmb e (A, D), _⟩ = (A, D)`, so the
  projection is onto.
* `parab_blocks`: for `g ∈ parab e`, the matrix `g.submatrix e e` has zero lower-left block and its
  diagonal blocks are the two components of `leviProj e g`; `mem_parab_of_toBlocks₂₁_eq_zero` is
  the converse, so parabolic membership is exactly block upper-triangularity in the `e`-ordering.

Hypotheses: `Field k`, finite index types with decidable equality where `GL` is formed; no
topology.
-/

open scoped Pointwise

namespace GppLocalTheta

variable {k : Type*} [Field k] {a b n : Type*} [Fintype n] [DecidableEq n]

/-- `GL_n(k)` and the linear automorphisms of `n → k`, as a multiplicative equivalence. -/
noncomputable def glMulEquiv : Matrix.GeneralLinearGroup n k ≃* ((n → k) ≃ₗ[k] (n → k)) :=
  (Matrix.GeneralLinearGroup.toLin (n := n) (R := k)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv k (n → k))

/-- The transport of `GL_n(k)` to linear automorphisms of `n → k`, acting by `mulVec`. -/
noncomputable def glEquiv : Matrix.GeneralLinearGroup n k →* ((n → k) ≃ₗ[k] (n → k)) :=
  glMulEquiv.toMonoidHom

theorem glEquiv_apply (g : Matrix.GeneralLinearGroup n k) (v : n → k) :
    glEquiv g v = (↑g : Matrix n n k).mulVec v := rfl

/-- The coordinate subspace of `e : a ⊕ b ≃ n`: vectors vanishing on the `b`-coordinates. -/
def coordSub (e : a ⊕ b ≃ n) : Submodule k (n → k) where
  carrier := {v | ∀ j : b, v (e (Sum.inr j)) = 0}
  add_mem' := fun hu hv j => by simp [hu j, hv j]
  zero_mem' := fun j => rfl
  smul_mem' := fun c v hv j => by simp [hv j]

/-- The parabolic subgroup attached to `e`: the stabilizer of the coordinate subspace, pulled back
along `glEquiv`. -/
noncomputable def parab (e : a ⊕ b ≃ n) : Subgroup (Matrix.GeneralLinearGroup n k) :=
  (MulAction.stabilizer ((n → k) ≃ₗ[k] (n → k)) (coordSub (k := k) e)).comap glEquiv

theorem mem_parab_iff (e : a ⊕ b ≃ n) (g : Matrix.GeneralLinearGroup n k) :
    g ∈ parab (k := k) e ↔ (coordSub (k := k) e).map (glEquiv g : (n → k) →ₗ[k] (n → k)) =
      coordSub (k := k) e := by
  unfold parab
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  rfl

/-- Restriction to the `a`-coordinates: the identification of `S_e` with `a → k`. -/
def isoA (e : a ⊕ b ≃ n) : coordSub (k := k) e ≃ₗ[k] (a → k) where
  toFun v := fun i => (v : n → k) (e (Sum.inl i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := ⟨fun m => Sum.elim x (fun _ => 0) (e.symm m), fun j => by simp⟩
  left_inv v := by
    apply Subtype.ext
    funext m
    obtain ⟨i | j, rfl⟩ := e.surjective m
    · simp
    · simp [v.2 j]
  right_inv x := by
    funext i
    simp

/-- Restriction to the `b`-coordinates, as a linear map `(n → k) →ₗ (b → k)`. -/
def projB (e : a ⊕ b ≃ n) : (n → k) →ₗ[k] (b → k) :=
  LinearMap.funLeft k k (fun j => e (Sum.inr j))

omit [Fintype n] [DecidableEq n] in
theorem projB_surjective (e : a ⊕ b ≃ n) : Function.Surjective (projB (k := k) e) := by
  intro x
  refine ⟨fun m => Sum.elim (fun _ => 0) x (e.symm m), ?_⟩
  funext j
  simp [projB]

omit [Fintype n] [DecidableEq n] in
theorem ker_projB (e : a ⊕ b ≃ n) : LinearMap.ker (projB (k := k) e) = coordSub e := by
  ext v
  simp only [LinearMap.mem_ker, coordSub, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
  constructor
  · intro h j; exact congrFun h j
  · intro h; funext j; exact h j

/-- The induced identification of the quotient `(n → k) ⧸ S_e` with `b → k`. -/
noncomputable def isoB (e : a ⊕ b ≃ n) : ((n → k) ⧸ coordSub (k := k) e) ≃ₗ[k] (b → k) :=
  (Submodule.quotEquivOfEq _ _ (ker_projB (k := k) e).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (projB_surjective e))

section Levi

/-- The `a`-block of `g ∈ parab e`, as a linear automorphism of `a → k`: the induced action on
`S_e`, transported along `isoA`. -/
noncomputable def leviAEquiv (e : a ⊕ b ≃ n) (g : parab (k := k) e) : (a → k) ≃ₗ[k] (a → k) :=
  (isoA e).symm.trans
    ((LinearEquiv.ofSubmodules (glEquiv g.1) (coordSub e) (coordSub e)
      ((mem_parab_iff e g.1).1 g.2)).trans (isoA e))

/-- The `b`-block of `g ∈ parab e`, as a linear automorphism of `b → k`: the induced action on the
quotient `(n → k) ⧸ S_e`, transported along `isoB`. -/
noncomputable def leviBEquiv (e : a ⊕ b ≃ n) (g : parab (k := k) e) : (b → k) ≃ₗ[k] (b → k) :=
  let h : (coordSub (k := k) e).map (glEquiv g.1 : (n → k) →ₗ[k] (n → k)) = coordSub e :=
    (mem_parab_iff e g.1).1 g.2
  let q : ((n → k) ⧸ coordSub (k := k) e) ≃ₗ[k] ((n → k) ⧸ coordSub (k := k) e) :=
    Submodule.Quotient.equiv (coordSub (k := k) e) (coordSub (k := k) e) (glEquiv g.1) h
  (isoB e).symm.trans (q.trans (isoB e))

theorem leviAEquiv_coe (e : a ⊕ b ≃ n) (g : parab (k := k) e) (x : a → k) :
    (((isoA e).symm (leviAEquiv e g x) : coordSub (k := k) e) : n → k) =
      glEquiv g.1 (((isoA e).symm x : coordSub (k := k) e) : n → k) := by
  simp [leviAEquiv]

omit [Fintype n] [DecidableEq n] in
theorem leviAEquiv_ext (e : a ⊕ b ≃ n) {f f' : (a → k) ≃ₗ[k] (a → k)}
    (h : ∀ x, (((isoA e).symm (f x) : coordSub (k := k) e) : n → k) =
      (((isoA e).symm (f' x) : coordSub (k := k) e) : n → k)) : f = f' := by
  apply LinearEquiv.ext
  intro x
  apply (isoA e).symm.injective
  exact Subtype.ext (h x)

/-- The `a`-block as a monoid homomorphism. -/
noncomputable def leviAHom (e : a ⊕ b ≃ n) : parab (k := k) e →* ((a → k) ≃ₗ[k] (a → k)) where
  toFun := leviAEquiv e
  map_one' := by
    apply leviAEquiv_ext e
    intro x
    rw [leviAEquiv_coe e]
    simp
  map_mul' g h := by
    apply leviAEquiv_ext e
    intro x
    rw [leviAEquiv_coe e]
    show _ = (((isoA e).symm (leviAEquiv e g (leviAEquiv e h x)) : coordSub (k := k) e) : n → k)
    rw [leviAEquiv_coe e, leviAEquiv_coe e]
    simp

omit [Fintype n] [DecidableEq n] in
theorem isoB_mk (e : a ⊕ b ≃ n) (v : n → k) :
    isoB (k := k) e (Submodule.Quotient.mk v) = projB e v := rfl

theorem leviBEquiv_apply (e : a ⊕ b ≃ n) (g : parab (k := k) e) (v : n → k) :
    leviBEquiv e g (projB e v) = projB e (glEquiv g.1 v) := by
  have h1 : (isoB (k := k) e).symm (projB e v) = Submodule.Quotient.mk v := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  unfold leviBEquiv
  simp only [LinearEquiv.trans_apply, h1]
  rfl

/-- The `b`-block as a monoid homomorphism. -/
noncomputable def leviBHom (e : a ⊕ b ≃ n) : parab (k := k) e →* ((b → k) ≃ₗ[k] (b → k)) where
  toFun := leviBEquiv e
  map_one' := by
    apply LinearEquiv.ext
    intro x
    obtain ⟨v, rfl⟩ := projB_surjective (k := k) e x
    rw [leviBEquiv_apply e]
    simp
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    obtain ⟨v, rfl⟩ := projB_surjective (k := k) e x
    show leviBEquiv e (g * h) (projB e v) = leviBEquiv e g (leviBEquiv e h (projB e v))
    rw [leviBEquiv_apply e, leviBEquiv_apply e, leviBEquiv_apply e]
    simp

variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The first component of the Levi projection: the `a`-block as an element of `GL_a(k)`. -/
noncomputable def leviProjA (e : a ⊕ b ≃ n) : parab (k := k) e →* Matrix.GeneralLinearGroup a k :=
  (glMulEquiv (n := a) (k := k)).symm.toMonoidHom.comp (leviAHom e)

/-- The second component of the Levi projection: the `b`-block as an element of `GL_b(k)`. -/
noncomputable def leviProjB (e : a ⊕ b ≃ n) : parab (k := k) e →* Matrix.GeneralLinearGroup b k :=
  (glMulEquiv (n := b) (k := k)).symm.toMonoidHom.comp (leviBHom e)

/-- The Levi projection of the parabolic onto `GL_a(k) × GL_b(k)`. -/
noncomputable def leviProj (e : a ⊕ b ≃ n) :
    parab (k := k) e →* Matrix.GeneralLinearGroup a k × Matrix.GeneralLinearGroup b k :=
  (leviProjA e).prod (leviProjB e)

omit [Fintype b] [DecidableEq b] in
theorem leviProjA_mulVec (e : a ⊕ b ≃ n) (g : parab (k := k) e) (x : a → k) :
    (↑(leviProjA e g) : Matrix a a k).mulVec x = leviAEquiv e g x := by
  have : glMulEquiv (leviProjA e g) = leviAEquiv e g := by
    simp [leviProjA, leviAHom]
  exact congrArg (fun f => f x) this

omit [Fintype a] [DecidableEq a] in
theorem leviProjB_mulVec (e : a ⊕ b ≃ n) (g : parab (k := k) e) (x : b → k) :
    (↑(leviProjB e g) : Matrix b b k).mulVec x = leviBEquiv e g x := by
  have : glMulEquiv (leviProjB e g) = leviBEquiv e g := by
    simp [leviProjB, leviBHom]
  exact congrArg (fun f => f x) this

/-- The block-diagonal matrix of a pair `(A, D)`, in the `e`-coordinates. -/
noncomputable def blockDiagHom (e : a ⊕ b ≃ n) : Matrix a a k × Matrix b b k →* Matrix n n k where
  toFun p := (Matrix.fromBlocks p.1 0 0 p.2).submatrix e.symm e.symm
  map_one' := by simp
  map_mul' p q := by
    rw [Matrix.submatrix_mul_equiv]
    simp [Matrix.fromBlocks_multiply]

/-- The Levi embedding: `GL_a(k) × GL_b(k)` into `GL_n(k)` by block-diagonal matrices. -/
noncomputable def leviEmb (e : a ⊕ b ≃ n) :
    Matrix.GeneralLinearGroup a k × Matrix.GeneralLinearGroup b k →*
      Matrix.GeneralLinearGroup n k :=
  (Units.map (blockDiagHom (k := k) e)).comp MulEquiv.prodUnits.symm.toMonoidHom

theorem leviEmb_val (e : a ⊕ b ≃ n) (A : Matrix.GeneralLinearGroup a k)
    (D : Matrix.GeneralLinearGroup b k) :
    (↑(leviEmb e (A, D)) : Matrix n n k) =
      (Matrix.fromBlocks (↑A) 0 0 (↑D)).submatrix e.symm e.symm := rfl

theorem leviEmb_mulVec_inl (e : a ⊕ b ≃ n) (A : Matrix.GeneralLinearGroup a k)
    (D : Matrix.GeneralLinearGroup b k) (v : n → k) (i : a) :
    ((↑(leviEmb e (A, D)) : Matrix n n k).mulVec v) (e (Sum.inl i)) =
      ((↑A : Matrix a a k).mulVec fun i' => v (e (Sum.inl i'))) i := by
  rw [leviEmb_val, Matrix.submatrix_mulVec_equiv]
  simp [Matrix.fromBlocks_mulVec, Function.comp_def]

theorem leviEmb_mulVec_inr (e : a ⊕ b ≃ n) (A : Matrix.GeneralLinearGroup a k)
    (D : Matrix.GeneralLinearGroup b k) (v : n → k) (j : b) :
    ((↑(leviEmb e (A, D)) : Matrix n n k).mulVec v) (e (Sum.inr j)) =
      ((↑D : Matrix b b k).mulVec fun j' => v (e (Sum.inr j'))) j := by
  rw [leviEmb_val, Matrix.submatrix_mulVec_equiv]
  simp [Matrix.fromBlocks_mulVec, Function.comp_def]

theorem leviEmb_maps_coordSub (e : a ⊕ b ≃ n) (A : Matrix.GeneralLinearGroup a k)
    (D : Matrix.GeneralLinearGroup b k) {v : n → k} (hv : v ∈ coordSub (k := k) e) :
    glEquiv (leviEmb e (A, D)) v ∈ coordSub (k := k) e := by
  intro j
  rw [glEquiv_apply, leviEmb_mulVec_inr]
  have : (fun j' => v (e (Sum.inr j'))) = 0 := funext fun j' => hv j'
  simp [this]

theorem leviEmb_mem_parab (e : a ⊕ b ≃ n) (A : Matrix.GeneralLinearGroup a k)
    (D : Matrix.GeneralLinearGroup b k) : leviEmb e (A, D) ∈ parab (k := k) e := by
  rw [mem_parab_iff]
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact leviEmb_maps_coordSub e A D hv
  · intro w hw
    refine ⟨glEquiv (leviEmb e (A⁻¹, D⁻¹)) w, leviEmb_maps_coordSub e _ _ hw, ?_⟩
    show glEquiv (leviEmb e (A, D)) (glEquiv (leviEmb e (A⁻¹, D⁻¹)) w) = w
    rw [← LinearEquiv.mul_apply, ← map_mul, ← map_mul]
    have h1 : ((A, D) * (A⁻¹, D⁻¹) : Matrix.GeneralLinearGroup a k × Matrix.GeneralLinearGroup b k)
        = 1 := by simp
    rw [h1, map_one, map_one]
    rfl

omit [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
theorem isoA_symm_coe (e : a ⊕ b ≃ n) (x : a → k) (m : n) :
    (((isoA e).symm x : coordSub (k := k) e) : n → k) m = Sum.elim x (fun _ => 0) (e.symm m) :=
  rfl

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
theorem leviAEquiv_apply (e : a ⊕ b ≃ n) (g : parab (k := k) e) (x : a → k) (i : a) :
    leviAEquiv e g x i = (glEquiv g.1 (((isoA e).symm x : coordSub (k := k) e) : n → k))
      (e (Sum.inl i)) := rfl

theorem leviProj_leviEmb (e : a ⊕ b ≃ n) (A : Matrix.GeneralLinearGroup a k)
    (D : Matrix.GeneralLinearGroup b k) :
    leviProj e ⟨leviEmb e (A, D), leviEmb_mem_parab e A D⟩ = (A, D) := by
  apply Prod.ext
  · apply Units.ext
    apply Matrix.ext_iff_mulVec.2
    intro x
    show (↑(leviProjA e ⟨leviEmb e (A, D), leviEmb_mem_parab e A D⟩) : Matrix a a k).mulVec x = _
    rw [leviProjA_mulVec]
    funext i
    rw [leviAEquiv_apply, glEquiv_apply, leviEmb_mulVec_inl]
    simp [isoA_symm_coe]
  · apply Units.ext
    apply Matrix.ext_iff_mulVec.2
    intro x
    obtain ⟨v, rfl⟩ := projB_surjective (k := k) e x
    show (↑(leviProjB e ⟨leviEmb e (A, D), leviEmb_mem_parab e A D⟩) : Matrix b b k).mulVec
      (projB e v) = _
    rw [leviProjB_mulVec, leviBEquiv_apply]
    funext j
    show (glEquiv (leviEmb e (A, D)) v) (e (Sum.inr j)) = _
    rw [glEquiv_apply, leviEmb_mulVec_inr]
    rfl

theorem glEquiv_single (g : Matrix.GeneralLinearGroup n k) (m i : n) :
    glEquiv g (Pi.single m 1) i = (↑g : Matrix n n k) i m := by
  rw [glEquiv_apply, Matrix.mulVec_single_one]
  rfl

omit [Fintype n] [Fintype a] [Fintype b] [DecidableEq b] in
theorem isoA_symm_single (e : a ⊕ b ≃ n) (i' : a) :
    (((isoA e).symm (Pi.single i' 1) : coordSub (k := k) e) : n → k) =
      Pi.single (e (Sum.inl i')) 1 := by
  funext m
  obtain ⟨s, rfl⟩ := e.surjective m
  rcases s with i | j <;> simp [isoA_symm_coe, Pi.single_apply]

omit [Fintype n] [Fintype a] [DecidableEq a] [Fintype b] in
theorem projB_single (e : a ⊕ b ≃ n) (j' : b) :
    projB (k := k) e (Pi.single (e (Sum.inr j')) 1) = Pi.single j' 1 := by
  funext j
  simp [projB, Pi.single_apply]

/-- The coherence lemma: parabolic membership is block upper-triangularity in the `e`-ordering, and
the Levi projection reads off the two diagonal blocks. -/
theorem parab_blocks (e : a ⊕ b ≃ n) (g : parab (k := k) e) :
    Matrix.toBlocks₂₁ ((↑g.1 : Matrix n n k).submatrix e e) = 0 ∧
      Matrix.toBlocks₁₁ ((↑g.1 : Matrix n n k).submatrix e e) = (↑(leviProj e g).1 : Matrix a a k) ∧
      Matrix.toBlocks₂₂ ((↑g.1 : Matrix n n k).submatrix e e) = (↑(leviProj e g).2 : Matrix b b k) := by
  have hS := (mem_parab_iff e g.1).1 g.2
  refine ⟨?_, ?_, ?_⟩
  · ext j i
    have hmem : glEquiv g.1 (Pi.single (e (Sum.inl i)) 1) ∈ coordSub (k := k) e := by
      have hin : (Pi.single (e (Sum.inl i)) 1 : n → k) ∈ coordSub (k := k) e := by
        rw [← isoA_symm_single e i]
        exact Subtype.property _
      have : glEquiv g.1 (Pi.single (e (Sum.inl i)) 1) ∈
          (coordSub (k := k) e).map (glEquiv g.1 : (n → k) →ₗ[k] (n → k)) :=
        ⟨_, hin, rfl⟩
      rwa [hS] at this
    have := hmem j
    rw [glEquiv_single] at this
    simpa [Matrix.toBlocks₂₁] using this
  · ext i i'
    have h1 := leviAEquiv_apply e g (Pi.single i' 1) i
    rw [isoA_symm_single, glEquiv_single] at h1
    have h2 := congrFun (leviProjA_mulVec e g (Pi.single i' 1)) i
    rw [Matrix.mulVec_single_one] at h2
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply]
    show (↑g.1 : Matrix n n k) (e (Sum.inl i)) (e (Sum.inl i')) = (↑(leviProjA e g) : Matrix a a k) i i'
    rw [← h1]
    exact h2.symm
  · ext j j'
    have h1 := leviBEquiv_apply e g (Pi.single (e (Sum.inr j')) 1)
    rw [projB_single] at h1
    have h2 := congrFun (leviProjB_mulVec e g (Pi.single j' 1)) j
    rw [Matrix.mulVec_single_one] at h2
    rw [h1] at h2
    simp only [Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply]
    show (↑g.1 : Matrix n n k) (e (Sum.inr j)) (e (Sum.inr j')) = (↑(leviProjB e g) : Matrix b b k) j j'
    have h3 := glEquiv_single g.1 (e (Sum.inr j')) (e (Sum.inr j))
    rw [← h3]
    exact h2.symm

omit [DecidableEq a] [DecidableEq b] in
/-- The reverse direction of the coherence lemma: a unit matrix whose reindexed lower-left block
vanishes lies in the parabolic. -/
theorem mem_parab_of_toBlocks₂₁_eq_zero (e : a ⊕ b ≃ n) (g : Matrix.GeneralLinearGroup n k)
    (h : Matrix.toBlocks₂₁ ((↑g : Matrix n n k).submatrix e e) = 0) : g ∈ parab (k := k) e := by
  have hmaps : ∀ v ∈ coordSub (k := k) e, glEquiv g v ∈ coordSub (k := k) e := by
    intro v hv j
    have hv' : v ∘ e = Sum.elim (fun i => v (e (Sum.inl i))) 0 := by
      funext s
      rcases s with i | j'
      · rfl
      · exact hv j'
    have key := congrFun (Matrix.submatrix_mulVec_equiv (↑g : Matrix n n k) (v ∘ e) e e)
      (Sum.inr j)
    rw [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id, Function.comp_apply] at key
    rw [glEquiv_apply, ← key, ← Matrix.fromBlocks_toBlocks ((↑g : Matrix n n k).submatrix e e),
      hv', Matrix.fromBlocks_mulVec, h]
    simp
  rw [mem_parab_iff]
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨v, hv, rfl⟩
    exact hmaps v hv
  · exact LinearEquiv.finrank_map_eq (glEquiv g) (coordSub (k := k) e)

end Levi

#print axioms glEquiv_apply
#print axioms mem_parab_iff
#print axioms leviProj
#print axioms leviEmb_mem_parab
#print axioms leviProj_leviEmb
#print axioms parab_blocks
#print axioms mem_parab_of_toBlocks₂₁_eq_zero

end GppLocalTheta
