import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Center
import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Quaternion

/-!
# The Cayley-Dickson doubling

For a non-associative ring `A` with a star anti-involution (`StarRing A`) and a parameter `γ : A` that
is central, star-fixed and in the left and right nucleus (`CDParam γ`; both nucleus conditions are
instances of associativity for an associative `A`, and `cdParam_neg_one` supplies the instance for
`γ = -1` in every `A`), the double `CD A γ` has underlying type `A × A` (components
`fst`, `snd`), with

  `(a, b) * (c, d) = (a c + γ d* b, d a + b c*)`,   `star (a, b) = (a*, -b)`,   `1 = (1, 0)`.

## Structure

* `CD.instNonAssocRing`: `CD A γ` is a `NonAssocRing` (for `NonAssocRing A`); `(1, 0)` is a
  two-sided unit.
* `CD.instStarRing`: `star` is an anti-involution of `CD A γ`. This is where `γ` central and
  star-fixed is used; `cdParam_neg_one` shows `γ = -1` satisfies it in every star ring.
* `CD.instRing`: when `A` is commutative the double is associative (`ℝ → ℂ → ℍ`).
* `CD.instCommRing`: when `A` is commutative with trivial star the double is commutative
  (`ℝ → ℂ`).
* `CD.instAlgebra`: `Algebra R (CD A γ)` over a trivial-star commutative semiring `R`, and
  `CD.finrank_eq`: the dimension of the double is twice the dimension of `A`.

## Identification with Mathlib's `ℂ` and `ℍ[ℝ]`

* `CD.complexEquiv : CD ℝ (-1) ≃+* ℂ`, carrying star to complex conjugation
  (`complexEquiv_star`) and the norm `x x*` to `Complex.normSq` (`complexEquiv_norm`).
* `CD.quaternionEquiv : CD (CD ℝ (-1)) (-1) ≃+* ℍ[ℝ]`, `(a, b) ↦ a + b j` with components taken
  directly, carrying star to quaternion conjugation (`quaternionEquiv_star`) and the norm to
  `Quaternion.normSq` (`quaternionEquiv_norm`); `quaternionAlgEquiv` is the same map as an
  `ℝ`-algebra isomorphism.

Source of the construction and the identifications: the ladder lane (Week 26), statements audited
by Flint (S-B1 with `γ` central and star-fixed, S-B2).
-/

/-- The parameter of a Cayley-Dickson doubling: central and fixed by the star. -/
class CDParam {A : Type*} [NonAssocRing A] [StarRing A] (γ : A) : Prop where
  central : ∀ x : A, γ * x = x * γ
  star_fixed : star γ = γ
  mul_assoc_left : ∀ x y : A, (γ * x) * y = γ * (x * y)
  mul_assoc_right : ∀ x y : A, x * (y * γ) = (x * y) * γ

/-- The Cayley-Dickson double of `A` with parameter `γ`. -/
@[ext]
structure CD (A : Type*) (γ : A) where
  fst : A
  snd : A

instance cdParam_neg_one {A : Type*} [NonAssocRing A] [StarRing A] : CDParam (-1 : A) where
  central x := by simp
  star_fixed := by simp
  mul_assoc_left x y := by simp
  mul_assoc_right x y := by simp

namespace CD

variable {A : Type*} {γ : A}

section Additive

variable [AddCommGroup A]

instance : Zero (CD A γ) := ⟨⟨0, 0⟩⟩
instance : Add (CD A γ) := ⟨fun x y => ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
instance : Neg (CD A γ) := ⟨fun x => ⟨-x.fst, -x.snd⟩⟩
instance : Sub (CD A γ) := ⟨fun x y => ⟨x.fst - y.fst, x.snd - y.snd⟩⟩
instance : SMul ℕ (CD A γ) := ⟨fun n x => ⟨n • x.fst, n • x.snd⟩⟩
instance : SMul ℤ (CD A γ) := ⟨fun n x => ⟨n • x.fst, n • x.snd⟩⟩

@[simp] theorem zero_fst : (0 : CD A γ).fst = 0 := rfl
@[simp] theorem zero_snd : (0 : CD A γ).snd = 0 := rfl
@[simp] theorem add_fst (x y : CD A γ) : (x + y).fst = x.fst + y.fst := rfl
@[simp] theorem add_snd (x y : CD A γ) : (x + y).snd = x.snd + y.snd := rfl
@[simp] theorem neg_fst (x : CD A γ) : (-x).fst = -x.fst := rfl
@[simp] theorem neg_snd (x : CD A γ) : (-x).snd = -x.snd := rfl
@[simp] theorem sub_fst (x y : CD A γ) : (x - y).fst = x.fst - y.fst := rfl
@[simp] theorem sub_snd (x y : CD A γ) : (x - y).snd = x.snd - y.snd := rfl

/-- The map to the product, used to transport the additive group structure. -/
def toProd (x : CD A γ) : A × A := (x.fst, x.snd)

omit [AddCommGroup A] in
theorem toProd_injective : Function.Injective (toProd (A := A) (γ := γ)) := by
  intro x y h
  have h1 : x.fst = y.fst := congrArg Prod.fst h
  have h2 : x.snd = y.snd := congrArg Prod.snd h
  exact CD.ext h1 h2

instance : AddCommGroup (CD A γ) :=
  toProd_injective.addCommGroup toProd rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

end Additive

section Unit

variable [NonAssocRing A]

instance : One (CD A γ) := ⟨⟨1, 0⟩⟩

@[simp] theorem one_fst : (1 : CD A γ).fst = 1 := rfl
@[simp] theorem one_snd : (1 : CD A γ).snd = 0 := rfl

instance : NatCast (CD A γ) := ⟨fun n => ⟨n, 0⟩⟩
instance : IntCast (CD A γ) := ⟨fun n => ⟨n, 0⟩⟩

@[simp] theorem natCast_fst (n : ℕ) : (n : CD A γ).fst = n := rfl
@[simp] theorem natCast_snd (n : ℕ) : (n : CD A γ).snd = 0 := rfl
@[simp] theorem intCast_fst (n : ℤ) : (n : CD A γ).fst = n := rfl
@[simp] theorem intCast_snd (n : ℤ) : (n : CD A γ).snd = 0 := rfl

end Unit

section Mult

variable [NonAssocRing A] [StarRing A]

instance : Mul (CD A γ) :=
  ⟨fun x y => ⟨x.fst * y.fst + γ * star y.snd * x.snd, y.snd * x.fst + x.snd * star y.fst⟩⟩

@[simp] theorem mul_fst (x y : CD A γ) :
    (x * y).fst = x.fst * y.fst + γ * star y.snd * x.snd := rfl
@[simp] theorem mul_snd (x y : CD A γ) :
    (x * y).snd = y.snd * x.fst + x.snd * star y.fst := rfl

instance instNonAssocRing : NonAssocRing (CD A γ) where
  left_distrib x y z := by
    ext <;> simp [mul_add, add_mul] <;> first | noncomm_ring | abel
  right_distrib x y z := by
    ext <;> simp [mul_add, add_mul] <;> first | noncomm_ring | abel
  zero_mul x := by ext <;> simp
  mul_zero x := by ext <;> simp
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  natCast_zero := by ext <;> simp
  natCast_succ n := by ext <;> simp
  intCast_ofNat n := by ext <;> simp
  intCast_negSucc n := by ext <;> simp

instance : Star (CD A γ) := ⟨fun x => ⟨star x.fst, -x.snd⟩⟩

@[simp] theorem star_fst (x : CD A γ) : (star x).fst = star x.fst := rfl
@[simp] theorem star_snd (x : CD A γ) : (star x).snd = -x.snd := rfl

variable [CDParam γ]

instance instStarRing : StarRing (CD A γ) where
  star_involutive x := by ext <;> simp
  star_mul x y := by
    ext
    · simp [star_add, star_mul, CDParam.star_fixed, star_star]
      rw [CDParam.mul_assoc_right (γ := γ), CDParam.mul_assoc_left (γ := γ)]
      exact (CDParam.central (γ := γ) _).symm
    · simp
  star_add x y := by
    ext
    · simp [star_add]
    · simp
      abel

end Mult

section Assoc

variable [CommRing A] [StarRing A] [CDParam γ]

/-- When `A` is commutative the double is associative (`ℝ → ℂ → ℍ`). -/
instance instRing : Ring (CD A γ) :=
  { (inferInstance : NonAssocRing (CD A γ)) with
    mul_assoc := fun x y z => by
      ext
      · simp [star_add, star_mul', star_star]
        ring
      · simp [star_add, star_mul', CDParam.star_fixed, star_star]
        ring }

end Assoc

section CommCase

variable [CommRing A] [StarRing A] [TrivialStar A] [CDParam γ]

/-- The double of a commutative ring with trivial star is commutative (`ℝ → ℂ`). -/
instance instCommRing : CommRing (CD A γ) :=
  { (inferInstance : Ring (CD A γ)) with
    mul_comm := fun x y => by
      ext
      · simp [star_trivial]
        ring
      · simp [star_trivial]
        ring }

end CommCase

section Scalars

variable {R : Type*} [CommSemiring R] [Ring A] [Module R A]

instance : SMul R (CD A γ) := ⟨fun r x => ⟨r • x.fst, r • x.snd⟩⟩

@[simp] theorem smul_fst (r : R) (x : CD A γ) : (r • x).fst = r • x.fst := rfl
@[simp] theorem smul_snd (r : R) (x : CD A γ) : (r • x).snd = r • x.snd := rfl

/-- Additive map to the product, used to transport the module structure. -/
def toProdAddHom : CD A γ →+ A × A where
  toFun := toProd
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module R (CD A γ) :=
  toProd_injective.module R toProdAddHom (fun _ _ => rfl)

/-- The double is `A × A` as an `R`-module. -/
def toProdLinearEquiv : CD A γ ≃ₗ[R] A × A where
  toFun := toProd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun p := ⟨p.1, p.2⟩
  left_inv x := by ext <;> rfl
  right_inv p := rfl

/-- **Doubling step.** The dimension of the double is twice the dimension of `A`. -/
theorem finrank_eq [StrongRankCondition R] [Module.Free R A] [Module.Finite R A] :
    Module.finrank R (CD A γ) = 2 * Module.finrank R A := by
  rw [(toProdLinearEquiv (R := R) (A := A) (γ := γ)).finrank_eq, Module.finrank_prod]
  ring

end Scalars

section StarScalars

variable {R : Type*} [CommSemiring R] [Star R] [TrivialStar R] [Ring A] [StarRing A] [Module R A]
  [StarModule R A]

instance : StarModule R (CD A γ) where
  star_smul r x := by
    ext
    · simp [star_smul]
    · simp [star_trivial]

end StarScalars

section Alg

variable {R : Type*} [CommSemiring R] [Star R] [TrivialStar R] [CommRing A] [StarRing A]
  [Algebra R A] [StarModule R A] [CDParam γ]

instance instAlgebra : Algebra R (CD A γ) :=
  Algebra.ofModule
    (fun r x y => by
      ext
      · simp [smul_add]
      · simp [smul_add])
    (fun r x y => by
      ext
      · simp [smul_add, star_smul, star_trivial]
      · simp [smul_add, star_smul, star_trivial])

end Alg


/-! ### Identification with `ℂ` and `ℍ[ℝ]` -/

section Identify

open scoped Quaternion

/-- The norm `N(x) = x x*` read in the first component. -/
def normFst {A : Type*} {γ : A} [Ring A] [StarRing A] (x : CD A γ) : A := (x * star x).fst

/-- Rung 2: `CD ℝ (-1) ≃+* ℂ`. -/
def complexEquiv : CD ℝ (-1) ≃+* ℂ where
  toFun x := ⟨x.fst, x.snd⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv x := by ext <;> rfl
  right_inv z := by apply Complex.ext <;> rfl
  map_mul' x y := by
    apply Complex.ext <;> simp [star_trivial] <;> ring
  map_add' x y := by apply Complex.ext <;> simp

theorem complexEquiv_star (x : CD ℝ (-1)) :
    complexEquiv (star x) = star (complexEquiv x) := by
  apply Complex.ext <;> simp [complexEquiv]

theorem complexEquiv_norm (x : CD ℝ (-1)) :
    normFst x = Complex.normSq (complexEquiv x) := by
  simp [normFst, complexEquiv, Complex.normSq_apply, star_trivial]

/-- Components of a rung-4 element as a quaternion: `(a, b) ↦ a + b j`, components taken directly. -/
def toQuat (x : CD (CD ℝ (-1)) (-1)) : ℍ[ℝ] := ⟨x.fst.fst, x.fst.snd, x.snd.fst, x.snd.snd⟩

/-- Rung 4: `CD (CD ℝ (-1)) (-1) ≃+* ℍ[ℝ]`, `(a, b) ↦ a + b j` with components taken directly. -/
def quaternionEquiv : CD (CD ℝ (-1)) (-1) ≃+* ℍ[ℝ] where
  toFun := toQuat
  invFun q := ⟨⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩⟩
  left_inv x := by ext <;> rfl
  right_inv q := by ext <;> rfl
  map_mul' x y := by
    ext <;> simp [toQuat, star_trivial] <;>
      first
      | (erw [QuaternionAlgebra.re_mul]; ring)
      | (erw [QuaternionAlgebra.imI_mul]; ring)
      | (erw [QuaternionAlgebra.imJ_mul]; ring)
      | (erw [QuaternionAlgebra.imK_mul]; ring)
  map_add' x y := by ext <;> rfl

theorem quaternionEquiv_apply (x : CD (CD ℝ (-1)) (-1)) : quaternionEquiv x = toQuat x := rfl

theorem quaternionEquiv_star (x : CD (CD ℝ (-1)) (-1)) :
    quaternionEquiv (star x) = star (quaternionEquiv x) := by
  rw [quaternionEquiv_apply, quaternionEquiv_apply]
  ext <;> first
    | (erw [Quaternion.re_star]; simp [toQuat, star_trivial])
    | (erw [Quaternion.imI_star]; simp [toQuat, star_trivial])
    | (erw [Quaternion.imJ_star]; simp [toQuat, star_trivial])
    | (erw [Quaternion.imK_star]; simp [toQuat, star_trivial])

theorem quaternionEquiv_norm (x : CD (CD ℝ (-1)) (-1)) :
    (normFst x).fst = Quaternion.normSq (quaternionEquiv x) := by
  rw [Quaternion.normSq_def']
  show _ = (toQuat x).re ^ 2 + (toQuat x).imI ^ 2 + (toQuat x).imJ ^ 2 + (toQuat x).imK ^ 2
  simp [normFst, toQuat, star_trivial]
  ring

/-- Rung 4 as an `ℝ`-algebra isomorphism. -/
noncomputable def quaternionAlgEquiv : CD (CD ℝ (-1)) (-1) ≃ₐ[ℝ] ℍ[ℝ] :=
  AlgEquiv.ofRingEquiv (f := quaternionEquiv) (fun r => by
    rw [quaternionEquiv_apply]
    ext <;> simp [toQuat, Algebra.algebraMap_eq_smul_one])

end Identify

#print axioms instNonAssocRing
#print axioms instStarRing
#print axioms instRing
#print axioms instCommRing
#print axioms instAlgebra
#print axioms finrank_eq
#print axioms complexEquiv
#print axioms complexEquiv_star
#print axioms complexEquiv_norm
#print axioms quaternionEquiv
#print axioms quaternionEquiv_star
#print axioms quaternionEquiv_norm
#print axioms quaternionAlgEquiv

end CD
