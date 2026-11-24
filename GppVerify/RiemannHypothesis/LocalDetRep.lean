import GppVerify.RiemannHypothesis.LocalThetaCorrespondence
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.RingTheory.Finiteness.Basic

/-!
# One-dimensional representations through the determinant

For a character `ψ : G →* ℂˣ` of a group `G`, `ofChar ψ` is the one-dimensional representation of
`G` on `ℂ` by the scalar `ψ g`. For `GL_n(k)` and a character `χ : kˣ →* ℂˣ`, `detChar n χ = χ ∘ det`
and `detRep n χ = ofChar (detChar n χ)`.

* `ofChar_apply`, `detRep_apply`: the action is multiplication by `ψ g`, respectively `χ (det g)`.
* `IsSmoothChar ψ`: the kernel of `ψ` is open.
* `continuous_glDet`: `det : GL_n(k) → kˣ` is continuous (for a topological ring `k`).
* `isSmoothChar_detChar`: `χ` smooth gives `χ ∘ det` smooth.
* `isSmoothRep_ofChar`, `isSmoothRep_detRep`: the resulting one-dimensional representations are
  smooth, in the sense of `IsSmoothRep`.

The construction restates, in its own authoring, the determinant representations used in the local
type II theta correspondence for GL_r × GL_n.
-/

namespace GppLocalTheta

section OfChar

variable {G : Type*} [Group G]

/-- The one-dimensional representation of `G` on `ℂ` through a character. -/
noncomputable def ofChar (ψ : G →* ℂˣ) : Representation ℂ G ℂ :=
  (Algebra.lsmul ℂ ℂ ℂ).toMonoidHom.comp ((Units.coeHom ℂ).comp ψ)

@[simp] theorem ofChar_apply (ψ : G →* ℂˣ) (g : G) (v : ℂ) : ofChar ψ g v = (ψ g : ℂ) * v := rfl

/-- A character is smooth when its kernel is open. -/
def IsSmoothChar [TopologicalSpace G] (ψ : G →* ℂˣ) : Prop := IsOpen {g : G | ψ g = 1}

theorem isSmoothRep_ofChar [TopologicalSpace G] {ψ : G →* ℂˣ} (h : IsSmoothChar ψ) :
    IsSmoothRep (ofChar ψ) := by
  intro v
  by_cases hv : v = 0
  · subst hv; simp
  · have hset : {g : G | ofChar ψ g v = v} = {g : G | ψ g = 1} := by
      ext g
      simp only [Set.mem_ofPred_eq, ofChar_apply]
      constructor
      · intro e
        have : (ψ g : ℂ) = 1 := mul_right_cancel₀ hv (by simpa using e)
        exact Units.ext this
      · intro e; simp [e]
    rw [hset]; exact h

end OfChar

section Det

variable {k : Type*} [Field k] (n : Type*) [Fintype n] [DecidableEq n]

/-- The character `χ ∘ det` of `GL_n(k)`. -/
def detChar (χ : kˣ →* ℂˣ) : Matrix.GeneralLinearGroup n k →* ℂˣ :=
  χ.comp Matrix.GeneralLinearGroup.det

@[simp] theorem detChar_apply (χ : kˣ →* ℂˣ) (g : Matrix.GeneralLinearGroup n k) :
    detChar n χ g = χ (Matrix.GeneralLinearGroup.det g) := rfl

/-- The one-dimensional representation of `GL_n(k)` through `χ ∘ det`. -/
noncomputable def detRep (χ : kˣ →* ℂˣ) : Representation ℂ (Matrix.GeneralLinearGroup n k) ℂ :=
  ofChar (detChar n χ)

@[simp] theorem detRep_apply (χ : kˣ →* ℂˣ) (g : Matrix.GeneralLinearGroup n k) (v : ℂ) :
    detRep n χ g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * v := rfl

variable {n} [TopologicalSpace k] [IsTopologicalRing k]

theorem continuous_glDet :
    Continuous (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup n k → kˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_det
  · simp only [← map_inv]
    exact Units.continuous_coe_inv.matrix_det

theorem isSmoothChar_detChar {χ : kˣ →* ℂˣ} (h : IsSmoothChar χ) :
    IsSmoothChar (detChar n χ) :=
  h.preimage continuous_glDet

theorem isSmoothRep_detRep {χ : kˣ →* ℂˣ} (h : IsSmoothChar χ) :
    IsSmoothRep (detRep n χ) :=
  isSmoothRep_ofChar (isSmoothChar_detChar h)

end Det

#print axioms isSmoothRep_ofChar
#print axioms continuous_glDet
#print axioms isSmoothRep_detRep

end GppLocalTheta
