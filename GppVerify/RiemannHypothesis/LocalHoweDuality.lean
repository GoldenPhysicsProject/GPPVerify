import GppVerify.RiemannHypothesis.LocalDetRep
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Intertwining

/-!
# Howe duality for the type II dual pair `GL_r × GL_n` over a local field, as a named statement

`HoweDualityGL` is the statement that the local theta correspondence for the dual pair
`GL_r(k) × GL_n(k)` is one-to-one on smooth irreducible representations: for every non-archimedean
local field `k`, all `r`, `n` and every smooth character `μ`,

* if two smooth irreducible representations `τ`, `τ'` of `GL_n(k)` both occur in the tensor
  quotient `OmQuot μ σ ·` with the same smooth irreducible `σ` of `GL_r(k)`, then `τ ≃ τ'`;
* symmetrically, if two smooth irreducible `σ`, `σ'` both occur with the same smooth irreducible
  `τ`, then `σ ≃ σ'`.

It is a `Prop`-valued definition; nothing here asserts it. Representations are over `ℂ` on types
in the base universe, as in the literature on the local type II correspondence.

The statement is restated in this module's own authoring from the local theta correspondence
literature, over the interface `OmQuot` and `IsSmoothRep` built in `LocalThetaCorrespondence`.
-/

namespace GppLocalTheta

/-- Howe duality for `GL_r × GL_n` over a non-archimedean local field: the correspondence is
one-to-one on smooth irreducible representations, in both directions. -/
def HoweDualityGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [IsTopologicalRing k] (r n : ℕ) (μ : kˣ →* ℂˣ), IsSmoothChar μ →
    (∀ (V W W' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      [AddCommGroup W'] [Module ℂ W']
      (σ : Representation ℂ (Matrix.GeneralLinearGroup (Fin r) k) V)
      (τ : Representation ℂ (Matrix.GeneralLinearGroup (Fin n) k) W)
      (τ' : Representation ℂ (Matrix.GeneralLinearGroup (Fin n) k) W'),
      IsSmoothRep σ → σ.IsIrreducible → IsSmoothRep τ → τ.IsIrreducible → IsSmoothRep τ' →
      τ'.IsIrreducible → OmQuot μ σ τ → OmQuot μ σ τ' → Nonempty (τ.Equiv τ')) ∧
    (∀ (V V' W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
      [AddCommGroup W] [Module ℂ W]
      (σ : Representation ℂ (Matrix.GeneralLinearGroup (Fin r) k) V)
      (σ' : Representation ℂ (Matrix.GeneralLinearGroup (Fin r) k) V')
      (τ : Representation ℂ (Matrix.GeneralLinearGroup (Fin n) k) W),
      IsSmoothRep σ → σ.IsIrreducible → IsSmoothRep σ' → σ'.IsIrreducible → IsSmoothRep τ →
      τ.IsIrreducible → OmQuot μ σ τ → OmQuot μ σ' τ → Nonempty (σ.Equiv σ'))

end GppLocalTheta
