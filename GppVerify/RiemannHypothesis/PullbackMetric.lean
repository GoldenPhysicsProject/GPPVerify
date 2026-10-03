import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic

/-!
# The pullback metric: one ambient self-adjoint intertwiner replaces the KMS metric search

Source: Codex, GPPDiscovery2 `research/2026-09-28_pullback_kms_metric_intertwiner.md`, §1.

Let `V` be the finite even Weil coordinate space, `𝓗` an ambient Hilbert space, `B : V → 𝓗`
injective and `Ã` Hermitian on `𝓗` with the intertwining relation `B A₊ = Ã B`. Put `G = B^* B`.

* `pullback_symmetrizes`: `G A₊ = A₊^* G` automatically;
* `pullback_posDef`: `G` is positive definite (injectivity of `B`);
* `pullback_displacement`: if the displacement vector is represented by the same ambient boundary
  state, `b = B e₀` and `η = B^* b`, then `η = G e₀`.

So the two separate metric identities `G A₊ = A₊^* G` and `G e₀ = η` reduce to producing one
injective embedding `B` into a self-adjoint ambient system. In the finite self-dual divisor model,
`B^* B` for the subgroup-state synthesis map is the critical GCD/KMS Gram
(`GppSelfDualDivisor.gram_eq`).

## Checks and scope

The abstract lemma checks and is proved over `ℂ` for finite index types. **Not formalized:** the
concrete arithmetic target (that the finite Weil pencil is intertwined with an ambient self-adjoint
compression), which the note leaves as the next task. No RH claim.
-/

open Matrix
open scoped ComplexOrder

namespace GppPullbackMetric

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **Metric symmetrization is automatic.** -/
theorem pullback_symmetrizes (B : Matrix m n ℂ) (A : Matrix n n ℂ) (At : Matrix m m ℂ)
    (hAt : At.IsHermitian) (hint : B * A = At * B) :
    (Bᴴ * B) * A = Aᴴ * (Bᴴ * B) := by
  have h1 : Aᴴ * Bᴴ = Bᴴ * At := by
    have := congrArg Matrix.conjTranspose hint
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hAt.eq] at this
    exact this
  calc (Bᴴ * B) * A = Bᴴ * (B * A) := by rw [Matrix.mul_assoc]
    _ = Bᴴ * (At * B) := by rw [hint]
    _ = (Bᴴ * At) * B := by rw [Matrix.mul_assoc]
    _ = (Aᴴ * Bᴴ) * B := by rw [h1]
    _ = Aᴴ * (Bᴴ * B) := by rw [Matrix.mul_assoc]

/-- **The pullback metric is positive definite.** -/
theorem pullback_posDef (B : Matrix m n ℂ) (hB : Function.Injective B.mulVec) :
    (Bᴴ * B).PosDef :=
  Matrix.PosDef.conjTranspose_mul_self B hB

/-- **The displacement vector is `G e₀`** when both come from the same ambient state. -/
theorem pullback_displacement (B : Matrix m n ℂ) (e₀ : n → ℂ) (b : m → ℂ) (η : n → ℂ)
    (hb : b = B.mulVec e₀) (hη : η = Bᴴ.mulVec b) : η = (Bᴴ * B).mulVec e₀ := by
  rw [hη, hb, Matrix.mulVec_mulVec]

end GppPullbackMetric
