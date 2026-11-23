import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# GNS for a positive-semidefinite bilinear form: a pairing is an inner product iff it is positive

The state-space construction behind axiom A3 of the shadow-theory package
(`MuseResearch/shadow-theory-axiom-package-2026-11-15.md`): *"the pairing is the inner product of the
state space — `H` is the completion of `Test` modulo the null space of the form."* This file proves
the construction once, for an arbitrary real vector space `V` and a bilinear form `B`, with no
reference to shadow theories, zeros or primes.

* `FormGNS.PSD B`: `B` is symmetric and `0 ≤ B v v`.
* `FormGNS.Space h`: the completion of `V` under the semi-inner product `B`. This is the Hausdorff
  completion, so the null space `{v | B v v = 0}` is quotiented automatically; no quotient is built.
* `FormGNS.vec`: the canonical linear map `V → Space h`.
* `inner_vec`: `⟪vec v, vec w⟫ = B v w` — **the pairing is the inner product**.
* `dense_range_vec`: the image is dense.
* **`psd_iff_exists_hilbert`**: `B` is positive-semidefinite **iff** `B` is the Gram form of some linear
  map into a real inner-product space. So for a datum whose pairing is `B`, "a state space exists" and
  "the pairing is positive" are *the same statement* — Daniel's A3, reflection positivity as the
  condition for the space to exist and not a further fact about a signed form.

Same template as the in-tree `PositiveDefiniteGNS.lean` (Kolmogorov's construction through
`PreInnerProductSpace.Core`), over `ℝ` and for a form on an arbitrary vector space rather than a group
algebra. Not here: the shadow datum's linear structure, the dilation action, the vacuum.
 No `sorry`, no axiom.
-/

universe u

namespace GppFormGNS

open UniformSpace
open scoped InnerProductSpace

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- A real bilinear form is **positive-semidefinite**: symmetric, and `0 ≤ B v v`. -/
structure PSD (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Prop where
  symm : ∀ v w, B v w = B w v
  nonneg : ∀ v, 0 ≤ B v v

variable {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}

set_option linter.unusedVariables false in
/-- `V`, to carry the semi-inner product induced by `B`. -/
@[nolint unusedArguments]
def PreSpace (h : PSD B) := V

variable (h : PSD B)

noncomputable instance : AddCommGroup (PreSpace h) := inferInstanceAs (AddCommGroup V)
noncomputable instance : Module ℝ (PreSpace h) := inferInstanceAs (Module ℝ V)

theorem hadd (x y z : V) : B (x + y) z = B x z + B y z := by simp

theorem hsmul (r : ℝ) (x y : V) : B (r • x) y = (starRingEnd ℝ) r * B x y := by simp

/-- `PSD` is exactly what `PreInnerProductSpace.Core` asks of a form. -/
noncomputable abbrev preCore : PreInnerProductSpace.Core ℝ (PreSpace h) where
  inner v w := B v w
  conj_inner_symm v w := by simpa using h.symm w v
  re_inner_nonneg v := h.nonneg v
  add_left x y z := hadd x y z
  smul_left x y r := hsmul r x y

noncomputable instance : SeminormedAddCommGroup (PreSpace h) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := preCore h)
noncomputable instance : InnerProductSpace ℝ (PreSpace h) :=
  InnerProductSpace.ofCore (preCore h)

lemma preSpace_inner_def (v w : PreSpace h) : ⟪v, w⟫_ℝ = B v w := rfl

/-- **The state space**: the Hausdorff completion of `V` under `B`. -/
abbrev Space := Completion (PreSpace h)

/-- `V → PreSpace h`, the identity. -/
def ofV : V →ₗ[ℝ] PreSpace h := LinearMap.id

/-- The canonical linear map `V → Space h`. -/
noncomputable def vec : V →ₗ[ℝ] Space h :=
  (Completion.toComplL : PreSpace h →L[ℝ] Space h).toLinearMap ∘ₗ ofV h

/-- **The pairing is the inner product.** -/
theorem inner_vec (v w : V) : ⟪vec h v, vec h w⟫_ℝ = B v w := by
  have e : ∀ x : V, vec h x = ((ofV h x : PreSpace h) : Space h) := fun x => rfl
  rw [e, e, Completion.inner_coe]
  rfl

/-- The image of `V` is dense in the state space. -/
theorem dense_range_vec : DenseRange (vec h) :=
  (Completion.denseRange_coe (α := PreSpace h) : _)

/-- A positive-semidefinite form is realised as a Gram form in a Hilbert space. -/
theorem exists_hilbert_of_psd (h : PSD B) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
      (ι : V →ₗ[ℝ] H), (∀ v w, B v w = ⟪ι v, ι w⟫_ℝ) ∧ DenseRange ι :=
  ⟨Space h, inferInstance, inferInstance, inferInstance, vec h,
    fun v w => (inner_vec h v w).symm, dense_range_vec h⟩

/-- Conversely, a Gram form is positive-semidefinite. -/
theorem psd_of_gram {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (ι : V →ₗ[ℝ] H)
    (hB : ∀ v w, B v w = ⟪ι v, ι w⟫_ℝ) : PSD B where
  symm v w := by rw [hB, hB, real_inner_comm]
  nonneg v := by rw [hB]; exact real_inner_self_nonneg

/-- **A pairing is an inner product iff it is positive-semidefinite.** Positivity is the condition
for the state space to exist, not a further property of a form that exists independently. -/
theorem psd_iff_exists_hilbert :
    PSD B ↔ ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
      (_ : CompleteSpace H) (ι : V →ₗ[ℝ] H), (∀ v w, B v w = ⟪ι v, ι w⟫_ℝ) ∧ DenseRange ι :=
  ⟨fun h => exists_hilbert_of_psd h, fun ⟨_, _, _, _, ι, hB, _⟩ => psd_of_gram ι hB⟩

end GppFormGNS

#print axioms GppFormGNS.inner_vec
#print axioms GppFormGNS.psd_iff_exists_hilbert
