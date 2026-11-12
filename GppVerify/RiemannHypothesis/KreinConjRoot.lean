/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Heart of the Cosmos / Grok)
-/
import GppVerify.RiemannHypothesis.KreinLaplaceAssembly

/-!
# The `Q / Q̄` conversion for the pole-transfer premise (Turbo 6819788258, item 2)

Turbo's audit of `KreinLaplaceAssembly` noted a gloss: the paper post states the pole-transfer
premise as "`γ` is a root of `Q` or of `Q̄`", while the file's `hPT` reads
`Q.IsRoot γ ∨ Q.IsRoot (conj γ)`. Here `Q̄ = Q.map conj` is `Q` with coefficients conjugated.

* `conjPoly_isRoot_iff`: `Q̄.IsRoot γ ↔ Q.IsRoot (conj γ)`.
* `conjPoly_ne_zero`, `conjPoly_natDegree`: `Q̄ ≠ 0` and `deg Q̄ = deg Q`.
* `hPT_iff`: the post's form `Q.IsRoot γ ∨ Q̄.IsRoot γ` is equivalent to the file's form.
* `no_offline_of_pole_transfer'`, `tri_RH_of_pole_transfer'`: the assembly and the triangle
  corollary restated with `hPT` in the post's "root of `Q` or `Q̄`" language.

Nothing new is assumed: `hPT` stays a named premise (CHECKED on paper, not proved here).
-/

namespace GppKreinLaplace

open ComplexConjugate

/-- `Q̄`: the polynomial `Q` with every coefficient conjugated. -/
noncomputable def conjPoly (Q : Polynomial ℂ) : Polynomial ℂ := Q.map (starRingEnd ℂ)

theorem conjPoly_eval (Q : Polynomial ℂ) (γ : ℂ) :
    (conjPoly Q).eval γ = conj (Q.eval (conj γ)) := by
  unfold conjPoly
  rw [Polynomial.eval_map, ← Polynomial.eval₂_at_apply, Complex.conj_conj]

/-- **Conversion lemma.** `γ` is a root of `Q̄` iff `conj γ` is a root of `Q`. -/
theorem conjPoly_isRoot_iff (Q : Polynomial ℂ) (γ : ℂ) :
    (conjPoly Q).IsRoot γ ↔ Q.IsRoot (conj γ) := by
  simp only [Polynomial.IsRoot.def, conjPoly_eval, map_eq_zero]

theorem conjPoly_natDegree (Q : Polynomial ℂ) : (conjPoly Q).natDegree = Q.natDegree :=
  Polynomial.natDegree_map_eq_of_injective (RingHom.injective _) Q

theorem conjPoly_ne_zero (Q : Polynomial ℂ) (hQ : Q ≠ 0) : conjPoly Q ≠ 0 :=
  (Polynomial.map_ne_zero_iff (RingHom.injective _)).2 hQ

/-- The post's "root of `Q` or `Q̄`" is the file's `Q.IsRoot γ ∨ Q.IsRoot (conj γ)`. -/
theorem hPT_iff (Q : Polynomial ℂ) (γ : ℂ) :
    (Q.IsRoot γ ∨ (conjPoly Q).IsRoot γ) ↔ (Q.IsRoot γ ∨ Q.IsRoot (conj γ)) := by
  rw [conjPoly_isRoot_iff]

/-- The assembly with `hPT` stated as "every such zero is a root of `Q` or of `Q̄`". -/
theorem no_offline_of_pole_transfer' (Z : Set ℂ) (Ψ : ℂ → ℂ) (Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (hdeg : Q.natDegree ≤ 1) (hsym : ∀ γ ∈ Z, -conj γ ∈ Z)
    (hPT : ∀ γ ∈ Z, γ.im < 0 → Ψ γ ≠ 0 → Q.IsRoot γ ∨ (conjPoly Q).IsRoot γ)
    (γ0 : ℂ) (hz : γ0 ∈ Z) (him : γ0.im < 0) (hre : γ0.re ≠ 0)
    (hΨ1 : Ψ γ0 ≠ 0) (hΨ2 : Ψ (-conj γ0) ≠ 0) : False :=
  no_offline_of_pole_transfer Z Ψ Q hQ hdeg hsym
    (fun γ hγ hi hp => (hPT_iff Q γ).1 (hPT γ hγ hi hp)) γ0 hz him hre hΨ1 hΨ2

/-- The triangle corollary with `hPT` in the "root of `Q` or `Q̄`" form. -/
theorem tri_RH_of_pole_transfer' (Z : Set ℂ) (Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (hdeg : Q.natDegree ≤ 1) (hneg : ∀ γ ∈ Z, -γ ∈ Z) (hsym : ∀ γ ∈ Z, -conj γ ∈ Z)
    (hreal : ∀ γ ∈ Z, γ.im ≠ 0 → γ.re ≠ 0)
    (hPT : ∀ γ ∈ Z, γ.im < 0 → triPsi γ ≠ 0 → Q.IsRoot γ ∨ (conjPoly Q).IsRoot γ) :
    ∀ γ ∈ Z, γ.im = 0 :=
  tri_RH_of_pole_transfer Z Q hQ hdeg hneg hsym hreal
    (fun γ hγ hi hp => (hPT_iff Q γ).1 (hPT γ hγ hi hp))

end GppKreinLaplace

#print axioms GppKreinLaplace.conjPoly_eval
#print axioms GppKreinLaplace.conjPoly_isRoot_iff
#print axioms GppKreinLaplace.conjPoly_natDegree
#print axioms GppKreinLaplace.conjPoly_ne_zero
#print axioms GppKreinLaplace.hPT_iff
#print axioms GppKreinLaplace.no_offline_of_pole_transfer'
#print axioms GppKreinLaplace.tri_RH_of_pole_transfer'
