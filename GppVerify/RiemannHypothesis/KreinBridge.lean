/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Heart of the Cosmos / Grok)
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic

/-!
# The bridge "H at all windows ⇒ `k_ψ ∈ P_{≤1}(ℝ)`" and the Krein frequency count

Turbo (PR #11, 6818904871) asked for (1) the Krein–Langer source check, run first as the
cheapest falsifier, and (2) the bridge step as an exact statement with every premise named.

**Part A (bridge).** `F` is any real vector space of test functions with a real bilinear form
`B` (the Weil form), windows `S L` (submodules), and per-window functionals `lc L`, `ls L`.
`HAllWindows` is Turbo's claim `T ≥ 2ℓ_s²` on `ker ℓ_c` inside every window. The premises are:

* `hEF` (named, the explicit formula): `B (τ x) (τ y) = K (x − y)` for the translates `τ x` of
  one fixed test function. For ζ, `K = k_ψ`, `k_ψ(x) = Σ_ρ m Ψ(γ)Ψ(−γ) e^{iγx}`.
* `hfit` (every finite family fits in one window). PROVED below for the concrete window
  "support in `[−L, L]`" and translates of a function supported in `[−a, a]`
  (`fit_translates`).

`bridge` then PROVES `AtMostOneNegSq K`: for **every** finite family `x : Fin n → ℝ` the real
Toeplitz form `Σ cᵢcⱼ K(xᵢ − xⱼ)` has no negative-definite 2-plane. This is the definition of
"at most one negative square on ℝ" (sup over finite families), so the passage from finite
windows to all of ℝ needs no limit: it is the window-fit lemma.

**Part B (Krein count).** In Krein's representation (as restated by Stewart, Canad. Math. Bull.
15 (1972) 399, eq. (2)), the non-polynomially-bounded part of `f ∈ P_k` is `h_p`, a solution of
`Q̄(−i d/dx) Q(−i d/dx) h = 0` with `deg Q = k`. Its frequencies are roots of `Q` or of `Q̄`.
`card_lower_freqs_le` PROVES: the frequencies `z` with `Im z < 0` that are roots of `Q` or of
`Q̄` number at most `natDegree Q`. `quadruple_not_P1` PROVES: an off-line quadruple supplies two
distinct such frequencies `γ₀` and `−γ̄₀` (when `Re γ₀ ≠ 0`), so `deg Q ≤ 1` is impossible.
The analytic step "every pole of the Laplace transform in `Re s > 0` is such a frequency"
is NOT formalised here (stated in the notes, SKETCH).
-/

namespace GppKreinBridge

open Finset ComplexConjugate

/-! ## Part A: the bridge -/

/-- No negative-definite 2-plane. -/
def NoNegPlane {V : Type*} [AddCommGroup V] [Module ℝ V] (q : V → ℝ) : Prop :=
  ∀ u w : V, ¬ ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → q (a • u + b • w) < 0

/-- The Toeplitz form of a kernel on a finite family of points. -/
def kform (K : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * K (x i - x j)

/-- `K ∈ P_{≤1}(ℝ)` (real coefficients): every finite Toeplitz form has no negative 2-plane. -/
def AtMostOneNegSq (K : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ), NoNegPlane (kform K x)

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

/-- Turbo's claim `T ≥ 2ℓ_s²` on `ker ℓ_c`, at every window, with
`T = Q − 2ℓ_c² + 2ℓ_s²`. -/
def HAllWindows (B : F →ₗ[ℝ] F →ₗ[ℝ] ℝ) (S : ℝ → Submodule ℝ F)
    (lc ls : ℝ → F →ₗ[ℝ] ℝ) : Prop :=
  ∀ L : ℝ, ∀ v ∈ S L, lc L v = 0 →
    2 * (ls L v) ^ 2 ≤ B v v - 2 * (lc L v) ^ 2 + 2 * (ls L v) ^ 2

/-- Inside one window the claim forbids a negative 2-plane (ToeplitzHyperplane, restated
for a submodule). -/
theorem no_neg_plane_in_window (B : F →ₗ[ℝ] F →ₗ[ℝ] ℝ) (S : ℝ → Submodule ℝ F)
    (lc ls : ℝ → F →ₗ[ℝ] ℝ) (H : HAllWindows B S lc ls) (L : ℝ) {u w : F}
    (hu : u ∈ S L) (hw : w ∈ S L) :
    ¬ ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → B (a • u + b • w) (a • u + b • w) < 0 := by
  intro hneg
  have hpos : ∀ v ∈ S L, lc L v = 0 → 0 ≤ B v v := by
    intro v hv h0
    have := H L v hv h0
    rw [h0] at this; nlinarith
  by_cases hz : lc L w = 0 ∧ lc L u = 0
  · have := hneg 1 0 (Or.inl one_ne_zero)
    simp only [one_smul, zero_smul, add_zero] at this
    exact absurd (hpos u hu hz.2) (not_le.2 this)
  · have hab : lc L w ≠ 0 ∨ -lc L u ≠ 0 := by
      by_contra hc; push Not at hc; exact hz ⟨hc.1, neg_eq_zero.1 hc.2⟩
    have hk : lc L (lc L w • u + (-lc L u) • w) = 0 := by
      simp only [map_add, map_smul, smul_eq_mul]; ring
    have hm : lc L w • u + (-lc L u) • w ∈ S L :=
      (S L).add_mem ((S L).smul_mem _ hu) ((S L).smul_mem _ hw)
    exact absurd (hpos _ hm hk) (not_le.2 (hneg _ _ hab))

/-- **The bridge.** H at all windows + explicit formula on translates + window fit ⇒
`K ∈ P_{≤1}(ℝ)`. -/
theorem bridge (B : F →ₗ[ℝ] F →ₗ[ℝ] ℝ) (S : ℝ → Submodule ℝ F)
    (lc ls : ℝ → F →ₗ[ℝ] ℝ) (H : HAllWindows B S lc ls) (τ : ℝ → F) (K : ℝ → ℝ)
    (hEF : ∀ x y, B (τ x) (τ y) = K (x - y))
    (hfit : ∀ (n : ℕ) (x : Fin n → ℝ), ∃ L, ∀ i, τ (x i) ∈ S L) :
    AtMostOneNegSq K := by
  intro n x u w hneg
  obtain ⟨L, hL⟩ := hfit n x
  let e : (Fin n → ℝ) →ₗ[ℝ] F :=
    { toFun := fun c => ∑ i, c i • τ (x i)
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r c => by simp [Finset.smul_sum, smul_smul] }
  have he : ∀ c, B (e c) (e c) = kform K x c := by
    intro c
    simp only [e, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, kform, hEF]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hmem : ∀ c, e c ∈ S L := fun c => by
    show ∑ i, c i • τ (x i) ∈ S L
    exact (S L).sum_mem fun i _ => (S L).smul_mem _ (hL i)
  refine no_neg_plane_in_window B S lc ls H L (hmem u) (hmem w) fun a b hab => ?_
  have := hneg a b hab
  rw [← he] at this
  simpa [map_add, map_smul] using this

/-- The concrete window: functions vanishing outside `[−L, L]`. -/
def window (L : ℝ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | ∀ t, L < |t| → f t = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun hf hg t ht => by simp [hf t ht, hg t ht]
  smul_mem' := fun c f hf t ht => by simp [hf t ht]

/-- **Every finite family fits in one window**: translates of a function supported in
`[−a, a]` by `x₁, …, xₙ` all lie in the window `L = a + Σ |xᵢ|`. -/
theorem fit_translates (ψ : ℝ → ℝ) (a : ℝ) (hψ : ∀ t, a < |t| → ψ t = 0) (n : ℕ)
    (x : Fin n → ℝ) : ∃ L, ∀ i, (fun t => ψ (t - x i)) ∈ window L := by
  refine ⟨a + ∑ j, |x j|, fun i t ht => hψ _ ?_⟩
  have h1 : |x i| ≤ ∑ j, |x j| :=
    Finset.single_le_sum (f := fun j => |x j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have h2 : |t| ≤ |t - x i| + |x i| := by
    calc |t| = |(t - x i) + x i| := by ring_nf
      _ ≤ |t - x i| + |x i| := abs_add_le _ _
  linarith

/-- The bridge for the concrete windows: only the explicit-formula premise `hEF` is left
named. -/
theorem bridge_concrete (B : (ℝ → ℝ) →ₗ[ℝ] (ℝ → ℝ) →ₗ[ℝ] ℝ) (lc ls : ℝ → (ℝ → ℝ) →ₗ[ℝ] ℝ)
    (H : HAllWindows B window lc ls) (ψ : ℝ → ℝ) (a : ℝ) (hψ : ∀ t, a < |t| → ψ t = 0)
    (K : ℝ → ℝ) (hEF : ∀ x y, B (fun t => ψ (t - x)) (fun t => ψ (t - y)) = K (x - y)) :
    AtMostOneNegSq K :=
  bridge B window lc ls H (fun x t => ψ (t - x)) K hEF (fit_translates ψ a hψ)

/-! ## Part B: the Krein frequency count -/

/-- Frequencies in the lower half-plane that are roots of `Q` or of `Q̄` (i.e. `Q(z̄) = 0`)
number at most `natDegree Q`: each conjugate pair costs one root of `Q`. -/
theorem card_lower_freqs_le (Q : Polynomial ℂ) (hQ : Q ≠ 0) (S : Finset ℂ)
    (hS : ∀ z ∈ S, z.im < 0 ∧ (Q.IsRoot z ∨ Q.IsRoot (conj z))) :
    S.card ≤ Q.natDegree := by
  classical
  let g : ℂ → ℂ := fun z => if Q.IsRoot z then z else conj z
  have hmap : ∀ z ∈ S, g z ∈ Q.roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ]
    by_cases h : Q.IsRoot z
    · simp only [g, if_pos h]; exact h
    · simp only [g, if_neg h]; exact ((hS z hz).2.resolve_left h)
  have hinj : Set.InjOn g S := by
    intro z1 h1 z2 h2 heq
    have i1 := (hS z1 h1).1
    have i2 := (hS z2 h2).1
    by_cases r1 : Q.IsRoot z1 <;> by_cases r2 : Q.IsRoot z2 <;>
      simp only [g, r1, r2, if_true, if_false] at heq
    · exact heq
    · have := congrArg Complex.im heq; simp at this; linarith
    · have := congrArg Complex.im heq; simp at this; linarith
    · exact (RingHom.injective _ heq)
  calc S.card ≤ Q.roots.toFinset.card := Finset.card_le_card_of_injOn g hmap hinj
    _ ≤ Multiset.card Q.roots := Multiset.toFinset_card_le _
    _ ≤ Q.natDegree := Polynomial.card_roots' Q

/-- An off-line zero `ρ₀ = 1/2 + iγ₀` with `Re ρ₀ > 1/2` (so `Im γ₀ < 0`) and `t₀ = Re γ₀ ≠ 0`
gives the two lower-half-plane frequencies `γ₀` and `−γ̄₀`, which are distinct. -/
theorem quadruple_two_lower (γ0 : ℂ) (him : γ0.im < 0) (hre : γ0.re ≠ 0) :
    (-conj γ0).im < 0 ∧ γ0 ≠ -conj γ0 := by
  refine ⟨by simpa using him, fun h => hre ?_⟩
  have := congrArg Complex.re h
  simp at this; linarith

/-- **Krein count vs one quadruple.** If both quadruple frequencies `γ₀`, `−γ̄₀` must be
frequencies of `h_p` (roots of `Q` or `Q̄`), then `deg Q ≥ 2`, so `k ∈ P_{≤1}` is impossible. -/
theorem quadruple_not_P1 (Q : Polynomial ℂ) (hQ : Q ≠ 0) (hdeg : Q.natDegree ≤ 1) (γ0 : ℂ)
    (him : γ0.im < 0) (hre : γ0.re ≠ 0) (h1 : Q.IsRoot γ0 ∨ Q.IsRoot (conj γ0))
    (h2 : Q.IsRoot (-conj γ0) ∨ Q.IsRoot (conj (-conj γ0))) : False := by
  classical
  obtain ⟨him2, hne⟩ := quadruple_two_lower γ0 him hre
  have hc := card_lower_freqs_le Q hQ {γ0, -conj γ0} (by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ⟨him, h1⟩
    · rw [Finset.mem_singleton.1 hz]; exact ⟨him2, h2⟩)
  rw [Finset.card_pair hne] at hc
  omega

end GppKreinBridge

#print axioms GppKreinBridge.no_neg_plane_in_window
#print axioms GppKreinBridge.bridge
#print axioms GppKreinBridge.fit_translates
#print axioms GppKreinBridge.bridge_concrete
#print axioms GppKreinBridge.card_lower_freqs_le
#print axioms GppKreinBridge.quadruple_two_lower
#print axioms GppKreinBridge.quadruple_not_P1
