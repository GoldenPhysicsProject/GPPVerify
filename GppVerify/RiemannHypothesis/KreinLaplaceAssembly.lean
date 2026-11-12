/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Heart of the Cosmos / Grok)
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# (L), (R) and the assembly "one negative square ⇒ no off-line zero" (Turbo 6819511196)

Turbo asked for (L) the Laplace identity as an exact statement, (G1) the polynomial bound
on Krein's integral term, (R) a concrete family with no common off-line zero of `Ψ`, and a
read of the primary Krein source.

What is formalised here:

* `laplace_term` (the single-term Laplace transform behind (L)): for `Re s > −Im γ`,
  `∫₀^∞ e^{iγx} e^{−sx} dx = 1/(s − iγ)`. With `ρ = 1/2 + iγ`, `iγ = ρ − 1/2`.
* `pole_right_half_iff`: the pole `s = iz` of `x^r e^{izx}` lies in `Re s > 0` iff `Im z < 0`.
* `tri_no_nonreal_zero` (R): the triangle `ψ = 1_{[−1/2,1/2]} ∗ 1_{[−1/2,1/2]}` has
  `Ψ(γ) = (sin(γ/2)/(γ/2))²`, and `Ψ` has **no** non-real zero. So one fixed `ψ` already has
  no off-line zero of `Ψ`; no family is needed.
* `no_offline_of_pole_transfer` (assembly): if `Q ≠ 0`, `deg Q ≤ 1`, and the named premise
  `hPT` holds (every zero `γ` with `Im γ < 0` and `Ψ γ ≠ 0` is a root of `Q` or `Q̄`), then
  every off-line zero is a zero of `Ψ`. `tri_RH_of_pole_transfer`: for the triangle, every zero
  is real (on the line).

`hPT` is exactly Krein's representation (CHECKED, secondary) + (L) + (G1) + the identity
theorem; it is NOT proved here (paper proof in the notes, CHECKED on paper).
-/

namespace GppKreinLaplace

open Finset ComplexConjugate MeasureTheory

/-- Single-term Laplace transform: `∫₀^∞ e^{(iγ − s)x} dx = 1/(s − iγ)` when `Re s > −Im γ`. -/
theorem laplace_term (γ s : ℂ) (hs : -γ.im < s.re) :
    ∫ x : ℝ in Set.Ioi 0, Complex.exp ((Complex.I * γ - s) * x) = 1 / (s - Complex.I * γ) := by
  have ha : (Complex.I * γ - s).re < 0 := by
    simp [Complex.sub_re, Complex.mul_re]; linarith
  rw [integral_exp_mul_complex_Ioi ha 0]
  have hne : s - Complex.I * γ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [Complex.sub_re, Complex.mul_re] at this; linarith
  have hne' : Complex.I * γ - s ≠ 0 := by
    intro h; apply hne; linear_combination -h
  field_simp
  simp

/-- `ρ = 1/2 + iγ` gives `iγ = ρ − 1/2`. -/
theorem i_gamma_eq (γ : ℂ) : Complex.I * γ = (1 / 2 + Complex.I * γ) - 1 / 2 := by ring

/-- The pole `s = i z` lies in `Re s > 0` iff `Im z < 0`. -/
theorem pole_right_half_iff (z : ℂ) : 0 < (Complex.I * z).re ↔ z.im < 0 := by
  simp [Complex.mul_re]

/-- Fourier transform of the triangle `max(0, 1 − |x|)`: `(sin(γ/2)/(γ/2))²`. -/
noncomputable def triPsi (γ : ℂ) : ℂ := (Complex.sin (γ / 2) / (γ / 2)) ^ 2

/-- **(R)**: the triangle's `Ψ` has no non-real zero. -/
theorem tri_no_nonreal_zero (γ : ℂ) (h : γ.im ≠ 0) : triPsi γ ≠ 0 := by
  have h2 : γ / 2 ≠ 0 := by
    intro h0; apply h
    have := congrArg Complex.im h0; simp at this; linarith
  have hs : Complex.sin (γ / 2) ≠ 0 := by
    intro h0
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.1 h0
    apply h
    have := congrArg Complex.im hk
    simp at this
    linarith
  exact pow_ne_zero _ (div_ne_zero hs h2)

/-- Lower-half-plane roots of `Q` or `Q̄` number at most `natDegree Q` (as in KreinBridge). -/
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

/-- **Assembly.** Zero set `Z` (in the `γ` variable) closed under `γ ↦ −γ̄`; `Q ≠ 0`,
`deg Q ≤ 1`; named pole-transfer premise `hPT`. Then every zero with `Im γ < 0`,
`Re γ ≠ 0` and `Ψ γ ≠ 0`, `Ψ(−γ̄) ≠ 0` is impossible. -/
theorem no_offline_of_pole_transfer (Z : Set ℂ) (Ψ : ℂ → ℂ) (Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (hdeg : Q.natDegree ≤ 1) (hsym : ∀ γ ∈ Z, -conj γ ∈ Z)
    (hPT : ∀ γ ∈ Z, γ.im < 0 → Ψ γ ≠ 0 → Q.IsRoot γ ∨ Q.IsRoot (conj γ))
    (γ0 : ℂ) (hz : γ0 ∈ Z) (him : γ0.im < 0) (hre : γ0.re ≠ 0)
    (hΨ1 : Ψ γ0 ≠ 0) (hΨ2 : Ψ (-conj γ0) ≠ 0) : False := by
  classical
  have him2 : (-conj γ0).im < 0 := by simpa using him
  have hne : γ0 ≠ -conj γ0 := fun h => hre (by
    have := congrArg Complex.re h; simp at this; linarith)
  have hc := card_lower_freqs_le Q hQ {γ0, -conj γ0} (by
    intro z hz'
    rcases Finset.mem_insert.1 hz' with rfl | hz'
    · exact ⟨him, hPT _ hz him hΨ1⟩
    · rw [Finset.mem_singleton.1 hz']
      exact ⟨him2, hPT _ (hsym _ hz) him2 hΨ2⟩)
  rw [Finset.card_pair hne] at hc
  omega

/-- **Triangle corollary.** With `Ψ = triPsi`, zero set closed under `γ ↦ −γ` and
`γ ↦ −γ̄`, no zero on the imaginary axis off `0` (`ζ` has no real zeros in the strip), and
the named premise `hPT`: every zero is real, i.e. every `ρ = 1/2 + iγ` is on the line. -/
theorem tri_RH_of_pole_transfer (Z : Set ℂ) (Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (hdeg : Q.natDegree ≤ 1) (hneg : ∀ γ ∈ Z, -γ ∈ Z) (hsym : ∀ γ ∈ Z, -conj γ ∈ Z)
    (hreal : ∀ γ ∈ Z, γ.im ≠ 0 → γ.re ≠ 0)
    (hPT : ∀ γ ∈ Z, γ.im < 0 → triPsi γ ≠ 0 → Q.IsRoot γ ∨ Q.IsRoot (conj γ)) :
    ∀ γ ∈ Z, γ.im = 0 := by
  intro γ hz
  by_contra h
  have key : ∀ g ∈ Z, g.im < 0 → False := fun g hg hgi => by
    have hgi' : g.im ≠ 0 := ne_of_lt hgi
    exact no_offline_of_pole_transfer Z triPsi Q hQ hdeg hsym hPT g hg hgi
      (hreal g hg hgi') (tri_no_nonreal_zero g hgi')
      (tri_no_nonreal_zero _ (by simpa using hgi'))
  rcases lt_or_gt_of_ne h with hl | hg
  · exact key γ hz hl
  · exact key (-γ) (hneg γ hz) (by simpa using hg)

end GppKreinLaplace

#print axioms GppKreinLaplace.laplace_term
#print axioms GppKreinLaplace.i_gamma_eq
#print axioms GppKreinLaplace.pole_right_half_iff
#print axioms GppKreinLaplace.tri_no_nonreal_zero
#print axioms GppKreinLaplace.card_lower_freqs_le
#print axioms GppKreinLaplace.no_offline_of_pole_transfer
#print axioms GppKreinLaplace.tri_RH_of_pole_transfer
