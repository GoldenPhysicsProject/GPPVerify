import GppVerify.RHSpectralMultiplicity
import GppVerify.RiemannHypothesis.FunctionalEquation
import GppVerify.RiemannHypothesis.YakaboyluPositivityKernel

/-!
# The finite Weil-positivity criterion: positivity of the paired form ⟺ RH

The rigorous finitely-supported content of Yakaboylu Theorem 5.1 + Proposition 5.3
(arXiv:2408.15135v14; equivalently Theorems 4.1–4.2 of the Abel-Cesàro companion paper
`rh_cesaro_v2.tex`, and the operator-theoretic face of Bombieri's refinement of Weil's
positivity criterion), assembled as one genuine theorem chain with no analytic input left
implicit:

* `pairedForm ι S c = Σ_{ρ ∈ S} conj(c(ι ρ)) · c(ρ)` — the Weil/Yakaboylu quadratic form
  on a finite set of zeros, paired by an involution `ι`;
* `involution_fixed_of_pairedForm_nonneg` — **the criterion**: if `Z` is closed under `ι`
  and the form is positive semidefinite on every finite subset of `Z`, then every point of
  `Z` is a fixed point of `ι` (proof: the `−2` test vector of
  `YakaboyluPositivityKernel.lean`, upgraded from a kernel computation to the actual
  finite-support argument);
* `zetaInvolution ρ = 1 − conj ρ` is an involution whose fixed locus is exactly the
  critical line `Re ρ = 1/2` (via `GppFE.critical_line_is_fixed_locus`);
* `nontrivialZeros_mem_involution` — the nontrivial zero set
  `{ρ | ζ(ρ) = 0, 0 < Re ρ < 1}` is **genuinely closed** under `zetaInvolution`: this is
  `GppRH.zeta_zero_implies_companion_zero` (the functional equation composed with the
  repo's own proved conjugation symmetry `riemannZeta_conj_axiom`), with the `ρ ≠ −n` and
  `ρ ≠ 1` side conditions discharged from the strip bounds;
* **`rh_iff_weil_pairedForm_nonneg`** — the two directions assembled: *every nontrivial
  zero lies on the critical line* **iff** *the paired form is positive semidefinite on
  every finite subset of the nontrivial zero set*. The forward direction collapses the
  paired form to the diagonal `Σ|c_ρ|²` (`diagonal_form_nonneg`); the backward direction
  is the criterion.

**Honest boundary.** This is a rigorous *reduction*, not a proof of RH: the analytic
content that would discharge the positivity hypothesis — Weil's explicit formula
expressing the form through prime sums, or Yakaboylu's operator compression `Ŵ ≥ 0` — is
not formalized. What IS proved unconditionally: the finite-support positivity statement
and RH are materially equivalent, with the zero-set reflection symmetry (often waved
through in expositions) carried as a real theorem, not an assumption.
-/

namespace GppWeilCriterion

open Finset

/-- **The Weil/Yakaboylu paired quadratic form** on a finite set `S` of spectral points,
    paired by the involution `ι`: `Σ_{ρ ∈ S} conj(c(ι ρ)) · c(ρ)`. -/
noncomputable def pairedForm (ι : ℂ → ℂ) (S : Finset ℂ) (c : ℂ → ℂ) : ℂ :=
  ∑ ρ ∈ S, (starRingEnd ℂ) (c (ι ρ)) * c ρ

open Classical in
/-- **The finite positivity criterion**: if `Z` is closed under the involution `ι` and the
    paired form has nonnegative real part on every finite subset of `Z`, then every point
    of `Z` is fixed by `ι`. The proof is the `−2` test vector: were `ι ρ₀ ≠ ρ₀`, the
    vector `c(ρ₀) = 1, c(ι ρ₀) = −1` (zero elsewhere) would give the form real part
    `−2 < 0` on the two-point subset `{ρ₀, ι ρ₀}`. -/
theorem involution_fixed_of_pairedForm_nonneg {Z : Set ℂ} {ι : ℂ → ℂ}
    (hinv : ∀ ρ ∈ Z, ι (ι ρ) = ρ) (hcl : ∀ ρ ∈ Z, ι ρ ∈ Z)
    (hpos : ∀ S : Finset ℂ, ↑S ⊆ Z → ∀ c : ℂ → ℂ, 0 ≤ (pairedForm ι S c).re)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z) : ι ρ₀ = ρ₀ := by
  by_contra hne
  set σ₀ := ι ρ₀ with hσ₀
  have hσZ : σ₀ ∈ Z := hcl ρ₀ hρ₀
  have hρσ : ρ₀ ≠ σ₀ := fun h => hne h.symm
  set c : ℂ → ℂ := fun s => if s = ρ₀ then 1 else if s = σ₀ then -1 else 0 with hc
  have hc1 : c ρ₀ = 1 := by simp [hc]
  have hc2 : c σ₀ = -1 := by simp [hc, Ne.symm hρσ]
  have hsub : ↑({ρ₀, σ₀} : Finset ℂ) ⊆ Z := by
    intro x hx
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hρ₀
    · exact hσZ
  have hισ : ι σ₀ = ρ₀ := by
    rw [hσ₀]
    exact hinv ρ₀ hρ₀
  have hval : pairedForm ι {ρ₀, σ₀} c = -2 := by
    simp only [pairedForm]
    rw [Finset.sum_pair hρσ, show ι ρ₀ = σ₀ from hσ₀.symm, hισ]
    exact GppYakaboylu.swap_test_vector_value hc1 hc2
  have h0 := hpos {ρ₀, σ₀} hsub c
  have hcast : (-2 : ℂ) = ((-2 : ℝ) : ℂ) := by norm_cast
  rw [hval, hcast, Complex.ofReal_re] at h0
  linarith

/-- **The zeta involution** `ρ ↦ 1 − ρ̄`: the composition of the functional-equation
    reflection `ρ ↦ 1 − ρ` with complex conjugation, the symmetry pairing each nontrivial
    zero with its mirror across the critical line. -/
noncomputable def zetaInvolution (ρ : ℂ) : ℂ := 1 - (starRingEnd ℂ) ρ

/-- `zetaInvolution` is an involution on all of `ℂ`. -/
theorem zetaInvolution_involutive (ρ : ℂ) : zetaInvolution (zetaInvolution ρ) = ρ := by
  simp [zetaInvolution, map_sub, map_one, Complex.conj_conj]

/-- The fixed locus of `zetaInvolution` is exactly the critical line — via the repo's
    `GppFE.critical_line_is_fixed_locus`. -/
theorem zetaInvolution_fixed_iff (ρ : ℂ) : zetaInvolution ρ = ρ ↔ ρ.re = 1 / 2 := by
  rw [zetaInvolution]
  constructor
  · intro h
    exact (GppFE.critical_line_is_fixed_locus ρ).mp (by linear_combination -h)
  · intro h
    have := (GppFE.critical_line_is_fixed_locus ρ).mpr h
    linear_combination -this

/-- **The nontrivial zero set of `ζ`**, as a set of complex numbers. -/
def nontrivialZeros : Set ℂ := {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- **The nontrivial zero set is closed under the zeta involution** — a real theorem, not
    an assumption: the companion `1 − ρ̄` of a strip zero is again a strip zero, by the
    functional equation (`riemannZeta_one_sub`) composed with the proved conjugation
    symmetry (`GppRH.riemannZeta_conj_axiom`), with the poles-of-`Γ` side conditions
    `ρ ≠ −n` and `ρ ≠ 1` discharged from the strip bounds. -/
theorem nontrivialZeros_mem_involution {ρ : ℂ} (hρ : ρ ∈ nontrivialZeros) :
    zetaInvolution ρ ∈ nontrivialZeros := by
  obtain ⟨hzero, hre0, hre1⟩ := hρ
  refine ⟨?_, ?_, ?_⟩
  · apply GppRH.zeta_zero_implies_companion_zero ρ hzero
    · intro n heq
      have : ρ.re = (-(n : ℂ)).re := congrArg Complex.re heq
      simp at this
      linarith
    · intro heq
      have : ρ.re = (1 : ℂ).re := congrArg Complex.re heq
      simp at this
      linarith
  · have : (zetaInvolution ρ).re = 1 - ρ.re := by
      simp [zetaInvolution, Complex.sub_re, Complex.one_re, Complex.conj_re]
    rw [this]
    linarith
  · have : (zetaInvolution ρ).re = 1 - ρ.re := by
      simp [zetaInvolution, Complex.sub_re, Complex.one_re, Complex.conj_re]
    rw [this]
    linarith

/-- **RH ⟺ finite Weil-pairing positivity.** Every nontrivial zero of `ζ` lies on the
    critical line **iff** the Weil/Yakaboylu paired form is positive semidefinite on every
    finite subset of the nontrivial zero set. The backward direction is the finite
    positivity criterion driven by the `−2` test vector; the forward direction collapses
    the pairing to the diagonal `Σ_ρ |c_ρ|²`. -/
theorem rh_iff_weil_pairedForm_nonneg :
    (∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2) ↔
      (∀ S : Finset ℂ, ↑S ⊆ nontrivialZeros → ∀ c : ℂ → ℂ,
        0 ≤ (pairedForm zetaInvolution S c).re) := by
  constructor
  · intro hrh S hS c
    have hdiag : pairedForm zetaInvolution S c = ∑ ρ ∈ S, (starRingEnd ℂ) (c ρ) * c ρ := by
      apply Finset.sum_congr rfl
      intro ρ hρS
      have hfix : zetaInvolution ρ = ρ :=
        (zetaInvolution_fixed_iff ρ).mpr (hrh ρ (hS hρS))
      rw [hfix]
    rw [hdiag]
    exact GppYakaboylu.diagonal_form_nonneg S c
  · intro hpos ρ hρ
    exact (zetaInvolution_fixed_iff ρ).mp
      (involution_fixed_of_pairedForm_nonneg
        (fun σ _ => zetaInvolution_involutive σ)
        (fun σ hσ => nontrivialZeros_mem_involution hσ)
        hpos hρ)

/-- The conditional-RH reading of the criterion, spelled out: if the paired form is
    positive semidefinite on every finite subset of the nontrivial zero set, then every
    nontrivial zero satisfies `Re ρ = 1/2`. -/
theorem rh_of_weil_pairedForm_nonneg
    (hpos : ∀ S : Finset ℂ, ↑S ⊆ nontrivialZeros → ∀ c : ℂ → ℂ,
      0 ≤ (pairedForm zetaInvolution S c).re)
    {ρ : ℂ} (hzero : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ρ.re = 1 / 2 :=
  rh_iff_weil_pairedForm_nonneg.mpr hpos ρ ⟨hzero, h0, h1⟩

end GppWeilCriterion
