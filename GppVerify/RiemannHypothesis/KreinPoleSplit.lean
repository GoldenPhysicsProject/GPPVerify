/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Heart of the Cosmos (Grok, GPPDiscovery5 seat). Turbo PR #11 6824324169, "next exact instruction".

# `PoleTransfer` split into hEF and a Krein-representation premise

`KreinHPsiChain.lean` left one premise, `PoleTransfer`, carrying the analytic load. This file
splits it into two exact `Prop`s and proves only the assembly direction.

1. **Multiplicity-weighted zero sum** (definition). `mult γ` is the order of vanishing of `ζ` at
   `ρ(γ) = 1/2 + iγ` (`GppXiZeroCounting.zeroMult`, i.e. `analyticOrderNatAt riemannZeta`).
   `zeroSum w = ∑' γ : Zgamma, (mult γ) · w γ`, with summability `ZeroSummable w` stated
   separately (a `tsum` is never used without its summability hypothesis). Every term carries
   its multiplicity, and `one_le_mult` (**PROVED**, from `one_le_zeroMult`) shows no zero of the
   strip has weight `0`, so no zero can drop out of the sum.
2. **`HEF`** (Weil's explicit formula on translates, named premise, NOT proved): for every `d`,
   `γ ↦ m_γ Ψ(γ) Ψ(−γ) e^{iγd}` is summable over `Zgamma` and
   `Kψ(d) = Σ_γ m_γ Ψ(γ) Ψ(−γ) e^{iγd}`. Paper status: CHECKED (secondary), NUMERICAL to 1.02e−8.
   `Ψ = GppKreinLaplace.triPsi`. (Lean's `triPsi 0 = 0` is harmless: `0 ∉ Zgamma` because
   `ζ(1/2) ≠ 0`; that fact is not used or formalised here.)
3. **`KreinRep`** (named premise, NOT proved): for any coefficients `a`, if `Kψ` has the
   multiplicity-weighted exponential expansion `Kψ(d) = Σ_γ m_γ a(γ) e^{iγd}` (summable at every
   `d`) and `Kψ ∈ P_{≤1}`, there is a nonzero `Q`, `deg Q ≤ 1`, with every zero `γ`, `Im γ < 0`,
   `a(γ) ≠ 0` a root of `Q` or `Q̄`. Paper content: Krein's representation of `P_{≤1}` kernels
   (CHECKED via Stewart 1972, secondary; Krein–Langer primary still owed) + (L) + (G1) + the
   identity theorem.
4. **Assembly** `poleTransfer_of_split : HEF → KreinRep → PoleTransfer` — **PROVED**
   (`Ψ(−γ) = Ψ(γ)`, so `a = Ψ(γ)Ψ(−γ) ≠ 0` iff `Ψ(γ) ≠ 0`). Converses are not claimed.
5. **Chain** `hPsiSplitChain : HPsi → HEF → KreinRep → NoRealZeroStrip → RiemannHypothesis` —
   **PROVED** (conditional), via `riemannHypothesis_of_hPsi`.

Honesty check: `kreinRep_of_RH : RiemannHypothesis → KreinRep` is **PROVED** (take `Q = X`), so
`KreinRep` is not a free premise. `HEF` is a classical theorem on paper (unconditional).
H_ψ: OPEN. ARP: OPEN. RH: OPEN.
-/
import GppVerify.RiemannHypothesis.KreinHPsiChain
import GppVerify.RiemannHypothesis.XiZeroCounting

namespace GppKreinPoleSplit

open GppKreinBridge GppKreinHPsi GppKreinHPsiChain ComplexConjugate

/-! ## 1. The multiplicity-weighted sum over the zero set -/

/-- Multiplicity of the zero `γ`: the order of vanishing of `ζ` at `ρ(γ) = 1/2 + iγ`. -/
noncomputable def mult (γ : ℂ) : ℕ := GppXiZeroCounting.zeroMult (rho γ)

/-- Every zero in the strip has multiplicity at least one (no zero has weight `0`). -/
theorem one_le_mult {γ : ℂ} (h : γ ∈ Zgamma) : 1 ≤ mult γ :=
  GppXiZeroCounting.one_le_zeroMult h

/-- Summability of the multiplicity-weighted family `γ ↦ m_γ w(γ)` over `Zgamma`. -/
def ZeroSummable (w : ℂ → ℂ) : Prop :=
  Summable fun γ : Zgamma => (mult (γ : ℂ) : ℂ) * w γ

/-- The multiplicity-weighted zero sum `Σ_{γ ∈ Zgamma} m_γ w(γ)` (used only with `ZeroSummable`). -/
noncomputable def zeroSum (w : ℂ → ℂ) : ℂ :=
  ∑' γ : Zgamma, (mult (γ : ℂ) : ℂ) * w γ

/-- `e^{iγd}`. -/
noncomputable def expTerm (d : ℝ) (γ : ℂ) : ℂ := Complex.exp (Complex.I * γ * d)

/-- `Kψ` has the multiplicity-weighted exponential expansion with coefficients `a`. -/
def HasZeroExpansion (a : ℂ → ℂ) : Prop :=
  ∀ d : ℝ, ZeroSummable (fun γ => a γ * expTerm d γ) ∧
    ((Kpsi d : ℝ) : ℂ) = zeroSum (fun γ => a γ * expTerm d γ)

/-! ## 2. hEF as its own `Prop` (named premise, NOT proved) -/

/-- Explicit-formula coefficient `Ψ(γ) Ψ(−γ)` for the triangle. -/
noncomputable def efCoeff (γ : ℂ) : ℂ := GppKreinLaplace.triPsi γ * GppKreinLaplace.triPsi (-γ)

/-- **Named premise `HEF`** (Weil's explicit formula on translates):
`Kψ(d) = Σ_{γ ∈ Zgamma} m_γ Ψ(γ) Ψ(−γ) e^{iγd}`, the family summable for every `d`. -/
def HEF : Prop := HasZeroExpansion efCoeff

/-! ## 3. Krein representation as its own `Prop` (named premise, NOT proved) -/

/-- **Named premise `KreinRep`**: a multiplicity-weighted exponential expansion of `Kψ` plus
`Kψ ∈ P_{≤1}` gives `Q ≠ 0`, `deg Q ≤ 1`, with every lower-half-plane zero whose coefficient is
nonzero a root of `Q` or `Q̄`. -/
def KreinRep : Prop :=
  ∀ a : ℂ → ℂ, HasZeroExpansion a → AtMostOneNegSq Kpsi →
    ∃ Q : Polynomial ℂ, Q ≠ 0 ∧ Q.natDegree ≤ 1 ∧
      ∀ γ ∈ Zgamma, γ.im < 0 → a γ ≠ 0 → Q.IsRoot γ ∨ Q.IsRoot (conj γ)

/-! ## 4. Assembly `HEF → KreinRep → PoleTransfer` (PROVED) -/

/-- The triangle's `Ψ` is even. -/
theorem triPsi_neg (γ : ℂ) : GppKreinLaplace.triPsi (-γ) = GppKreinLaplace.triPsi γ := by
  unfold GppKreinLaplace.triPsi
  rw [neg_div, Complex.sin_neg, neg_div_neg_eq]

theorem efCoeff_ne_zero {γ : ℂ} (h : GppKreinLaplace.triPsi γ ≠ 0) : efCoeff γ ≠ 0 := by
  unfold efCoeff
  rw [triPsi_neg]
  exact mul_ne_zero h h

/-- **Assembly.** `HEF → KreinRep → PoleTransfer` (this direction only). -/
theorem poleTransfer_of_split (hE : HEF) (hK : KreinRep) : PoleTransfer := by
  intro hP
  obtain ⟨Q, hQ, hdeg, h⟩ := hK efCoeff hE hP
  exact ⟨Q, hQ, hdeg, fun γ hγ him hΨ => h γ hγ him (efCoeff_ne_zero hΨ)⟩

/-! ## 5. The chain in split form (PROVED, conditional) -/

theorem riemannHypothesis_of_split (h : HPsi) (hE : HEF) (hK : KreinRep)
    (hN : NoRealZeroStrip) : RiemannHypothesis :=
  riemannHypothesis_of_hPsi h (poleTransfer_of_split hE hK) hN

/-- The split chain as one statement. -/
def HPsiSplitChain : Prop :=
  HPsi → HEF → KreinRep → NoRealZeroStrip → RiemannHypothesis

theorem hPsiSplitChain : HPsiSplitChain := riemannHypothesis_of_split

/-- **Honesty check.** RH implies `KreinRep` (take `Q = X`): the premise is not free. -/
theorem kreinRep_of_RH (hRH : RiemannHypothesis) : KreinRep := by
  intro _ _ _
  refine ⟨Polynomial.X, Polynomial.X_ne_zero, by rw [Polynomial.natDegree_X], ?_⟩
  intro γ hγ him _
  exfalso
  obtain ⟨hz, h0, h1⟩ := hγ
  have htriv : ¬∃ n : ℕ, rho γ = -2 * (n + 1) := by
    rintro ⟨n, hn⟩
    rw [hn] at h0
    have hre : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [hre] at h0
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h1' : rho γ ≠ 1 := fun e => by rw [e, Complex.one_re] at h1; linarith
  have := hRH (rho γ) hz htriv h1'
  rw [rho_re] at this
  linarith

end GppKreinPoleSplit

#print axioms GppKreinPoleSplit.one_le_mult
#print axioms GppKreinPoleSplit.triPsi_neg
#print axioms GppKreinPoleSplit.efCoeff_ne_zero
#print axioms GppKreinPoleSplit.poleTransfer_of_split
#print axioms GppKreinPoleSplit.riemannHypothesis_of_split
#print axioms GppKreinPoleSplit.hPsiSplitChain
#print axioms GppKreinPoleSplit.kreinRep_of_RH
