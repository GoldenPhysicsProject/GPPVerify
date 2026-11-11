/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude's GW-EF sheet, Codex's interpolation,
Turbo's audits; ported by Heart of the Cosmos / Grok)
-/
import GppVerify.RiemannHypothesis.KernelTheory

/-!
# GW-EF assembly: `rh_of_arp` as the ζ corollary of the theorem about theories

GW-EF-2 (`gwef2_factorisation`), GW-EF-3 (`gwef3_interpolation`) and
`online_of_pairing_nonneg` now live in `GwefFactorisation.lean` (same namespace
`GppGwefAssembly`, unchanged). Per Turbo (GPP-bridge PR #11, issuecomment-6806968693, item 1),
`rh_of_arp` is no longer proved here directly from `online_of_pairing_nonneg`: it is the
ζ corollary `GppKernelTheory.rh_of_arp'` of
`GppKernelTheory.KernelTheory.principalSeries_of_reflectionPositive` (reflection positivity forces
the principal series, proved once for the class of kernel theories), applied to the ζ datum
`GppKernelTheory.zetaTheory` with reflection positivity supplied by ARP
(`GppKernelTheory.reflectionPositive_of_arp`). Statement and name of `rh_of_arp` are unchanged.

## Honest boundary

`rh_of_arp` is the converse direction of Weil's criterion: an implication with ARP as a
hypothesis. ARP (equivalently `GppKernelTheory.ZetaReflectionPositivityObligation`) is **not**
proved anywhere in the tree, so nothing here proves RH. RH OPEN, ARP OPEN. This file adds no
`open_` stub and no axiom.

Daniel Toupin / Golden Physics Project, with AI assistance (Claude wrote the GW-EF sheet,
Codex the interpolation, Turbo audited and specified the kernel-theory form; Heart of the Cosmos /
Grok ported).
-/

open Complex MeasureTheory Filter
open GppMeyerSpectralWeil GppWeilCriterion GppArithmeticReflection GppGwefInterp

noncomputable section

namespace GppGwefAssembly

/-! ### `rh_of_arp`: the converse direction of Weil's criterion -/

/-- **`rh_of_arp`.** Arithmetic reflection positivity implies that every nontrivial zero of `ζ`
lies on the critical line. Now the ζ corollary `GppKernelTheory.rh_of_arp'` of the theorem about
theories (`KernelTheory.principalSeries_of_reflectionPositive`) for the ζ datum `zetaTheory`.
ARP is a hypothesis here and is OPEN, so this does not prove RH. In tree: PROVED (conditional on
ARP, which is OPEN). -/
theorem rh_of_arp (harp : ArithmeticReflectionPositivity) :
    ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2 :=
  GppKernelTheory.rh_of_arp' harp

/-! ### The sheet's statement of `rh_of_arp`, verbatim

The four named premises and the five-hypothesis signature exactly as on Claude's GW-EF sheet
(GPP-bridge `MuseResearch/claude-code-gwef-sheet-refresh-2026-11-10.lean`, `ef462ed`,
namespace `GppGWEF`). Each premise is a theorem in the tree, so the premises are redundant, and
`rh_of_arp_sheet` follows from `rh_of_arp`. -/

/-- **GW-EF-1** as on the sheet. Sheet status: PROVED in-tree (PR #551). -/
def ExplicitFormulaZeroSum : Prop :=
  ∀ f : ℝ → ℝ, IsTestFunction f →
    Summable (fun ρ : nontrivialZeros =>
      (GppXiZeroCounting.zeroMult ρ : ℂ) * spectralTransform (autocorr f) ρ) ∧
    ∑' ρ : nontrivialZeros, (GppXiZeroCounting.zeroMult ρ : ℂ) * spectralTransform (autocorr f) ρ =
      (weilForm (autocorr f) : ℂ)

/-- Polynomial zero counting as on the sheet. Sheet status: PROVED in-tree (E3). -/
def ZeroCountingPolynomial : Prop :=
  ∃ N : ℕ, Summable (fun ρ : nontrivialZeros =>
    (GppXiZeroCounting.zeroMult ρ : ℝ) * ((1 + ‖(ρ : ℂ)‖) ^ N)⁻¹)

/-- Zero-data symmetry as on the sheet. Sheet status: PROVED in-tree (E3). -/
def ZeroDataSymmetric : Prop :=
  ∀ ρ ∈ nontrivialZeros,
    zetaInvolution ρ ∈ nontrivialZeros ∧
      GppXiZeroCounting.zeroMult (zetaInvolution ρ) = GppXiZeroCounting.zeroMult ρ ∧
    (starRingEnd ℂ) ρ ∈ nontrivialZeros ∧
      GppXiZeroCounting.zeroMult ((starRingEnd ℂ) ρ) = GppXiZeroCounting.zeroMult ρ

/-- Positive multiplicities as on the sheet. Sheet status: PROVED in-tree (E3). -/
def ZeroMultPositive : Prop := ∀ ρ ∈ nontrivialZeros, 1 ≤ GppXiZeroCounting.zeroMult ρ

/-- **`rh_of_arp`, the sheet's exact statement** (five hypotheses, conclusion
`∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2`). Sheet status: PROVED modulo `gwef3_interpolation`.
In tree: PROVED, from `rh_of_arp`; ARP is a hypothesis and is OPEN, so RH stays OPEN. -/
theorem rh_of_arp_sheet
    (_hEF : ExplicitFormulaZeroSum) (_hZC : ZeroCountingPolynomial)
    (_hsym : ZeroDataSymmetric) (_hmult : ZeroMultPositive)
    (harp : ArithmeticReflectionPositivity) :
    ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2 :=
  rh_of_arp harp

end GppGwefAssembly
