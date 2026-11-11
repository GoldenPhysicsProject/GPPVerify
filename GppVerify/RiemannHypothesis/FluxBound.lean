/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Turbo's reduction note, ported by Heart of the Cosmos / Grok)
-/
import GppVerify.RiemannHypothesis.ArithmeticReflectionPositivity
import GppVerify.RiemannHypothesis.ExplicitFormulaAssembly
import GppVerify.RiemannHypothesis.GwefAssembly
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# (FLUX-BOUND): the absolute limit step of the flux reduction, as a named hypothesis

Source: GPP-bridge `MuseResearch/round3-flux-reduction-2026-11-10.md` (commit `b212665`),
Turbo's round-3 reduction of the orbit-trace obligation (FLUX=∂). The note discharges the
finite-window identity (R1, from the centred Poisson identity, i.e. `adelicPoissonScaled`
with the `q = 0` terms moved across), the main-term cancellation (R2), relative exhaustion
(R3, the classical PNT error term) and the identification of the absolute defect with the
zero-side sum (R4, `explicit_formula_zeroSum`). The one step it does not close is the
absolute limit step, isolated there as **(FLUX-BOUND)**. This file records that step as a
named proposition and parks it as an `open_` stub. Nothing here proves it, and nothing in
the tree assumes it.

## Reading of the flux defect used here

The note's section 3 states (FLUX-BOUND) for "the flux defect kernel `D_h`" of an
autocorrelation datum `h = f ⋆ f̃`. The tree has no flux kernel, so this file uses the
note's own zero-free smoothed form (falsifier F2, and R2's tail term):

  `D_h(W) = Σ_n Λ(n) n^{-1/2} h(W - log n) - e^{W/2} ∫ h(v) e^{-v/2} dv`,

the prime-orbit tail at edge `W` minus its `ψ → x` main term (`= e^{W/2} ĥ(1/2)`, the
pole growth that R2 cancels). No zero of any L-function appears in the definition.
(FLUX-BOUND) is: for every smooth compactly supported `f`, `D_{f ⋆ f̃}` is bounded on
`[0, ∞)`.

## Status

**OPEN.** By the note's R5, given R1–R4, (FLUX-BOUND) is equivalent to RH: a zero with
real part `β > 1/2` puts a mode `e^{(β - 1/2) W}` into `D_h` for suitable `f`, and if all
zeros are on the line `D_h` is a bounded oscillatory sum. That equivalence is **not**
formalized here. (FLUX-BOUND) is RH-strength and is not a lemma on the way to RH.
No claim about RH, which remains OPEN.

## (SIGN) is the same target (round 4)

Source: GPP-bridge `MuseResearch/round4-sign-flux-dictionary-2026-11-10.md` (commit
`d44e7d5`), Turbo's round-4 dictionary between (SIGN), the operator form of the round-2
Hankel construction, and (FLUX-BOUND). The note proves (on paper) that the two are one
statement, in both directions, under exactly these hypotheses (its section 5):

* **(H1)** the Hankel/trace pairing on the cone is the Weil form,
  `Q_W(h) = B_∂(h) + ∫ μ Ĥ` (classical; not a named theorem in this tree);
* **(H2)** flux R1 (`GlobalTate.Poisson.adelicPoissonScaled`, in tree), R2 (residue of `ζ` at
  `s = 1`, STANDARD) and R4 (GW-EF-1, `GppExplicitFormulaAssembly.explicit_formula_zeroSum`,
  in tree, though only in its assembled form; the windowed form R4 uses is not formalized).
  R3 (PNT error term) is **not** used;
* **(H3)** GW-EF-2 (the factorisation `Φ(f ⋆ f̃)(s) = Ψf(s) Ψf(1 - s)`) and `rh_of_arp`.
  **In tree, PROVED** (`GppVerify/RiemannHypothesis/GwefAssembly.lean`):
  `GppGwefAssembly.gwef2_factorisation` and `GppGwefAssembly.rh_of_arp`
  (`ArithmeticReflectionPositivity → ∀ ρ ∈ nontrivialZeros, ρ.re = 1/2`, ARP its only
  hypothesis; GW-EF-3 closed from the in-tree density theorem `gaussian_annihilator`);
* **(H4)** the test class is the sheet's class.

In its assembled form (the note's D3.2, `margin(h) ≥ 0` on every cone datum) (SIGN) is the
statement already in the tree as `GppArithmeticReflection.ArithmeticReflectionPositivity`.
So (SIGN) gets no separate registration: `FluxBound` and `ArithmeticReflectionPositivity` are
the one remaining statement in its two dialects, and the open step tying them is
`open_flux_bound_iff_arp` below. The note's direction (FLUX-BOUND) ⟹ (SIGN) uses only
boundedness of the defect (its F1), which is exactly what `FluxBound` asserts. Its F1 kills an
off-line zero `ρ₀` with the Gaussian datum of the sheet; in this file's compactly supported
class one needs instead a datum with `Ψf(ρ₀) Ψf(1 - ρ₀) ≠ 0`, which a nonzero entire Mellin
transform supplies. That substitution is part of the open step, not proved here.

The equivalence is RH-strength. It removes one of two bookkeeping targets; it does not make
either side easier. `fluxDefect_autocorr_eq_mirror` (proved below) checks that this file's
`fluxDefect` is the note's `𝒟(W) = T(W) - c₀ e^{W/2}` with `T(W) = Σ Λ(n) n^{-1/2} h(log n - W)`
and `c₀ = ∫ h(v) e^{v/2} dv`, using only that autocorrelations are even.

Daniel Toupin / Golden Physics Project, with AI assistance (Turbo wrote the reduction and
dictionary notes and the round-5 finite-window note; Heart of the Cosmos / Grok registered the
hypothesis and its finite companion).
-/

namespace GppFluxBound

open MeasureTheory ArithmeticFunction
open scoped ContDiff

/-- The smoothed prime-side flux defect at edge `W` for a datum `h` (zero-free):
`Σ_n Λ(n) n^{-1/2} h(W - log n) - e^{W/2} ∫ h(v) e^{-v/2} dv`. For compactly supported `h`
only finitely many terms of the sum are nonzero. -/
noncomputable def fluxDefect (h : ℝ → ℝ) (W : ℝ) : ℝ :=
  (∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) * h (W - Real.log n)) -
    Real.exp (W / 2) * ∫ v : ℝ, h v * Real.exp (-v / 2)

/-- **(FLUX-BOUND), named, not asserted.** For every smooth compactly supported `f`, the
flux defect of the autocorrelation datum `f ⋆ f̃` is bounded on `[0, ∞)`. Turbo's
reduction note (R5) shows this is RH-strength (equivalent to RH given R1–R4); it is OPEN. -/
def FluxBound : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
    ∃ C : ℝ, ∀ W : ℝ, 0 ≤ W →
      |fluxDefect (GppArithmeticReflection.autocorr f) W| ≤ C

/-- OPEN (FLUX-BOUND): `FluxBound`, the absolute limit step of the flux reduction
(GPP-bridge `MuseResearch/round3-flux-reduction-2026-11-10.md`, section 3). RH-strength by
that note's R5: it needs zero-location input of Weil-positivity strength and cannot come
from window or exhaustion analysis alone. Parked as a named stub per GPPVerify honesty
rules; nothing in the tree assumes it. -/
theorem open_flux_bound : True := trivial

/-- The registered defect is the round-4 note's `𝒟(W) = T(W) - c₀ e^{W/2}`: on an
autocorrelation the two readings `h(W - log n)` / `h(log n - W)` and `e^{-v/2}` / `e^{v/2}` agree,
because `autocorr f` is even. PROVED (no zero data, no RH). -/
theorem fluxDefect_autocorr_eq_mirror (f : ℝ → ℝ) (W : ℝ) :
    fluxDefect (GppArithmeticReflection.autocorr f) W =
      (∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          GppArithmeticReflection.autocorr f (Real.log n - W)) -
        Real.exp (W / 2) *
          ∫ v : ℝ, GppArithmeticReflection.autocorr f v * Real.exp (v / 2) := by
  have hev := GppExplicitFormulaAssembly.autocorr_even f
  have hsum : ∀ n : ℕ, GppArithmeticReflection.autocorr f (W - Real.log n) =
      GppArithmeticReflection.autocorr f (Real.log n - W) := fun n => by
    rw [← hev, neg_sub]
  have hint : (∫ v : ℝ, GppArithmeticReflection.autocorr f v * Real.exp (-v / 2)) =
      ∫ v : ℝ, GppArithmeticReflection.autocorr f v * Real.exp (v / 2) := by
    rw [← integral_neg_eq_self (fun v : ℝ => GppArithmeticReflection.autocorr f v *
      Real.exp (v / 2))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [hev, neg_div]
  unfold fluxDefect
  simp_rw [hsum]
  rw [hint]

/-- OPEN (round 4 dictionary): `FluxBound ↔ ArithmeticReflectionPositivity`, i.e.
(FLUX-BOUND) ⟺ (SIGN) in (SIGN)'s assembled form. Proved on paper in GPP-bridge
`MuseResearch/round4-sign-flux-dictionary-2026-11-10.md` (`d44e7d5`) under its hypotheses
(H1)–(H4); not formalized. Its (H3) input is in tree and proved:
`GppGwefAssembly.gwef2_factorisation` (GW-EF-2) and `GppGwefAssembly.rh_of_arp`. Still
missing, and kept as named hypotheses of the paper argument, not assumed anywhere: (H1) the
Hankel/trace pairing is the Weil form, the windowed form of R4, and the compactly supported
replacement for the Gaussian datum of F1. RH-strength; ARP OPEN; RH OPEN. -/
theorem open_flux_bound_iff_arp : True := trivial

/-! ## Round 5: the certified finite companion (seed datum)

Source: GPP-bridge `MuseResearch/round5-finite-window-flux-2026-11-10.md` (commit `12deca7`,
SHA-256 `3a6c47205091dd11e561c313202e92d40ab93733f966d13e5f84206b09d93852`), Turbo's round-5
note. For the seed bump `φ(u) = sin²(πu)` on `[0,1]` and its autocorrelation `G₀`, the note
proves on paper that `sup_{2 ≤ w ≤ W} |𝒟(w)| ≤ C₂(W) = Ztot + Triv + Tail(W)`, with
`Ztot = 3.405373e-4` (the verified on-line zeros), `Triv = 2.12269391584518e-3` (trivial zeros,
exact) and `Tail(W) ≤ 7.2e-25` for `W ≤ 12`. Its inputs are the Platt/LMFDB zero list to
`T₀ = 1132490.66` (DATA), GW-EF-1, Rosser's explicit `N(T)` bound and Kadiri's (or Ford's)
zero-free region. None of those external inputs is in this tree or in Mathlib, so the
companion is registered here as a named statement with an `open_` stub: PROVED on paper,
OPEN in Lean.

Scope, stated exactly. The statement below is the tabulated window `[2, 12]` with the
constant rounded up in the seventh digit. The seed bump is `C¹` but not `C²` at `0` and `1`,
so `seedBump` is **not** in `FluxBound`'s smooth test class: the companion is a finite
statement about a neighbouring datum, not an instance of `FluxBound`. The uniform statement
over all windows is exactly (FLUX-BOUND), RH-strength, OPEN.
-/

/-- The seed bump `φ(u) = sin²(πu)` on `[0, 1]`, zero elsewhere (the programme's banked
ladder/Hankel datum). -/
noncomputable def seedBump : ℝ → ℝ :=
  Set.indicator (Set.Icc (0 : ℝ) 1) fun u => Real.sin (Real.pi * u) ^ 2

/-- **Round-5 finite companion, named, not asserted.** On the window `[2, 12]` the flux defect
of the seed autocorrelation is at most `2.463232e-3` (Turbo's `C₂(W) = 2.463231e-3`, rounded
up). PROVED on paper under DATA + cited classical inputs; not formalized. -/
def FluxBoundFiniteSeed : Prop :=
  ∀ w : ℝ, 2 ≤ w → w ≤ 12 →
    |fluxDefect (GppArithmeticReflection.autocorr seedBump) w| ≤ 2463232 / 10 ^ 9

/-- OPEN (round-5 finite companion): `FluxBoundFiniteSeed`. Proved on paper in GPP-bridge
`MuseResearch/round5-finite-window-flux-2026-11-10.md` (`12deca7`) from the verified zero list
to `T₀ = 1132490.66` (DATA), GW-EF-1, Rosser's explicit `N(T)` and an explicit zero-free region;
none of these external inputs is in the tree, so it is parked as a named stub. Finite-window
only: it says nothing about (FLUX-BOUND) or RH, which remain OPEN. -/
theorem open_flux_bound_finite_seed : True := trivial

end GppFluxBound
