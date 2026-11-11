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

/-! ## Round 7A: the general-datum finite-window certificate over the class `𝒞`

Source: GPP-bridge `MuseResearch/round7a-smooth-datum-certificate-2026-11-10.md` (commit
`8647765`), Turbo's round-7A note, verdict CERTIFIED_GENERAL. It generalizes round 5 from the
seed bump to every datum `K` (a real profile, with two-sided Laplace transform
`L_K(λ) = ∫ K(u) e^{λu} du` and `Ψ_K(ρ) = L_K(ρ - 1/2)`) in the class `𝒞` of data satisfying

* **(HK)** `∫ |K(u)| e^{σu} du < ∞` for every `σ ∈ [-2, 1]`;
* **(HD)** strip decay: `|L_K(x + iγ)| ≤ A (1 + |γ|)^{-q}` for `|x| ≤ 2`, `|γ| ≥ 14`, `q > 2`;
* **(HC)** an explicit bound `Arch` on the archimedean term `C_K(w)` for `w ≥ 2`.

Theorem (S1.2 of the note): `sup_{[2,W]} |D_K| ≤ Ztot_K + Arch + Tail_K(W)`, with `Ztot_K` the
exact sum over the verified zeros below `T₀ = 1132490.658714411` and `Tail_K(W)` the
partial-summation tail from Rosser's `N(T)` envelope and Kadiri's zero-free region. Its inputs
are the Platt/LMFDB zero list (DATA), the windowed explicit formula R4, Rosser 1941 and
Kadiri 2005; none is in this tree or in Mathlib, so the theorem is registered as a named
statement with an `open_` stub: PROVED on paper, OPEN in Lean.

What is registered here, and how it is typed.

* `laplace7A`, `defect7A`: the note's `L_K` and `D_K(W) = T_K(W) - L_K(1/2) e^{W/2}`. PROVED:
  `defect7A_eq_fluxDefect_mirror` (it is this file's `fluxDefect` of the mirrored profile), so
  on even data (autocorrelations, centred Gaussians) it is `fluxDefect` itself.
* (HC) is typed through the note's Lemma A representation `archTerm7A` (the contour integral on
  `Re s = -3/2` against `-ζ'/ζ`); the identity of that integral with R4's archimedean term is
  Lemma A, PROVED on paper, not formalized. Lemma M (the majorant of `ζ'/ζ` on that line) is the
  named statement `ZetaLogDerivMajorant7A`, and **`hc7A_of_majorant` is PROVED here**: Lemma M
  plus integrability of the majorant gives (HC) with `Arch = e^{-4} ‖L_K‖_arch`.
* **Constant in Lemma M (audit correction, Heart of the Cosmos / Grok).** The note writes the
  digamma constant as `π/2 + 1/5 + 1/75 = 1.6842 ≤ 1.7`; the sum is `1.78413`, so the displayed
  assembly gives `5.48154`, not `5.38162 ≤ 5.40`. The inequality with `5.40` still holds on the
  note's falsifier grid (worst margin `3.322`), but the written proof supports `5.49`, which is
  the constant registered here. Under `5.49` the Gaussian packet's archimedean constant is
  `e^{-4} · 47.82966 = 0.8760309` instead of `0.8638517`; the `κ = 2` certificate (Lemma B
  series) is unaffected.
* `ZeroSumBelow7A` sums over distinct nontrivial zeros with `0 < Im ρ ≤ T₀`; it agrees with
  the note's `Ztot` (a sum over the (I0) list) when those zeros are simple.

Scope, stated exactly. `𝒞` needs explicit `(A, q)` and `Arch` per datum: the sheet's
hypothesis (P) gives (HD) only qualitatively. Finite windows only: the uniform statement
`sup_w |D_K(w)| < ∞` is (FLUX-BOUND), RH-strength, OPEN, and nothing below asserts it.
-/

open Complex in
/-- Two-sided Laplace transform of a real profile: `L_K(z) = ∫ K(u) e^{zu} du`. -/
noncomputable def laplace7A (K : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, (K u : ℂ) * Complex.exp (z * u)

/-- The round-7A defect `D_K(W) = Σ Λ(n) n^{-1/2} K(log n - W) - e^{W/2} ∫ K(v) e^{v/2} dv`
(zero-free; `∫ K(v) e^{v/2} dv = L_K(1/2) = c_{0,K}`). -/
noncomputable def defect7A (K : ℝ → ℝ) (W : ℝ) : ℝ :=
  (∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) * K (Real.log n - W)) -
    Real.exp (W / 2) * ∫ v : ℝ, K v * Real.exp (v / 2)

/-- The round-7A defect is this file's `fluxDefect` of the mirrored profile `u ↦ K (-u)`.
PROVED (no zero data, no RH). -/
theorem defect7A_eq_fluxDefect_mirror (K : ℝ → ℝ) (W : ℝ) :
    defect7A K W = fluxDefect (fun u => K (-u)) W := by
  have hint : (∫ v : ℝ, K (-v) * Real.exp (-v / 2)) = ∫ v : ℝ, K v * Real.exp (v / 2) := by
    have := integral_neg_eq_self (fun v : ℝ => K v * Real.exp (v / 2)) volume
    simpa [neg_div] using this
  unfold defect7A fluxDefect
  simp only [neg_sub]
  rw [hint]

/-- On an even profile the round-7A defect is `fluxDefect` itself. PROVED. -/
theorem defect7A_eq_fluxDefect_of_even (K : ℝ → ℝ) (hK : ∀ u, K (-u) = K u) (W : ℝ) :
    defect7A K W = fluxDefect K W := by
  rw [defect7A_eq_fluxDefect_mirror]
  simp only [hK]

/-- **(HK)**, the datum regularity hypothesis of round 7A. -/
def HK7A (K : ℝ → ℝ) : Prop :=
  ∀ σ ∈ Set.Icc (-2 : ℝ) 1, Integrable (fun u : ℝ => |K u| * Real.exp (σ * u))

/-- **(HD)**, strip decay with explicit constants `(A, q)`, `q > 2`. -/
def HD7A (K : ℝ → ℝ) (q A : ℝ) : Prop :=
  2 < q ∧ ∀ x γ : ℝ, |x| ≤ 2 → 14 ≤ |γ| →
    ‖laplace7A K (x + γ * Complex.I)‖ ≤ A * (1 + |γ|) ^ (-q)

/-- The archimedean term in the note's Lemma A form:
`C_K(W) = (1/2π) ∫ L_K(-2 + iξ) e^{(-2+iξ)W} (-ζ'/ζ)(-3/2 + iξ) dξ`. -/
noncomputable def archTerm7A (K : ℝ → ℝ) (W : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ ξ : ℝ,
    laplace7A K (-2 + ξ * Complex.I) * Complex.exp ((-2 + ξ * Complex.I) * W) *
      (-(deriv riemannZeta (-3 / 2 + ξ * Complex.I) / riemannZeta (-3 / 2 + ξ * Complex.I)))

/-- **(HC)**, an explicit archimedean bound `Arch` on `[2, ∞)`. -/
def HC7A (K : ℝ → ℝ) (Arch : ℝ) : Prop :=
  ∀ w : ℝ, 2 ≤ w → ‖archTerm7A K w‖ ≤ Arch

/-- The majorant `M(ξ) = 5.49 + (1/2) log(6.25 + ξ²)` (constant corrected from the note's
`5.40`; see the section docstring). -/
noncomputable def archMajorant7A (ξ : ℝ) : ℝ :=
  549 / 100 + Real.log (625 / 100 + ξ ^ 2) / 2

/-- The named archimedean norm `‖L_K‖_arch = (1/2π) ∫ |L_K(-2 + iξ)| M(ξ) dξ`. -/
noncomputable def archNorm7A (K : ℝ → ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ ξ : ℝ, ‖laplace7A K (-2 + ξ * Complex.I)‖ * archMajorant7A ξ

/-- **Lemma M, named, not asserted:** `|ζ'/ζ(-3/2 + iξ)| ≤ M(ξ)` for all real `ξ`. -/
def ZetaLogDerivMajorant7A : Prop :=
  ∀ ξ : ℝ, ‖deriv riemannZeta (-3 / 2 + ξ * Complex.I) / riemannZeta (-3 / 2 + ξ * Complex.I)‖
    ≤ archMajorant7A ξ

/-- OPEN (round-7A Lemma M): `ZetaLogDerivMajorant7A`. On paper it is the functional-equation
assembly `log 2π + (π/2)|cot| + |ψ(5/2 - iξ)| + |ζ'/ζ(5/2 - iξ)|`, each piece standard; with the
digamma constant summed correctly (`π/2 + 1/5 + 1/75 = 1.78413`) the total is `5.48154 ≤ 5.49`.
LIBRARY GAP: the Binet–Hermite digamma bound and the cotangent identity are not assembled in
Mathlib. Not RH-strength. -/
theorem open_zeta_logderiv_majorant : True := trivial

/-- **(HC) from Lemma M, PROVED.** If Lemma M holds and the majorant integrand is integrable,
then every datum satisfies (HC) with `Arch = e^{-4} ‖L_K‖_arch`: on `w ≥ 2`,
`|e^{(-2+iξ)w}| = e^{-2w} ≤ e^{-4}`. -/
theorem hc7A_of_majorant (hM : ZetaLogDerivMajorant7A) (K : ℝ → ℝ)
    (hint : Integrable (fun ξ : ℝ =>
      ‖laplace7A K (-2 + ξ * Complex.I)‖ * archMajorant7A ξ)) :
    HC7A K (Real.exp (-4) * archNorm7A K) := by
  intro w hw
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hexp : ∀ ξ : ℝ, ‖Complex.exp ((-2 + ξ * Complex.I) * w)‖ ≤ Real.exp (-4) := by
    intro ξ
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have : ((-2 + ξ * Complex.I) * (w : ℂ)).re = -2 * w := by
      simp [Complex.mul_re]
    rw [this]; linarith
  have hpt : ∀ ξ : ℝ,
      ‖laplace7A K (-2 + ξ * Complex.I) * Complex.exp ((-2 + ξ * Complex.I) * w) *
        (-(deriv riemannZeta (-3 / 2 + ξ * Complex.I) /
          riemannZeta (-3 / 2 + ξ * Complex.I)))‖ ≤
      Real.exp (-4) * (‖laplace7A K (-2 + ξ * Complex.I)‖ * archMajorant7A ξ) := by
    intro ξ
    rw [norm_mul, norm_mul, norm_neg]
    have h1 := hexp ξ
    have h2 := hM ξ
    have hL := norm_nonneg (laplace7A K (-2 + ξ * Complex.I))
    have hE := norm_nonneg (Complex.exp ((-2 + ξ * Complex.I) * w))
    calc ‖laplace7A K (-2 + ξ * Complex.I)‖ * ‖Complex.exp ((-2 + ξ * Complex.I) * w)‖ *
          ‖deriv riemannZeta (-3 / 2 + ξ * Complex.I) / riemannZeta (-3 / 2 + ξ * Complex.I)‖
        ≤ ‖laplace7A K (-2 + ξ * Complex.I)‖ * Real.exp (-4) * archMajorant7A ξ := by
          gcongr
      _ = Real.exp (-4) * (‖laplace7A K (-2 + ξ * Complex.I)‖ * archMajorant7A ξ) := by ring
  unfold archTerm7A archNorm7A
  rw [norm_mul]
  have hc : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hc]
  have hbound := (norm_integral_le_integral_norm _).trans
    (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => norm_nonneg _)
      (hint.const_mul (Real.exp (-4))) (Filter.Eventually.of_forall hpt))
  rw [integral_const_mul] at hbound
  calc 1 / (2 * Real.pi) * ‖∫ ξ : ℝ, laplace7A K (-2 + ξ * Complex.I) *
        Complex.exp ((-2 + ξ * Complex.I) * w) *
          (-(deriv riemannZeta (-3 / 2 + ξ * Complex.I) /
            riemannZeta (-3 / 2 + ξ * Complex.I)))‖
      ≤ 1 / (2 * Real.pi) * (Real.exp (-4) * ∫ ξ : ℝ,
          ‖laplace7A K (-2 + ξ * Complex.I)‖ * archMajorant7A ξ) := by
        gcongr
    _ = Real.exp (-4) * (1 / (2 * Real.pi) * ∫ ξ : ℝ,
          ‖laplace7A K (-2 + ξ * Complex.I)‖ * archMajorant7A ξ) := by ring

/-- The verification height `T₀ = 1132490.658714411` of the (I0) zero list. -/
noncomputable def zeroHeight7A : ℝ := 1132490658714411 / 10 ^ 9

/-- `Ztot_K = 2 Σ_{0 < Im ρ ≤ T₀} |L_K(ρ - 1/2)|` over distinct nontrivial zeros. -/
noncomputable def ZeroSumBelow7A (K : ℝ → ℝ) : ℝ :=
  2 * ∑' ρ : {ρ : ℂ // ρ ∈ GppWeilCriterion.nontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ zeroHeight7A},
    ‖laplace7A K ((ρ : ℂ) - 1 / 2)‖

/-- Rosser's upper envelope
`N_env(t) = (t/2π) log(t/2πe) + 7/8 + 0.137 log t + 0.443 log log t + 1.588`. -/
noncomputable def rosserEnvelope7A (t : ℝ) : ℝ :=
  t / (2 * Real.pi) * Real.log (t / (2 * Real.pi * Real.exp 1)) + 7 / 8 +
    137 / 1000 * Real.log t + 443 / 1000 * Real.log (Real.log t) + 1588 / 1000

/-- Kadiri's de la Vallée Poussin width `c₁ / log t`, `c₁ = 1 / 5.69693`. -/
noncomputable def kadiriWidth7A (t : ℝ) : ℝ := (100000 / 569693) / Real.log t

/-- The tail majorant `A t^{-q} e^{(1/2 - width(t)) W}`. -/
noncomputable def tailMajorant7A (q A W t : ℝ) : ℝ :=
  A * t ^ (-q) * Real.exp ((1 / 2 - kadiriWidth7A t) * W)

/-- `Tail_K(W) = 2 [∫_{T₀}^∞ (-∂_t majorant) N_env dt - majorant(T₀) N(T₀)]`,
`N(T₀) = 2001052`. -/
noncomputable def tail7A (q A W : ℝ) : ℝ :=
  2 * ((∫ t in Set.Ioi zeroHeight7A, -(deriv (tailMajorant7A q A W) t) * rosserEnvelope7A t) -
    tailMajorant7A q A W zeroHeight7A * 2001052)

/-- **Round-7A general-datum finite-window theorem, named, not asserted.** Every datum of the
class `𝒞` ((HK), (HD) with `(q, A)`, (HC) with `Arch`) has
`|D_K(w)| ≤ Ztot_K + Arch + Tail_K(W)` on `[2, W]`, for `2 ≤ W < 1107 q` (the range where the
tail majorant decreases from `T₀` on). PROVED on paper (note S1.2), OPEN in Lean. -/
def FluxBoundFiniteClass7A : Prop :=
  ∀ (K : ℝ → ℝ) (q A Arch : ℝ), HK7A K → HD7A K q A → HC7A K Arch →
    ∀ W : ℝ, 2 ≤ W → W < 1107 * q →
      ∀ w ∈ Set.Icc (2 : ℝ) W, |defect7A K w| ≤ ZeroSumBelow7A K + Arch + tail7A q A W

/-- OPEN (round-7A general theorem): `FluxBoundFiniteClass7A`. Proved on paper in GPP-bridge
`MuseResearch/round7a-smooth-datum-certificate-2026-11-10.md` (`8647765`) from the (I0) zero
list (DATA), windowed R4 with Lemma A, Rosser 1941 and Kadiri 2005. LIBRARY GAP: none of those
inputs is in the tree or Mathlib. Finite windows only; (FLUX-BOUND) and RH stay OPEN. -/
theorem open_flux_bound_finite_class : True := trivial

/-- The centred Gaussian packet `K_a(u) = e^{-a u²}` (the GW-EF sheet's F1 family). -/
noncomputable def gaussPacket7A (a : ℝ) (u : ℝ) : ℝ := Real.exp (-a * u ^ 2)

/-- The width-`κ` ladder bump `sin²(πu/κ)` on `[0, κ]`. -/
noncomputable def ladderBump7A (κ : ℝ) : ℝ → ℝ :=
  Set.indicator (Set.Icc (0 : ℝ) κ) fun u => Real.sin (Real.pi * u / κ) ^ 2

/-- **Membership of the two families in `𝒞`, named, not asserted:** every Gaussian packet
(`a > 0`) satisfies (HK) and (HD) at every `q > 2`, and every ladder-bump autocorrelation with
`κ ∈ [1, 3]` satisfies (HK) and (HD) at `q = 6`. (HC) then follows from Lemma M through
`hc7A_of_majorant`. -/
def FamiliesInClass7A : Prop :=
  (∀ a : ℝ, 0 < a → HK7A (gaussPacket7A a) ∧ ∀ q : ℝ, 2 < q → ∃ A, HD7A (gaussPacket7A a) q A) ∧
  (∀ κ : ℝ, 1 ≤ κ → κ ≤ 3 →
    HK7A (GppArithmeticReflection.autocorr (ladderBump7A κ)) ∧
      ∃ A, HD7A (GppArithmeticReflection.autocorr (ladderBump7A κ)) 6 A)

/-- OPEN (round-7A families): `FamiliesInClass7A`. Proved on paper (note S2.2, S3.2: the packet
from `L_a(λ) = √(π/a) e^{λ²/(4a)}`, the bumps from the closed form `S_κ` with explicit
`A(κ)`). LIBRARY GAP: the Gaussian Laplace closed form is in Mathlib
(`integral_cexp_quadratic`) but the strip estimates are not assembled here. -/
theorem open_families_in_class : True := trivial

/-- **Round-7A certified instances, named, not asserted.** On `[2, 12]`: the Gaussian packet
`a = 1/2` has `|D| ≤ 0.876031` (corrected Lemma M constant; the note prints `0.8638517`), and
the `κ = 2` ladder-bump autocorrelation has `|fluxDefect| ≤ 0.01643609` (the note's
`0.01643608713`, rounded up). -/
def FluxBoundFiniteInstances7A : Prop :=
  (∀ w : ℝ, 2 ≤ w → w ≤ 12 → |defect7A (gaussPacket7A (1 / 2)) w| ≤ 876031 / 10 ^ 6) ∧
  (∀ w : ℝ, 2 ≤ w → w ≤ 12 →
    |fluxDefect (GppArithmeticReflection.autocorr (ladderBump7A 2)) w| ≤ 1643609 / 10 ^ 8)

/-- OPEN (round-7A instances): `FluxBoundFiniteInstances7A`. Proved on paper from the general
theorem plus the per-family constants (note S2.3, S3.4); the measured suprema are `0.2383792`
and `0.0163792`. LIBRARY GAP: the general theorem's external inputs. Finite windows only. -/
theorem open_flux_bound_finite_instances : True := trivial

end GppFluxBound
