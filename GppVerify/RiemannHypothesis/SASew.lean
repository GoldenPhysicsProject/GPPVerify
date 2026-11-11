/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Turbo's round-7 target note, registered by Heart of the Cosmos / Grok)
-/
import GppVerify.RiemannHypothesis.FluxBound
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# (SA-sew): the sewing form of the prime-sublattice self-adjointness target, registered

Source: GPP-bridge `MuseResearch/round7-prime-sublattice-target-2026-11-10.md` (commit `db24e8c`),
Turbo's round-7 note, section 3, and `MuseResearch/round2-trace-construction-2026-11-10.md`
(sections 1.3 and 7) for the unit-stratum boundary form `B_∂` and (FLUX=∂).

## What is registered, and what is not

The chain paper's literal missing step ("`H_BC` restricted to the prime sublattice is
self-adjoint", `rem:rh-optical`) is TRUE-AND-EMPTY: in both rigorous readings the restricted
operator is diagonal / multiplication, already self-adjoint, and the literal dictionary to (SIGN)
is refuted at the `F_θ` control (round-7 section 3). It is **not** registered here, and must not be.

The content-carrying form is **(SA-sew)**: for the completed scale (dilation) operator `A` of the
trace construction, the boundary form of the adjoint `A*` is exhausted by the unit-stratum
boundary form `B_∂` on `ℂ²_∂` — the prime strata contribute no residual boundary term.

* `unitBoundaryForm` is `B_∂`: on unit-stratum boundary values `a = (𝒜(0), 𝒜(1))`,
  `B_∂(a, b) = conj (a 1) * b 0 + conj (a 0) * b 1` (the trace note's
  `𝒜_f(1) conj 𝒜_g(0) + 𝒜_f(0) conj 𝒜_g(1)`, written with Mathlib's convention that inner
  products are conjugate-linear in the first slot).
* `greenForm T x y = ⟪T x, y⟫ - ⟪x, T y⟫` is the (von Neumann / Green) boundary form of a
  partially defined operator `T`, to be applied to `T = A*`.
* `ScaleSewingDatum` bundles what the trace construction has to supply: a complex inner product
  space `E`, the adjoint scale operator `A*` (as a `LinearPMap`), the unit-stratum boundary map
  `Γ : dom A* → ℂ²_∂`, and the state map `Π` (field `stateMap`).
* `SASew S` is the actual statement: `greenForm S.Astar x y = I * B_∂ (Γ x, Γ y)` for all
  `x, y ∈ dom A*`.

**Gap, in one sentence.** The completed scale operator of `𝔸 ⋊ ℚ^×` is not constructed in this
tree (round-7 GAP-Z / GAP-D: the paper supplies no operator and no domain data), so (SA-sew) is
typed as a predicate on a datum `S`, and the target is `SASew S` for the trace-construction datum
once that datum exists; every link to the Weil form is a named hypothesis on `S`.

## The equivalence cycle, at the strength the inputs support

Round 7 places (SA-sew) in the cycle (SA-sew) ⟺ (FLUX=∂) ⟺ ARP = (SIGN) ⟺ (FLUX-BOUND).

* **(SA-sew) ⟹ ARP** (`arp_of_saSew`). The round-note input is the trace note's section 7
  conclusion with (H1): the exhausted completion makes `Π` a Hilbert-space state map with
  `Q_W(f ⋆ f̃) = ‖Π f‖²`. That input is carried as the named hypothesis `SewGramLink S`; the
  remaining step (a Gram value is nonnegative, so ARP) is PROVED here.
* **ARP ⟹ RH** is in tree (`GppGwefAssembly.rh_of_arp`), so `rh_of_saSew` is PROVED modulo
  `SewGramLink S` and `SASew S`.
* **ARP ⟹ (FLUX-BOUND)** is the round-4 dictionary's (SIGN) ⟹ (FLUX-BOUND) half, carried as
  `ArpToFluxBound` (the open step `GppFluxBound.open_flux_bound_iff_arp`).
* **(FLUX-BOUND) ⟹ (SA-sew)** is the round-3 reduction (R1–R4 plus the absolute remainder) with
  the standard boundary-form correspondence (FLUX=∂) ⟺ (SA-sew), carried as `FluxBoundToSew S`.
* The cycle then closes as theorems: `saSew_iff_arp`, `saSew_iff_fluxBound`.

The two structural facts about the statement itself are PROVED: `greenForm` and `I • B_∂` have the
same skew-Hermitian symmetry, so (SA-sew) is shape-consistent (`unitBoundaryForm_conj_symm`,
`greenForm_skew`, `saSew_shape_consistent`), and under (SA-sew) the adjoint is symmetric on the
kernel of the unit-stratum boundary map (`symmetric_on_ker_of_saSew`): the completion closes
with no prime-stratum boundary condition.

## Status

(SA-sew), (FLUX=∂), ARP, (SIGN), (FLUX-BOUND): **OPEN**, registered, not claimed. RH: **OPEN**.
No `sorry`, no axiom; the three carried inputs are hypotheses of the lemmas that use them, and
nothing in the tree assumes them.

Daniel Toupin / Golden Physics Project, with AI assistance (Turbo wrote the round-2, -3, -4 and -7
notes; Heart of the Cosmos / Grok registered (SA-sew) and its implications).
-/

namespace GppSASew

open GppArithmeticReflection GppFluxBound
open scoped ContDiff ComplexConjugate InnerProductSpace

/-- **`B_∂`, the unit-stratum boundary form** on boundary values `a = (𝒜(0), 𝒜(1)) ∈ ℂ²_∂`:
`B_∂(a, b) = conj (a 1) * b 0 + conj (a 0) * b 1` (trace note section 1.3, conjugate-linear in the
first slot). Rank two, Hermitian. -/
def unitBoundaryForm (a b : Fin 2 → ℂ) : ℂ :=
  conj (a 1) * b 0 + conj (a 0) * b 1

/-- `B_∂` is Hermitian: `B_∂(b, a) = conj (B_∂(a, b))`. PROVED. -/
theorem unitBoundaryForm_conj_symm (a b : Fin 2 → ℂ) :
    unitBoundaryForm b a = conj (unitBoundaryForm a b) := by
  simp only [unitBoundaryForm, map_add, map_mul, Complex.conj_conj]
  ring

section Green

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The (von Neumann / Green) boundary form of a partially defined operator `T`:
`greenForm T x y = ⟪T x, y⟫ - ⟪x, T y⟫` on `dom T`. Applied to `T = A*` it is the adjoint
boundary form that (SA-sew) speaks about. -/
noncomputable def greenForm (T : E →ₗ.[ℂ] E) (x y : T.domain) : ℂ :=
  ⟪T x, (y : E)⟫_ℂ - ⟪(x : E), T y⟫_ℂ

/-- The Green form is skew-Hermitian: `greenForm T y x = - conj (greenForm T x y)`. PROVED. -/
theorem greenForm_skew (T : E →ₗ.[ℂ] E) (x y : T.domain) :
    greenForm T y x = -conj (greenForm T x y) := by
  simp only [greenForm, map_sub, inner_conj_symm]
  ring

end Green

/-- **The data the trace construction must supply** for (SA-sew): a complex inner product space
`E` (the orbit-trace space completed with `ℂ²_∂`), the adjoint `Astar = A*` of the completed scale
(dilation) operator, the unit-stratum boundary map `Γ : dom A* → ℂ²_∂` (Mellin boundary values
`(𝒜(0), 𝒜(1))`), and the state map `Π` (field `stateMap`) (the transversal difference of `O_f`). Not constructed in
this tree (round-7 GAP-Z, GAP-D). -/
structure ScaleSewingDatum (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  /-- The adjoint of the completed scale operator. -/
  Astar : E →ₗ.[ℂ] E
  /-- Unit-stratum boundary values on the adjoint domain. -/
  Γ : Astar.domain →ₗ[ℂ] (Fin 2 → ℂ)
  /-- The state map `f ↦ Π f`. -/
  stateMap : (ℝ → ℝ) → E

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **(SA-sew), named, not asserted.** The adjoint boundary form of the completed scale operator
is exhausted by the unit stratum: for all `x, y ∈ dom A*`,
`⟪A* x, y⟫ - ⟪x, A* y⟫ = I * B_∂(Γ x, Γ y)`. No residual boundary term from the prime strata.
OPEN (round-7 note section 3; equivalent to (FLUX=∂) by the standard boundary-form
correspondence). -/
def SASew (S : ScaleSewingDatum E) : Prop :=
  ∀ x y : S.Astar.domain,
    greenForm S.Astar x y = Complex.I * unitBoundaryForm (S.Γ x) (S.Γ y)

/-- `I • B_∂` has exactly the Green form's skew-Hermitian symmetry, so the identity (SA-sew)
asks for is shape-consistent (it cannot fail for symmetry reasons alone). PROVED. -/
theorem saSew_shape_consistent (a b : Fin 2 → ℂ) :
    Complex.I * unitBoundaryForm b a = -conj (Complex.I * unitBoundaryForm a b) := by
  rw [unitBoundaryForm_conj_symm, map_mul, Complex.conj_I]
  ring

/-- **Under (SA-sew) the adjoint is symmetric on `ker Γ`**: once the unit-stratum boundary values
vanish there is no boundary term left at all, i.e. the completion closes with no prime-stratum
boundary condition. PROVED (from (SA-sew), which is OPEN). -/
theorem symmetric_on_ker_of_saSew {S : ScaleSewingDatum E} (h : SASew S)
    {x y : S.Astar.domain} (hx : S.Γ x = 0) :
    ⟪S.Astar x, (y : E)⟫_ℂ = ⟪(x : E), S.Astar y⟫_ℂ := by
  have := h x y
  rw [hx] at this
  simp only [greenForm, unitBoundaryForm, Pi.zero_apply, map_zero, zero_mul, zero_add,
    mul_zero] at this
  exact sub_eq_zero.mp this

/-- **Named round-note input (trace note section 7 with (H1)).** Under (SA-sew) the state map is a
Hilbert-space Gram realisation of the Weil form on the test class:
`Q_W(f ⋆ f̃) = ‖Π f‖²`. Carried as a hypothesis, not asserted; OPEN. -/
abbrev SewGramLink (S : ScaleSewingDatum E) : Prop :=
  SASew S → ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
    weilForm (autocorr f) = ‖S.stateMap f‖ ^ 2

/-- **Named round-note input (round-4 dictionary, (SIGN) ⟹ (FLUX-BOUND) half).** Carried as a
hypothesis, not asserted; this is one direction of `GppFluxBound.open_flux_bound_iff_arp`. -/
abbrev ArpToFluxBound : Prop :=
  ArithmeticReflectionPositivity → FluxBound

/-- **Named round-note input (round-3 reduction + boundary-form correspondence).** (FLUX-BOUND)
closes the flux reduction to (FLUX=∂), which is (SA-sew) for the trace-construction datum.
Carried as a hypothesis, not asserted. -/
abbrev FluxBoundToSew (S : ScaleSewingDatum E) : Prop :=
  FluxBound → SASew S

/-- **(SA-sew) ⟹ ARP.** PROVED modulo the named input `SewGramLink S`: a Gram value
`‖Π f‖²` is nonnegative. (SA-sew) is OPEN, so ARP stays OPEN. -/
theorem arp_of_saSew {S : ScaleSewingDatum E} (hlink : SewGramLink S) (h : SASew S) :
    ArithmeticReflectionPositivity := by
  intro f hf hc
  rw [hlink h f hf hc]
  positivity

/-- **(SA-sew) ⟹ RH**, through the in-tree `GppGwefAssembly.rh_of_arp` (round-7 T8 chain).
PROVED modulo `SewGramLink S`; (SA-sew) is OPEN, RH is OPEN. -/
theorem rh_of_saSew {S : ScaleSewingDatum E} (hlink : SewGramLink S) (h : SASew S) :
    ∀ ρ ∈ GppWeilCriterion.nontrivialZeros, ρ.re = 1 / 2 :=
  GppGwefAssembly.rh_of_arp (arp_of_saSew hlink h)

/-- **(SA-sew) ⟹ (FLUX-BOUND).** PROVED modulo `SewGramLink S` and `ArpToFluxBound`. -/
theorem fluxBound_of_saSew {S : ScaleSewingDatum E} (hlink : SewGramLink S)
    (hdict : ArpToFluxBound) (h : SASew S) : FluxBound :=
  hdict (arp_of_saSew hlink h)

/-- **ARP ⟹ (SA-sew).** PROVED modulo `ArpToFluxBound` and `FluxBoundToSew S`. -/
theorem saSew_of_arp {S : ScaleSewingDatum E} (hdict : ArpToFluxBound)
    (hred : FluxBoundToSew S) (h : ArithmeticReflectionPositivity) : SASew S :=
  hred (hdict h)

/-- **The cycle closes: (SA-sew) ⟺ ARP**, PROVED modulo the three named round-note inputs.
Both sides OPEN. -/
theorem saSew_iff_arp {S : ScaleSewingDatum E} (hlink : SewGramLink S)
    (hdict : ArpToFluxBound) (hred : FluxBoundToSew S) :
    SASew S ↔ ArithmeticReflectionPositivity :=
  ⟨arp_of_saSew hlink, saSew_of_arp hdict hred⟩

/-- **The cycle closes: (SA-sew) ⟺ (FLUX-BOUND)**, PROVED modulo the three named round-note
inputs. Both sides OPEN. -/
theorem saSew_iff_fluxBound {S : ScaleSewingDatum E} (hlink : SewGramLink S)
    (hdict : ArpToFluxBound) (hred : FluxBoundToSew S) :
    SASew S ↔ FluxBound :=
  ⟨fluxBound_of_saSew hlink hdict, hred⟩

/-- OPEN (SA-sew): `SASew S` for the trace-construction datum `S` (round-7 note section 3). The
completed scale operator of `𝔸 ⋊ ℚ^×` is not constructed in this tree (GAP-Z, GAP-D), so the
target is typed on a datum; equivalent to ARP, (SIGN) and (FLUX-BOUND) modulo the named inputs
below. RH-strength; parked per GPPVerify honesty rules. -/
theorem open_sa_sew : True := trivial

/-- OPEN (round-note input): `SewGramLink S`, the trace note's section 7 conclusion with (H1)
(`Q_W(f ⋆ f̃) = ‖Π f‖²` under (FLUX=∂)). Not formalized; carried as a hypothesis. -/
theorem open_sew_gram_link : True := trivial

/-- OPEN (round-note input): `FluxBoundToSew S`, the round-3 flux reduction (R1–R4 and the
absolute remainder) composed with the standard boundary-form correspondence
(FLUX=∂) ⟺ (SA-sew). Not formalized; carried as a hypothesis. -/
theorem open_flux_bound_to_sew : True := trivial

end GppSASew
