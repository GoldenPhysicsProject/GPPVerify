/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Heart of the Cosmos (Grok, GPPDiscovery5 seat). Turbo PR #11 6821237527, item 1.

# H_ψ for ζ, triangle ψ, as a Lean-typed statement (no proof claim)

Labels (same as GPPDiscovery5 `lean/s-eq-delta/num/krein_H/H_STATEMENT.md`, commit 636747f):
* `HPsi` (the Toeplitz form of H_ψ): **OPEN**. Stated here, not proved.
* `HPsiWindows` (the `HAllWindows` form, KreinBridge line 64): **OPEN**. Stated here, not proved.
* `HPsiEquiv` (Toeplitz form ↔ `HAllWindows` form for any B, ℓ_c, ℓ_s on `F_ψ` with the
  translate kernel `Kψ` and the cosh pairing): a **named premise**, not proved here.
  Paper argument: first ⟺ by `claim_iff_hyperplane` (PROVED in ToeplitzHyperplane), window
  quantifier vacuous by `fit_translates` (PROVED in KreinBridge).
* `hEF` (Weil's explicit formula on translates, `Kψ (x − y) = Σ_ρ …`): CHECKED (secondary:
  Connes arXiv:1509.05576 §2.1.1 citing Weil), NUMERICAL to 1.02e−8 (400 zeros). Not used here.
* Chain H_ψ ⇒ RH: SKETCH. ARP: OPEN. RH: OPEN.

Everything below is a definition. There are no theorems, no `sorry`, no axioms.

Kernel (zero-free side; normalisation pinned by the hEF numerics):
  Kψ(d) = 2 Ψ(i/2)² cosh(d/2) − Σ_{n≥2} Λ(n) n^{−1/2} [g(log n + d) + g(−log n + d)]
          + (1/π) ∫_0^∞ Ψ(t)² cos(t d) (Re ψ_Γ(1/4 + i t/2) − log π) dt,
  Ψ(t) = (sin(t/2)/(t/2))², Ψ(i/2) = 16 sinh²(1/4), g = ψ ⋆ ψ, ψ(t) = max(0, 1 − |t|),
  ψ_Γ = Γ'/Γ (`logDeriv Complex.Gamma`).
-/
import GppVerify.RiemannHypothesis.KreinBridge
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace GppKreinHPsi

open GppKreinBridge MeasureTheory

/-- The triangle test function `ψ(t) = max(0, 1 − |t|)`, supported in `[−1, 1]`. -/
noncomputable def triPsi (t : ℝ) : ℝ := max 0 (1 - |t|)

/-- Translate `τ_x ψ = ψ(· − x)`. -/
noncomputable def tau (x : ℝ) : ℝ → ℝ := fun t => triPsi (t - x)

/-- Fourier transform of the triangle on the real axis, `Ψ(t) = (sin(t/2)/(t/2))²`. -/
noncomputable def bigPsi (t : ℝ) : ℝ := if t = 0 then 1 else (Real.sin (t / 2) / (t / 2)) ^ 2

/-- `Ψ(i/2) = Ψ(−i/2) = 16 sinh²(1/4)`. -/
noncomputable def bigPsiI2 : ℝ := 16 * Real.sinh (1 / 4) ^ 2

/-- Autocorrelation `g = ψ ⋆ ψ` in closed form. -/
noncomputable def triG (y : ℝ) : ℝ :=
  if |y| ≤ 1 then 2 / 3 - y ^ 2 + |y| ^ 3 / 2
  else if |y| ≤ 2 then (2 - |y|) ^ 3 / 6 else 0

/-- Pole term `2 Ψ(i/2)² cosh(d/2)`. -/
noncomputable def poleTerm (d : ℝ) : ℝ := 2 * bigPsiI2 ^ 2 * Real.cosh (d / 2)

/-- Prime term `Σ_n Λ(n) n^{−1/2} [g(log n + d) + g(−log n + d)]` (finitely many nonzero terms,
since `g` vanishes off `[−2, 2]`). -/
noncomputable def primeTerm (d : ℝ) : ℝ :=
  ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n *
    (triG (Real.log n + d) + triG (-Real.log n + d))

/-- Archimedean term `(1/π) ∫_0^∞ Ψ(t)² cos(t d) (Re ψ_Γ(1/4 + it/2) − log π) dt`. -/
noncomputable def archTerm (d : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ t in Set.Ioi (0 : ℝ), bigPsi t ^ 2 * Real.cos (t * d) *
    ((logDeriv Complex.Gamma ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I)).re - Real.log Real.pi)

/-- The translate kernel `Kψ(d) = B(τ_0 ψ, τ_d ψ)` on the zero-free side. -/
noncomputable def Kpsi (d : ℝ) : ℝ := poleTerm d - primeTerm d + archTerm d

/-- **H_ψ, Toeplitz form** (OPEN): positivity of `kform Kψ` on the cosh hyperplane. -/
def HPsi : Prop :=
  ∀ (n : ℕ) (x c : Fin n → ℝ), ∑ i, c i * Real.cosh (x i / 2) = 0 → 0 ≤ kform Kpsi x c

/-- `F_ψ = span_ℝ {τ_x ψ}`. -/
noncomputable def Fpsi : Submodule ℝ (ℝ → ℝ) := Submodule.span ℝ (Set.range tau)

/-- The windowed spaces `S L = F_ψ ∩ window L`. -/
noncomputable def Spsi (L : ℝ) : Submodule ℝ (ℝ → ℝ) := Fpsi ⊓ window L

/-- The data `HAllWindows` consumes on `F_ψ`: a bilinear `B` whose translate kernel is `Kψ`,
and L-independent `ℓ_c, ℓ_s` with the cosh / sinh pairings on translates. -/
structure WeilData where
  B : (ℝ → ℝ) →ₗ[ℝ] (ℝ → ℝ) →ₗ[ℝ] ℝ
  lc : (ℝ → ℝ) →ₗ[ℝ] ℝ
  ls : (ℝ → ℝ) →ₗ[ℝ] ℝ
  hK : ∀ x y, B (tau x) (tau y) = Kpsi (x - y)
  hlc : ∀ x, lc (tau x) = bigPsiI2 * Real.cosh (x / 2)
  hls : ∀ x, ls (tau x) = bigPsiI2 * Real.sinh (x / 2)

/-- **H_ψ, `HAllWindows` form** (OPEN) for given Weil data. -/
def HPsiWindows (W : WeilData) : Prop :=
  HAllWindows W.B Spsi (fun _ => W.lc) (fun _ => W.ls)

/-- **Named premise** (not proved here): the two forms agree for every choice of Weil data. -/
def HPsiEquiv : Prop := ∀ W : WeilData, HPsiWindows W ↔ HPsi

end GppKreinHPsi
