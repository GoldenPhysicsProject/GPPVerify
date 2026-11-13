/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Flint (D3 seat). Routed task: Turbo to Flint, 2026-11-12 (Heart of the Cosmos via
PR #11 comment 6832868926; Daniel's direction). Item 4 of the routed task.

# `WeilIsGram`: the Weil form of `Kψ` as an Abel–Cesàro Gram limit

`HPsi` (`GppKreinHPsi.HPsi`, OPEN) is the positivity of the Toeplitz form of the
translate kernel `Kψ` on the cosh hyperplane:
`∑ i, c i * Real.cosh (x i / 2) = 0 → 0 ≤ kform Kpsi x c`, where
`kform K x c = ∑ i, ∑ j, c i * c j * K (x i - x j)`.

**Entrywise reading.** Contracted against a configuration `(x, c)` on the cosh
hyperplane, `WeilIsGram` says that the Toeplitz value `kform Kpsi x c` is the
`ε → 0⁺` limit of Abel–Cesàro Gram values: entrywise,
`Kψ (xᵢ − xⱼ) = lim_{ε → 0⁺} ⟨Fᵢ, Fⱼ⟩_ε`, contracted against the configuration
with `F = Σᵢ cᵢ Fᵢ`, i.e. `kform Kpsi x c = lim_{ε → 0⁺} ⟨F, F⟩_ε`
where `⟨·, ·⟩_ε` is `GppCesaroAbel.abelForm`. The vectors `Fᵢ` are finite
character sums (exponents `α ε`, coefficients `d ε`) in the Abel–Cesàro form of
`CesaroAbelState.lean`.

**The Gram condition is clause two.** The second clause of `WeilIsGram` —
at every `ε > 0`, `⟨F, F⟩_ε` is a nonnegative real number
(`(abelForm ε (α ε) (d ε) (d ε)).im = 0` and `0 ≤ (abelForm ε (α ε) (d ε) (d ε)).re`) —
is the Gram condition: a sesquilinear form value that is real and nonnegative
at every `ε > 0` is a Gram value, and its `ε → 0⁺` limit is then automatically a
nonnegative real. In the strip `|Re αᵢ| < ε / 2` this clause is **automatic**:
it is exactly the PROVED `GppCesaroAbel.abelForm_self_nonneg` (the form is the
integral of `ε e^{−ε|u|} |F(u)|² ≥ 0` there). So the content of `WeilIsGram` is
the approximation clause (the limit), with clause two recording that the
approximants are genuine Gram values, not merely a formal limit.

**Why the family must depend on `ε`.** The quantifier shape of `WeilIsGram`
— `m`, `α`, `d` all functions of `ε` — is forced; the simpler shapes are FALSE
(Flint's falsifications, 2026-11-12):

* *Finite fixed families are FALSE*: a single finite character family,
  independent of `ε`, has an Abel–Cesàro limit that is a finite exponential
  polynomial in the configuration (the diagonal/shadow selection of
  `tendsto_abelForm`), but `Kψ` is not a finite exponential polynomial — its
  archimedean term `archTerm` is a genuine integral transform, not a finite
  sum of exponentials.
* *On-line-only families are FALSE*: families with all exponents on the
  critical line (`Re α = 0`) have bounded diagonal limits, while the pole term
  of `Kψ` grows like `cosh (d / 2)` in the separation `d`; that cosh growth is
  not an on-line Gram limit.
* *`ε`-independent families are FALSE*: the pole characters of `Kψ` sit at
  `Re α = ±1/2`, outside every fixed strip `|Re α| < ε` for small `ε`; a family
  fixed once and for all cannot track them through the strip as `ε → 0⁺`
  (outside the strip the character formula is an analytic continuation, not a
  positive integral — the located boundary of `CesaroAbelState.lean`).

**Status.** `WeilIsGram` is **OPEN**: it is a sufficient Gram form of `HPsi`,
stated here exactly, and NOT attempted in this file. What is proved here is
only the implication `hPsi_of_weilIsGram` (**PROVED**): `WeilIsGram → HPsi` —
the limit of the nonnegative reals of clause two is a nonnegative real.
`HPsi`, and with it the Krein chain to RH, remain OPEN; `KreinDecomp` is not
touched.
-/
import GppVerify.RiemannHypothesis.CesaroAbelState
import GppVerify.RiemannHypothesis.CesaroGNS
import GppVerify.RiemannHypothesis.KreinBridge
import GppVerify.RiemannHypothesis.KreinHPsi

namespace GppCesaroWeilGram

open Filter Topology

/-- **WeilIsGram (OPEN — stated, not proved)**: for every configuration
`(x, c)` on the cosh hyperplane there is an `ε`-dependent finite character
family whose Abel–Cesàro self-form is a nonnegative real at every `ε > 0`
(the Gram condition, clause two) and tends, as `ε → 0⁺`, to the Toeplitz
value `kform Kpsi x c`. See the file header for the entrywise reading and for
why the `ε`-dependence of the family is forced. -/
def WeilIsGram : Prop :=
  ∀ (n : ℕ) (x c : Fin n → ℝ), ∑ i, c i * Real.cosh (x i / 2) = 0 →
    ∃ (m : ℝ → ℕ) (α : ∀ ε : ℝ, Fin (m ε) → ℂ) (d : ∀ ε : ℝ, Fin (m ε) → ℂ),
      (∀ ε : ℝ, 0 < ε → (GppCesaroAbel.abelForm ε (α ε) (d ε) (d ε)).im = 0
        ∧ 0 ≤ (GppCesaroAbel.abelForm ε (α ε) (d ε) (d ε)).re)
      ∧ Tendsto (fun ε : ℝ => GppCesaroAbel.abelForm ε (α ε) (d ε) (d ε)) (𝓝[>] 0)
          (𝓝 ((GppKreinBridge.kform GppKreinHPsi.Kpsi x c : ℝ) : ℂ))

/-- **PROVED**: `WeilIsGram → HPsi`. On the cosh hyperplane, the Toeplitz value
`kform Kpsi x c` is the `ε → 0⁺` limit of the real parts of the Gram values of
clause two, each of which is `≥ 0` for `ε > 0`; a limit of nonnegative reals is
nonnegative. -/
theorem hPsi_of_weilIsGram (hWG : WeilIsGram) : GppKreinHPsi.HPsi := by
  intro n x c hker
  obtain ⟨m, α, d, hpos, hlim⟩ := hWG n x c hker
  have hre : Tendsto (fun ε : ℝ => (GppCesaroAbel.abelForm ε (α ε) (d ε) (d ε)).re)
      (𝓝[>] 0) (𝓝 (GppKreinBridge.kform GppKreinHPsi.Kpsi x c)) :=
    (Complex.continuous_re.tendsto _).comp hlim
  exact ge_of_tendsto hre (eventually_nhdsWithin_of_forall fun ε hε => (hpos ε hε).2)

end GppCesaroWeilGram

#print axioms GppCesaroWeilGram.hPsi_of_weilIsGram
