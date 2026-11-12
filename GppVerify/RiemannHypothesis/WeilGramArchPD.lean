/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Daniel Toupin / Golden Physics Project. This seat: Heart of the Cosmos / Grok (GPPDiscovery5).
Audit: Turbo. Branch heart/archpd (based on heart/weilgram-attack f9f7676).

# Archimedean block positive definite on `ker ℓ_c`, and the operator-norm contraction

Turbo 6837243506 asked for one statement-level sub-piece of `WeilGramContraction`: state "the
archimedean block is positive definite on `ker ℓ_c`" as a named Prop and prove its exact relation
to the operator-norm contraction `‖A^{-1/2} P A^{-1/2}‖ ≤ 1`, without proving the Prop.

Notation, window `L`, configuration `x`, coefficient vector `c ∈ ker ℓ_c`:
* `A(c) = kform archTerm x c` (archimedean block),
* `P(c) = kform (primeTermS S) x c + 2Ψ(i/2)²(Σ cᵢ sinh(xᵢ/2))²` (S-prime block + pole correction).
`SemilocalArchDom S L` (from `WeilGramContraction`) is the one-sided bound `P ≤ A`.

For `A` positive definite, `T = A⁻¹P` is self-adjoint for the `A`-inner product, with
`⟪T c, c⟫_A = P(c)` and `‖c‖_A² = A(c)`, and `‖T‖_A = ‖A^{-1/2} P A^{-1/2}‖`. So the
operator-norm contraction is, at form level, the **two-sided** bound `|P| ≤ A`
(`SemilocalArchNormBound`). The abstract Hilbert-space step
`‖T‖ ≤ 1 ↔ ∀ v, |⟪T v, v⟫| ≤ ‖v‖²` for symmetric `T` is PROVED here (`opNorm_le_one_iff_inner`);
the change of inner product `⟪·,·⟫ ↦ ⟪·,·⟫_A` on the finite-dimensional `ker ℓ_c` is standard
linear algebra (CHECKED, not formalized here).

Exact relations, all PROVED:
* `archNormBound_iff`: `NormBound ↔ ArchDom ∧ LowerDom` (`LowerDom`: `−A ≤ P`).
  So the operator-norm contraction is the RH-strength `ArchDom` **plus** an extra lower bound;
  it is strictly a stronger statement shape, not a weaker one.
* `archNormBound_archPosSemi`: `NormBound` forces `A ≥ 0` on `ker ℓ_c` (semi-definite only).
* `archDom_iff_ratio` (given `ArchPosDef L`): `ArchDom ↔ ∀ c ≠ 0, P(c)/A(c) ≤ 1`.
* `archNormBound_iff_absRatio` (given `ArchPosDef L`): `NormBound ↔ ∀ c ≠ 0, |P(c)/A(c)| ≤ 1`.
* `hPsi_iff_archDomAll_of_posDef`: under `ArchPosDefAll`, `HPsi ↔ ∀ L > 0, RatioBound`.

Named Props (OPEN): `ArchPosDef L`, `ArchPosDefAll`, `SemilocalArchNormBound`,
`SemilocalArchLowerDom`. Nothing here proves `ArchPosDef`; `SemilocalArchDomAll` stays equivalent
to H_ψ. H_ψ, ARP, RH: OPEN.
-/
import GppVerify.RiemannHypothesis.WeilGramContraction
import Mathlib.Analysis.InnerProductSpace.Rayleigh

namespace GppWeilGramArchPD

open GppKreinBridge GppKreinHPsi GppHPsiPlan GppWeilGram GppWeilGramContraction

/-- `A(c)`: the archimedean block. -/
noncomputable def archQ {n : ℕ} (x c : Fin n → ℝ) : ℝ := kform archTerm x c

/-- `P(c)`: the `S`-prime block plus the rank-one pole correction. -/
noncomputable def primePoleQ (S : Finset ℕ) {n : ℕ} (x c : Fin n → ℝ) : ℝ :=
  kform (primeTermS S) x c + 2 * bigPsiI2 ^ 2 * (∑ i, c i * Real.sinh (x i / 2)) ^ 2

/-- **Named Prop (OPEN)**: the archimedean block is positive definite on `ker ℓ_c`, window `L`. -/
def ArchPosDef (L : ℝ) : Prop :=
  ∀ (n : ℕ) (x c : Fin n → ℝ), (∀ i j, |x i - x j| ≤ L) →
    ∑ i, c i * Real.cosh (x i / 2) = 0 → c ≠ 0 → 0 < archQ x c

/-- **Named Prop (OPEN)**: `ArchPosDef` on every window. -/
def ArchPosDefAll : Prop := ∀ L > 0, ArchPosDef L

/-- **Named Prop (OPEN)**: form-level operator-norm contraction `|P| ≤ A`
(`‖A^{-1/2} P A^{-1/2}‖ ≤ 1`). -/
def SemilocalArchNormBound (S : Finset ℕ) (L : ℝ) : Prop :=
  ∀ (n : ℕ) (x c : Fin n → ℝ), (∀ i j, |x i - x j| ≤ L) →
    ∑ i, c i * Real.cosh (x i / 2) = 0 → |primePoleQ S x c| ≤ archQ x c

/-- **Named Prop (OPEN)**: the lower half `−A ≤ P`. -/
def SemilocalArchLowerDom (S : Finset ℕ) (L : ℝ) : Prop :=
  ∀ (n : ℕ) (x c : Fin n → ℝ), (∀ i j, |x i - x j| ≤ L) →
    ∑ i, c i * Real.cosh (x i / 2) = 0 → -archQ x c ≤ primePoleQ S x c

/-- **Named Prop**: Rayleigh-ratio form `P(c)/A(c) ≤ 1` for `c ≠ 0`. -/
def SemilocalArchRatioBound (S : Finset ℕ) (L : ℝ) : Prop :=
  ∀ (n : ℕ) (x c : Fin n → ℝ), (∀ i j, |x i - x j| ≤ L) →
    ∑ i, c i * Real.cosh (x i / 2) = 0 → c ≠ 0 → primePoleQ S x c / archQ x c ≤ 1

/-- **PROVED**: `SemilocalArchDom` is `P ≤ A` in this notation. -/
theorem archDom_iff_le (S : Finset ℕ) (L : ℝ) :
    SemilocalArchDom S L ↔ ∀ (n : ℕ) (x c : Fin n → ℝ), (∀ i j, |x i - x j| ≤ L) →
      ∑ i, c i * Real.cosh (x i / 2) = 0 → primePoleQ S x c ≤ archQ x c :=
  Iff.rfl

/-- **PROVED**: operator-norm contraction = archimedean domination + lower domination. -/
theorem archNormBound_iff (S : Finset ℕ) (L : ℝ) :
    SemilocalArchNormBound S L ↔ SemilocalArchDom S L ∧ SemilocalArchLowerDom S L := by
  constructor
  · intro h
    refine ⟨fun n x c hx hc => ?_, fun n x c hx hc => ?_⟩
    · exact (le_abs_self _).trans (h n x c hx hc)
    · exact (abs_le.mp (h n x c hx hc)).1
  · rintro ⟨h1, h2⟩ n x c hx hc
    exact abs_le.mpr ⟨h2 n x c hx hc, h1 n x c hx hc⟩

/-- **PROVED**: the operator-norm contraction implies archimedean domination. -/
theorem archNormBound_archDom {S : Finset ℕ} {L : ℝ} (h : SemilocalArchNormBound S L) :
    SemilocalArchDom S L :=
  ((archNormBound_iff S L).mp h).1

/-- **PROVED**: the operator-norm contraction forces `A ≥ 0` on `ker ℓ_c` (semi-definite). -/
theorem archNormBound_archPosSemi {S : Finset ℕ} {L : ℝ} (h : SemilocalArchNormBound S L)
    {n : ℕ} (x c : Fin n → ℝ) (hx : ∀ i j, |x i - x j| ≤ L)
    (hc : ∑ i, c i * Real.cosh (x i / 2) = 0) : 0 ≤ archQ x c :=
  (abs_nonneg _).trans (h n x c hx hc)

/-- **PROVED**: given `ArchPosDef L`, archimedean domination is the Rayleigh-ratio bound. -/
theorem archDom_iff_ratio {L : ℝ} (hA : ArchPosDef L) (S : Finset ℕ) :
    SemilocalArchDom S L ↔ SemilocalArchRatioBound S L := by
  constructor
  · intro h n x c hx hc hc0
    exact (div_le_one (hA n x c hx hc hc0)).mpr (h n x c hx hc)
  · intro h n x c hx hc
    by_cases hc0 : c = 0
    · subst hc0
      have h0 : primePoleQ S x (0 : Fin n → ℝ) = 0 ∧ archQ x (0 : Fin n → ℝ) = 0 := by
        simp [primePoleQ, archQ, kform]
      show primePoleQ S x 0 ≤ archQ x 0
      rw [h0.1, h0.2]
    · exact (div_le_one (hA n x c hx hc hc0)).mp (h n x c hx hc hc0)

/-- **PROVED**: given `ArchPosDef L`, the operator-norm contraction is `|P/A| ≤ 1`. -/
theorem archNormBound_iff_absRatio {L : ℝ} (hA : ArchPosDef L) (S : Finset ℕ) :
    SemilocalArchNormBound S L ↔ ∀ (n : ℕ) (x c : Fin n → ℝ), (∀ i j, |x i - x j| ≤ L) →
      ∑ i, c i * Real.cosh (x i / 2) = 0 → c ≠ 0 → |primePoleQ S x c / archQ x c| ≤ 1 := by
  constructor
  · intro h n x c hx hc hc0
    have hpos := hA n x c hx hc hc0
    rw [abs_div, abs_of_pos hpos, div_le_one hpos]
    exact h n x c hx hc
  · intro h n x c hx hc
    by_cases hc0 : c = 0
    · subst hc0
      have h0 : primePoleQ S x (0 : Fin n → ℝ) = 0 ∧ archQ x (0 : Fin n → ℝ) = 0 := by
        simp [primePoleQ, archQ, kform]
      show |primePoleQ S x 0| ≤ archQ x 0
      rw [h0.1, h0.2, abs_zero]
    · have hpos := hA n x c hx hc hc0
      have := h n x c hx hc hc0
      rwa [abs_div, abs_of_pos hpos, div_le_one hpos] at this

/-- **PROVED**: under `ArchPosDefAll`, `HPsi` is the matched-window Rayleigh-ratio bound. -/
theorem hPsi_iff_archDomAll_of_posDef (hA : ArchPosDefAll) :
    HPsi ↔ ∀ L > 0, SemilocalArchRatioBound (primesBelowExp L) L := by
  rw [hPsi_iff_semilocalArchDomAll]
  exact forall₂_congr fun L hL => archDom_iff_ratio (hA L hL) _

/-- **PROVED (abstract operator step)**: a symmetric bounded operator on a real inner product
space has norm `≤ 1` iff its quadratic form is bounded by `‖v‖²` in absolute value. -/
theorem opNorm_le_one_iff_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (hT : (T : E →ₗ[ℝ] E).IsSymmetric) :
    ‖T‖ ≤ 1 ↔ ∀ v, |inner ℝ (T v) v| ≤ ‖v‖ ^ 2 := by
  constructor
  · intro h v
    calc |inner ℝ (T v) v| ≤ ‖T v‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖T‖ * ‖v‖ * ‖v‖ := by gcongr; exact T.le_opNorm v
      _ ≤ 1 * ‖v‖ * ‖v‖ := by gcongr
      _ = ‖v‖ ^ 2 := by ring
  · intro h
    rw [T.norm_eq_iSup_rayleighQuotient hT]
    refine ciSup_le fun v => ?_
    by_cases hv : v = 0
    · subst hv; simp
    · have hpos : 0 < ‖v‖ ^ 2 := by positivity
      rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
        abs_div, abs_of_pos hpos, div_le_one hpos]
      simpa using h v

end GppWeilGramArchPD

#print axioms GppWeilGramArchPD.archNormBound_iff
#print axioms GppWeilGramArchPD.archNormBound_archPosSemi
#print axioms GppWeilGramArchPD.archDom_iff_ratio
#print axioms GppWeilGramArchPD.archNormBound_iff_absRatio
#print axioms GppWeilGramArchPD.hPsi_iff_archDomAll_of_posDef
#print axioms GppWeilGramArchPD.opNorm_le_one_iff_inner
