/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Daniel Toupin / Golden Physics Project. This seat: Heart of the Cosmos / Grok (GPPDiscovery5).
Audit: Turbo. Branch heart/weilgram-attack (based on heart/weilgram 99f3b3a).

# Semilocal WeilIsGram, contraction form (Connes S-local route)

On a window-`L` configuration in `ker ℓ_c`, the `S`-local Weil form splits as

  `kform (KS S) = kform archTerm − 2Ψ(i/2)² (Σ cᵢ sinh(xᵢ/2))² − kform (primeTermS S)`,

using the PROVED rank-one pole block (`kform_poleTerm_of_ker`). So positivity is *exactly* the
statement that the finite-`S` prime (p-adic scattering) block plus a rank-one pole correction is
dominated, as a quadratic form, by the archimedean block. This is the form-level (Loewner) version
of "the compressed S-local cutoff operator is a contraction": with `A = archimedean block`,
`P = S-prime block + pole correction`, it reads `P ≤ A` on `ker ℓ_c`.

* PROVED: `kform_add`, `kform_sub`, `kform_KS_split`, `kform_KS_of_ker`,
  `semilocalPos_iff_contraction`, `semilocalContraction_iff_archDom`,
  `semilocalPos_congr_cover` (S-independence once `S` covers `L`),
  `semilocalPos_anti_window`, `archDom_prime_le_arch` (necessary condition: the `S`-prime block is
  ≤ the archimedean block on `ker ℓ_c`), `hPsi_iff_semilocalContractionAll`,
  `hPsi_iff_semilocalArchDomAll`.
* Named Props (OPEN, RH-strength, each *equivalent* to H_ψ): `SemilocalContractionAll`,
  `SemilocalArchDomAll`.

Honest scope. Every equivalence here is a reformulation, not a reduction: no RH-strength content
is removed. The genuine operator-contraction statement (`‖A^{-1/2} P A^{-1/2}‖ ≤ 1`) would further
need the archimedean block positive definite on `ker ℓ_c` for window `L`; that is NOT established
here (OPEN). Connes–Consani 2021 (archimedean place) proves Weil positivity only for test functions
with log-support of width `< log 2`, where no prime contributes; our `g = ψ ⋆ ψ` has support
`[−2, 2]` and already sees `log 2` (`not_primeSupportVanish`, PROVED), so that theorem does not
apply (literature: CHECKED as to scope; not formalized). H_ψ, ARP, RH: OPEN.
-/
import GppVerify.RiemannHypothesis.WeilGramSemilocal

namespace GppWeilGramContraction

open GppKreinBridge GppKreinHPsi GppHPsiPlan GppWeilGram

/-- **PROVED**: `kform` is additive in the kernel. -/
theorem kform_add (K K' : ℝ → ℝ) {n : ℕ} (x c : Fin n → ℝ) :
    kform (fun d => K d + K' d) x c = kform K x c + kform K' x c := by
  unfold kform
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **PROVED**: `kform` is subtractive in the kernel. -/
theorem kform_sub (K K' : ℝ → ℝ) {n : ℕ} (x c : Fin n → ℝ) :
    kform (fun d => K d - K' d) x c = kform K x c - kform K' x c := by
  unfold kform
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **PROVED**: place split of the `S`-local form. -/
theorem kform_KS_split (S : Finset ℕ) {n : ℕ} (x c : Fin n → ℝ) :
    kform (KS S) x c = kform poleTerm x c - kform (primeTermS S) x c + kform archTerm x c := by
  have h1 := kform_sub poleTerm (primeTermS S) x c
  have h2 := kform_add (fun d => poleTerm d - primeTermS S d) archTerm x c
  have hK : KS S = fun d => (poleTerm d - primeTermS S d) + archTerm d := rfl
  rw [hK, h2, h1]

/-- **PROVED**: on `ker ℓ_c` the pole block is rank one, so
`kform (KS S) = kform archTerm − 2Ψ(i/2)²(Σ cᵢ sinh(xᵢ/2))² − kform (primeTermS S)`. -/
theorem kform_KS_of_ker (S : Finset ℕ) {n : ℕ} (x c : Fin n → ℝ)
    (hc : ∑ i, c i * Real.cosh (x i / 2) = 0) :
    kform (KS S) x c = kform archTerm x c
      - 2 * bigPsiI2 ^ 2 * (∑ i, c i * Real.sinh (x i / 2)) ^ 2 - kform (primeTermS S) x c := by
  rw [kform_KS_split, kform_poleTerm_of_ker x c hc]
  ring

/-- **Named Prop (OPEN in general)**: form-level contraction. On window-`L` configurations in
`ker ℓ_c`, the `S`-prime (p-adic scattering) block is dominated by the pole + archimedean block. -/
def SemilocalContraction (S : Finset ℕ) (L : ℝ) : Prop :=
  ∀ (n : ℕ) (x c : Fin n → ℝ), (∀ i j, |x i - x j| ≤ L) →
    ∑ i, c i * Real.cosh (x i / 2) = 0 →
      kform (primeTermS S) x c ≤ kform (fun d => poleTerm d + archTerm d) x c

/-- **Named Prop (OPEN in general)**: archimedean domination. The `S`-prime block plus the rank-one
pole correction is dominated by the archimedean block alone. -/
def SemilocalArchDom (S : Finset ℕ) (L : ℝ) : Prop :=
  ∀ (n : ℕ) (x c : Fin n → ℝ), (∀ i j, |x i - x j| ≤ L) →
    ∑ i, c i * Real.cosh (x i / 2) = 0 →
      kform (primeTermS S) x c + 2 * bigPsiI2 ^ 2 * (∑ i, c i * Real.sinh (x i / 2)) ^ 2
        ≤ kform archTerm x c

/-- **PROVED**: `SemilocalPos S L ↔ SemilocalContraction S L`. -/
theorem semilocalPos_iff_contraction (S : Finset ℕ) (L : ℝ) :
    SemilocalPos S L ↔ SemilocalContraction S L := by
  constructor
  · intro h n x c hx hc
    have := h n x c hx hc
    rw [kform_KS_split] at this
    rw [kform_add]
    linarith
  · intro h n x c hx hc
    have := h n x c hx hc
    rw [kform_add] at this
    rw [kform_KS_split]
    linarith

/-- **PROVED**: `SemilocalContraction S L ↔ SemilocalArchDom S L`. -/
theorem semilocalContraction_iff_archDom (S : Finset ℕ) (L : ℝ) :
    SemilocalContraction S L ↔ SemilocalArchDom S L := by
  constructor
  · intro h n x c hx hc
    have := h n x c hx hc
    rw [kform_add, kform_poleTerm_of_ker x c hc] at this
    linarith
  · intro h n x c hx hc
    have := h n x c hx hc
    rw [kform_add, kform_poleTerm_of_ker x c hc]
    linarith

/-- **PROVED (necessary condition)**: archimedean domination forces the `S`-prime block to be at
most the archimedean block on `ker ℓ_c`. -/
theorem archDom_prime_le_arch {S : Finset ℕ} {L : ℝ} (h : SemilocalArchDom S L) {n : ℕ}
    (x c : Fin n → ℝ) (hx : ∀ i j, |x i - x j| ≤ L) (hc : ∑ i, c i * Real.cosh (x i / 2) = 0) :
    kform (primeTermS S) x c ≤ kform archTerm x c := by
  have h1 := h n x c hx hc
  have h2 : 0 ≤ 2 * bigPsiI2 ^ 2 * (∑ i, c i * Real.sinh (x i / 2)) ^ 2 := by positivity
  linarith

/-- **PROVED (S-independence)**: once `S` and `S'` both cover `L`, the `S`- and `S'`-local
positivity statements on window `L` coincide (both are `HPsiWindow L`). -/
theorem semilocalPos_congr_cover {S S' : Finset ℕ} {L : ℝ} (hS : Covers S L) (hS' : Covers S' L) :
    SemilocalPos S L ↔ SemilocalPos S' L :=
  (hPsiWindow_iff_semilocalPos hS).symm.trans (hPsiWindow_iff_semilocalPos hS')

/-- **PROVED**: for fixed `S`, positivity on window `L` gives it on every smaller window. -/
theorem semilocalPos_anti_window {S : Finset ℕ} {L L' : ℝ} (hL : L' ≤ L) (h : SemilocalPos S L) :
    SemilocalPos S L' :=
  fun n x c hx hc => h n x c (fun i j => (hx i j).trans hL) hc

/-- **Named Prop (OPEN, RH-strength, equivalent to H_ψ)**: matched-window form contraction. -/
def SemilocalContractionAll : Prop := ∀ L > 0, SemilocalContraction (primesBelowExp L) L

/-- **Named Prop (OPEN, RH-strength, equivalent to H_ψ)**: matched-window archimedean domination. -/
def SemilocalArchDomAll : Prop := ∀ L > 0, SemilocalArchDom (primesBelowExp L) L

/-- **PROVED**: `HPsi ↔ SemilocalContractionAll` (reformulation, not a reduction). -/
theorem hPsi_iff_semilocalContractionAll : HPsi ↔ SemilocalContractionAll := by
  rw [hPsi_iff_semilocalWeilIsGram]
  exact forall₂_congr fun L _ => semilocalPos_iff_contraction _ L

/-- **PROVED**: `HPsi ↔ SemilocalArchDomAll` (reformulation, not a reduction). -/
theorem hPsi_iff_semilocalArchDomAll : HPsi ↔ SemilocalArchDomAll := by
  rw [hPsi_iff_semilocalContractionAll]
  exact forall₂_congr fun L _ => semilocalContraction_iff_archDom _ L

end GppWeilGramContraction

#print axioms GppWeilGramContraction.kform_KS_of_ker
#print axioms GppWeilGramContraction.semilocalPos_iff_contraction
#print axioms GppWeilGramContraction.semilocalContraction_iff_archDom
#print axioms GppWeilGramContraction.archDom_prime_le_arch
#print axioms GppWeilGramContraction.semilocalPos_congr_cover
#print axioms GppWeilGramContraction.hPsi_iff_semilocalContractionAll
#print axioms GppWeilGramContraction.hPsi_iff_semilocalArchDomAll
