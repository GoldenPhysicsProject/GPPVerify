import GppVerify.RiemannHypothesis.LinearZetaTheory

/-!
# AKG, stated in Lean as an exact named definition — and what the statement is

Build order, bridge `9f0e414` / `7e03889` (Turbo, with Daniel's direction): after the linear datum, the
GNS, and the free principal-series instance, **AKG** as an exact named definition: *a Hilbert space and
vectors built from the primes and the archimedean place only, realising the Weil form* (package §3.1; RH goal
hunt note, Heart Round 11; `AKG ⇔ SemilocalArchDomAll ∀L ⇔ H_ψ`).

**The definition.** `GppAKG.AKG` asserts: there is a real Hilbert space `H` and a **linear** map
`ι : ZetaTest → H` such that, for every smooth compactly supported test `f`,

  `weilForm (autocorr f) = ‖ι f‖²`,

where `weilForm = poleTerm + archimedeanTerm − primeSide` is *assembled from the pole, the gamma factor and
the primes only* (in-tree `GppArithmeticReflection.weilForm`) — **no zero appears in the statement**. The
right-hand side is the squared norm of the vector `ι f`, so the left-hand side is the Gram quadratic form of
a Hilbert space.

**What the statement is (theorem `akg_iff_arp`).** As a proposition, `AKG` is *equivalent to
`ArithmeticReflectionPositivity`*: `→` since a norm square is `≥ 0`; `←` by the GNS construction
(`FormGNS.psd_iff_exists_hilbert`) applied to the real bilinear form `Re corr(Θ g, f)` of the linear ζ datum,
whose diagonal is `weilForm (autocorr f)` by the explicit formula (`gram_zeta_eq`). So **AKG and ARP are the
same open statement; neither is proved.**

**What the equivalence cannot see.** The phrase "built from the primes and the archimedean place only" has two
readings. As a constraint on the *statement* (no zeros occur in it) it is satisfied — that is `AKG` above. As
a constraint on the *witness* (the space `H` and the map `ι` are *exhibited* by a construction out of the
prime and archimedean data, rather than obtained as the abstract GNS space of a form already known to be
positive) it is content that no proposition can carry: any positive-semidefinite form is a Gram form of
*some* Hilbert space (`FormGNS`), so the existential statement is the positivity, whoever builds the
witness. The `d = 1` content of the celestial identification (package §4) is exactly this gap
(`modelIdentification_iff_arp`): pinning the witness to a model that is reflection-positive *by
construction* is what is owed, and this file does not supply it.

Not here: any construction of `H` or `ι`; `H_ψ`, `SemilocalArchDomAll`, `WeilIsGram` (their in-tree
equivalence with AKG is asserted in the notes, not proved here); ARP, RH — all OPEN. No `sorry`, no axiom.
-/

open Complex MeasureTheory
open scoped InnerProductSpace
open GppMeyerSpectralWeil GppWeilCriterion GppArithmeticReflection GppKernelTheory GppFormGNS
  GppShadowTheory GppXiZeroCounting GppGwefAssembly

noncomputable section

namespace GppAKG

/-- **The diagonal of the reflected Gram form is the Weil form** (explicit formula + factorisation,
through the in-tree GW-EF-1/GW-EF-2): `corr(Θ f, f) = weilForm (autocorr f)` as a complex number. -/
theorem gram_zeta_eq (f : ZetaTest) :
    shadowZeta.gram f = ((weilForm (autocorr f.1) : ℝ) : ℂ) := by
  refine (KernelTheory.gram_spectral shadowZeta.toKernelTheory f).trans ?_
  obtain ⟨-, hsum⟩ := GppExplicitFormulaAssembly.explicit_formula_zeroSum f.2
  have hfac : ∀ ρ : nontrivialZeros,
      (zeroMult ρ : ℂ) * spectralTransform (autocorr f.1) ρ =
        (zeroMult ρ : ℂ) *
          (spectralTransform f.1 ρ * spectralTransform f.1 (1 - ρ)) := fun ρ => by
    rw [gwef2_factorisation f.2]
  simp_rw [hfac] at hsum
  exact hsum

/-- **AKG**, as a named proposition: a real Hilbert space and a linear map out of the test functions whose
Gram quadratic form *is* the Weil form `weilForm (autocorr ·)` (pole + gamma factor + primes; no zeros). -/
def AKG : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
    (ι : ZetaTest →ₗ[ℝ] H), ∀ f : ZetaTest, weilForm (autocorr f.1) = ‖ι f‖ ^ 2

/-- **`AKG ⇔ ARP`.** The statement carries exactly the positivity of the Weil form. Both are OPEN. -/
theorem akg_iff_arp : AKG ↔ ArithmeticReflectionPositivity := by
  constructor
  · rintro ⟨H, _, _, _, ι, h⟩ f hf1 hf2
    exact le_of_le_of_eq (sq_nonneg _) (h ⟨f, ⟨hf1, hf2⟩⟩).symm
  · intro harp
    have hrp : shadowZeta.ReflectionPositive := shadowZeta_reflectionPositive_iff_arp.mpr harp
    obtain ⟨H, _, _, _, ι, hB, -⟩ := linearZeta.reflectionPositive_iff_stateSpace.mp hrp
    refine ⟨H, inferInstance, inferInstance, inferInstance, ι, fun f => ?_⟩
    have h1 : (shadowZeta.corr (shadowZeta.Θ f) f).re = ⟪ι f, ι f⟫_ℝ := hB f f
    have h3 : (shadowZeta.gram f).re = weilForm (autocorr f.1) := by
      rw [gram_zeta_eq f, Complex.ofReal_re]
    calc weilForm (autocorr f.1) = (shadowZeta.corr (shadowZeta.Θ f) f).re := h3.symm
      _ = ⟪ι f, ι f⟫_ℝ := h1
      _ = ‖ι f‖ ^ 2 := real_inner_self_eq_norm_sq _

/-- **AKG ⇔ RH** (through `arp_iff_rh`). RH is OPEN. -/
theorem akg_iff_rh : AKG ↔ ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2 :=
  akg_iff_arp.trans arp_iff_rh

end GppAKG

#print axioms GppAKG.gram_zeta_eq
#print axioms GppAKG.akg_iff_arp
#print axioms GppAKG.akg_iff_rh
