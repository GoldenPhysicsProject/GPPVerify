import GppVerify.RiemannHypothesis.KernelTheory

/-!
# Shadow theories (boundary dimension one): the axiom package, as Lean

The Lean shape of `MuseResearch/shadow-theory-axiom-package-2026-11-15.md` (GPP-bridge; Turbo's build
order, bridge `9f0e414`; Flint-audited with three edits). Daniel's direction: do for the `d = 1` shadow
theory what Segal / VOA / the bootstrap did for CFT — distil the axioms from the built object.

**What is formalised here, and what is not.**

* `ShadowTheory` is `GppKernelTheory.KernelTheory` plus one field, `Ψ_conj` (reality of the character
  transform). `Ψ_conj` is a **package addition** over the in-tree datum.
* `shadowZeta` is `zetaTheory` with `Ψ_conj` **discharged** (`spectralTransform_conj`): the ζ datum's
  character transform is real-symmetric because its test functions are real.
* `gram_im_eq_zero`: what `Ψ_conj` buys — the reflected Gram form `corr (Θ f) f` is *real*, so "the
  pairing is an inner product" (A3) is a statement about a real quadratic form, not a complex one.
* `principalSeries_of_shadowTheory`: the closing theorem of the package (every weight on `Re = 1/2`,
  given reflection positivity), by the in-tree `KernelTheory.principalSeries_of_reflectionPositive`.
* `rh_of_shadowModel`: the read-out, from ARP. ARP is **OPEN**; this does not prove RH.
* `ShadowIso`, `reflectionPositive_transport`, `rh_of_identification`: the model-level identification
  of package §4, in its exact Lean shape — an isomorphism of shadow theories transports reflection
  positivity. **`modelIdentification_iff_arp`** records that, with the target theory left arbitrary,
  the identification is *equivalent to ARP*: the content of Daniel's "`s` is `Δ`" is not in the
  isomorphism's shape but in pinning the target to the celestial model, whose `ShadowTheory` instance
  with reflection positivity by construction is **OWED** (not in-tree). Label-level identification
  (`s_eq_delta_label`) is proved elsewhere and is not touched here.

**Not formalised (OWED / not attempted):** the GNS completion of A3 (the state space as a Hilbert
space — `PositiveDefiniteGNS.lean` is the in-tree precedent), the unitary dilation action `U` and the
vacuum `Ω` of A4/A5, local factorisation A6, and the celestial instance. The Lean structure carries
the *datum*, not the Hilbert-space dressing. ARP, `WeilIsGram`, `H_ψ`, AKG, and RH remain **OPEN**.
No `sorry`, no axiom.

Task and spec: Turbo. Daniel's principle (standing, 2026-11-15): neither half is negative; sign lives
in the reading.
-/

open Complex MeasureTheory
open GppMeyerSpectralWeil GppWeilCriterion GppArithmeticReflection GppGwefAssembly GppKernelTheory

noncomputable section

namespace GppShadowTheory

/-! ### Reality of the ζ character transform -/

/-- **`Ψ_conj` for the ζ datum.** The spectral transform of a *real* test function satisfies
`ĝ(s̄) = conj ĝ(s)`. -/
theorem spectralTransform_conj (g : ℝ → ℝ) (s : ℂ) :
    spectralTransform g (starRingEnd ℂ s) = starRingEnd ℂ (spectralTransform g s) := by
  unfold spectralTransform
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_sub, map_div₀,
    map_one, map_ofNat, Complex.conj_ofReal]

/-! ### The datum -/

/-- **A shadow theory at `d = 1`**: a kernel theory whose character transform is real-symmetric.
(`Ψ_conj` is a package addition over `GppKernelTheory.KernelTheory`.) -/
structure ShadowTheory extends KernelTheory where
  /-- Conjugation symmetry of the character transform (reality of the datum). -/
  Ψ_conj : ∀ f s, Ψ f (starRingEnd ℂ s) = starRingEnd ℂ (Ψ f s)

namespace ShadowTheory

variable (T : ShadowTheory)

/-- The weight set is invariant under conjugation, as an equivalence of the subtype. -/
def conjEquiv : T.W ≃ T.W where
  toFun ρ := ⟨starRingEnd ℂ ρ, (T.conj_closed ρ ρ.2).1⟩
  invFun ρ := ⟨starRingEnd ℂ ρ, (T.conj_closed ρ ρ.2).1⟩
  left_inv _ := Subtype.ext (Complex.conj_conj _)
  right_inv _ := Subtype.ext (Complex.conj_conj _)

/-- **What `Ψ_conj` buys: the reflected Gram form is real.** `Im corr(Θf, f) = 0`. So A3's inner
product is a real quadratic form, and `ReflectionPositive` is positivity of a real number. -/
theorem gram_im_eq_zero (f : T.Test) : (T.gram f).im = 0 := by
  rw [KernelTheory.gram_spectral]
  set t : T.W → ℂ := fun ρ => (T.m ρ : ℂ) * (T.Ψ f ρ * T.Ψ f (1 - ρ)) with ht
  have hconj : ∀ ρ : T.W, starRingEnd ℂ (t ρ) = t (T.conjEquiv ρ) := by
    intro ρ
    have hm : T.m (starRingEnd ℂ ρ) = T.m ρ := (T.conj_closed ρ ρ.2).2
    have h1 : (1 : ℂ) - starRingEnd ℂ (ρ : ℂ) = starRingEnd ℂ (1 - ρ) := by
      rw [map_sub, map_one]
    show starRingEnd ℂ ((T.m ρ : ℂ) * (T.Ψ f ρ * T.Ψ f (1 - ρ)))
      = (T.m (starRingEnd ℂ ρ) : ℂ) * (T.Ψ f (starRingEnd ℂ ρ) * T.Ψ f (1 - starRingEnd ℂ ρ))
    rw [hm, h1, T.Ψ_conj f ρ, T.Ψ_conj f (1 - ρ), map_mul, map_mul, map_natCast]
  have h1 : starRingEnd ℂ (∑' ρ : T.W, t ρ) = ∑' ρ : T.W, t ρ := by
    rw [Complex.conj_tsum]
    simp_rw [hconj]
    exact Equiv.tsum_eq T.conjEquiv t
  exact Complex.conj_eq_iff_im.mp h1

/-! ### The closing theorem and the read-out -/

/-- **Closing theorem of the package.** In any shadow theory, reflection positivity (A3) puts every
weight on the principal line. -/
theorem principalSeries_of_shadowTheory (hA3 : T.ReflectionPositive) : ∀ ρ ∈ T.W, ρ.re = 1 / 2 :=
  T.toKernelTheory.principalSeries_of_reflectionPositive hA3

end ShadowTheory

/-! ### The arithmetic model -/

/-- **The arithmetic model** `zetaTheory`, with `Ψ_conj` discharged. -/
def shadowZeta : ShadowTheory :=
  { zetaTheory with Ψ_conj := fun f s => spectralTransform_conj f.1 s }

theorem shadowZeta_W : shadowZeta.W = nontrivialZeros := rfl

/-- The open field A3 of the arithmetic model is exactly the in-tree ζ obligation (`= ARP`). -/
theorem shadowZeta_reflectionPositive_iff_arp :
    shadowZeta.ReflectionPositive ↔ ArithmeticReflectionPositivity :=
  zeta_obligation_iff_arp

/-- **Read-out.** A shadow theory with the ζ spectral function has all its weights on the line.
ARP is OPEN; this does not prove RH. -/
theorem rh_of_shadowModel (harp : ArithmeticReflectionPositivity) :
    ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2 :=
  shadowZeta.principalSeries_of_shadowTheory (reflectionPositive_of_arp harp)

/-! ### The model-level identification (package §4), in its exact Lean shape -/

/-- **An isomorphism of shadow theories**: an equivalence of test spaces intertwining the fold `Θ`,
matching the character transforms (`Ψ_arith = Ψ_cel`), and preserving the pairing. (The dilation
action `U` and vacuum `Ω` of A4/A5 are not part of the Lean datum.) -/
structure ShadowIso (T C : ShadowTheory) where
  e : T.Test ≃ C.Test
  e_Θ : ∀ f, e (T.Θ f) = C.Θ (e f)
  e_Ψ : ∀ f s, C.Ψ (e f) s = T.Ψ f s
  e_corr : ∀ g f, C.corr (e g) (e f) = T.corr g f

/-- The identity isomorphism. -/
def ShadowIso.refl (T : ShadowTheory) : ShadowIso T T where
  e := Equiv.refl _
  e_Θ _ := rfl
  e_Ψ _ _ := rfl
  e_corr _ _ := rfl

/-- **An isomorphism of shadow theories transports reflection positivity (A3).** -/
theorem reflectionPositive_transport {T C : ShadowTheory} (φ : ShadowIso T C)
    (hC : C.ReflectionPositive) : T.ReflectionPositive := by
  intro f
  have h := hC (φ.e f)
  have hg : C.gram (φ.e f) = T.gram f := by
    unfold KernelTheory.gram
    rw [← φ.e_Θ, φ.e_corr]
  rw [hg] at h
  exact h

/-- **The identification theorem, conditional shape.** If the arithmetic model is isomorphic to a
shadow theory `C` that is reflection-positive (for the celestial model, by construction), then
every nontrivial zero is on the line. The hypothesis pair `(hC, φ)` is the open content: for the
celestial `C`, `hC` is by construction and `φ` is equivalent to ARP. -/
theorem rh_of_identification (C : ShadowTheory) (hC : C.ReflectionPositive)
    (φ : ShadowIso shadowZeta C) : ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2 :=
  shadowZeta.principalSeries_of_shadowTheory (reflectionPositive_transport φ hC)

/-- ARP follows from a reflection-positive model isomorphic to the arithmetic one. -/
theorem arp_of_identification (C : ShadowTheory) (hC : C.ReflectionPositive)
    (φ : ShadowIso shadowZeta C) : ArithmeticReflectionPositivity :=
  shadowZeta_reflectionPositive_iff_arp.mp (reflectionPositive_transport φ hC)

/-- The identification with *some* reflection-positive shadow theory. -/
def ModelIdentification : Prop :=
  ∃ C : ShadowTheory, C.ReflectionPositive ∧ Nonempty (ShadowIso shadowZeta C)

/-- **The identification is the open field, restated — and nothing weaker.** With the target theory
arbitrary, `ModelIdentification` is *equivalent to ARP*. (The converse direction takes `C` to be the
arithmetic model itself, so this equivalence is not evidence for ARP: it says the *shape* of the
identification carries no content beyond A3 until the target is pinned to the celestial model, whose
`ShadowTheory` instance is OWED.) -/
theorem modelIdentification_iff_arp : ModelIdentification ↔ ArithmeticReflectionPositivity :=
  ⟨fun ⟨C, hC, ⟨φ⟩⟩ => arp_of_identification C hC φ,
   fun harp => ⟨shadowZeta, reflectionPositive_of_arp harp, ⟨ShadowIso.refl shadowZeta⟩⟩⟩

end GppShadowTheory

#print axioms GppShadowTheory.spectralTransform_conj
#print axioms GppShadowTheory.ShadowTheory.gram_im_eq_zero
#print axioms GppShadowTheory.ShadowTheory.principalSeries_of_shadowTheory
#print axioms GppShadowTheory.rh_of_shadowModel
#print axioms GppShadowTheory.reflectionPositive_transport
#print axioms GppShadowTheory.modelIdentification_iff_arp
