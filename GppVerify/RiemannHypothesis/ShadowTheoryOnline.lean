import GppVerify.RiemannHypothesis.ShadowTheory

/-!
# A3 is equivalent to the principal-series property of the weights (shadow theories, `Ψ_conj`)

`ShadowTheory.lean` (#607) proves the closing theorem: reflection positivity (A3) puts every weight on
the principal line. With `Ψ_conj` the **converse** also holds, and it is elementary:

  on the line `1 − ρ = ρ̄`, so `Ψf(1−ρ) = Ψf(ρ̄) = conj Ψf(ρ)` (`Ψ_conj`), and the reflected term
  `m(ρ) Ψf(ρ) Ψf(1−ρ) = m(ρ) ‖Ψf(ρ)‖²` is a nonnegative real.

* `reflectionPositive_of_online`: all weights on the line ⇒ A3.
* **`reflectionPositive_iff_online`**: for a shadow theory, A3 ⇔ every weight has `Re = 1/2`.
* **`arp_iff_rh`**: for the ζ datum, `ArithmeticReflectionPositivity ⇔ ∀ ρ ∈ nontrivialZeros, Re ρ = 1/2`.
  This is Weil's criterion, now with both directions in the tree through the GW-EF explicit formula
  (the forward direction was `rh_of_arp`).

**What this says about the programme, plainly.** The closing theorem of the shadow-theory package is
not a one-way route: A3 *is* the principal-series property of the weights. So an identification
`shadowZeta ≅ C` with a reflection-positive `C` can deliver RH only if `C`'s weight set is shown to lie
on the line *independently of the zeros* — and an isomorphism preserves `Ψ` and `corr`, which (by the
spectral identity and interpolation) pins `C`'s weights to the ζ zeros.
 ARP and RH remain OPEN.

No `sorry`, no axiom.
-/

open Complex
open GppMeyerSpectralWeil GppWeilCriterion GppArithmeticReflection GppGwefAssembly GppKernelTheory

noncomputable section

namespace GppShadowTheory

namespace ShadowTheory

variable (T : ShadowTheory)

/-- On the principal line the reflected term is `m ‖Ψf‖²`. -/
theorem reflected_term_online (f : T.Test) (ρ : T.W) (hρ : (ρ : ℂ).re = 1 / 2) :
    (T.m ρ : ℂ) * (T.Ψ f ρ * T.Ψ f (1 - ρ)) = ((T.m ρ * ‖T.Ψ f ρ‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : (1 : ℂ) - ρ = starRingEnd ℂ ρ := by
    apply Complex.ext <;> simp [hρ]; linarith
  rw [h1, T.Ψ_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- **All weights on the line ⇒ A3.** -/
theorem reflectionPositive_of_online (hon : ∀ ρ ∈ T.W, ρ.re = 1 / 2) : T.ReflectionPositive := by
  intro f
  rw [KernelTheory.gram_spectral]
  have hterm : ∀ ρ : T.W, (T.m ρ : ℂ) * (T.Ψ f ρ * T.Ψ f (1 - ρ))
      = ((T.m ρ * ‖T.Ψ f ρ‖ ^ 2 : ℝ) : ℂ) := fun ρ => T.reflected_term_online f ρ (hon ρ ρ.2)
  simp_rw [hterm]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  exact tsum_nonneg fun ρ => by positivity

/-- **A3 ⇔ the weights are principal.** The closing theorem is an equivalence. -/
theorem reflectionPositive_iff_online : T.ReflectionPositive ↔ ∀ ρ ∈ T.W, ρ.re = 1 / 2 :=
  ⟨T.principalSeries_of_shadowTheory, T.reflectionPositive_of_online⟩

end ShadowTheory

/-- **Weil's criterion, both directions, for the ζ datum:** ARP ⇔ the nontrivial zeros are on the
line. (ARP and RH are both OPEN; this is the equivalence between them in the tree.) -/
theorem arp_iff_rh :
    ArithmeticReflectionPositivity ↔ ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2 :=
  shadowZeta_reflectionPositive_iff_arp.symm.trans shadowZeta.reflectionPositive_iff_online

/-- RH ⇒ ARP, the converse of `rh_of_arp`. -/
theorem arp_of_rh (hrh : ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2) : ArithmeticReflectionPositivity :=
  arp_iff_rh.mpr hrh

end GppShadowTheory

#print axioms GppShadowTheory.ShadowTheory.reflectionPositive_iff_online
#print axioms GppShadowTheory.arp_iff_rh
