import GppVerify.RiemannHypothesis.MeyerSpectralWeil
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Mellin interpolation: the spectral transform hits any finite set of prescribed values

Input to the Step 4 bridge (Weil's localization argument) of the full-construction brief.
Blueprint: Gemini (via Daniel Toupin), revision 2 audited PASS by Turbo
(bridge `MuseResearch/turbo-note-2026-11-07-mellin-interpolation-audit.md`).

For a finite set `S ⊆ ℂ`, the vectors `(ĝ(s))_{s ∈ S}`, `ĝ(s) = ∫ g(u) e^{(s − 1/2) u} du`,
over the repo's test class (`IsTestFunction`: real, `C^∞`, compact support) span all of
`ℂ^S` over `ℂ` (`span_spectralVectors_eq_top`). Since the test class is real, a single `g`
cannot hit arbitrary complex values (`ĝ(s̄) = conj ĝ(s)`); the span statement is the
honest form for real test functions.

The three links of the audited blueprint:
1. (`linearIndependent_exp`) `u ↦ e^{a u}`, `a ∈ ℂ` distinct, are linearly independent over
   `ℂ` — Dedekind/Artin independence of characters (`linearIndependent_monoidHom`) for the
   homomorphisms `Multiplicative ℝ →* ℂ`.
2. (pairing) If `Σ c_s ĝ(s) = 0` for every test `g`, the kernel `K(u) = Σ c_s e^{(s−1/2)u}`
   integrates to zero against every smooth bump, hence vanishes
   (`ae_eq_zero_of_integral_contDiff_smul_eq_zero`, continuity), hence all `c_s = 0`.
3. (finite-dimensional linear algebra) A proper subspace of `ℂ^S` is killed by a nonzero
   functional (`Submodule.exists_le_ker_of_lt_top`), contradicting 2.

No claim about RH.

Daniel Toupin / Golden Physics Project, with AI assistance from Gemini (blueprint), Turbo
(audit) and Claude Code (Lean).
-/

namespace GppMellinInterpolation

open MeasureTheory Complex GppMeyerSpectralWeil
open scoped ContDiff

/-- The exponential character `u ↦ e^{a u}` as a monoid hom `Multiplicative ℝ →* ℂ`. -/
noncomputable def expChar (a : ℂ) : Multiplicative ℝ →* ℂ where
  toFun u := Complex.exp (a * ((Multiplicative.toAdd u : ℝ) : ℂ))
  map_one' := by simp
  map_mul' x y := by simp [toAdd_mul, mul_add, Complex.exp_add]

theorem hasDerivAt_exp_mul (a : ℂ) :
    HasDerivAt (fun t : ℝ => Complex.exp (a * (t : ℂ))) a 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul a).cexp
  simpa using h

theorem expChar_injective : Function.Injective expChar := by
  intro a b h
  have hf : (fun t : ℝ => Complex.exp (a * (t : ℂ))) = fun t : ℝ => Complex.exp (b * (t : ℂ)) := by
    funext t
    have := DFunLike.congr_fun h (Multiplicative.ofAdd t)
    simpa [expChar] using this
  have ha := hasDerivAt_exp_mul a
  rw [hf] at ha
  exact ha.unique (hasDerivAt_exp_mul b)

/-- **Link 1.** Distinct exponentials are linearly independent over `ℂ`. -/
theorem linearIndependent_exp :
    LinearIndependent ℂ (fun a : ℂ => fun u : ℝ => Complex.exp (a * (u : ℂ))) := by
  have h1 := (linearIndependent_monoidHom (Multiplicative ℝ) ℂ).comp expChar expChar_injective
  let F : (Multiplicative ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun u : ℝ => Multiplicative.ofAdd u)
  have hF : LinearMap.ker F = ⊥ :=
    LinearMap.ker_eq_bot.mpr (LinearMap.funLeft_injective_of_surjective _ _ _
      (fun x => ⟨Multiplicative.toAdd x, rfl⟩))
  have h2 := h1.map' F hF
  exact h2

/-- The vector of spectral values on `S`. -/
noncomputable def spectralVector (S : Finset ℂ) (g : ℝ → ℝ) : S → ℂ :=
  fun s => spectralTransform g s

/-- **Mellin interpolation (span form).** -/
theorem span_spectralVectors_eq_top (S : Finset ℂ) :
    Submodule.span ℂ {w | ∃ g, IsTestFunction g ∧ w = spectralVector S g} = ⊤ := by
  by_contra hne
  obtain ⟨ℓ, hℓ, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  -- coefficients of ℓ
  set c : S → ℂ := fun s => ℓ (Pi.single s 1) with hc
  have hℓsum : ∀ w : S → ℂ, ℓ w = ∑ s, c s * w s := by
    intro w
    conv_lhs => rw [show w = ∑ s, w s • Pi.single s (1 : ℂ) by
      ext t; simp [Finset.sum_apply, Pi.single_apply]]
    simp [map_sum, c, mul_comm]
  -- the kernel
  set K : ℝ → ℂ := fun u => ∑ s : S, c s * Complex.exp (((s : ℂ) - 1 / 2) * u) with hK
  have hKcont : Continuous K := by
    refine continuous_finsetSum _ (fun s _ => continuous_const.mul ?_)
    exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hpair : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ u, g u • K u = 0 := by
    intro g hg hgc
    have hmem : spectralVector S g ∈ Submodule.span ℂ
        {w | ∃ g, IsTestFunction g ∧ w = spectralVector S g} :=
      Submodule.subset_span ⟨g, ⟨hg, hgc⟩, rfl⟩
    have h0 : ℓ (spectralVector S g) = 0 := hker hmem
    rw [hℓsum] at h0
    have hint : ∀ s : S, Integrable
        (fun u : ℝ => (g u : ℂ) * Complex.exp (((s : ℂ) - 1 / 2) * u)) := by
      intro s
      refine Continuous.integrable_of_hasCompactSupport ?_ ?_
      · exact (Complex.continuous_ofReal.comp hg.continuous).mul
          (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
      · exact (hgc.comp_left Complex.ofReal_zero).mul_right
    have hexp : ∫ u, g u • K u =
        ∑ s : S, c s * ∫ u, (g u : ℂ) * Complex.exp (((s : ℂ) - 1 / 2) * u) := by
      simp_rw [hK, Finset.smul_sum]
      rw [integral_finsetSum _ (fun s _ => ?_)]
      · refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        simp only [real_smul]
        ring
      · have := (hint s).const_mul (c s)
        refine this.congr (Filter.Eventually.of_forall fun u => ?_)
        simp only [real_smul]
        ring
    rw [hexp]
    simpa [spectralVector, spectralTransform] using h0
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hKcont.locallyIntegrable (μ := volume)) hpair
  have hK0 : K = 0 := (hKcont.ae_eq_iff_eq volume continuous_const).mp hae
  -- linear independence forces c = 0
  have hc0 : ∀ s : S, c s = 0 := by
    have hli := linearIndependent_exp
    have hinj : Function.Injective (fun s : S => (s : ℂ) - 1 / 2) := by
      intro x y h; exact Subtype.ext (by simpa using h)
    have hli' := hli.comp _ hinj
    have := linearIndependent_iff'.mp hli' Finset.univ (fun s => c s) ?_
    · intro s; exact this s (Finset.mem_univ s)
    · funext u
      have := congrFun hK0 u
      simpa [hK, Finset.sum_apply] using this
  apply hℓ
  ext w
  simp [hℓsum, hc0]

end GppMellinInterpolation

#print axioms GppMellinInterpolation.span_spectralVectors_eq_top
