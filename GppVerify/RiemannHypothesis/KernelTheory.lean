import GppVerify.RiemannHypothesis.GwefFactorisation
import GppVerify.RiemannHypothesis.CesaroPrincipalSeriesSelector

/-!
# Kernel theories: reflection positivity forces the principal series (theorem about theories)

Turbo, GPP-bridge PR #11 issuecomment-6805665010. Daniel's framing: it is a CFT, the proof is
a theorem about theories, and the arithmetic is an instance.

1. **The datum** `KernelTheory`: a test space, a reflection `Θ` with `Θ² = id`, a dilation
   character transform `Ψ` intertwining `Θ` with the shadow `s ↦ 1 - s`, a weight set with
   multiplicities closed under the shadow involution `ι s = 1 - s̄` and conjugation, a correlator
   pairing with its spectral identity, and the density (interpolation) of the spectral image.
   The dilation character norm is the symmetric Cesàro mean (`characterNorm`, in-tree
   `GppCesaroPrincipalSeriesSelector`). No primes and no zeros appear in the datum.
2. **The theorem** `KernelTheory.principalSeries_of_reflectionPositive`: reflection positivity
   (`0 ≤ Re corr(Θf, f)` for every test) forces every weight onto `Re = 1/2`, equivalently
   every weight has finite Cesàro character norm (`cesaroFinite_of_reflectionPositive`).
   Proved once, for the class.
3. **The ζ instance** `zetaTheory`: Tate/log-variable test space, `Θ f = f(-·)`, weights the
   nontrivial zeros with multiplicity. Every datum field is filled by an in-tree theorem
   (GW-EF-3 interpolation, zero symmetry, positive multiplicities). Reflection positivity of
   `zetaTheory` is the one open obligation; `reflectionPositive_of_arp` shows ARP supplies it
   through GW-EF-1 (explicit formula) and GW-EF-2 (factorisation). `rh_of_arp'` re-derives
   `rh_of_arp` as the ζ corollary.

Labels: everything here PROVED (standard axioms). Reflection positivity of `zetaTheory`
(equivalently ARP; AFT's factor map for the completed kernel) is OPEN, so RH is OPEN.
No `sorry`, no axiom, no `open_` stub.

Daniel Toupin / Golden Physics Project, with AI assistance (Heart of the Cosmos / Grok).
Task and spec: Turbo.
-/

open Complex MeasureTheory
open GppMeyerSpectralWeil GppWeilCriterion GppArithmeticReflection GppGwefAssembly

noncomputable section

namespace GppKernelTheory

/-- **The datum: an abstract kernel theory.** -/
structure KernelTheory where
  /-- The test space. -/
  Test : Type
  /-- The reflection (shadow involution on tests). -/
  Θ : Test → Test
  Θ_invol : ∀ f, Θ (Θ f) = f
  /-- The dilation character transform: `Ψ f s` is the coefficient of `f` on the dilation
  character of weight `s`. -/
  Ψ : Test → ℂ → ℂ
  /-- The reflection acts on characters as the shadow `s ↦ 1 - s`. -/
  Ψ_Θ : ∀ f s, Ψ (Θ f) s = Ψ f (1 - s)
  /-- The weights of the theory, with multiplicities. -/
  W : Set ℂ
  m : ℂ → ℕ
  m_pos : ∀ ρ ∈ W, 1 ≤ m ρ
  shadow_closed : ∀ ρ ∈ W, zetaInvolution ρ ∈ W ∧ m (zetaInvolution ρ) = m ρ
  conj_closed : ∀ ρ ∈ W, (starRingEnd ℂ) ρ ∈ W ∧ m ((starRingEnd ℂ) ρ) = m ρ
  /-- The correlator pairing. -/
  corr : Test → Test → ℂ
  /-- The spectral identity: the pairing is the sum over the theory's weights. -/
  spectral : ∀ g f, corr g f = ∑' ρ : W, (m ρ : ℂ) * (Ψ g ρ * Ψ f ρ)
  /-- Density of the spectral image: every finite, shadow-closed, conjugation-symmetric
  weight datum is a limit of reflected Gram forms. -/
  interpolation : ∀ (S : Finset ℂ), ↑S ⊆ W → (∀ ρ ∈ S, zetaInvolution ρ ∈ S) →
    ∀ v : ℂ → ℂ, (∀ ρ ∈ S, (starRingEnd ℂ) ρ ∈ S ∧ v ((starRingEnd ℂ) ρ) = (starRingEnd ℂ) (v ρ)) →
    ∀ ε : ℝ, 0 < ε → ∃ f : Test, ‖corr (Θ f) f - pairedForm zetaInvolution S v‖ < ε

namespace KernelTheory

variable (T : KernelTheory)

/-- The reflected Gram form `G(f) = corr(Θf, f)`. -/
def gram (f : T.Test) : ℂ := T.corr (T.Θ f) f

/-- **Reflection positivity** of the datum: the reflected Gram form is positive. -/
def ReflectionPositive : Prop := ∀ f : T.Test, 0 ≤ (T.gram f).re

/-- The reflected Gram form in spectral form: `Σ m(ρ) Ψf(ρ) Ψf(1 - ρ)`. -/
theorem gram_spectral (f : T.Test) :
    T.gram f = ∑' ρ : T.W, (T.m ρ : ℂ) * (T.Ψ f ρ * T.Ψ f (1 - ρ)) := by
  unfold gram
  rw [T.spectral]
  congr 1; funext ρ
  rw [T.Ψ_Θ, mul_comm (T.Ψ f (1 - (ρ : ℂ)))]

/-- **The theorem about theories.** Reflection positivity of a kernel theory forces every
weight onto the principal series `Re = 1/2`. (Lift of `online_of_pairing_nonneg`.) -/
theorem principalSeries_of_reflectionPositive (hRP : T.ReflectionPositive) :
    ∀ ρ ∈ T.W, ρ.re = 1 / 2 := by
  classical
  intro ρ₀ hρ₀
  by_contra hne
  set x : ℝ := ρ₀.re with hx
  set v : ℂ → ℂ := fun ρ => if ρ.re = x then 1 else if ρ.re = 1 - x then -1 else 0 with hv
  set S : Finset ℂ :=
    {ρ₀, zetaInvolution ρ₀, (starRingEnd ℂ) ρ₀, zetaInvolution ((starRingEnd ℂ) ρ₀)} with hS
  have hιre : ∀ ρ : ℂ, (zetaInvolution ρ).re = 1 - ρ.re := fun ρ => by simp [zetaInvolution]
  have hcre : ∀ ρ : ℂ, ((starRingEnd ℂ) ρ).re = ρ.re := fun ρ => by simp
  have hx2 : x ≠ 1 - x := fun h => hne (by linarith)
  have hι0 : zetaInvolution ρ₀ ∈ T.W := (T.shadow_closed ρ₀ hρ₀).1
  have hc0 : (starRingEnd ℂ) ρ₀ ∈ T.W := (T.conj_closed ρ₀ hρ₀).1
  have hιc0 : zetaInvolution ((starRingEnd ℂ) ρ₀) ∈ T.W := (T.shadow_closed _ hc0).1
  have hSZ : ↑S ⊆ T.W := by
    intro ρ hρ
    simp only [hS, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hρ
    rcases hρ with rfl | rfl | rfl | rfl <;> assumption
  have hinv : ∀ ρ : ℂ, zetaInvolution (zetaInvolution ρ) = ρ := zetaInvolution_involutive
  have hSι : ∀ ρ ∈ S, zetaInvolution ρ ∈ S := by
    intro ρ hρ
    simp only [hS, Finset.mem_insert, Finset.mem_singleton] at hρ ⊢
    rcases hρ with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (hinv _)
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl (hinv _)))
  have hvreal : ∀ ρ, (starRingEnd ℂ) (v ρ) = v ρ := by
    intro ρ; simp only [hv]; split_ifs <;> simp
  have hvre : ∀ ρ, v ((starRingEnd ℂ) ρ) = v ρ := by
    intro ρ; simp only [hv, hcre]
  have hSconj : ∀ ρ ∈ S,
      (starRingEnd ℂ) ρ ∈ S ∧ v ((starRingEnd ℂ) ρ) = (starRingEnd ℂ) (v ρ) := by
    intro ρ hρ
    refine ⟨?_, by rw [hvre, hvreal]⟩
    simp only [hS, Finset.mem_insert, Finset.mem_singleton] at hρ ⊢
    have hcz : ∀ ρ : ℂ, (starRingEnd ℂ) (zetaInvolution ρ) = 1 - ρ := fun ρ => by
      simp [zetaInvolution]
    rcases hρ with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [hcz]; simp [zetaInvolution]
    · exact Or.inl (by simp)
    · refine Or.inr (Or.inl ?_)
      rw [hcz]; simp [zetaInvolution]
  have hterm : ∀ ρ ∈ S, (starRingEnd ℂ) (v (zetaInvolution ρ)) * v ρ = -1 := by
    intro ρ hρ
    have hre : ρ.re = x ∨ ρ.re = 1 - x := by
      simp only [hS, Finset.mem_insert, Finset.mem_singleton] at hρ
      rcases hρ with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (by rw [hιre])
      · exact Or.inl (by rw [hcre])
      · exact Or.inr (by rw [hιre, hcre])
    rw [hvreal]
    simp only [hv, hιre]
    rcases hre with h | h
    · simp [h, show (1 - x) ≠ x from fun h' => hx2 h'.symm]
    · have : ρ.re ≠ x := fun h' => hx2 (by linarith)
      simp only [h, if_true]
      norm_num
      exact fun h' => hx2 h'.symm
  have hpf : pairedForm zetaInvolution S v = -(S.card : ℂ) := by
    unfold pairedForm
    rw [Finset.sum_congr rfl hterm]
    simp
  have hcard : 2 ≤ S.card := by
    have hne2 : ρ₀ ≠ zetaInvolution ρ₀ :=
      fun h => hne ((zetaInvolution_fixed_iff ρ₀).1 h.symm)
    calc 2 = ({ρ₀, zetaInvolution ρ₀} : Finset ℂ).card := (Finset.card_pair hne2).symm
      _ ≤ S.card := Finset.card_le_card (by
        intro ρ hρ
        simp only [hS, Finset.mem_insert, Finset.mem_singleton] at hρ ⊢
        rcases hρ with rfl | rfl <;> simp)
  obtain ⟨f, hlt⟩ := T.interpolation S hSZ hSι v (fun ρ hρ => hSconj ρ hρ) 1 one_pos
  have h0 := hRP f
  unfold gram at h0
  rw [hpf] at hlt
  have hre : (-(S.card : ℂ)).re = -(S.card : ℝ) := by simp
  have hcardR : (2 : ℝ) ≤ S.card := by exact_mod_cast hcard
  have h1 := (Complex.abs_re_le_norm _).trans_lt hlt
  have h2 := abs_lt.1 h1
  simp only [Complex.sub_re, hre] at h2
  linarith [h2.2]

/-- The dilation character norm of a weight: the symmetric Cesàro mean of its squared
half-density character (in-tree `GppCesaroPrincipalSeriesSelector.cesaroMean`). -/
def characterNorm (ρ : ℂ) (R : ℝ) : ℝ := GppCesaroPrincipalSeriesSelector.cesaroMean ρ.re R

/-- A weight is a state when its Cesàro character norm is eventually bounded. -/
def CesaroFinite (ρ : ℂ) : Prop := ∃ M : ℝ, ∀ᶠ R : ℝ in Filter.atTop, characterNorm ρ R ≤ M

/-- Cesàro-finite iff principal series (in-tree selector). -/
theorem cesaroFinite_iff (ρ : ℂ) : CesaroFinite ρ ↔ ρ.re = 1 / 2 :=
  GppCesaroPrincipalSeriesSelector.eventually_bounded_iff_critical ρ.re

/-- **The theorem about theories, Cesàro form.** Reflection positivity forces every weight to
have finite Cesàro character norm. -/
theorem cesaroFinite_of_reflectionPositive (hRP : T.ReflectionPositive) :
    ∀ ρ ∈ T.W, CesaroFinite ρ := fun ρ hρ =>
  (cesaroFinite_iff ρ).2 (T.principalSeries_of_reflectionPositive hRP ρ hρ)

end KernelTheory

/-! ### The ζ instance -/

/-- Log-variable test functions (smooth, compactly supported). -/
def ZetaTest : Type := {f : ℝ → ℝ // IsTestFunction f}

/-- The reflection `f ↦ f(-·)` preserves the test class. -/
def zetaReflect (f : ZetaTest) : ZetaTest :=
  ⟨fun x => f.1 (-x), by
    refine ⟨f.2.1.comp contDiff_neg, ?_⟩
    exact f.2.2.comp_homeomorph (Homeomorph.neg ℝ)⟩

theorem spectralTransform_reflect (f : ℝ → ℝ) (s : ℂ) :
    spectralTransform (fun x => f (-x)) s = spectralTransform f (1 - s) := by
  unfold spectralTransform
  rw [← integral_neg_eq_self]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [neg_neg]
  congr 2
  push_cast; ring

/-- **The ζ datum.** -/
def zetaTheory : KernelTheory where
  Test := ZetaTest
  Θ := zetaReflect
  Θ_invol f := by
    apply Subtype.ext; funext x; simp [zetaReflect]
  Ψ f s := spectralTransform f.1 s
  Ψ_Θ f s := spectralTransform_reflect f.1 s
  W := nontrivialZeros
  m := GppXiZeroCounting.zeroMult
  m_pos _ hρ := GppXiZeroCounting.one_le_zeroMult hρ
  shadow_closed _ hρ := ⟨(GppXiZeroCounting.zeroData_symmetric hρ).1,
    (GppXiZeroCounting.zeroData_symmetric hρ).2.1⟩
  conj_closed _ hρ := ⟨(GppXiZeroCounting.zeroData_symmetric hρ).2.2.1,
    (GppXiZeroCounting.zeroData_symmetric hρ).2.2.2⟩
  corr g f := ∑' ρ : nontrivialZeros,
    (GppXiZeroCounting.zeroMult ρ : ℂ) * (spectralTransform g.1 ρ * spectralTransform f.1 ρ)
  spectral _ _ := rfl
  interpolation S hS hSι v hv ε hε := by
    have hloc : ∀ R : ℝ, {ρ ∈ nontrivialZeros | ‖ρ‖ ≤ R}.Finite := fun R =>
      (GppXiZeroCounting.finite_zeros_xi R).subset fun ρ hρ =>
        ⟨hρ.2, (GppXiReflection.xi_eq_zero_iff_nontrivial ρ).2 hρ.1⟩
    obtain ⟨f, hf, hlt⟩ := gwef3_interpolation nontrivialZeros GppXiZeroCounting.zeroMult hloc
      (fun ρ hρ => GppXiZeroCounting.one_le_zeroMult hρ)
      GppXiZeroCounting.zeroCountingPolynomial
      (fun ρ hρ => ⟨hρ.2.1, hρ.2.2⟩)
      (fun ρ hρ => ⟨(GppXiZeroCounting.zeroData_symmetric hρ).1,
        (GppXiZeroCounting.zeroData_symmetric hρ).2.1⟩)
      (fun ρ hρ => ⟨(GppXiZeroCounting.zeroData_symmetric hρ).2.2.1,
        (GppXiZeroCounting.zeroData_symmetric hρ).2.2.2⟩) S hS hSι v hv ε hε
    refine ⟨⟨f, hf⟩, ?_⟩
    have hsum : (∑' ρ : nontrivialZeros, (GppXiZeroCounting.zeroMult ρ : ℂ) *
        (spectralTransform (fun x => f (-x)) ρ * spectralTransform f ρ)) =
        ∑' ρ : nontrivialZeros, (GppXiZeroCounting.zeroMult ρ : ℂ) *
        (spectralTransform f ρ * spectralTransform f (1 - ρ)) := by
      congr 1; funext ρ
      rw [spectralTransform_reflect, mul_comm (spectralTransform f (1 - (ρ : ℂ)))]
    change ‖(∑' ρ : nontrivialZeros, (GppXiZeroCounting.zeroMult ρ : ℂ) *
        (spectralTransform (fun x => f (-x)) ρ * spectralTransform f ρ)) -
        pairedForm zetaInvolution S v‖ < ε
    rw [hsum]; exact hlt

/-- **The one open obligation, routed.** ARP supplies reflection positivity of the ζ datum
(through GW-EF-1 and GW-EF-2). Reflection positivity of `zetaTheory` itself is OPEN. -/
theorem reflectionPositive_of_arp (harp : ArithmeticReflectionPositivity) :
    zetaTheory.ReflectionPositive := by
  intro f
  rw [KernelTheory.gram_spectral]
  obtain ⟨-, hsum⟩ := GppExplicitFormulaAssembly.explicit_formula_zeroSum f.2
  have hfac : ∀ ρ : nontrivialZeros,
      (GppXiZeroCounting.zeroMult ρ : ℂ) * spectralTransform (autocorr f.1) ρ =
        (GppXiZeroCounting.zeroMult ρ : ℂ) *
          (spectralTransform f.1 ρ * spectralTransform f.1 (1 - ρ)) := fun ρ => by
    rw [gwef2_factorisation f.2]
  simp_rw [hfac] at hsum
  change 0 ≤ (∑' ρ : nontrivialZeros, (GppXiZeroCounting.zeroMult ρ : ℂ) *
      (spectralTransform f.1 ρ * spectralTransform f.1 (1 - ρ))).re
  rw [hsum, Complex.ofReal_re]
  exact harp f.1 f.2.1 f.2.2


/-- Converse: reflection positivity of the ζ datum is exactly ARP. -/
theorem arp_of_reflectionPositive (hRP : zetaTheory.ReflectionPositive) :
    ArithmeticReflectionPositivity := by
  intro f h1 h2
  have h := hRP ⟨f, h1, h2⟩
  rw [KernelTheory.gram_spectral zetaTheory ⟨f, h1, h2⟩] at h
  obtain ⟨-, hsum⟩ := GppExplicitFormulaAssembly.explicit_formula_zeroSum (f := f) ⟨h1, h2⟩
  have hfac : ∀ ρ : nontrivialZeros,
      (GppXiZeroCounting.zeroMult ρ : ℂ) * spectralTransform (autocorr f) ρ =
        (GppXiZeroCounting.zeroMult ρ : ℂ) *
          (spectralTransform f ρ * spectralTransform f (1 - ρ)) := fun ρ => by
    rw [gwef2_factorisation (f := f) ⟨h1, h2⟩]
  simp_rw [hfac] at hsum
  change 0 ≤ (∑' ρ : nontrivialZeros, (GppXiZeroCounting.zeroMult ρ : ℂ) *
      (spectralTransform f ρ * spectralTransform f (1 - ρ))).re at h
  rw [hsum, Complex.ofReal_re] at h
  exact h

/-- **The named open obligation** (the factor-map field for the completed kernel): reflection
positivity of the ζ datum. OPEN. Equivalent to ARP (`zeta_obligation_iff_arp`). -/
def ZetaReflectionPositivityObligation : Prop := zetaTheory.ReflectionPositive

theorem zeta_obligation_iff_arp :
    ZetaReflectionPositivityObligation ↔ ArithmeticReflectionPositivity :=
  ⟨arp_of_reflectionPositive, reflectionPositive_of_arp⟩

/-- **`rh_of_arp` as the ζ corollary of the theorem about theories.** ARP is OPEN; this does
not prove RH. -/
theorem rh_of_arp' (harp : ArithmeticReflectionPositivity) :
    ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2 :=
  zetaTheory.principalSeries_of_reflectionPositive (reflectionPositive_of_arp harp)

end GppKernelTheory

#print axioms GppKernelTheory.KernelTheory.principalSeries_of_reflectionPositive
#print axioms GppKernelTheory.KernelTheory.cesaroFinite_of_reflectionPositive
#print axioms GppKernelTheory.zetaTheory
#print axioms GppKernelTheory.reflectionPositive_of_arp
#print axioms GppKernelTheory.rh_of_arp'
#print axioms GppKernelTheory.zeta_obligation_iff_arp
