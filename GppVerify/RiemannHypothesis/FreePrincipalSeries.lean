import GppVerify.RiemannHypothesis.LinearShadowTheory

/-!
# The free principal-series model: a reflection-positive linear shadow theory

A **sanity check** for the shadow-theory package (`MuseResearch/shadow-theory-axiom-package-2026-11-15.md`,
build order bridge `9f0e414`), not "the celestial model" and not isomorphic to ζ. It shows that the
datum `LinearShadowTheory` (#609) is non-vacuous and that its A3 and its closing theorem fire on an honest
instance:

* weights `ρ_n = 1/2 + i n`, `n ∈ ℤ` (the *discrete* principal-series lattice — Fourier series on the
  compact dilation circle), each with multiplicity `1`;
* tests: finitely supported Hermitian sequences `u : ℤ → ℂ`, `u(−n) = conj u(n)`, a real vector space;
* `Ψ f ρ_n = u(n)` (and `0` off the lattice), `Θ f = conj ∘ u` (equivalently `u(−·)`);
* `corr g f = Σ_n u_g(n) u_f(n)`, so `corr(Θ f, f) = Σ_n |u_f(n)|²`.

**A3 holds by construction** (`freePS_reflectionPositive`), through the in-tree equivalence
`reflectionPositive_of_online` (every weight on `Re = 1/2`) — the lattice is on the principal line — and the
state space is `ℓ²(ℤ)` (`freePS_stateSpace`, through `reflectionPositive_iff_stateSpace`).

**Why discrete, and what that means.** The datum's spectral identity is a `tsum` over a *set of weights*
`W : Set ℂ`, so it can carry only a *countable* spectrum. The continuous Plancherel model (`L²` of the
principal series `ℝ`, via `mellinL2`) does not fit the `KernelTheory` shape: a continuous spectral measure
would need `∑' ρ : W` replaced by `∫`. That is a finding about the *datum*, recorded here so that the
celestial instance (whose natural spectrum is continuous) is not mis-stated as an instance of `KernelTheory`
as it stands. The lattice model is the compact-circle truncation of the same structure.

Not here: the dilation action, the vacuum, local factorisation; any relation to the arithmetic model;
ARP, RH, AKG — all untouched. No `sorry`, no axiom.
-/

open Complex Finset
open scoped InnerProductSpace
open GppKernelTheory GppWeilCriterion GppShadowTheory

noncomputable section

namespace GppFreePS

/-- The lattice of principal-series weights `ρ_n = 1/2 + i n`. -/
def pt (n : ℤ) : ℂ := 1 / 2 + (n : ℂ) * Complex.I

theorem pt_injective : Function.Injective pt := by
  intro a b h
  have := congrArg Complex.im h
  simpa [pt] using this

theorem pt_re (n : ℤ) : (pt n).re = 1 / 2 := by simp [pt]

theorem conj_pt (n : ℤ) : starRingEnd ℂ (pt n) = pt (-n) := by
  simp [pt, map_ofNat]

theorem one_sub_pt (n : ℤ) : (1 : ℂ) - pt n = pt (-n) := by
  simp [pt]; ring

theorem zetaInvolution_pt (n : ℤ) : zetaInvolution (pt n) = pt n := by
  unfold zetaInvolution
  rw [conj_pt]
  simp [pt]; ring

/-- Hermitian finitely supported sequences, as a real submodule of `ℤ →₀ ℂ`. -/
def herm : Submodule ℝ (ℤ →₀ ℂ) where
  carrier := {u | ∀ n, u (-n) = starRingEnd ℂ (u n)}
  add_mem' := fun {a b} ha hb n => by simp [ha n, hb n]
  zero_mem' := fun n => by simp
  smul_mem' := fun c u hu n => by simp [hu n, Complex.real_smul]

/-- The test space: finitely supported Hermitian sequences, a real vector space. -/
abbrev Test : Type := herm

theorem herm_apply (f : Test) (n : ℤ) : f.1 (-n) = starRingEnd ℂ (f.1 n) := f.2 n

open Classical in
/-- The character transform: `Ψ f ρ_n = u_f(n)`, and `0` off the lattice. -/
def Ψ (f : Test) (s : ℂ) : ℂ := if h : ∃ n, pt n = s then f.1 h.choose else 0

theorem Ψ_pt (f : Test) (n : ℤ) : Ψ f (pt n) = f.1 n := by
  have h : ∃ m, pt m = pt n := ⟨n, rfl⟩
  rw [Ψ, dif_pos h, pt_injective h.choose_spec]

theorem Ψ_off (f : Test) (s : ℂ) (h : ¬ ∃ n, pt n = s) : Ψ f s = 0 := by
  rw [Ψ, dif_neg h]

/-- The reflection: complex conjugation of the sequence (equivalently `u ↦ u(−·)`). -/
def Θ (f : Test) : Test :=
  ⟨Finsupp.mapRange (starRingEnd ℂ) (map_zero _) f.1, fun n => by
    simp [Finsupp.mapRange_apply, herm_apply f n]⟩

theorem Θ_apply (f : Test) (n : ℤ) : (Θ f).1 n = starRingEnd ℂ (f.1 n) := by
  simp [Θ, Finsupp.mapRange_apply]

theorem Θ_invol (f : Test) : Θ (Θ f) = f := by
  apply Subtype.ext
  ext n
  rw [Θ_apply, Θ_apply, Complex.conj_conj]

theorem Ψ_Θ (f : Test) (s : ℂ) : Ψ (Θ f) s = Ψ f (1 - s) := by
  by_cases h : ∃ n, pt n = s
  · obtain ⟨n, rfl⟩ := h
    rw [Ψ_pt, one_sub_pt, Ψ_pt, Θ_apply, herm_apply]
  · have h' : ¬ ∃ m, pt m = 1 - s := by
      rintro ⟨m, hm⟩
      exact h ⟨-m, by rw [← one_sub_pt, hm]; ring⟩
    rw [Ψ_off _ _ h, Ψ_off _ _ h']

theorem Ψ_conj (f : Test) (s : ℂ) : Ψ f (starRingEnd ℂ s) = starRingEnd ℂ (Ψ f s) := by
  by_cases h : ∃ n, pt n = s
  · obtain ⟨n, rfl⟩ := h
    rw [conj_pt, Ψ_pt, Ψ_pt, herm_apply]
  · have h' : ¬ ∃ m, pt m = starRingEnd ℂ s := by
      rintro ⟨m, hm⟩
      refine h ⟨-m, ?_⟩
      have := congrArg (starRingEnd ℂ) hm
      rw [Complex.conj_conj, conj_pt] at this
      exact this
    rw [Ψ_off _ _ h, Ψ_off _ _ h', map_zero]

theorem Ψ_add (f g : Test) (s : ℂ) : Ψ (f + g) s = Ψ f s + Ψ g s := by
  by_cases h : ∃ n, pt n = s
  · obtain ⟨n, rfl⟩ := h
    simp [Ψ_pt]
  · simp [Ψ_off _ _ h]

theorem Ψ_smul (c : ℝ) (f : Test) (s : ℂ) : Ψ (c • f) s = (c : ℂ) * Ψ f s := by
  by_cases h : ∃ n, pt n = s
  · obtain ⟨n, rfl⟩ := h
    simp [Ψ_pt, Complex.real_smul]
  · simp [Ψ_off _ _ h]

/-- The weights `ρ_n = 1/2 + i n`. -/
def W : Set ℂ := Set.range pt

/-- The pairing, by its spectral identity. -/
def corr (g f : Test) : ℂ := ∑' ρ : W, ((1 : ℕ) : ℂ) * (Ψ g ρ * Ψ f ρ)

theorem summable_pair (a b : ℤ →₀ ℂ) : Summable (fun n : ℤ => a n * b n) := by
  refine summable_of_hasFiniteSupport (Set.Finite.subset a.support.finite_toSet ?_)
  intro n hn
  simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hn
  simpa using hn.1

/-- **The pairing is the finite sum `Σ_n u_g(n) u_f(n)`.** -/
theorem corr_eq (g f : Test) : corr g f = ∑' n : ℤ, g.1 n * f.1 n := by
  have e := Equiv.tsum_eq (Equiv.ofInjective pt pt_injective)
    (fun ρ : Set.range pt => ((1 : ℕ) : ℂ) * (Ψ g ρ * Ψ f ρ))
  refine e.symm.trans (tsum_congr fun n => ?_)
  show ((1 : ℕ) : ℂ) * (Ψ g (pt n) * Ψ f (pt n)) = _
  rw [Ψ_pt, Ψ_pt]; simp

theorem corr_add_left (g₁ g₂ f : Test) : corr (g₁ + g₂) f = corr g₁ f + corr g₂ f := by
  simp only [corr_eq]
  rw [← (summable_pair g₁.1 f.1).tsum_add (summable_pair g₂.1 f.1)]
  refine tsum_congr fun n => ?_
  simp [add_mul]

theorem corr_smul_left (c : ℝ) (g f : Test) : corr (c • g) f = (c : ℂ) * corr g f := by
  simp only [corr_eq]
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  simp [Complex.real_smul, mul_assoc]

theorem corr_add_right (g f₁ f₂ : Test) : corr g (f₁ + f₂) = corr g f₁ + corr g f₂ := by
  simp only [corr_eq]
  rw [← (summable_pair g.1 f₁.1).tsum_add (summable_pair g.1 f₂.1)]
  refine tsum_congr fun n => ?_
  simp [mul_add]

theorem corr_smul_right (c : ℝ) (g f : Test) : corr g (c • f) = (c : ℂ) * corr g f := by
  simp only [corr_eq]
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  simp [Complex.real_smul]
  ring

/-- **Interpolation**: every finite, shadow-closed, conjugation-symmetric weight datum is realised
*exactly* as a reflected Gram form. -/
theorem interp (S : Finset ℂ) (hS : (↑S : Set ℂ) ⊆ W)
    (_hι : ∀ ρ ∈ S, zetaInvolution ρ ∈ S) (v : ℂ → ℂ)
    (hv : ∀ ρ ∈ S, starRingEnd ℂ ρ ∈ S ∧ v (starRingEnd ℂ ρ) = starRingEnd ℂ (v ρ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : Test, ‖corr (Θ f) f - pairedForm zetaInvolution S v‖ < ε := by
  classical
  set T : Finset ℤ := S.preimage pt pt_injective.injOn with hT
  let u : ℤ →₀ ℂ := Finsupp.onFinset T (fun n => if pt n ∈ S then v (pt n) else 0) (by
    intro n hn
    rw [hT, Finset.mem_preimage]
    by_contra hnS
    exact hn (by simp [hnS]))
  have hu : ∀ n, u n = if pt n ∈ S then v (pt n) else 0 := fun n => rfl
  have hherm : u ∈ herm := by
    intro n
    rw [hu, hu]
    by_cases h : pt n ∈ S
    · have h2 := hv _ h
      rw [conj_pt] at h2
      rw [if_pos h, if_pos h2.1, h2.2]
    · have h2 : pt (-n) ∉ S := by
        intro h3
        have := (hv _ h3).1
        rw [conj_pt, neg_neg] at this
        exact h this
      rw [if_neg h, if_neg h2, map_zero]
  refine ⟨⟨u, hherm⟩, ?_⟩
  have hsum : corr (Θ ⟨u, hherm⟩) ⟨u, hherm⟩ = ∑ n ∈ T, starRingEnd ℂ (u n) * u n := by
    rw [corr_eq]
    simp only [Θ_apply]
    refine tsum_eq_sum fun n hn => ?_
    have : u n = 0 := by
      by_contra h
      exact hn (by
        rw [hT, Finset.mem_preimage]
        by_contra hnS
        exact h (by rw [hu, if_neg hnS]))
    simp [this]
  have hpair : pairedForm zetaInvolution S v = ∑ n ∈ T, starRingEnd ℂ (u n) * u n := by
    set G : ℂ → ℂ := fun ρ =>
      starRingEnd ℂ (if ρ ∈ S then v ρ else 0) * (if ρ ∈ S then v ρ else 0) with hG
    have e1 : ∑ n ∈ T, starRingEnd ℂ (u n) * u n = ∑ n ∈ T, G (pt n) :=
      Finset.sum_congr rfl fun n _ => by simp only [hu, hG]
    have e2 : ∑ n ∈ T, G (pt n) = ∑ ρ ∈ S, G ρ := by
      rw [hT]
      exact Finset.sum_preimage pt S pt_injective.injOn G
        (fun ρ hρ hnot => absurd (hS (Finset.mem_coe.mpr hρ)) hnot)
    rw [e1, e2]
    unfold pairedForm
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    obtain ⟨n, rfl⟩ := hS (Finset.mem_coe.mpr hρ)
    simp only [hG, zetaInvolution_pt, if_pos hρ]
  rw [hsum, hpair, sub_self, norm_zero]
  exact hε

/-- **The free principal-series model**, as a linear shadow theory. -/
def freePS : LinearShadowTheory where
  Test := Test
  Θ := Θ
  Θ_invol := Θ_invol
  Ψ := Ψ
  Ψ_Θ := Ψ_Θ
  W := W
  m := fun _ => 1
  m_pos := fun _ _ => le_refl 1
  shadow_closed := fun ρ hρ => by
    obtain ⟨n, rfl⟩ := hρ
    exact ⟨by rw [zetaInvolution_pt]; exact ⟨n, rfl⟩, rfl⟩
  conj_closed := fun ρ hρ => by
    obtain ⟨n, rfl⟩ := hρ
    exact ⟨by rw [conj_pt]; exact ⟨-n, rfl⟩, rfl⟩
  corr := corr
  spectral := fun g f => rfl
  interpolation := fun S hS hι v hv ε hε => interp S hS hι v hv ε hε
  Ψ_conj := Ψ_conj
  instACG := inferInstance
  instMod := inferInstance
  Θ_add := fun f g => by
    apply Subtype.ext; ext n
    simp [Θ_apply]
  Θ_smul := fun c f => by
    apply Subtype.ext; ext n
    simp [Θ_apply, Complex.real_smul]
  Ψ_add := Ψ_add
  Ψ_smul := Ψ_smul
  corr_add_left := corr_add_left
  corr_smul_left := corr_smul_left
  corr_add_right := corr_add_right
  corr_smul_right := corr_smul_right

/-- Every weight of the free model is on the principal line. -/
theorem freePS_online : ∀ ρ ∈ freePS.W, ρ.re = 1 / 2 := by
  intro ρ hρ
  obtain ⟨n, rfl⟩ := hρ
  exact pt_re n

/-- **A3 holds for the free model, by construction.** -/
theorem freePS_reflectionPositive : freePS.ReflectionPositive :=
  ShadowTheory.reflectionPositive_of_online freePS.toShadowTheory freePS_online

/-- **The state space exists** (it is `ℓ²(ℤ)`): the pairing across the fold is an inner product on a
real Hilbert space receiving the tests. Through the in-tree equivalence A3 ⇔ state space. -/
theorem freePS_stateSpace :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
      (ι : freePS.Test →ₗ[ℝ] H),
      (∀ g f, (freePS.corr (freePS.Θ g) f).re = ⟪ι g, ι f⟫_ℝ) ∧ DenseRange ι :=
  freePS.reflectionPositive_iff_stateSpace.mp freePS_reflectionPositive

end GppFreePS

#print axioms GppFreePS.freePS
#print axioms GppFreePS.freePS_reflectionPositive
#print axioms GppFreePS.freePS_stateSpace
