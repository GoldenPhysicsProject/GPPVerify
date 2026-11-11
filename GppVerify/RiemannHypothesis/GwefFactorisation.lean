/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude's GW-EF sheet, Codex's interpolation,
Turbo's audits; ported by Heart of the Cosmos / Grok)
-/
import GppVerify.RiemannHypothesis.GwefInterp

/-!
# GW-EF factorisation: GW-EF-2, GW-EF-3 and the positivity-forces-the-line lemma

Split out of `GwefAssembly.lean` (Turbo, GPP-bridge PR #11 issuecomment-6806968693, item 1) so that
`KernelTheory.lean` can sit between these lemmas and `rh_of_arp`: `rh_of_arp` now lives in
`GwefAssembly.lean` as the ζ corollary `GppKernelTheory.rh_of_arp'` of the theorem about theories.
Content below is unchanged from `GwefAssembly.lean` at `c46b860`; namespace kept as
`GppGwefAssembly`, so every declaration keeps its full name.

Source: Claude's GW-EF sheet, GPP-bridge
`MuseResearch/claude-code-gwef-sheet-refresh-2026-11-10.lean` (with the paper argument in
`MuseResearch/claude-code-note-2026-11-10-gwef-2-3-attack.md`, audited by Turbo in
`MuseResearch/turbo-note-2026-11-10-gwef-audit.md`). The sheet proved GW-EF-2 and reduced
`rh_of_arp` to one `sorry`, `gwef3_interpolation`. This file is item (H3) of Turbo's round-4
dictionary (`MuseResearch/round4-sign-flux-dictionary-2026-11-10.md`), ported on Turbo's
instruction (GPP-bridge PR #11, issuecomment-6783244755).

What is new relative to the sheet: `gwef3_interpolation` is **proved** here from the in-tree
density theorem (`GppGwefInterp.gaussian_annihilator` and
`GppGwefInterp.StripData.density_iff_annihilator`, PRs #553/#554), by approximating the
finitely supported vector `v` in the real Hilbert subspace and using continuity of the
quadratic form. The sheet's four named premises of `rh_of_arp` (GW-EF-1, polynomial zero
counting, zero-data symmetry, positive multiplicities) are all theorems in the tree, so
`rh_of_arp` below takes ARP as its **only** hypothesis.

* `gwef2_factorisation` — `Φ(f ⋆ f̃)(s) = Ψf(s) · Ψf(1 - s)` (Fubini + change of variables).
* `gwef2_pairing` — the same identity in pairing form, `conj Ψf(ιρ) · Ψf(ρ)`.
* `gwef3_interpolation` — every finitely supported, `ι`-closed, conjugation-symmetric datum
  is a limit of the zero-side quadratic form over test functions.
* `online_of_pairing_nonneg` — nonnegativity of that quadratic form forces `Re = 1/2`.
* `rh_of_arp` — now in `GwefAssembly.lean`, as `GppKernelTheory.rh_of_arp'`.

## Honest boundary

`rh_of_arp` is the converse direction of Weil's criterion: an implication with ARP as a
hypothesis. ARP is **not** proved anywhere in the tree, so nothing here proves RH. RH OPEN,
ARP OPEN. This file adds no `open_` stub and no axiom.

Daniel Toupin / Golden Physics Project, with AI assistance (Claude wrote the GW-EF sheet,
Codex the interpolation, Turbo audited both; Heart of the Cosmos / Grok ported and closed
`gwef3_interpolation` from the in-tree density theorem).
-/

open Complex MeasureTheory Filter
open GppMeyerSpectralWeil GppWeilCriterion GppArithmeticReflection GppGwefInterp
open scoped ContDiff

noncomputable section

namespace GppGwefAssembly

/-! ### GW-EF-2: the pairing factorisation -/

/-- **GW-EF-2 (factorisation).** `Φ(f ⋆ f̃)(s) = Ψf(s) · Ψf(1 - s)` for a test function `f`,
with `Ψ = spectralTransform` and `autocorr f x = ∫ f(y) f(y - x) dy`. Fubini on the compactly
supported continuous integrand, then the substitution `x = y - z`.

Sheet status: PROVED on the sheet (`GppGWEF.gwef2_factorisation`, Claude's GW-EF refresh,
GPP-bridge `ef462ed`); the statement here is the sheet's, verbatim. In tree: PROVED. -/
theorem gwef2_factorisation {f : ℝ → ℝ} (hf : IsTestFunction f) (s : ℂ) :
    spectralTransform (autocorr f) s = spectralTransform f s * spectralTransform f (1 - s) := by
  set c : ℂ := s - 1 / 2 with hc
  have hfc : Continuous f := hf.1.continuous
  let H : ℝ × ℝ → ℂ := fun p => (f p.2 : ℂ) * (f (p.2 - p.1) : ℂ) * Complex.exp (c * p.1)
  have hHc : Continuous H := by
    refine Continuous.mul (Continuous.mul ?_ ?_) ?_
    · exact Complex.continuous_ofReal.comp (hfc.comp continuous_snd)
    · exact Complex.continuous_ofReal.comp (hfc.comp (continuous_snd.sub continuous_fst))
    · exact Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst))
  have hHs : HasCompactSupport H := by
    have hK : IsCompact (tsupport f) := hf.2
    refine HasCompactSupport.intro
      ((hK.prod hK).image (show Continuous fun q : ℝ × ℝ => (q.2 - q.1, q.2) by fun_prop)) ?_
    intro p hp
    by_contra hne
    apply hp
    have h1 : f p.2 ≠ 0 := by
      intro h; apply hne; simp [H, h]
    have h2 : f (p.2 - p.1) ≠ 0 := by
      intro h; apply hne; simp [H, h]
    refine ⟨(p.2 - p.1, p.2), ⟨subset_tsupport f h2, subset_tsupport f h1⟩, ?_⟩
    simp
  have hHi : Integrable H (volume.prod volume) := hHc.integrable_of_hasCompactSupport hHs
  have hL : spectralTransform (autocorr f) s = ∫ x : ℝ, ∫ y : ℝ, H (x, y) := by
    unfold spectralTransform autocorr
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [H]
    rw [← integral_complex_ofReal, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    push_cast; ring
  rw [hL, integral_integral_swap hHi]
  set K : ℂ := ∫ z : ℝ, (f z : ℂ) * Complex.exp ((1 - s - 1 / 2) * z) with hK
  have hinner : ∀ y : ℝ, ∫ x : ℝ, H (x, y) = (f y : ℂ) * Complex.exp (c * y) * K := by
    intro y
    have h1 : ∀ x : ℝ, H (x, y) = (f y : ℂ) *
        ((fun z : ℝ => (f z : ℂ) * Complex.exp (c * ((y : ℂ) - z))) (y - x)) := by
      intro x
      simp only [H]
      push_cast
      have : (y : ℂ) - ((y : ℂ) - x) = x := by ring
      rw [this]; ring
    simp_rw [h1]
    rw [integral_const_mul, integral_sub_left_eq_self
      (fun z : ℝ => (f z : ℂ) * Complex.exp (c * ((y : ℂ) - z))) volume y]
    rw [hK]
    have : ∀ z : ℝ, (f z : ℂ) * Complex.exp (c * ((y : ℂ) - z)) =
        Complex.exp (c * y) * ((f z : ℂ) * Complex.exp ((1 - s - 1 / 2) * z)) := by
      intro z
      have e : c * ((y : ℂ) - z) = c * y + (1 - s - 1 / 2) * z := by rw [hc]; ring
      rw [e, Complex.exp_add]; ring
    simp_rw [this]
    rw [integral_const_mul]; ring
  simp_rw [hinner]
  rw [integral_mul_const]
  unfold spectralTransform
  rfl

/-- For real `f` the transform is conjugation-equivariant: `Ψf(s̄) = conj Ψf(s)`. -/
theorem spectralTransform_conj (f : ℝ → ℝ) (s : ℂ) :
    spectralTransform f ((starRingEnd ℂ) s) = (starRingEnd ℂ) (spectralTransform f s) :=
  GppGwefInterp.spectralTransform_conjugate f s

/-- **GW-EF-2 (pairing form).** At every `ρ`, `Φ(f ⋆ f̃)(ρ) = conj Ψf(ιρ) · Ψf(ρ)`, with
`ι ρ = 1 - ρ̄`: the summand of `pairedForm ι` with coefficients `c = Ψf`. -/
theorem gwef2_pairing {f : ℝ → ℝ} (hf : IsTestFunction f) (ρ : ℂ) :
    spectralTransform (autocorr f) ρ =
      (starRingEnd ℂ) (spectralTransform f (zetaInvolution ρ)) * spectralTransform f ρ := by
  rw [gwef2_factorisation hf, mul_comm, ← spectralTransform_conj]
  congr 2
  simp [zetaInvolution]

/-! ### GW-EF-3: interpolation, from the in-tree density theorem -/

/-- **GW-EF-3 (interpolation), bundled form.** For strip data `D`, every finitely supported,
`ι`-closed, conjugation-symmetric datum `v` is a limit of the zero-side quadratic form
`Q f = Σ_{ρ ∈ Z} m(ρ) Ψf(ρ) Ψf(1 - ρ)` over test functions. No point of `Z` is assumed to lie
on the line. Proof: `v` (cut off to `S`) is a vector of the real Hilbert subspace; the
spectral map has dense range there (`gaussian_annihilator`); the quadratic form is
continuous and agrees with `Q` on the range (`quadraticForm_spectralMap`). -/
theorem StripData.interpolation (D : StripData)
    (S : Finset ℂ) (hS : ↑S ⊆ D.Z) (hSι : ∀ ρ ∈ S, zetaInvolution ρ ∈ S)
    (v : ℂ → ℂ)
    (hv : ∀ ρ ∈ S, (starRingEnd ℂ) ρ ∈ S ∧ v ((starRingEnd ℂ) ρ) = (starRingEnd ℂ) (v ρ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : ℝ → ℝ, IsTestFunction f ∧
      ‖(∑' ρ : D.Z, (D.m ρ : ℂ) * (spectralTransform f ρ * spectralTransform f (1 - ρ))) -
        pairedForm zetaInvolution S v‖ < ε := by
  classical
  -- the target vector: `v` on `S`, zero elsewhere
  let u : D.Z → ℂ := fun ρ => if (ρ : ℂ) ∈ S then v ρ else 0
  have hfin : {ρ : D.Z | (ρ : ℂ) ∈ S}.Finite :=
    S.finite_toSet.preimage Subtype.val_injective.injOn
  have hmem : Memℓp u 2 := by
    apply (memℓp_gen_iff (p := 2) (by norm_num)).2
    apply summable_of_hasFiniteSupport
    refine hfin.subset fun ρ hρ => ?_
    by_contra h
    exact hρ (by simp [u, show (ρ : ℂ) ∉ S from h])
  let U : SpectralHilbert D.Z := ⟨u, hmem⟩
  have hUreal : U ∈ D.realSubspace := by
    intro ρ
    change u (D.conjugate ρ) = (starRingEnd ℂ) (u ρ)
    change (if (starRingEnd ℂ) (ρ : ℂ) ∈ S then v ((starRingEnd ℂ) ρ) else 0) =
      (starRingEnd ℂ) (if (ρ : ℂ) ∈ S then v ρ else 0)
    by_cases hρ : (ρ : ℂ) ∈ S
    · rw [if_pos (hv _ hρ).1, if_pos hρ, (hv _ hρ).2]
    · have hc : (starRingEnd ℂ) (ρ : ℂ) ∉ S := fun h => hρ (by simpa using (hv _ h).1)
      rw [if_neg hc, if_neg hρ, map_zero]
  let UR : D.realSubspace := ⟨U, hUreal⟩
  -- the quadratic form of `U` is the paired form
  have hQU : quadraticForm D.iota U = pairedForm zetaInvolution S v := by
    rw [quadraticForm_eq_tsum]
    let G : ℂ → ℂ := fun z => if z ∈ S then (starRingEnd ℂ) (v (zetaInvolution z)) * v z else 0
    have hterm : ∀ ρ : D.Z, (starRingEnd ℂ) (U (D.iota ρ)) * U ρ = G ρ := by
      intro ρ
      change (starRingEnd ℂ) (if zetaInvolution (ρ : ℂ) ∈ S then v (zetaInvolution ρ) else 0) *
        (if (ρ : ℂ) ∈ S then v ρ else 0) = G ρ
      by_cases hρ : (ρ : ℂ) ∈ S
      · simp [G, hρ, hSι _ hρ]
      · simp [G, hρ]
    have hsupp : Function.support G ⊆ D.Z := by
      intro z hz
      by_contra h
      apply hz
      have : z ∉ S := fun h' => h (hS h')
      simp [G, this]
    rw [show (fun ρ : D.Z => (starRingEnd ℂ) (U (D.iota ρ)) * U ρ) = fun ρ : D.Z => G ρ from
      funext hterm, tsum_subtype_eq_of_support_subset hsupp,
      tsum_eq_sum (s := S) (fun z hz => by simp [G, hz])]
    unfold pairedForm
    exact Finset.sum_congr rfl fun z hz => by simp [G, hz]
  -- density and continuity
  have hdense : DenseRange D.realSpectralMap :=
    (D.density_iff_annihilator).2 (gaussian_annihilator D)
  have hcont : Continuous fun x : D.realSubspace => quadraticForm D.iota (x : SpectralHilbert D.Z) :=
    (quadraticForm_continuous D.iota).comp continuous_subtype_val
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.1 hcont UR ε hε
  obtain ⟨f, hf⟩ := hdense.exists_dist_lt UR hδ
  refine ⟨f, f.property, ?_⟩
  have h := hball (D.realSpectralMap f) (by rw [dist_comm]; exact hf)
  rw [dist_eq_norm] at h
  have hQf : quadraticForm D.iota ((D.realSpectralMap f : D.realSubspace) : SpectralHilbert D.Z) =
      ∑' ρ : D.Z, (D.m ρ : ℂ) * (spectralTransform f ρ * spectralTransform f (1 - ρ)) :=
    D.quadraticForm_spectralMap f
  rw [hQf] at h
  rw [← hQU]
  exact h

/-- **GW-EF-3 (interpolation), the sheet's unbundled statement.** -/
theorem gwef3_interpolation
    (Z : Set ℂ) (m : ℂ → ℕ)
    (hloc : ∀ R : ℝ, {ρ ∈ Z | ‖ρ‖ ≤ R}.Finite)
    (hmpos : ∀ ρ ∈ Z, 1 ≤ m ρ)
    (hcount : ∃ N : ℕ, Summable (fun ρ : Z => (m ρ : ℝ) * ((1 + ‖(ρ : ℂ)‖) ^ N)⁻¹))
    (hstrip : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1)
    (hι : ∀ ρ ∈ Z, zetaInvolution ρ ∈ Z ∧ m (zetaInvolution ρ) = m ρ)
    (hconj : ∀ ρ ∈ Z, (starRingEnd ℂ) ρ ∈ Z ∧ m ((starRingEnd ℂ) ρ) = m ρ)
    (S : Finset ℂ) (hS : ↑S ⊆ Z) (hSι : ∀ ρ ∈ S, zetaInvolution ρ ∈ S)
    (v : ℂ → ℂ)
    (hv : ∀ ρ ∈ S, (starRingEnd ℂ) ρ ∈ S ∧ v ((starRingEnd ℂ) ρ) = (starRingEnd ℂ) (v ρ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : ℝ → ℝ, IsTestFunction f ∧
      ‖(∑' ρ : Z, (m ρ : ℂ) * (spectralTransform f ρ * spectralTransform f (1 - ρ))) -
        pairedForm zetaInvolution S v‖ < ε :=
  StripData.interpolation ⟨Z, m, hloc, hmpos, hcount, hstrip, hι, hconj⟩ S hS hSι v hv ε hε

/-! ### Positivity of the pairing forces the line -/

/-- **Positivity of the pairing forces the line (abstract form).** Same hypotheses on `Z`, `m`
as `gwef3_interpolation`. If `Σ_{ρ ∈ Z} m(ρ) Ψf(ρ) Ψf(1 - ρ)` has nonnegative real part for
every test function `f`, then every point of `Z` has real part `1/2`. The witness datum is
`+1` on `Re = Re ρ₀`, `-1` on `Re = 1 - Re ρ₀`, supported on the quartet of `ρ₀`, whose paired
form is `-#S ≤ -2`. -/
theorem online_of_pairing_nonneg
    (Z : Set ℂ) (m : ℂ → ℕ)
    (hloc : ∀ R : ℝ, {ρ ∈ Z | ‖ρ‖ ≤ R}.Finite)
    (hmpos : ∀ ρ ∈ Z, 1 ≤ m ρ)
    (hcount : ∃ N : ℕ, Summable (fun ρ : Z => (m ρ : ℝ) * ((1 + ‖(ρ : ℂ)‖) ^ N)⁻¹))
    (hstrip : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1)
    (hι : ∀ ρ ∈ Z, zetaInvolution ρ ∈ Z ∧ m (zetaInvolution ρ) = m ρ)
    (hconj : ∀ ρ ∈ Z, (starRingEnd ℂ) ρ ∈ Z ∧ m ((starRingEnd ℂ) ρ) = m ρ)
    (hpos : ∀ f : ℝ → ℝ, IsTestFunction f →
      0 ≤ (∑' ρ : Z, (m ρ : ℂ) * (spectralTransform f ρ * spectralTransform f (1 - ρ))).re) :
    ∀ ρ ∈ Z, ρ.re = 1 / 2 := by
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
  have hι0 : zetaInvolution ρ₀ ∈ Z := (hι ρ₀ hρ₀).1
  have hc0 : (starRingEnd ℂ) ρ₀ ∈ Z := (hconj ρ₀ hρ₀).1
  have hιc0 : zetaInvolution ((starRingEnd ℂ) ρ₀) ∈ Z := (hι _ hc0).1
  have hSZ : ↑S ⊆ Z := by
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
  obtain ⟨f, hf, hlt⟩ := gwef3_interpolation Z m hloc hmpos hcount hstrip hι hconj S hSZ hSι v
    (fun ρ hρ => hSconj ρ hρ) 1 one_pos
  have h0 := hpos f hf
  rw [hpf] at hlt
  have hre : (-(S.card : ℂ)).re = -(S.card : ℝ) := by simp
  have hcardR : (2 : ℝ) ≤ S.card := by exact_mod_cast hcard
  have h1 := (Complex.abs_re_le_norm _).trans_lt hlt
  have h2 := abs_lt.1 h1
  simp only [Complex.sub_re, hre] at h2
  linarith [h2.2]

end GppGwefAssembly
