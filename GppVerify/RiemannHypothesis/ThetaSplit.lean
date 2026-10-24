import GppVerify.RiemannHypothesis.RiemannPhi

/-!
# The theta split of Λ and the two-wave form of ξ

Source: Astra, `work/2026-10-24_astra_phi_halfwave_boundary_identity.md` (GPP-bridge `fb8d916`;
PR #11 comment 6379118669). Daniel Toupin / Golden Physics Project, with AI assistance from Astra
(statement) and Claude Code (formalization).

Write `ψ(x) = ∑_{n≥1} e^{−πn²x}` (`GppRiemannPhi.psi`) and `I(s) = ∫₁^∞ ψ(x) x^{s/2−1} dx`.

* `completedRiemannZeta₀_eq_split`: **Riemann's split**, for every `s ∈ ℂ`,
  `Λ₀(s) = I(s) + I(1 − s)`, where `Λ₀(s) = Λ(s) + 1/s + 1/(1 − s)` is Mathlib's entire
  `completedRiemannZeta₀`. The proof uses Mathlib's own definition of `Λ₀` as the Mellin transform
  of the modified theta kernel, so it holds on all of `ℂ` with no analytic continuation step.
* `completedRiemannZeta_eq_split`: `Λ(s) = I(s) + I(1 − s) − 1/s − 1/(1 − s)`.
* `halfWave`: `B(s) = 1/4 + (s − 1/2) ψ(1) + s(s − 1) I(s)/2`. This is the right-hand side of
  Astra's half-wave boundary identity `A(s − 1/2) = B(s)`.
* `halfWave_add_reflect`: `B(s) + B(1 − s) = 1/2 + s(s − 1) Λ₀(s)/2` for every `s`.
* `halfWave_add_reflect_eq_xi`: for `s ≠ 0, 1`, `B(s) + B(1 − s) = s(s − 1) Λ(s)/2 = ξ(s)`.

**Scope.** The identification `A(s − 1/2) = B(s)` with Astra's
`A(z) = 4∫₀^∞ Φ(u) e^{2zu} du` (two integrations by parts and `θ′(1) = −θ(1)/4`) is not
formalized here. Neither is the endpoint expansion of `A(it)`. Classical identity, not claimed
novel. Nothing here bears on the location of the zeros. No claim about RH.
-/

open Real Complex HurwitzZeta MeasureTheory Set GppRiemannPhi

namespace GppThetaSplit

/-- `I(s) = ∫₁^∞ ψ(x) x^{s/2−1} dx`. -/
noncomputable def I (s : ℂ) : ℂ := ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (s / 2 - 1) * psi x

/-- The modified theta kernel behind Mathlib's `Λ₀`. -/
noncomputable abbrev fm : ℝ → ℂ := (hurwitzEvenFEPair 0).f_modif

lemma mellinConvergent_fm (w : ℂ) : MellinConvergent fm w :=
  ((hurwitzEvenFEPair 0).isStrongFEPair_toStrongFEPair.hasMellin w).1

lemma mellinConvergent_indicator {S : Set ℝ} (hS : MeasurableSet S) (w : ℂ) :
    MellinConvergent (S.indicator fm) w := by
  have h : (fun t : ℝ => (t : ℂ) ^ (w - 1) • S.indicator fm t) =
      S.indicator (fun t : ℝ => (t : ℂ) ^ (w - 1) • fm t) := by
    ext t; by_cases ht : t ∈ S <;> simp [ht]
  unfold MellinConvergent
  rw [h]
  exact (mellinConvergent_fm w).indicator hS

lemma fm_of_one_lt {x : ℝ} (hx : 1 < x) : fm x = 2 * (psi x : ℂ) := by
  simp only [fm, WeakFEPair.f_modif, Pi.add_apply, indicator_of_mem (mem_Ioi.mpr hx),
    indicator_of_notMem (notMem_Ioo_of_ge hx.le), add_zero]
  change (evenKernel 0 x : ℂ) - (if (0 : UnitAddCircle) = 0 then 1 else 0) = _
  rw [if_pos rfl, ← one_add_two_mul_psi (by linarith)]
  push_cast; ring

lemma fm_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    fm x = (x : ℂ) ^ (-1 / 2 : ℂ) * (2 * (psi x⁻¹ : ℂ)) := by
  simp only [fm, WeakFEPair.f_modif, Pi.add_apply, indicator_of_mem hx,
    indicator_of_notMem (notMem_Ioi.mpr hx.2.le), zero_add]
  change (evenKernel 0 x : ℂ) - ((1 : ℂ) * ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (1 : ℂ) = _
  have hx0 := hx.1
  have hfe := psi_functional_equation hx0
  rw [← one_add_two_mul_psi hx0, smul_eq_mul, mul_one, one_mul,
    ofReal_cpow hx0.le, ← one_div x]
  have hc : (x : ℂ) ^ (-1 / 2 : ℂ) = ((1 / x ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [one_div, ofReal_inv, ofReal_cpow hx0.le, ← cpow_neg]; congr 1; push_cast; ring
  rw [hc, show ((-(1 / 2 : ℝ) : ℝ) : ℂ) = (-1 / 2 : ℂ) by push_cast; ring, hc]
  have hfe' : ((1 + 2 * psi x : ℝ) : ℂ) = ((1 / x ^ (1 / 2 : ℝ) * (1 + 2 * psi (1 / x)) : ℝ) : ℂ) :=
    congrArg _ hfe
  push_cast at hfe' ⊢
  rw [hfe']; ring

lemma fm_split : fm = (Ioi 1).indicator fm + (Ioo 0 1).indicator fm := by
  ext x
  rcases lt_or_ge 1 x with h1 | h1
  · simp [indicator_of_mem (mem_Ioi.mpr h1), notMem_Ioo_of_ge h1.le]
  rcases lt_or_ge 0 x with h0 | h0
  · rcases h1.lt_or_eq with h1 | rfl
    · simp [indicator_of_mem (mem_Ioo.mpr ⟨h0, h1⟩), not_lt.mpr h1.le]
    · simp [fm, WeakFEPair.f_modif]
  · have : x ∉ Ioo (0 : ℝ) 1 := fun h => absurd h.1 (not_lt.mpr h0)
    simp [fm, WeakFEPair.f_modif, this, not_lt.mpr (h0.trans zero_le_one)]

/-- The tail piece is `2I`. -/
lemma mellin_tail (w : ℂ) :
    mellin ((Ioi 1).indicator fm) w = 2 * ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (w - 1) * psi x := by
  have h : (fun t : ℝ => (t : ℂ) ^ (w - 1) • (Ioi 1).indicator fm t) =
      (Ioi 1).indicator (fun t : ℝ => (t : ℂ) ^ (w - 1) • fm t) := by
    ext t; by_cases ht : t ∈ Ioi (1 : ℝ) <;> simp [ht]
  unfold mellin
  rw [h, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, sup_of_le_right zero_le_one,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [smul_eq_mul, fm_of_one_lt ht]
  ring

/-- The `(0, 1)` piece is the tail piece reflected by `x ↦ 1/x`. -/
lemma mellin_head (w : ℂ) :
    mellin ((Ioo 0 1).indicator fm) w = mellin ((Ioi 1).indicator fm) (1 / 2 - w) := by
  have h : mellin ((Ioo 0 1).indicator fm) w =
      mellin (fun t : ℝ => (t : ℂ) ^ (-1 / 2 : ℂ) • (Ioi 1).indicator fm t⁻¹) w := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    congr 1
    beta_reduce
    rcases lt_or_ge t 1 with h1 | h1
    · have hinv : 1 < t⁻¹ := (one_lt_inv₀ ht).mpr h1
      rw [indicator_of_mem (mem_Ioo.mpr ⟨ht, h1⟩), indicator_of_mem (mem_Ioi.mpr hinv),
        fm_of_mem_Ioo ⟨ht, h1⟩, fm_of_one_lt hinv, smul_eq_mul]
    · have hinv : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
      rw [indicator_of_notMem (notMem_Ioo_of_ge h1), indicator_of_notMem (notMem_Ioi.mpr hinv),
        smul_zero]
  rw [h, mellin_cpow_smul, mellin_comp_inv]
  congr 1; ring

/-- **Riemann's split.** For every `s ∈ ℂ`, `Λ₀(s) = I(s) + I(1 − s)`. -/
theorem completedRiemannZeta₀_eq_split (s : ℂ) : completedRiemannZeta₀ s = I s + I (1 - s) := by
  have hadd := hasMellin_add
    (mellinConvergent_indicator (S := Ioi (1 : ℝ)) measurableSet_Ioi (s / 2))
    (mellinConvergent_indicator (S := Ioo (0 : ℝ) 1) measurableSet_Ioo (s / 2))
  have hΛ : completedRiemannZeta₀ s = mellin fm (s / 2) / 2 := rfl
  rw [hΛ]
  conv_lhs => rw [fm_split]
  rw [show ((Ioi 1).indicator fm + (Ioo 0 1).indicator fm) =
      fun t => (Ioi 1).indicator fm t + (Ioo 0 1).indicator fm t from rfl, hadd.2,
    mellin_head, mellin_tail, mellin_tail, I, I]
  have e2 : 1 / 2 - s / 2 - 1 = (1 - s) / 2 - 1 := by ring
  rw [e2]; ring

/-- `Λ(s) = I(s) + I(1 − s) − 1/s − 1/(1 − s)`. -/
theorem completedRiemannZeta_eq_split (s : ℂ) :
    completedRiemannZeta s = I s + I (1 - s) - 1 / s - 1 / (1 - s) := by
  rw [completedRiemannZeta_eq, completedRiemannZeta₀_eq_split]

/-- The half-wave `B(s) = 1/4 + (s − 1/2) ψ(1) + s(s − 1) I(s)/2`. -/
noncomputable def halfWave (s : ℂ) : ℂ := 1 / 4 + (s - 1 / 2) * psi 1 + s * (s - 1) * I s / 2

/-- **Two-wave form, entire version.** `B(s) + B(1 − s) = 1/2 + s(s − 1) Λ₀(s)/2`. -/
theorem halfWave_add_reflect (s : ℂ) :
    halfWave s + halfWave (1 - s) = 1 / 2 + s * (s - 1) * completedRiemannZeta₀ s / 2 := by
  rw [completedRiemannZeta₀_eq_split, halfWave, halfWave]
  ring

/-- **Two-wave form of ξ.** For `s ≠ 0, 1`, `B(s) + B(1 − s) = s(s − 1) Λ(s)/2`. -/
theorem halfWave_add_reflect_eq_xi {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    halfWave s + halfWave (1 - s) = s * (s - 1) * completedRiemannZeta s / 2 := by
  have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  rw [halfWave_add_reflect, completedRiemannZeta_eq]
  field_simp
  ring

end GppThetaSplit
