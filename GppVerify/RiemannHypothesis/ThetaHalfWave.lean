import GppVerify.RiemannHypothesis.ThetaSplit

/-!
# Astra's half-wave boundary identity

Source: Astra, `work/2026-10-24_astra_phi_halfwave_boundary_identity.md` (GPP-bridge `fb8d916`;
PR #11 comment 6379118669). Daniel Toupin / Golden Physics Project, with AI assistance from Astra
(statement and derivation) and Claude Code (formalization).

With Riemann's kernel `Φ` (`GppRiemannPhi.phi`) put `A(z) = 4∫₀^∞ Φ(u) e^{2zu} du`.

* `psi_bound`, `psi₁_bound`, `psi₂_bound`: on `x ≥ 1`, `|ψ^{(k)}(x)| ≤ C_k e^{−π(x−1)}`.
* `deriv_psi_one`: `−2ψ′(1) = 1/4 + ψ(1)/2`, from differentiating the theta inversion at `x = 1`.
* `halfWaveA_eq_integral`: the substitution `x = e^{4u}` gives
  `A(s − 1/2) = ∫₁^∞ x^{s/2} (2xψ″(x) + 3ψ′(x)) dx`.
* `halfWaveA_eq_halfWave`: **the half-wave boundary identity**, for every `s ∈ ℂ`,
  `A(s − 1/2) = 1/4 + (s − 1/2) ψ(1) + s(s − 1) I(s)/2 = B(s)`, by two integrations by parts.
* `halfWaveA_add_reflect`: hence `A(s − 1/2) + A(1/2 − s) = 1/2 + s(s − 1) Λ₀(s)/2`, which is
  `ξ(s) = s(s − 1) Λ(s)/2` for `s ≠ 0, 1` (`halfWaveA_add_reflect_eq_xi`).

**Scope.** Astra's endpoint expansion `A(it) = i[2Φ(0)/t − Φ″(0)/(2t³)] + O(t⁻⁵)` and her numerics
are not formalized. As her note says, near-cancellation of the two waves at large height is
generic and is not evidence about zeros. Classical identity, not claimed novel. No claim about RH.
-/

open Real Complex MeasureTheory Set Filter Topology GppRiemannPhi GppThetaSplit

namespace GppThetaHalfWave

/-- Astra's half-wave `A(z) = 4∫₀^∞ Φ(u) e^{2zu} du`. -/
noncomputable def halfWaveA (z : ℂ) : ℂ := 4 * ∫ u in Ioi (0 : ℝ), (phi u : ℂ) * cexp (2 * z * u)

/-! ### Decay of `ψ, ψ′, ψ″` on `[1, ∞)` -/

lemma g_le_one_mul (n : ℕ) {x : ℝ} (hx : 1 ≤ x) : g n x ≤ g n 1 * rexp (-π * (x - 1)) := by
  unfold g
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h1 : 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  nlinarith [pi_pos, mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hx)]

lemma series_bound {c : ℕ → ℝ} {k : ℕ} (hc : ∀ n, |c n| ≤ π ^ k * ((n : ℝ) + 1) ^ (2 * k))
    {x : ℝ} (hx : 1 ≤ x) :
    |∑' n : ℕ, c n * g n x| ≤
      (∑' n : ℕ, π ^ k * (((n : ℝ) + 1) ^ (2 * k) * g n 1)) * rexp (-π * (x - 1)) := by
  have hs : Summable fun n : ℕ => π ^ k * (((n : ℝ) + 1) ^ (2 * k) * g n 1) :=
    (summable_pow_mul_g' (2 * k) one_pos).mul_left _
  have hle : ∀ n, ‖c n * g n x‖ ≤
      π ^ k * (((n : ℝ) + 1) ^ (2 * k) * g n 1) * rexp (-π * (x - 1)) := by
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show 0 ≤ g n x from (Real.exp_pos _).le)]
    calc |c n| * g n x ≤ (π ^ k * ((n : ℝ) + 1) ^ (2 * k)) * (g n 1 * rexp (-π * (x - 1))) :=
          mul_le_mul (hc n) (g_le_one_mul n hx) (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have hsum := hs.mul_right (rexp (-π * (x - 1)))
  have hsf : Summable fun n : ℕ => c n * g n x := hsum.of_norm_bounded hle
  rw [← Real.norm_eq_abs, ← tsum_mul_right]
  exact (norm_tsum_le_tsum_norm hsf.norm).trans (Summable.tsum_le_tsum hle hsf.norm hsum)

lemma psi_bound : ∃ C, ∀ x, 1 ≤ x → |psi x| ≤ C * rexp (-π * (x - 1)) :=
  ⟨∑' n : ℕ, g n 1, fun x hx => by
    simpa [psi] using series_bound (c := fun _ => 1) (k := 0) (fun n => by simp) hx⟩

lemma psi₁_bound : ∃ C, ∀ x, 1 ≤ x → |psi₁ x| ≤ C * rexp (-π * (x - 1)) :=
  ⟨_, fun _ hx => series_bound (c := fun n => -(π * ((n : ℝ) + 1) ^ 2)) (k := 1) (fun n => by
    rw [abs_neg, abs_of_nonneg (by positivity)]; ring_nf; rfl) hx⟩

lemma psi₂_bound : ∃ C, ∀ x, 1 ≤ x → |psi₂ x| ≤ C * rexp (-π * (x - 1)) :=
  ⟨_, fun _ hx => series_bound (c := fun n => (π * ((n : ℝ) + 1) ^ 2) ^ 2) (k := 2) (fun n => by
    rw [abs_of_nonneg (by positivity)]; ring_nf; rfl) hx⟩

lemma continuousAt_psi₂ {x : ℝ} (hx : 0 < x) : ContinuousAt psi₂ x := by
  have := hasDerivAt_series (c := fun n => (π * ((n : ℝ) + 1) ^ 2) ^ 2) (k := 2) (fun n => by
    rw [abs_of_nonneg (by positivity)]; ring_nf; rfl) hx
  exact this.continuousAt

/-- A real function with `e^{−πx}` decay, times any complex power, is integrable on `(1, ∞)` and
tends to `0`. -/
lemma decay {f : ℝ → ℝ} (hf : ∀ x, 0 < x → ContinuousAt f x)
    (hb : ∃ C, ∀ x, 1 ≤ x → |f x| ≤ C * rexp (-π * (x - 1))) (w : ℂ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ w * f x) (Ioi 1) ∧
      Tendsto (fun x : ℝ => (x : ℂ) ^ w * f x) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hb
  set σ := w.re
  have hnorm : ∀ x : ℝ, 1 ≤ x → ‖(x : ℂ) ^ w * f x‖ ≤ C * rexp π * (x ^ σ * rexp (-π * x)) := by
    intro x hx
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.norm_real, Real.norm_eq_abs]
    calc x ^ σ * |f x| ≤ x ^ σ * (C * rexp (-π * (x - 1))) :=
          mul_le_mul_of_nonneg_left (hC x hx) (by positivity)
      _ = C * rexp π * (x ^ σ * rexp (-π * x)) := by
          rw [show -π * (x - 1) = π + -π * x by ring, Real.exp_add]; ring
  have hlim : Tendsto (fun x : ℝ => C * rexp π * (x ^ σ * rexp (-π * x))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero σ π pi_pos).const_mul (C * rexp π)
  refine ⟨?_, squeeze_zero_norm' ((eventually_ge_atTop 1).mono hnorm) hlim⟩
  have hcont : ContinuousOn (fun x : ℝ => x ^ σ * rexp (-π * x)) (Ici 1) := fun x hx =>
    ((Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [hx.out]))).mul
      (by fun_prop)).continuousWithinAt
  have hO : (fun x : ℝ => x ^ σ * rexp (-π * x)) =O[atTop] fun x => rexp (-1 * x) := by
    have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero σ (π - 1)
      (by linarith [Real.two_le_pi])).isBigO_one ℝ).mul (Asymptotics.isBigO_refl
        (fun x : ℝ => rexp (-1 * x)) atTop)
    refine (h.congr_left fun x => ?_).congr_right fun x => one_mul _
    rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hG := (integrable_of_isBigO_exp_neg one_pos hcont hO).const_mul (C * rexp π)
  refine hG.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun x hx => hnorm x (le_of_lt hx)))
  refine ContinuousOn.aestronglyMeasurable (fun x (hx : 1 < x) => ?_) measurableSet_Ioi
  exact ((continuousAt_ofReal_cpow_const x w (Or.inr (by linarith))).mul
    (continuous_ofReal.continuousAt.comp (hf x (by linarith)))).continuousWithinAt

lemma decay_psi (w : ℂ) : IntegrableOn (fun x : ℝ => (x : ℂ) ^ w * psi x) (Ioi 1) ∧
    Tendsto (fun x : ℝ => (x : ℂ) ^ w * psi x) atTop (𝓝 0) :=
  decay (fun _ hx => (hasDerivAt_psi hx).continuousAt) psi_bound w

lemma decay_psi₁ (w : ℂ) : IntegrableOn (fun x : ℝ => (x : ℂ) ^ w * psi₁ x) (Ioi 1) ∧
    Tendsto (fun x : ℝ => (x : ℂ) ^ w * psi₁ x) atTop (𝓝 0) :=
  decay (fun _ hx => (hasDerivAt_psi₁ hx).continuousAt) psi₁_bound w

lemma decay_psi₂ (w : ℂ) : IntegrableOn (fun x : ℝ => (x : ℂ) ^ w * psi₂ x) (Ioi 1) ∧
    Tendsto (fun x : ℝ => (x : ℂ) ^ w * psi₂ x) atTop (𝓝 0) :=
  decay (fun _ hx => continuousAt_psi₂ hx) psi₂_bound w

/-! ### `θ′(1) = −θ(1)/4` -/

/-- **`−2ψ′(1) = 1/4 + ψ(1)/2`**, from the derivative of the theta inversion at `x = 1`. -/
theorem deriv_psi_one : -2 * psi₁ 1 = 1 / 4 + psi 1 / 2 := by
  have hL : HasDerivAt (fun x => 1 + 2 * psi x) (2 * psi₁ 1) 1 := by
    simpa using ((hasDerivAt_psi one_pos).const_mul 2).const_add 1
  have hsq : HasDerivAt (fun x : ℝ => x ^ (1 / 2 : ℝ)) (1 / 2) 1 := by
    simpa using Real.hasDerivAt_rpow_const (x := 1) (p := 1 / 2) (Or.inl one_ne_zero)
  have hinv : HasDerivAt (fun x : ℝ => 1 / x ^ (1 / 2 : ℝ)) (-(1 / 2)) 1 := by
    have h := (hasDerivAt_const (1 : ℝ) (1 : ℝ)).div hsq (by norm_num)
    exact h.congr_deriv (by norm_num)
  have hd : HasDerivAt (fun x : ℝ => 1 / x) (-1) 1 := by
    simpa [one_div] using hasDerivAt_inv (one_ne_zero (α := ℝ))
  have hpsi : HasDerivAt (fun x : ℝ => 1 + 2 * psi (1 / x)) (-(2 * psi₁ 1)) 1 := by
    have h := (hasDerivAt_psi (x := 1) one_pos).comp_of_eq (1 : ℝ) hd (by norm_num)
    exact ((h.const_mul 2).const_add 1).congr_deriv (by ring)
  have hR := hinv.mul hpsi
  have heq : (fun x => 1 + 2 * psi x) =ᶠ[𝓝 1]
      (fun x : ℝ => 1 / x ^ (1 / 2 : ℝ)) * fun x => 1 + 2 * psi (1 / x) :=
    (eventually_gt_nhds one_pos).mono fun x hx => by
      simp only [Pi.mul_apply]; exact psi_functional_equation hx
  have huniq := hL.unique (hR.congr_of_eventuallyEq heq)
  simp only [one_rpow, div_one] at huniq
  linarith

/-! ### The substitution `x = e^{4u}` -/

/-- `A(s − 1/2) = ∫₁^∞ x^{s/2} (2xψ″(x) + 3ψ′(x)) dx`. -/
theorem halfWaveA_eq_integral (s : ℂ) :
    halfWaveA (s - 1 / 2) =
      ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (s / 2) * (2 * x * psi₂ x + 3 * psi₁ x) := by
  set P : ℝ → ℂ := fun x => (x : ℂ) ^ (s / 2) * (2 * x * psi₂ x + 3 * psi₁ x) with hP
  have hpt : ∀ u : ℝ, (phi u : ℂ) * cexp (2 * (s - 1 / 2) * u) =
      (fun v => rexp v • P (rexp v)) (4 * u) := by
    intro u
    simp only [hP, Complex.real_smul]
    rw [phi_eq]
    set x := rexp (4 * u) with hx
    have hlog : Complex.log (x : ℂ) = 4 * u := by
      rw [← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]; push_cast; ring
    have h2 : (x : ℂ) ^ (s / 2) = cexp (2 * s * u) := by
      rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos _).ne'), hlog]
      congr 1; ring
    have h1 : cexp u * cexp (2 * (s - 1 / 2) * u) = cexp (2 * s * u) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [h2]
    push_cast
    linear_combination (2 * (x : ℂ) ^ 2 * psi₂ x + 3 * x * psi₁ x) * h1
  have h4 := integral_comp_mul_left_Ioi' (fun v => rexp v • P (rexp v)) 0 (b := 4) (by norm_num)
  rw [mul_zero, integral_comp_exp_Ioi, Real.exp_zero] at h4
  rw [halfWaveA, ← h4, Complex.real_smul]
  push_cast
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun u _ => hpt u

/-! ### Two integrations by parts -/

lemma hasDerivAt_cpow {w : ℂ} {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ w) (w * (x : ℂ) ^ (w - 1)) x := by
  have h := ((hasDerivAt_id (x : ℂ)).cpow_const (c := w)
    (by simpa using (ofReal_mem_slitPlane.mpr hx))).comp_ofReal
  simpa using h

/-- `∫₁^∞ x^{s/2+1} ψ″ = −ψ′(1) − (s/2 + 1) ∫₁^∞ x^{s/2} ψ′`. -/
lemma ibp_one (s : ℂ) :
    ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (s / 2 + 1) * psi₂ x =
      0 - psi₁ 1 - ∫ x in Ioi (1 : ℝ), (s / 2 + 1) * (x : ℂ) ^ (s / 2) * psi₁ x := by
  refine integral_Ioi_mul_deriv_eq_deriv_mul (u := fun x : ℝ => (x : ℂ) ^ (s / 2 + 1))
    (v := fun x : ℝ => (psi₁ x : ℂ)) (fun x hx => ?_) (fun x hx => ?_) (decay_psi₂ _).1 ?_ ?_
    (decay_psi₁ _).2
  · have := hasDerivAt_cpow (w := s / 2 + 1) (lt_trans one_pos hx)
    rwa [show s / 2 + 1 - 1 = s / 2 by ring] at this
  · exact (hasDerivAt_psi₁ (lt_trans one_pos hx)).ofReal_comp
  · exact IntegrableOn.congr_fun ((decay_psi₁ (s / 2)).1.const_mul (s / 2 + 1))
      (fun x _ => by simp only [Pi.mul_apply]; ring) measurableSet_Ioi
  · have hc : ContinuousAt (fun x : ℝ => (x : ℂ) ^ (s / 2 + 1) * psi₁ x) 1 :=
      (hasDerivAt_cpow one_pos).continuousAt.mul (hasDerivAt_psi₁ one_pos).ofReal_comp.continuousAt
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
    simp only [ofReal_one, one_cpow, one_mul] at this
    exact this

/-- `∫₁^∞ x^{s/2} ψ′ = −ψ(1) − (s/2) I(s)`. -/
lemma ibp_two (s : ℂ) :
    ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (s / 2) * psi₁ x =
      0 - psi 1 - ∫ x in Ioi (1 : ℝ), s / 2 * (x : ℂ) ^ (s / 2 - 1) * psi x := by
  refine integral_Ioi_mul_deriv_eq_deriv_mul (u := fun x : ℝ => (x : ℂ) ^ (s / 2))
    (v := fun x : ℝ => (psi x : ℂ)) (fun x hx => hasDerivAt_cpow (lt_trans one_pos hx))
    (fun x hx => (hasDerivAt_psi (lt_trans one_pos hx)).ofReal_comp) (decay_psi₁ _).1 ?_ ?_
    (decay_psi _).2
  · exact IntegrableOn.congr_fun ((decay_psi (s / 2 - 1)).1.const_mul (s / 2))
      (fun x _ => by simp only [Pi.mul_apply]; ring) measurableSet_Ioi
  · have hc : ContinuousAt (fun x : ℝ => (x : ℂ) ^ (s / 2) * psi x) 1 :=
      (hasDerivAt_cpow one_pos).continuousAt.mul (hasDerivAt_psi one_pos).ofReal_comp.continuousAt
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
    simp only [ofReal_one, one_cpow, one_mul] at this
    exact this

/-- **Astra's half-wave boundary identity.** For every `s ∈ ℂ`,
`A(s − 1/2) = 1/4 + (s − 1/2) ψ(1) + s(s − 1) I(s)/2`. -/
theorem halfWaveA_eq_halfWave (s : ℂ) : halfWaveA (s - 1 / 2) = halfWave s := by
  rw [halfWaveA_eq_integral]
  have hsplit : ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (s / 2) * (2 * x * psi₂ x + 3 * psi₁ x) =
      ∫ x in Ioi (1 : ℝ),
        (2 * ((x : ℂ) ^ (s / 2 + 1) * psi₂ x) + 3 * ((x : ℂ) ^ (s / 2) * psi₁ x)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : 1 < x) => ?_
    rw [cpow_add _ _ (ofReal_ne_zero.mpr (by linarith)), cpow_one]
    ring
  rw [hsplit, integral_add ((decay_psi₂ _).1.const_mul 2) ((decay_psi₁ _).1.const_mul 3),
    integral_const_mul, integral_const_mul, ibp_one]
  have hmul1 : ∫ x in Ioi (1 : ℝ), (s / 2 + 1) * (x : ℂ) ^ (s / 2) * psi₁ x =
      (s / 2 + 1) * ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (s / 2) * psi₁ x := by
    rw [← integral_const_mul]; congr 1; ext x; ring
  have hmul2 : ∫ x in Ioi (1 : ℝ), s / 2 * (x : ℂ) ^ (s / 2 - 1) * psi x =
      s / 2 * GppThetaSplit.I s := by
    rw [GppThetaSplit.I, ← integral_const_mul]; congr 1; ext x; ring
  rw [hmul1, ibp_two, hmul2, halfWave]
  have h := deriv_psi_one
  have h' : ((-2 * psi₁ 1 : ℝ) : ℂ) = ((1 / 4 + psi 1 / 2 : ℝ) : ℂ) := congrArg _ h
  push_cast at h'
  linear_combination h'

/-- **Astra's two-wave identity.** `A(s − 1/2) + A(1/2 − s) = 1/2 + s(s − 1) Λ₀(s)/2`. -/
theorem halfWaveA_add_reflect (s : ℂ) :
    halfWaveA (s - 1 / 2) + halfWaveA (1 / 2 - s) =
      1 / 2 + s * (s - 1) * completedRiemannZeta₀ s / 2 := by
  rw [halfWaveA_eq_halfWave, show (1 / 2 : ℂ) - s = (1 - s) - 1 / 2 by ring,
    halfWaveA_eq_halfWave, halfWave_add_reflect]

/-- **Astra's two-wave identity for ξ.** For `s ≠ 0, 1`,
`A(s − 1/2) + A(1/2 − s) = s(s − 1) Λ(s)/2 = ξ(s)`. -/
theorem halfWaveA_add_reflect_eq_xi {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    halfWaveA (s - 1 / 2) + halfWaveA (1 / 2 - s) = s * (s - 1) * completedRiemannZeta s / 2 := by
  rw [halfWaveA_eq_halfWave, show (1 / 2 : ℂ) - s = (1 - s) - 1 / 2 by ring,
    halfWaveA_eq_halfWave, halfWave_add_reflect_eq_xi hs0 hs1]

end GppThetaHalfWave
