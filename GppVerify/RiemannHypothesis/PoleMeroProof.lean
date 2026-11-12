/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Heart of the Cosmos (Grok, GPPDiscovery5 seat). Turbo PR #11 6830680258, "next exact
instruction": `PoleMero` first, then the first two `ExpLaplaceMero` inputs.

# `PoleMero` PROVED; `ExpLaplaceMero` inputs

1. **Exported finiteness (PROVED).** `nontrivialZeros_ball_finite` is the local `hZfin` of
   `GppXiZeroCounting.zeroCountingPolynomial`, restated verbatim as a standalone theorem
   (`zeroCountingPolynomial` itself is not edited; its statement is unchanged).
   `zgamma_ball_finite : {γ ∈ Zgamma : ‖γ‖ ≤ T}.Finite` follows by `ρ = 1/2 + iγ`
   (`rho` injective, `‖ρ‖ ≤ 1/2 + ‖γ‖`); `zgamma_ball_finite'` is the subtype form.
2. **`PoleMero` PROVED as stated** (`IdentityStepSplit.PoleMero`, not widened). Take
   `F s := Σ_γ m_γ a(γ)/(s − iγ)` (the pole sum itself, so equality on `Re s > 1/2` is `rfl`).
   Near any `z₀`, split off the finite set `S z₀ δ = {γ : ‖γ‖ ≤ ‖z₀‖ + 2δ}`; off it every pole is
   at distance `> δ` from `B(z₀, δ)` (`far`), so the tail is holomorphic on the ball by
   `Complex.differentiableOn_tsum_of_summable_norm` with dominator `‖m_γ a(γ)‖/δ`
   (`tail_analyticAt`), and `F = finite part + tail` on the ball (`decomp`). Hence
   `MeromorphicAt F z₀` (`MeromorphicAt.fun_sum`, `.add`, `.congr`), and at a lower zero `γ₀`
   the remaining finite terms have poles `iγ ≠ iγ₀`, so `g := (finite part without γ₀) + tail`
   is analytic at `iγ₀` and `F = g + m_{γ₀} a(γ₀)/(s − iγ₀)` on `B(iγ₀, 1)`.
3. **`ExpLaplaceMero` inputs.** `integral_mul_cexp_Ioi : ∫_{(0,∞)} d e^{zd} dd = 1/z²` for
   `Re z < 0` is PROVED (integration by parts against `integral_exp_mul_complex_Ioi`). The
   coefficient-vanishing lemma is stated as the named Prop `CoeffVanish` (NOT proved, no proof
   attempted in this step). `ExpLaplaceMero` itself is untouched and not yet assembled.

Chain: `IdentityStep ⇐ ExpLaplaceMero` (`identityStep_of_expLaplaceMero`), so the fine chain is
`HPsiExpChain : HPsi → KreinDecomp → ExpLaplaceMero → RH`. `KreinDecomp`, `HPsi` untouched.
No converse claimed. H_ψ: OPEN. ARP: OPEN. RH: OPEN.
-/
import GppVerify.RiemannHypothesis.IdentityStepSplit

namespace GppPoleMeroProof

open GppKreinBridge GppKreinHPsi GppKreinHPsiChain GppKreinPoleSplit GppKreinRepSplit
  GppSpectralMatchingSplit GppIdentityStepSplit ComplexConjugate MeasureTheory Set Filter Topology
  Asymptotics

/-! ## 1. Finiteness of the zeros in a ball (PROVED, exported) -/

open GppLogDerivZeroFree GppXiZeroCounting in
/-- **Exported finiteness lemma.** Only finitely many nontrivial zeros of `ζ` have `‖ρ‖ ≤ r`.
This is the local `hZfin` of `GppXiZeroCounting.zeroCountingPolynomial`, given verbatim as a
standalone theorem; `zeroCountingPolynomial` itself is not touched. -/
theorem nontrivialZeros_ball_finite (r : ℝ) :
    {ρ : GppWeilCriterion.nontrivialZeros | ‖(ρ : ℂ)‖ ≤ r}.Finite := by
  by_cases hr : 0 < r
  · have hfin := (MeromorphicOn.divisor xi (Metric.closedBall (0 : ℂ) r)).finiteSupport
      (isCompact_closedBall 0 r)
    refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
    refine hfin.subset ?_
    rintro _ ⟨ρ, hρ, rfl⟩
    have hmem : (ρ : ℂ) ∈ Metric.closedBall (0 : ℂ) r := by simpa using hρ
    rw [Function.mem_support, divisor_xi_apply hmem, ← zeroMult_eq_orderNat_xi ρ.2]
    have := one_le_zeroMult ρ.2
    omega
  · refine (Set.finite_empty).subset ?_
    intro ρ hρ
    exfalso
    have : ‖(ρ : ℂ)‖ ≤ r := hρ
    have hρ0 : (ρ : ℂ) ≠ 0 := fun h => by
      have := ρ.2.2.1; simp [h] at this
    have := norm_pos_iff.2 hρ0
    exact hr (lt_of_lt_of_le this ‹_›)

theorem rho_norm_le (γ : ℂ) : ‖rho γ‖ ≤ 1 / 2 + ‖γ‖ := by
  unfold rho
  calc ‖(1 / 2 : ℂ) + Complex.I * γ‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖Complex.I * γ‖ := norm_add_le _ _
    _ = 1 / 2 + ‖γ‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
      norm_num

theorem rho_injective : Function.Injective rho := by
  intro x y h
  unfold rho at h
  exact mul_left_cancel₀ Complex.I_ne_zero (add_left_cancel h)

/-- **`{γ ∈ Zgamma : ‖γ‖ ≤ T}` is finite** for every `T` (PROVED). -/
theorem zgamma_ball_finite (T : ℝ) : {γ : ℂ | γ ∈ Zgamma ∧ ‖γ‖ ≤ T}.Finite := by
  have hf := (nontrivialZeros_ball_finite (T + 1 / 2)).image Subtype.val
  refine (hf.preimage rho_injective.injOn).subset ?_
  rintro γ ⟨hγ, hT⟩
  refine ⟨⟨rho γ, hγ⟩, ?_, rfl⟩
  show ‖rho γ‖ ≤ T + 1 / 2
  linarith [rho_norm_le γ]

/-- Subtype form of `zgamma_ball_finite`. -/
theorem zgamma_ball_finite' (T : ℝ) : {γ : Zgamma | ‖(γ : ℂ)‖ ≤ T}.Finite := by
  refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
  refine (zgamma_ball_finite T).subset ?_
  rintro _ ⟨γ, hγ, rfl⟩
  exact ⟨γ.2, hγ⟩

/-! ## 2. Pole terms, the finite part near a point, and the tail -/

/-- The term `m_γ a(γ)/(s − iγ)` of the pole sum. -/
noncomputable def poleTerm (a : ℂ → ℂ) (γ : Zgamma) (s : ℂ) : ℂ :=
  (mult (γ : ℂ) : ℂ) * poleCoeff a s γ

/-- The finitely many zeros with `‖γ‖ ≤ ‖z₀‖ + 2δ`. -/
noncomputable def S (z₀ : ℂ) (δ : ℝ) : Finset Zgamma :=
  (zgamma_ball_finite' (‖z₀‖ + 2 * δ)).toFinset

/-- The tail `Σ_{γ ∉ S} m_γ a(γ)/(s − iγ)`. -/
noncomputable def tail (a : ℂ → ℂ) (F : Finset Zgamma) (s : ℂ) : ℂ :=
  ∑' γ : Zgamma, if γ ∈ F then 0 else poleTerm a γ s

theorem poleTerm_norm_le (a : ℂ → ℂ) (γ : Zgamma) (s : ℂ) {R : ℝ} (hR : 0 < R)
    (h : R ≤ ‖s - Complex.I * γ‖) :
    ‖poleTerm a γ s‖ ≤ ‖(mult (γ : ℂ) : ℂ) * a γ‖ / R := by
  unfold poleTerm poleCoeff
  rw [← mul_div_assoc, norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hR h

/-- Off `S z₀ δ`, every pole is at distance `> δ` from the ball `B(z₀, δ)`. -/
theorem far {z₀ : ℂ} {δ : ℝ} {γ : Zgamma} (hγ : γ ∉ S z₀ δ) {s : ℂ}
    (hs : s ∈ Metric.ball z₀ δ) : δ < ‖s - Complex.I * γ‖ := by
  have h1 : ‖z₀‖ + 2 * δ < ‖(γ : ℂ)‖ := by
    unfold S at hγ
    rw [Set.Finite.mem_toFinset] at hγ
    simpa using hγ
  rw [Metric.mem_ball, dist_eq_norm] at hs
  have h2 : ‖Complex.I * (γ : ℂ)‖ = ‖(γ : ℂ)‖ := by simp
  have h3 := norm_sub_norm_le (Complex.I * (γ : ℂ)) s
  have h4 := norm_sub_norm_le s z₀
  have h5 : ‖Complex.I * (γ : ℂ) - s‖ = ‖s - Complex.I * γ‖ := norm_sub_rev _ _
  linarith

theorem analyticAt_poleTerm (a : ℂ → ℂ) (γ : Zgamma) {z : ℂ} (hz : z - Complex.I * γ ≠ 0) :
    AnalyticAt ℂ (poleTerm a γ) z := by
  unfold poleTerm poleCoeff
  exact analyticAt_const.mul (analyticAt_const.div (analyticAt_id.sub analyticAt_const) hz)

theorem meromorphicAt_poleTerm (a : ℂ → ℂ) (γ : Zgamma) (z : ℂ) :
    MeromorphicAt (poleTerm a γ) z := by
  unfold poleTerm poleCoeff
  exact (MeromorphicAt.const _ z).mul ((MeromorphicAt.const _ z).div
    ((analyticAt_id.sub analyticAt_const).meromorphicAt))

/-- **M-test tail (PROVED)**: the tail is analytic at `z₀` (holomorphic on `B(z₀, δ)` by
`Complex.differentiableOn_tsum_of_summable_norm`, dominator `‖m_γ a(γ)‖/δ`). -/
theorem tail_analyticAt (a : ℂ → ℂ) (ha : ZeroSummable a) (z₀ : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    AnalyticAt ℂ (tail a (S z₀ δ)) z₀ := by
  have hD : DifferentiableOn ℂ (tail a (S z₀ δ)) (Metric.ball z₀ δ) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun γ : Zgamma => ‖(mult (γ : ℂ) : ℂ) * a γ‖ / δ)
      (ha.norm.div_const δ) ?_ Metric.isOpen_ball ?_
    · intro γ
      by_cases hγ : γ ∈ S z₀ δ
      · simp only [hγ, if_true]; exact differentiableOn_const 0
      · simp only [hγ, if_false]
        intro s hs
        have hne : s - Complex.I * γ ≠ 0 := by
          intro h0; have := far hγ hs; rw [h0, norm_zero] at this; linarith
        exact (analyticAt_poleTerm a γ hne).differentiableAt.differentiableWithinAt
    · intro γ s hs
      by_cases hγ : γ ∈ S z₀ δ
      · simp only [hγ, if_true, norm_zero]; positivity
      · simp only [hγ, if_false]
        exact poleTerm_norm_le a γ s hδ (le_of_lt (far hγ hs))
  exact hD.analyticAt (Metric.ball_mem_nhds z₀ hδ)

/-- **Local decomposition (PROVED)**: on `B(z₀, δ)` the pole sum is the finite sum over
`S z₀ δ` plus the tail. -/
theorem decomp (a : ℂ → ℂ) (ha : ZeroSummable a) (z₀ : ℂ) {δ : ℝ} (hδ : 0 < δ) {s : ℂ}
    (hs : s ∈ Metric.ball z₀ δ) :
    zeroSum (poleCoeff a s) = (∑ γ ∈ S z₀ δ, poleTerm a γ s) + tail a (S z₀ δ) s := by
  have hsplit : ∀ γ : Zgamma, poleTerm a γ s =
      (if γ ∈ S z₀ δ then poleTerm a γ s else 0) +
        (if γ ∈ S z₀ δ then 0 else poleTerm a γ s) := by
    intro γ; split_ifs <;> simp
  have h1 : Summable (fun γ : Zgamma => if γ ∈ S z₀ δ then poleTerm a γ s else 0) :=
    summable_of_ne_finset_zero (s := S z₀ δ) (fun γ hγ => if_neg hγ)
  have h2 : Summable (fun γ : Zgamma => if γ ∈ S z₀ δ then 0 else poleTerm a γ s) := by
    refine Summable.of_norm_bounded (ha.norm.div_const δ) (fun γ => ?_)
    by_cases hγ : γ ∈ S z₀ δ
    · simp only [hγ, if_true, norm_zero]; positivity
    · simp only [hγ, if_false]
      exact poleTerm_norm_le a γ s hδ (le_of_lt (far hγ hs))
  show ∑' γ : Zgamma, poleTerm a γ s = _
  rw [tsum_congr hsplit, h1.tsum_add h2, tsum_eq_sum (s := S z₀ δ) (fun γ hγ => if_neg hγ)]
  unfold tail
  congr 1
  exact Finset.sum_congr rfl (fun γ hγ => if_pos hγ)

/-! ## 3. `PoleMero` PROVED -/

/-- **`PoleMero` PROVED** (as stated in `IdentityStepSplit`, not widened). `F s := Σ_γ m_γ
a(γ)/(s − iγ)` itself; meromorphic at every point (finite part + analytic tail); equal to the
pole sum on `Re s > 1/2` by definition; principal part `m_γ a(γ)/(s − iγ)` at every lower
zero (the remaining finite terms have poles `iγ' ≠ iγ`). -/
theorem poleMero : PoleMero := by
  intro a ha
  refine ⟨fun s => zeroSum (poleCoeff a s), ?_, fun s _ => rfl, ?_⟩
  · intro z₀ _
    have hfin : MeromorphicAt
        (fun s => (∑ γ ∈ S z₀ 1, poleTerm a γ s) + tail a (S z₀ 1) s) z₀ :=
      (MeromorphicAt.fun_sum (fun γ _ => meromorphicAt_poleTerm a γ z₀)).add
        (tail_analyticAt a ha z₀ one_pos).meromorphicAt
    refine hfin.congr ?_
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds z₀ one_pos)] with s hs
    exact (decomp a ha z₀ one_pos hs).symm
  · intro γ₀ hγ₀ _
    set z₀ : ℂ := Complex.I * γ₀ with hz₀
    set γ' : Zgamma := ⟨γ₀, hγ₀⟩ with hγ'
    have hmem : γ' ∈ S z₀ 1 := by
      unfold S
      rw [Set.Finite.mem_toFinset]
      show ‖γ₀‖ ≤ ‖z₀‖ + 2 * 1
      have : ‖z₀‖ = ‖γ₀‖ := by rw [hz₀]; simp
      linarith
    refine ⟨fun s => (∑ γ ∈ (S z₀ 1).erase γ', poleTerm a γ s) + tail a (S z₀ 1) s, ?_, ?_⟩
    · refine AnalyticAt.add ?_ (tail_analyticAt a ha z₀ one_pos)
      have hall : ∀ γ ∈ (S z₀ 1).erase γ', AnalyticAt ℂ (poleTerm a γ) z₀ := by
        intro γ hγ
        have hne : γ ≠ γ' := Finset.ne_of_mem_erase hγ
        have hne' : z₀ - Complex.I * γ ≠ 0 := by
          intro h
          apply hne
          apply Subtype.ext
          have : Complex.I * γ₀ = Complex.I * (γ : ℂ) := sub_eq_zero.mp h
          exact (mul_left_cancel₀ Complex.I_ne_zero this).symm
        exact analyticAt_poleTerm a γ hne'
      have := Finset.analyticAt_sum _ hall
      convert this using 1
      funext s
      exact (Finset.sum_apply s _ _).symm
    · filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds z₀ one_pos)] with s hs
      have hterm : poleTerm a γ' s = (mult γ₀ : ℂ) * a γ₀ / (s - Complex.I * γ₀) := by
        simp only [poleTerm, poleCoeff, hγ', mul_div_assoc]
      show zeroSum (poleCoeff a s) = _
      rw [decomp a ha z₀ one_pos hs, ← Finset.add_sum_erase _ _ hmem, hterm]
      ring

/-! ## 4. Chains (PROVED, conditional) -/

/-- With `PoleMero` and `LaplaceHolo` discharged, `IdentityStep` rests on `ExpLaplaceMero` alone. -/
theorem identityStep_of_expLaplaceMero (hE : ExpLaplaceMero) : IdentityStep :=
  identityStep_of_poleMero_expLaplaceMero poleMero hE

/-- The fine chain is now three named premises. -/
def HPsiExpChain : Prop := HPsi → KreinDecomp → ExpLaplaceMero → RiemannHypothesis

theorem hPsiExpChain : HPsiExpChain := fun h hD hE => hPsiPoleExpChain h hD poleMero hE

/-! ## 5. `ExpLaplaceMero` inputs: the `1/z²` Laplace integral (PROVED) and `CoeffVanish` (named) -/

theorem real_mul_exp_integrable {c : ℝ} (hc : c < 0) :
    IntegrableOn (fun x : ℝ => x * Real.exp (c * x)) (Ioi 0) := by
  have hO : (fun x : ℝ => x * Real.exp (c * x)) =O[atTop] fun x => Real.exp (-(-c / 2) * x) := by
    have h1 : (fun x : ℝ => x) =O[atTop] fun x => Real.exp (-c / 2 * x) := by
      simpa using (isLittleO_pow_exp_pos_mul_atTop 1 (by linarith : 0 < -c / 2)).isBigO
    refine (h1.mul (isBigO_refl (fun x : ℝ => Real.exp (c * x)) atTop)).congr_right ?_
    intro x; rw [← Real.exp_add]; ring_nf
  exact integrable_of_isBigO_exp_neg (by linarith) (by fun_prop) hO

theorem mul_cexp_integrable {z : ℂ} (hz : z.re < 0) :
    IntegrableOn (fun x : ℝ => (x : ℂ) * Complex.exp (z * x)) (Ioi 0) := by
  refine (real_mul_exp_integrable hz).mono' (by fun_prop) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hx), Complex.norm_exp]
  simp [Complex.mul_re]

/-- **`∫_{(0,∞)} d e^{z d} dd = 1/z²` for `Re z < 0` (PROVED).** -/
theorem integral_mul_cexp_Ioi {z : ℂ} (hz : z.re < 0) :
    ∫ x : ℝ in Ioi 0, (x : ℂ) * Complex.exp (z * x) = 1 / z ^ 2 := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => (x : ℂ)) 1 x := fun x _ => by
    simpa using (hasDerivAt_id x).ofReal_comp
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => Complex.exp (z * x) / z)
      (Complex.exp (z * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => z * (x : ℂ)) (z * 1) x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).const_mul z
    have h2 := (h1.cexp).div_const z
    exact h2.congr_deriv (by rw [mul_one, mul_div_cancel_right₀ _ hz0])
  have huv' : IntegrableOn ((fun x : ℝ => (x : ℂ)) * fun x : ℝ => Complex.exp (z * x)) (Ioi 0) :=
    mul_cexp_integrable hz
  have hu'v : IntegrableOn ((fun _ : ℝ => (1 : ℂ)) * fun x : ℝ => Complex.exp (z * x) / z) (Ioi 0) := by
    have := (integrableOn_exp_mul_complex_Ioi hz 0).div_const z
    exact IntegrableOn.congr_fun this (fun x _ => by simp) measurableSet_Ioi
  have h0 : Tendsto ((fun x : ℝ => (x : ℂ)) * fun x : ℝ => Complex.exp (z * x) / z)
      (𝓝[>] 0) (𝓝 0) := by
    have : Continuous ((fun x : ℝ => (x : ℂ)) * fun x : ℝ => Complex.exp (z * x) / z) := by
      fun_prop
    have h := this.tendsto 0
    simp only [Pi.mul_apply, Complex.ofReal_zero, zero_mul] at h
    exact tendsto_nhdsWithin_of_tendsto_nhds h
  have hinf : Tendsto ((fun x : ℝ => (x : ℂ)) * fun x : ℝ => Complex.exp (z * x) / z)
      atTop (𝓝 0) := by
    have hr : Tendsto (fun x : ℝ => x * Real.exp (z.re * x)) atTop (𝓝 0) := by
      have := (isLittleO_pow_exp_pos_mul_atTop 1 (by linarith : 0 < -z.re)).tendsto_div_nhds_zero
      refine this.congr' (Eventually.of_forall fun x => ?_)
      simp only [pow_one]
      rw [div_eq_mul_inv, ← Real.exp_neg]; ring_nf
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hr' : Tendsto (fun x : ℝ => x * Real.exp (z.re * x) / ‖z‖) atTop (𝓝 0) := by
      simpa using hr.div_const ‖z‖
    refine hr'.congr' ((eventually_ge_atTop 0).mono fun x hx => ?_)
    simp only [Pi.mul_apply]
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hx, Complex.norm_exp]
    simp [Complex.mul_re]; ring
  have := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h0 hinf
  rw [this]
  have e : ∫ x : ℝ in Ioi 0, (1 : ℂ) * (Complex.exp (z * x) / z) =
      (∫ x : ℝ in Ioi 0, Complex.exp (z * x)) / z := by
    simp only [one_mul]; exact integral_div z _
  rw [e, integral_exp_mul_complex_Ioi hz 0]
  field_simp
  simp

/-- **Named premise `CoeffVanish` (NOT proved).** If the quasi-exponential
`(c₀ + c₁d)e^{iβd} + (c₂ + c₃d)e^{iβ̄d}` is integrable against `e^{−sd}` on `(0,∞)` for every
`Re s > 1/2`, then the coefficients of any exponential growing faster than `e^{d/2}` vanish.
(Paper: `Re(iβ̄) = −Re(iβ)`, so at most one block grows; take real `s ∈ (1/2, Re(iβ))`.) -/
def CoeffVanish : Prop :=
  ∀ β c₀ c₁ c₂ c₃ : ℂ,
    (∀ s : ℂ, 1 / 2 < s.re → IntegrableOn (fun d : ℝ =>
      ((c₀ + c₁ * d) * Complex.exp (Complex.I * β * d) +
        (c₂ + c₃ * d) * Complex.exp (Complex.I * conj β * d)) * Complex.exp (-s * d)) (Ioi 0)) →
    (1 / 2 < (Complex.I * β).re → c₀ = 0 ∧ c₁ = 0) ∧
      (1 / 2 < (Complex.I * conj β).re → c₂ = 0 ∧ c₃ = 0)

end GppPoleMeroProof

#print axioms GppPoleMeroProof.nontrivialZeros_ball_finite
#print axioms GppPoleMeroProof.rho_norm_le
#print axioms GppPoleMeroProof.rho_injective
#print axioms GppPoleMeroProof.zgamma_ball_finite
#print axioms GppPoleMeroProof.zgamma_ball_finite'
#print axioms GppPoleMeroProof.poleTerm_norm_le
#print axioms GppPoleMeroProof.far
#print axioms GppPoleMeroProof.analyticAt_poleTerm
#print axioms GppPoleMeroProof.meromorphicAt_poleTerm
#print axioms GppPoleMeroProof.tail_analyticAt
#print axioms GppPoleMeroProof.decomp
#print axioms GppPoleMeroProof.poleMero
#print axioms GppPoleMeroProof.identityStep_of_expLaplaceMero
#print axioms GppPoleMeroProof.hPsiExpChain
#print axioms GppPoleMeroProof.real_mul_exp_integrable
#print axioms GppPoleMeroProof.mul_cexp_integrable
#print axioms GppPoleMeroProof.integral_mul_cexp_Ioi
