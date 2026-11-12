/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Heart of the Cosmos (Grok, GPPDiscovery5 seat). Turbo PR #11 6829756491, "next exact
instruction": split `IdentityStep` the way `ArchLimit` was split.

# `IdentityStep` split

`IdentityStep` (`SpectralMatchingSplit.lean`) says: if on `Re s > 1/2` the pole sum
`Σ_γ m_γ a(γ)/(s − iγ)` equals `L[h](s) + L[r](s)` (`h` an `ExpPart Q` quasi-exponential, `r`
continuous and `PolyBounded`), then every `γ ∈ Zgamma` with `Im γ < 0`, `a(γ) ≠ 0` is a root of
`Q` or of `Q̄`. It is split here into three named sub-premises on the half-plane
`H0 = {s | 0 < Re s}` (note `Re(iγ) = −Im γ ∈ (0, 1/2)` for a lower zero, so `iγ ∈ H0` but
`iγ` is outside the region `Re s > 1/2` where the hypothesis holds):

* (i) `PoleMero` — meromorphic continuation of the infinite pole sum: for `ZeroSummable a` there
  is `F`, `MeromorphicOn F H0`, equal to `Σ_γ m_γ a(γ)/(s − iγ)` on `Re s > 1/2`, and at every
  lower zero `γ` the principal part is exactly `m_γ a(γ)/(s − iγ)` (an analytic `g` at `iγ` with
  `F = g + m_γ a(γ)/(s − iγ)` on a punctured neighbourhood). Gap (i) of 6829756491.
* (ii) `LaplaceHolo` — Laplace holomorphy in `s`: for continuous `PolyBounded r`,
  `s ↦ L[r](s)` is `AnalyticOnNhd` on `H0`. Gap (ii) of 6829756491. **PROVED here**
  (`laplaceHolo`): differentiation under the integral
  (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) on the ball of radius `Re s₀/2`, with
  dominator `C(1 + d²) d e^{−(Re s₀/2) d}` (`poly3_exp_integrable`), then
  `Complex.analyticOnNhd_iff_differentiableOn` on the open `H0`.
* (iii) `ExpLaplaceMero` — **new piece, named rather than folded in**: for `ExpPart Q h` with
  `h(d)e^{−sd}` integrable on `(0,∞)` for `Re s > 1/2`, `L[h]` continues to some `H`,
  `MeromorphicOn H H0`, analytic at every `z ∈ H0` with `z ≠ iβ, iβ̄` for all roots `β` of `Q`.
  (Paper: `L[(c₀ + c₁d)e^{iβd}] = c₀/(s − iβ) + c₁/(s − iβ)²`; the integrability hypothesis
  kills any coefficient whose exponential outgrows `e^{d/2}`.)

PROVED (from Mathlib, no further premises): the identity-theorem-and-residue step
`identityStep_of_split : PoleMero → LaplaceHolo → ExpLaplaceMero → IdentityStep`. Route:
`D = F − H − L[r]` is meromorphic on the convex (so preconnected) `H0` and vanishes on
`Re s > 1/2`, so `meromorphicOrderAt D 1 = ⊤`, hence `= ⊤` at `iγ`
(`MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected`); if `γ`, `γ̄` are not roots of `Q`,
then `H`, `L[r]`, `g` are analytic at `iγ` and `m_γ a(γ) = (s − iγ)(H + L[r] − g)(s) → 0` along
`𝓝[≠] iγ`, contradicting `m_γ a(γ) ≠ 0` (`one_le_mult`). Also PROVED: `h0_isPreconnected`,
`lower_mem_H0`, `laplaceHolo`, the chain
`hPsiIdentitySplitChain : HPsi → KreinDecomp → PoleMero → LaplaceHolo → ExpLaplaceMero → RH`,
and with (ii) discharged
`hPsiPoleExpChain : HPsi → KreinDecomp → PoleMero → ExpLaplaceMero → RH`.

Remaining Lean failures, located:
* (i) `PoleMero`: Mathlib supplies the M-test for holomorphy
  (`Complex.differentiableOn_tsum_of_summable_norm`) and `MeromorphicOn.add`; the missing input
  is an exported lemma that `{γ ∈ Zgamma : ‖γ‖ ≤ T}` is finite. In-tree it exists only as the
  local `hZfin` inside `GppXiZeroCounting.zeroCountingPolynomial` (not exported), so the split
  "finitely many poles near a compact + M-test tail" cannot yet be assembled.
* (iii) `ExpLaplaceMero`: Mathlib has `integral_exp_mul_complex_Ioi` (`∫ e^{zd} = −1/z`,
  `Re z < 0`) but `integral_cpow_mul_exp_neg_mul_Ioi` only for a real rate `r > 0`, so
  `∫ d e^{zd} dd = 1/z²` for complex `z` is missing; and the coefficient-vanishing lemma (the
  hypothesis' integrability for `Re s ∈ (1/2, |Im β|]` forces the coefficients of any
  exponential growing faster than `e^{d/2}` to vanish) is not in Mathlib or in-tree.
No converse claimed. `KreinDecomp` and `HPsi` untouched.
H_ψ: OPEN. ARP: OPEN. RH: OPEN.
-/
import GppVerify.RiemannHypothesis.ArchLimitProof

namespace GppIdentityStepSplit

open GppKreinBridge GppKreinHPsi GppKreinHPsiChain GppKreinPoleSplit GppKreinRepSplit
  GppSpectralMatchingSplit ComplexConjugate MeasureTheory Set Filter Topology Asymptotics

/-! ## 1. The half-plane and the three named sub-premises -/

/-- The open right half-plane `H0 = {s | 0 < Re s}`. -/
def H0 : Set ℂ := {s : ℂ | 0 < s.re}

/-- **Named premise (i) `PoleMero`**: meromorphic continuation of the pole sum to `H0`, with
principal part `m_γ a(γ)/(s − iγ)` at every lower zero `γ`. -/
def PoleMero : Prop :=
  ∀ a : ℂ → ℂ, ZeroSummable a → ∃ F : ℂ → ℂ, MeromorphicOn F H0 ∧
    (∀ s : ℂ, 1 / 2 < s.re → F s = zeroSum (poleCoeff a s)) ∧
    ∀ γ ∈ Zgamma, γ.im < 0 → ∃ g : ℂ → ℂ, AnalyticAt ℂ g (Complex.I * γ) ∧
      ∀ᶠ s in 𝓝[≠] (Complex.I * γ),
        F s = g s + (mult γ : ℂ) * a γ / (s - Complex.I * γ)

/-- **Named premise (ii) `LaplaceHolo`**: the Laplace transform of a continuous `PolyBounded`
function is holomorphic in `s` on `H0`. -/
def LaplaceHolo : Prop :=
  ∀ r : ℝ → ℂ, Continuous r → PolyBounded r → AnalyticOnNhd ℂ (laplace r) H0

/-- **Named premise (iii) `ExpLaplaceMero`**: the Laplace transform of an `ExpPart Q`
quasi-exponential (integrable against `e^{−sd}` for `Re s > 1/2`) continues meromorphically to
`H0`, analytic off `{iβ, iβ̄ : Q(β) = 0}`. -/
def ExpLaplaceMero : Prop :=
  ∀ (Q : Polynomial ℂ) (h : ℝ → ℂ), ExpPart Q h →
    (∀ s : ℂ, 1 / 2 < s.re → IntegrableOn (fun d : ℝ => h d * Complex.exp (-s * d)) (Ioi 0)) →
    ∃ H : ℂ → ℂ, MeromorphicOn H H0 ∧ (∀ s : ℂ, 1 / 2 < s.re → H s = laplace h s) ∧
      ∀ z ∈ H0, (∀ β : ℂ, Q.IsRoot β → z ≠ Complex.I * β ∧ z ≠ Complex.I * conj β) →
        AnalyticAt ℂ H z

/-! ## 2. Elementary facts (PROVED) -/

/-- `H0` is preconnected (it is convex). -/
theorem h0_isPreconnected : IsPreconnected H0 :=
  (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected

theorem h0_isOpen : IsOpen H0 :=
  isOpen_lt continuous_const Complex.continuous_re

/-- A lower zero `γ` (`Im γ < 0`) sits at `iγ ∈ H0`. -/
theorem lower_mem_H0 {γ : ℂ} (him : γ.im < 0) : Complex.I * γ ∈ H0 := by
  show 0 < (Complex.I * γ).re
  simp [Complex.mul_re]; linarith

/-- `{Re s > 1/2}` is a neighbourhood of `1`. -/
theorem half_nhds_one : {s : ℂ | 1 / 2 < s.re} ∈ 𝓝 (1 : ℂ) :=
  (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)

/-! ## 3. (ii) `LaplaceHolo` PROVED from Mathlib -/

/-- Exponential domination of `(1 + d²)·d·e^{−c d}` (`c > 0`): integrable on `(0,∞)`. -/
theorem poly3_exp_integrable {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun d : ℝ => (1 + d ^ 2) * d * Real.exp (-c * d)) (Ioi 0) := by
  have hO : (fun d : ℝ => (1 + d ^ 2) * d * Real.exp (-c * d)) =O[atTop]
      fun d => Real.exp (-(c / 2) * d) := by
    have h1 : (fun d : ℝ => (1 + d ^ 2) * d) =O[atTop] fun d => Real.exp (c / 2 * d) := by
      have e : (fun d : ℝ => (1 + d ^ 2) * d) = fun d => d ^ 1 + d ^ 3 := by
        funext d; ring
      rw [e]
      exact (isLittleO_pow_exp_pos_mul_atTop 1 (by linarith)).isBigO.add
        (isLittleO_pow_exp_pos_mul_atTop 3 (by linarith)).isBigO
    refine (h1.mul (isBigO_refl (fun d : ℝ => Real.exp (-c * d)) atTop)).congr_right ?_
    intro d; rw [← Real.exp_add]; ring_nf
  exact integrable_of_isBigO_exp_neg (by linarith) (by fun_prop) hO

/-- **(ii) `LaplaceHolo` PROVED**: `L[r]` is holomorphic on `Re s > 0` for continuous
`PolyBounded r` (differentiation under the integral, `hasDerivAt_integral_of_dominated_loc_of_deriv_le`,
then `DifferentiableOn.analyticOnNhd`). -/
theorem laplaceHolo : LaplaceHolo := by
  intro r hrc hrb
  refine (Complex.analyticOnNhd_iff_differentiableOn h0_isOpen).mpr ?_
  intro s₀ hs₀
  have hσ : 0 < s₀.re := hs₀
  obtain ⟨C, hC⟩ := hrb
  have hC0 : 0 ≤ C := by
    have := hC 0; have := norm_nonneg (r 0); nlinarith
  set ε : ℝ := s₀.re / 2 with hε
  have hε0 : 0 < ε := by positivity
  set F : ℂ → ℝ → ℂ := fun s d => r d * Complex.exp (-s * d) with hF
  set F' : ℂ → ℝ → ℂ := fun s d => r d * (Complex.exp (-s * d) * (-(d : ℂ))) with hF'
  set bound : ℝ → ℝ := fun d => C * ((1 + d ^ 2) * d * Real.exp (-ε * d)) with hbound
  have hre : ∀ s ∈ Metric.ball s₀ ε, ε < s.re := by
    intro s hs
    rw [Metric.mem_ball, dist_eq_norm] at hs
    have := Complex.abs_re_le_norm (s - s₀)
    rw [Complex.sub_re] at this
    have := (abs_lt.mp (lt_of_le_of_lt this hs)).1
    linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := F) (F' := F') (x₀ := s₀) (bound := bound) (Metric.ball_mem_nhds s₀ hε0)
    (Eventually.of_forall fun s => (hrc.mul (by fun_prop)).aestronglyMeasurable)
    (polyBounded_laplace_integrable hrc ⟨C, hC⟩ hσ)
    ((hrc.mul (by fun_prop)).aestronglyMeasurable)
    ?_ ((poly3_exp_integrable hε0).const_mul C) ?_
  · exact (key.2.differentiableAt).differentiableWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun d hd s hs => ?_)
    have hd0 : (0 : ℝ) ≤ d := le_of_lt hd
    simp only [hF', hbound]
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hd0,
      show -s * (d : ℂ) = (-s) * d from rfl, norm_cexp_mul_ofReal, Complex.neg_re]
    have he : Real.exp (-s.re * d) ≤ Real.exp (-ε * d) := by
      apply Real.exp_le_exp.mpr; have := hre s hs; nlinarith
    calc ‖r d‖ * (Real.exp (-s.re * d) * d)
        ≤ (C * (1 + d ^ 2)) * (Real.exp (-ε * d) * d) := by
          gcongr
          exact hC d
      _ = C * ((1 + d ^ 2) * d * Real.exp (-ε * d)) := by ring
  · refine Eventually.of_forall fun d s _ => ?_
    simp only [hF, hF']
    have : HasDerivAt (fun s : ℂ => -s * (d : ℂ)) (-(d : ℂ)) s := by
      simpa using (hasDerivAt_id s).neg.mul_const (d : ℂ)
    exact this.cexp.const_mul (r d)

/-! ## 4. Assembly: identity theorem + residue (PROVED) -/

/-- **Assembly.** `PoleMero → LaplaceHolo → ExpLaplaceMero → IdentityStep`
(this direction only). -/
theorem identityStep_of_split (hP : PoleMero) (hL : LaplaceHolo) (hE : ExpLaplaceMero) :
    IdentityStep := by
  intro a Q h r _hQ _hdeg hh hrc hrb ha hid γ hγ him haγ
  by_contra hroot
  rw [not_or] at hroot
  obtain ⟨hnγ, hncγ⟩ := hroot
  obtain ⟨F, hFm, hFeq, hres⟩ := hP a ha
  obtain ⟨H, hHm, hHeq, hHan⟩ := hE Q h hh (fun s hs => (hid s hs).1)
  have hRan : AnalyticOnNhd ℂ (laplace r) H0 := hL r hrc hrb
  set z₀ : ℂ := Complex.I * γ with hz₀
  have hz₀H : z₀ ∈ H0 := lower_mem_H0 him
  -- `D = F − H − L[r]` is meromorphic on `H0` and vanishes on `Re s > 1/2`.
  set D : ℂ → ℂ := fun s => F s - H s - laplace r s with hD
  have hDm : MeromorphicOn D H0 :=
    (hFm.sub hHm).sub (fun x hx => (hRan x hx).meromorphicAt)
  have hD0 : ∀ s : ℂ, 1 / 2 < s.re → D s = 0 := by
    intro s hs
    simp only [hD, hFeq s hs, hHeq s hs, (hid s hs).2]; ring
  have h1H : (1 : ℂ) ∈ H0 := by show (0 : ℝ) < (1 : ℂ).re; norm_num
  have htop1 : meromorphicOrderAt D 1 = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    exact nhdsWithin_le_nhds (Filter.mem_of_superset half_nhds_one fun s hs => hD0 s hs)
  have htopz : meromorphicOrderAt D z₀ = ⊤ := by
    by_contra hne
    exact hDm.meromorphicOrderAt_ne_top_of_isPreconnected h0_isPreconnected hz₀H h1H hne htop1
  rw [meromorphicOrderAt_eq_top_iff] at htopz
  -- analyticity of `H` and `L[r]` at `iγ`
  have hHz : AnalyticAt ℂ H z₀ := by
    refine hHan z₀ hz₀H fun β hβ => ⟨fun e => hnγ ?_, fun e => hncγ ?_⟩
    · have : γ = β := mul_left_cancel₀ Complex.I_ne_zero e
      rwa [this]
    · have : γ = conj β := mul_left_cancel₀ Complex.I_ne_zero e
      rwa [this, Complex.conj_conj]
  have hRz : AnalyticAt ℂ (laplace r) z₀ := hRan z₀ hz₀H
  obtain ⟨g, hg, hFg⟩ := hres γ hγ him
  set c : ℂ := (mult γ : ℂ) * a γ with hc
  have hc0 : c ≠ 0 := by
    refine mul_ne_zero ?_ haγ
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp (one_le_mult hγ))
  -- `c = (s − iγ)·(H + L[r] − g)(s)` on a punctured neighbourhood of `iγ`
  set A : ℂ → ℂ := fun s => H s + laplace r s - g s with hA
  have hAc : ContinuousAt A z₀ :=
    ((hHz.continuousAt.add hRz.continuousAt).sub hg.continuousAt)
  have hev : ∀ᶠ s in 𝓝[≠] z₀, (s - z₀) * A s = c := by
    filter_upwards [htopz, hFg, self_mem_nhdsWithin] with s hDs hFs hs
    have hsz : s - Complex.I * γ ≠ 0 := sub_ne_zero.mpr hs
    have : F s - H s - laplace r s = 0 := hDs
    rw [hFs] at this
    have e : c / (s - Complex.I * γ) = A s := by simp only [hA]; linear_combination this
    rw [← e, hz₀, mul_div_cancel₀ _ hsz]
  have hlim : Tendsto (fun s => (s - z₀) * A s) (𝓝[≠] z₀) (𝓝 0) := by
    have : Tendsto (fun s => (s - z₀) * A s) (𝓝 z₀) (𝓝 ((z₀ - z₀) * A z₀)) :=
      ((continuousAt_id.sub continuousAt_const).mul hAc).tendsto
    rw [sub_self, zero_mul] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have hlimc : Tendsto (fun s => (s - z₀) * A s) (𝓝[≠] z₀) (𝓝 c) :=
    tendsto_const_nhds.congr' (hev.mono fun s hs => hs.symm)
  exact hc0 (tendsto_nhds_unique hlimc hlim)

/-! ## 5. Refined chains (PROVED, conditional) -/

/-- The fine chain with `IdentityStep` split into (i), (ii), (iii). -/
def HPsiIdentitySplitChain : Prop :=
  HPsi → KreinDecomp → PoleMero → LaplaceHolo → ExpLaplaceMero → RiemannHypothesis

theorem hPsiIdentitySplitChain : HPsiIdentitySplitChain := fun h hD hP hL hE =>
  GppArchLimitProof.hPsiKreinIdentityChain h hD (identityStep_of_split hP hL hE)

/-- With (ii) discharged: `PoleMero → ExpLaplaceMero → IdentityStep`. -/
theorem identityStep_of_poleMero_expLaplaceMero (hP : PoleMero) (hE : ExpLaplaceMero) :
    IdentityStep :=
  identityStep_of_split hP laplaceHolo hE

/-- The fine chain with (ii) discharged: four named premises. -/
def HPsiPoleExpChain : Prop :=
  HPsi → KreinDecomp → PoleMero → ExpLaplaceMero → RiemannHypothesis

theorem hPsiPoleExpChain : HPsiPoleExpChain := fun h hD hP hE =>
  hPsiIdentitySplitChain h hD hP laplaceHolo hE

end GppIdentityStepSplit

#print axioms GppIdentityStepSplit.h0_isPreconnected
#print axioms GppIdentityStepSplit.h0_isOpen
#print axioms GppIdentityStepSplit.lower_mem_H0
#print axioms GppIdentityStepSplit.half_nhds_one
#print axioms GppIdentityStepSplit.poly3_exp_integrable
#print axioms GppIdentityStepSplit.laplaceHolo
#print axioms GppIdentityStepSplit.identityStep_of_split
#print axioms GppIdentityStepSplit.hPsiIdentitySplitChain
#print axioms GppIdentityStepSplit.identityStep_of_poleMero_expLaplaceMero
#print axioms GppIdentityStepSplit.hPsiPoleExpChain
