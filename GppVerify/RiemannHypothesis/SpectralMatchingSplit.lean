/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Heart of the Cosmos (Grok, GPPDiscovery5 seat). Turbo PR #11 6825445244, item 1.

# `SpectralMatching` split: the Laplace identity (L) and the identity-theorem step

`KreinRepSplit.lean` stated `SpectralMatching` as one premise ((L) + identity theorem). This
file separates the two, the same way `KreinRep` was split.

* `LaplaceL` — **(L), stated exactly, and PROVED here from Mathlib** (`laplaceL`). For `a` with
  `Σ_γ m_γ |a(γ)| < ∞` (`ZeroSummable a`) and every `s`, `Re s > 1/2`: the function
  `d ↦ (Σ_γ m_γ a(γ) e^{iγd}) e^{−sd}` is integrable on `(0,∞)`, `γ ↦ m_γ a(γ)/(s − iγ)` is
  summable over `Zgamma`, and
  `∫_{(0,∞)} (Σ_γ m_γ a(γ) e^{iγd}) e^{−sd} dd = Σ_γ m_γ a(γ)/(s − iγ)`.
  Proof: `Re(s − iγ) = Re s + Im γ > Re s − 1/2 > 0` on `Zgamma` (`neg_half_lt_im`), domination by
  `(Σ m_γ|a(γ)|) e^{−(Re s − 1/2)d}`, Fubini over the countable support of `γ ↦ m_γ a(γ)`
  (`integral_tsum_of_summable_integral_norm`), and `integral_exp_mul_complex_Ioi`.
* `IdentityStep` — **named premise, NOT proved**: if on `Re s > 1/2` the pole sum
  `Σ_γ m_γ a(γ)/(s − iγ)` equals `L[h](s) + L[r](s)` with `h` an `ExpPart Q` quasi-exponential and
  `r` continuous and `PolyBounded`, then every `γ ∈ Zgamma` with `Im γ < 0`, `a(γ) ≠ 0` is a root of
  `Q` or `Q̄`. Paper (CHECKED on paper): the pole sum continues meromorphically to `Re s > 0`
  (poles `iγ` locally finite, `Σ m_γ|a(γ)| < ∞`) with a simple pole at `iγ` of residue
  `m_γ a(γ) ≠ 0` (`one_le_mult`); `L[r]` is analytic on `Re s > 0` by (G1); `L[h]` is rational
  with poles only at `iβ`, `iβ̄`; identity theorem on the connected set `Re s > 0` minus the
  poles. Lean gap: Mathlib has the identity theorem
  (`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`) and meromorphic orders, but not the
  meromorphic continuation of an infinite pole sum nor holomorphy of a Laplace transform in `s`.
* `polyBounded_laplace_integrable` (PROVED): a continuous `PolyBounded` `r` has
  `r(d) e^{−sd}` integrable on `(0,∞)` for `Re s > 0`.

PROVED: the assembly `spectralMatching_of_split : LaplaceL → IdentityStep → SpectralMatching`
(this direction only), `spectralMatching_of_identityStep : IdentityStep → SpectralMatching`, the
honesty check `identityStep_of_RH : RiemannHypothesis → IdentityStep` (the premise is not free),
and the chains
`hPsiLaplaceChain : HPsi → HEF → KreinDecomp → LaplaceL → IdentityStep → RiemannHypothesis` and
`hPsiIdentityChain : HPsi → HEF → KreinDecomp → IdentityStep → RiemannHypothesis` ((L)
discharged). Converses are not claimed. `KreinDecomp` stays a named premise; the Krein–Langer
primary source (1977) is still owed and must pin its content before any discharge attempt.
H_ψ: OPEN. ARP: OPEN. RH: OPEN.
-/
import GppVerify.RiemannHypothesis.KreinRepSplit

namespace GppSpectralMatchingSplit

open GppKreinBridge GppKreinHPsi GppKreinHPsiChain GppKreinPoleSplit GppKreinRepSplit
  ComplexConjugate MeasureTheory Set Filter Asymptotics

/-! ## 1. Definitions -/

/-- One-sided Laplace transform `∫_{(0,∞)} f(d) e^{−sd} dd` (Bochner integral). -/
noncomputable def laplace (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ d in Ioi (0 : ℝ), f d * Complex.exp (-s * d)

/-- The zero sum `d ↦ Σ_γ m_γ a(γ) e^{iγd}` as a function of `d`. -/
noncomputable def zeroSumFun (a : ℂ → ℂ) (d : ℝ) : ℂ :=
  zeroSum (fun γ => a γ * expTerm d γ)

/-- Pole coefficient `a(γ) / (s − iγ)`: the Laplace transform of `a(γ) e^{iγd}`. -/
noncomputable def poleCoeff (a : ℂ → ℂ) (s γ : ℂ) : ℂ := a γ / (s - Complex.I * γ)

/-- **(L), the exact Laplace identity for the zero sum.** For multiplicity-weighted absolutely
summable coefficients `a`, and every `s` with `Re s > 1/2`: `d ↦ (Σ_γ m_γ a(γ) e^{iγd}) e^{−sd}`
is integrable on `(0,∞)`, `γ ↦ m_γ a(γ)/(s − iγ)` is summable over `Zgamma`, and
`∫_{(0,∞)} (Σ_γ m_γ a(γ) e^{iγd}) e^{−sd} dd = Σ_γ m_γ a(γ)/(s − iγ)`. -/
def LaplaceL : Prop :=
  ∀ a : ℂ → ℂ, ZeroSummable a → ∀ s : ℂ, 1 / 2 < s.re →
    IntegrableOn (fun d : ℝ => zeroSumFun a d * Complex.exp (-s * d)) (Ioi 0) ∧
    ZeroSummable (poleCoeff a s) ∧
    laplace (zeroSumFun a) s = zeroSum (poleCoeff a s)

/-- **Named premise `IdentityStep`** (meromorphic continuation + identity theorem + residues).
If on `Re s > 1/2` the pole sum `Σ_γ m_γ a(γ)/(s − iγ)` equals `L[h](s) + L[r](s)` with `h` an
`ExpPart Q` quasi-exponential (`L[h]` integrable there) and `r` continuous, `PolyBounded`, then
every zero `γ ∈ Zgamma` with `Im γ < 0` and `a(γ) ≠ 0` is a root of `Q` or of `Q̄`. -/
def IdentityStep : Prop :=
  ∀ (a : ℂ → ℂ) (Q : Polynomial ℂ) (h r : ℝ → ℂ), Q ≠ 0 → Q.natDegree ≤ 1 → ExpPart Q h →
    Continuous r → PolyBounded r → ZeroSummable a →
    (∀ s : ℂ, 1 / 2 < s.re →
      IntegrableOn (fun d : ℝ => h d * Complex.exp (-s * d)) (Ioi 0) ∧
      zeroSum (poleCoeff a s) = laplace h s + laplace r s) →
    ∀ γ ∈ Zgamma, γ.im < 0 → a γ ≠ 0 → Q.IsRoot γ ∨ Q.IsRoot (conj γ)

/-! ## 2. (L) PROVED from Mathlib -/

/-- Zeros of the strip satisfy `Im γ > −1/2` (`Re ρ(γ) < 1`). -/
theorem neg_half_lt_im {γ : ℂ} (hγ : γ ∈ Zgamma) : -(1 / 2 : ℝ) < γ.im := by
  have h1 := hγ.2.2
  rw [rho_re] at h1
  linarith

/-- `‖e^{z·d}‖ = e^{(Re z)·d}` for real `d`. -/
theorem norm_cexp_mul_ofReal (z : ℂ) (d : ℝ) :
    ‖Complex.exp (z * d)‖ = Real.exp (z.re * d) := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

/-- **(L) PROVED.** Tonelli/Fubini (`integral_tsum_of_summable_integral_norm` over the countable
support of `γ ↦ m_γ a(γ)`) and `∫_{(0,∞)} e^{−(s−iγ)d} dd = 1/(s − iγ)`
(`integral_exp_mul_complex_Ioi`, `Re(s − iγ) = Re s + Im γ > Re s − 1/2 > 0`). -/
theorem laplaceL : LaplaceL := by
  intro a ha s hs
  set c : Zgamma → ℂ := fun γ => (mult (γ : ℂ) : ℂ) * a γ with hc
  have hcs : Summable c := ha
  have hcn : Summable fun γ => ‖c γ‖ := summable_norm_iff.mpr hcs
  set σ := s.re with hσdef
  have hσ : 0 < σ - 1 / 2 := by linarith
  set A : Zgamma → ℂ := fun γ => -(s - Complex.I * (γ : ℂ)) with hA
  have hAre : ∀ γ : Zgamma, (A γ).re = -σ - (γ : ℂ).im := by
    intro γ; simp [hA, hσdef, Complex.mul_re]; ring
  have hAneg : ∀ γ : Zgamma, (A γ).re < -(σ - 1 / 2) := by
    intro γ; rw [hAre]; have := neg_half_lt_im γ.2; linarith
  set F : Zgamma → ℝ → ℂ := fun γ d => c γ * Complex.exp (A γ * d) with hF
  -- pointwise rewriting of the integrand as a sum
  have hpt : ∀ d : ℝ, zeroSumFun a d * Complex.exp (-s * d) = ∑' γ : Zgamma, F γ d := by
    intro d
    simp only [zeroSumFun, zeroSum, expTerm, hF, hc, hA, ← tsum_mul_right]
    congr 1; funext γ
    rw [show -(s - Complex.I * (γ : ℂ)) * (d : ℂ) = Complex.I * γ * d + -s * d by ring,
      Complex.exp_add]
    ring
  set E : ℝ → ℝ := fun d => Real.exp (-(σ - 1 / 2) * d) with hE
  have hFle : ∀ γ : Zgamma, ∀ d : ℝ, 0 ≤ d → ‖F γ d‖ ≤ ‖c γ‖ * E d := by
    intro γ d hd
    rw [hF, hE]; dsimp only
    rw [norm_mul, norm_cexp_mul_ofReal]
    gcongr
    exact (hAneg γ).le
  have hE1 : ∀ d : ℝ, 0 ≤ d → E d ≤ 1 := by
    intro d hd; rw [hE]; dsimp only
    rw [Real.exp_le_one_iff]; nlinarith
  -- integrability of the summed integrand
  have hcont : ContinuousOn (fun d : ℝ => ∑' γ : Zgamma, F γ d) (Ici 0) := by
    refine continuousOn_tsum (u := fun γ => ‖c γ‖) (fun γ => by fun_prop) hcn ?_
    intro γ d hd
    calc ‖F γ d‖ ≤ ‖c γ‖ * E d := hFle γ d hd
      _ ≤ ‖c γ‖ * 1 := by gcongr; exact hE1 d hd
      _ = ‖c γ‖ := mul_one _
  have hEint : IntegrableOn E (Ioi 0) := by
    rw [hE]; exact integrableOn_exp_mul_Ioi (by linarith) 0
  have hint : IntegrableOn (fun d : ℝ => ∑' γ : Zgamma, F γ d) (Ioi 0) := by
    refine (hEint.const_mul (∑' γ, ‖c γ‖)).mono'
      ((hcont.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun d hd => ?_)
    rw [← tsum_mul_right]
    exact tsum_of_norm_bounded (hcn.mul_right (E d)).hasSum fun γ => hFle γ d (le_of_lt hd)
  have hint' : IntegrableOn (fun d : ℝ => zeroSumFun a d * Complex.exp (-s * d)) (Ioi 0) := by
    simp_rw [hpt]; exact hint
  -- summability of the pole coefficients
  have hpole : ∀ γ : Zgamma, (mult (γ : ℂ) : ℂ) * poleCoeff a s γ = c γ / -(A γ) := by
    intro γ; simp only [poleCoeff, hc, hA, neg_neg]; ring
  have hnormA : ∀ γ : Zgamma, σ - 1 / 2 ≤ ‖-(A γ)‖ := by
    intro γ
    calc σ - 1 / 2 ≤ -(A γ).re := by have := hAneg γ; linarith
      _ = (-(A γ)).re := by simp
      _ ≤ ‖-(A γ)‖ := Complex.re_le_norm _
  have hpoleS : ZeroSummable (poleCoeff a s) := by
    show Summable fun γ : Zgamma => (mult (γ : ℂ) : ℂ) * poleCoeff a s γ
    simp_rw [hpole]
    refine Summable.of_norm_bounded (hcn.mul_right (σ - 1 / 2)⁻¹) fun γ => ?_
    rw [norm_div, div_eq_mul_inv]
    gcongr
    exact hnormA γ
  refine ⟨hint', hpoleS, ?_⟩
  -- the integral identity, via the countable support of `c`
  set S : Set Zgamma := Function.support c with hS
  have hSc : S.Countable := hcs.countable_support
  have : Countable S := hSc.to_subtype
  have hsuppF : ∀ d : ℝ, Function.support (fun γ => F γ d) ⊆ S := by
    intro d γ hγ h0
    apply hγ
    simp only [hF]
    rw [show c γ = 0 from by simpa [hS] using h0, zero_mul]
  have hsuppP : Function.support (fun γ : Zgamma => c γ / -(A γ)) ⊆ S := by
    intro γ hγ h0
    apply hγ
    show c γ / -(A γ) = 0
    rw [show c γ = 0 from by simpa [hS] using h0, zero_div]
  have hFint : ∀ γ : Zgamma, IntegrableOn (F γ) (Ioi 0) := fun γ =>
    (integrableOn_exp_mul_complex_Ioi (hAneg γ |>.trans (by linarith)) 0).const_mul (c γ)
  have hFval : ∀ γ : Zgamma, ∫ d in Ioi (0 : ℝ), F γ d = c γ / -(A γ) := by
    intro γ
    simp only [hF]
    rw [integral_const_mul, integral_exp_mul_complex_Ioi
      (hAneg γ |>.trans (by linarith)) 0]
    simp [div_neg, neg_div]
    rw [div_eq_mul_inv]
  have hFnorm : ∀ γ : Zgamma, ∫ d in Ioi (0 : ℝ), ‖F γ d‖ = ‖c γ‖ * (-(A γ).re)⁻¹ := by
    intro γ
    simp only [hF, norm_mul, norm_cexp_mul_ofReal]
    rw [integral_const_mul, integral_exp_mul_Ioi (hAneg γ |>.trans (by linarith)) 0]
    simp [neg_div, inv_neg]
  have hFsum : Summable fun γ : S => ∫ d in Ioi (0 : ℝ), ‖F γ d‖ := by
    refine Summable.of_nonneg_of_le (fun γ => integral_nonneg fun _ => norm_nonneg _)
      (fun γ => ?_) ((hcn.mul_right (σ - 1 / 2)⁻¹).subtype S)
    rw [hFnorm]
    show _ ≤ ‖c γ‖ * (σ - 1 / 2)⁻¹
    gcongr
    have := hAneg γ; linarith
  calc laplace (zeroSumFun a) s
      = ∫ d in Ioi (0 : ℝ), ∑' γ : Zgamma, F γ d := by
        rw [laplace]; exact integral_congr_ae (Eventually.of_forall hpt)
    _ = ∫ d in Ioi (0 : ℝ), ∑' γ : S, F γ d := by
        congr 1; funext d; exact (tsum_subtype_eq_of_support_subset (hsuppF d)).symm
    _ = ∑' γ : S, ∫ d in Ioi (0 : ℝ), F γ d :=
        (integral_tsum_of_summable_integral_norm (F := fun (γ : S) d => F γ d)
          (fun γ => hFint γ) hFsum).symm
    _ = ∑' γ : S, c γ / -(A γ) := by
        congr 1; funext γ; exact hFval γ
    _ = ∑' γ : Zgamma, c γ / -(A γ) := tsum_subtype_eq_of_support_subset hsuppP
    _ = zeroSum (poleCoeff a s) := by
        rw [zeroSum]; congr 1; funext γ; exact (hpole γ).symm

/-! ## 3. Laplace integrability of a (G1) remainder -/

/-- A continuous `PolyBounded` `r` has `d ↦ r(d) e^{−sd}` integrable on `(0,∞)` for `Re s > 0`. -/
theorem polyBounded_laplace_integrable {r : ℝ → ℂ} (hrc : Continuous r) (hrb : PolyBounded r)
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun d : ℝ => r d * Complex.exp (-s * d)) (Ioi 0) := by
  obtain ⟨C, hC⟩ := hrb
  have hO : (fun d : ℝ => (1 + d ^ 2) * Real.exp (-s.re * d)) =O[atTop]
      fun d => Real.exp (-(s.re / 2) * d) := by
    have h1 : (fun d : ℝ => 1 + d ^ 2) =O[atTop] fun d => Real.exp (s.re / 2 * d) := by
      refine IsBigO.add ?_ ?_
      · simpa using (isLittleO_pow_exp_pos_mul_atTop 0 (by linarith : 0 < s.re / 2)).isBigO
      · exact (isLittleO_pow_exp_pos_mul_atTop 2 (by linarith : 0 < s.re / 2)).isBigO
    refine (h1.mul (isBigO_refl (fun d : ℝ => Real.exp (-s.re * d)) atTop)).congr_right ?_
    intro d; rw [← Real.exp_add]; ring_nf
  have hg : IntegrableOn (fun d : ℝ => C * ((1 + d ^ 2) * Real.exp (-s.re * d))) (Ioi 0) :=
    (integrable_of_isBigO_exp_neg (by linarith) (by fun_prop) hO).const_mul C
  refine hg.mono' ((hrc.mul (by fun_prop)).aestronglyMeasurable) ?_
  refine Eventually.of_forall fun d => ?_
  rw [norm_mul, show -s * (d : ℂ) = (-s) * d from rfl, norm_cexp_mul_ofReal, Complex.neg_re,
    ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hC d) (Real.exp_pos _).le

/-! ## 4. Assembly `LaplaceL → IdentityStep → SpectralMatching` (PROVED) -/

/-- **Assembly.** `LaplaceL → IdentityStep → SpectralMatching` (this direction only). -/
theorem spectralMatching_of_split (hL : LaplaceL) (hI : IdentityStep) : SpectralMatching := by
  intro a Q h r hQ hdeg hh hrc hrb hzs
  have ha : ZeroSummable a := by
    simpa [ZeroSummable, expTerm] using (hzs 0).1
  refine hI a Q h r hQ hdeg hh hrc hrb ha fun s hs => ?_
  obtain ⟨hint, -, hlap⟩ := hL a ha s hs
  have hr := polyBounded_laplace_integrable hrc hrb (s := s) (by linarith)
  have hfun : (fun d : ℝ => h d * Complex.exp (-s * d)) =
      fun d => zeroSumFun a d * Complex.exp (-s * d) - r d * Complex.exp (-s * d) := by
    funext d; rw [zeroSumFun, (hzs d).2]; ring
  have hhint : IntegrableOn (fun d : ℝ => h d * Complex.exp (-s * d)) (Ioi 0) := by
    rw [hfun]; exact hint.sub hr
  refine ⟨hhint, ?_⟩
  rw [← hlap, laplace, laplace, laplace, ← integral_add hhint hr]
  congr 1; funext d; rw [zeroSumFun, (hzs d).2]; ring

/-- With (L) discharged: `IdentityStep → SpectralMatching`. -/
theorem spectralMatching_of_identityStep (hI : IdentityStep) : SpectralMatching :=
  spectralMatching_of_split laplaceL hI

/-- **Honesty check.** RH implies `IdentityStep` (no lower zeros): the premise is not free. -/
theorem identityStep_of_RH (hRH : RiemannHypothesis) : IdentityStep := by
  intro _ _ _ _ _ _ _ _ _ _ _ γ hγ him _
  exact (no_lower_zero_of_RH hRH hγ him).elim

/-! ## 5. Refined chains (PROVED, conditional) -/

/-- The chain with `SpectralMatching` split into (L) and the identity step. -/
def HPsiLaplaceChain : Prop :=
  HPsi → HEF → KreinDecomp → LaplaceL → IdentityStep → RiemannHypothesis

theorem hPsiLaplaceChain : HPsiLaplaceChain := fun h hE hD hL hI =>
  hPsiFineChain h hE hD (spectralMatching_of_split hL hI)

/-- The chain with (L) discharged: four named premises. -/
def HPsiIdentityChain : Prop := HPsi → HEF → KreinDecomp → IdentityStep → RiemannHypothesis

theorem hPsiIdentityChain : HPsiIdentityChain := fun h hE hD hI =>
  hPsiLaplaceChain h hE hD laplaceL hI

end GppSpectralMatchingSplit

#print axioms GppSpectralMatchingSplit.neg_half_lt_im
#print axioms GppSpectralMatchingSplit.norm_cexp_mul_ofReal
#print axioms GppSpectralMatchingSplit.laplaceL
#print axioms GppSpectralMatchingSplit.polyBounded_laplace_integrable
#print axioms GppSpectralMatchingSplit.spectralMatching_of_split
#print axioms GppSpectralMatchingSplit.spectralMatching_of_identityStep
#print axioms GppSpectralMatchingSplit.identityStep_of_RH
#print axioms GppSpectralMatchingSplit.hPsiLaplaceChain
#print axioms GppSpectralMatchingSplit.hPsiIdentityChain
