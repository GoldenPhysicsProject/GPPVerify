/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Heart of the Cosmos (Grok, GPPDiscovery5 seat). Turbo PR #11 6831568718, "next exact
instruction": prove `CoeffVanish` as stated, then assemble `ExpLaplaceMero`.

# `CoeffVanish` PROVED; `ExpLaplaceMero` PROVED

1. **`CoeffVanish` PROVED as stated** (`GppPoleMeroProof.CoeffVanish`, not widened, not
   restated). `Re(iβ̄) = −Re(iβ)` (`re_I_mul_conj`), so at most one block grows. For the block
   with `a := Re(iβ) > 1/2` take the real point `s := (1/2 + a)/2 ∈ (1/2, a)`. The other block
   times `e^{−sd}` has exponent real part `−a − s < 0`, so it is integrable
   (`block_integrable`: `integrableOn_exp_mul_complex_Ioi` + `mul_cexp_integrable`).
   Subtracting it from the integrable sum leaves `(c₀ + c₁d)e^{(iβ − s)d}` integrable on
   `(0,∞)` with `ε := Re(iβ − s) > 0`. Its norm is `‖c₀ + c₁d‖ e^{εd}`. If `c₁ ≠ 0` this is
   `≥ 1` for `d ≥ (1 + ‖c₀‖)/‖c₁‖`; if `c₁ = 0, c₀ ≠ 0` it is `≥ ‖c₀‖` for `d ≥ 0`. A function
   bounded below by a positive constant on a half-line is not integrable on `(0,∞)`
   (`not_integrableOn_of_norm_ge`: `Integrable.measure_norm_ge_lt_top` vs
   `Real.volume_Ici = ∞`). Hence `c₀ = c₁ = 0` (`grow_vanish`, `block_vanish`). The conjugate
   block is the same lemma with the two blocks swapped.
2. **`ExpLaplaceMero` PROVED as stated** (`GppIdentityStepSplit.ExpLaplaceMero`, not widened).
   For `h = 0` take `H = 0`. Otherwise `h = (c₀ + c₁d)e^{iβd} + (c₂ + c₃d)e^{iβ̄d}` with
   `Q(β) = 0`; take the rational function
   `H(s) = c₀/(s − iβ) + c₁/(s − iβ)² + c₂/(s − iβ̄) + c₃/(s − iβ̄)²`.
   By `CoeffVanish` each block either has vanishing coefficients or has `Re w ≤ 1/2 < Re s`
   (`w = iβ` or `iβ̄`), so `Re(w − s) < 0` and `∫_{(0,∞)} (c + c'd)e^{(w−s)d} dd =
   c/(s − w) + c'/(s − w)²` (`block_laplace`: `integral_exp_mul_complex_Ioi` and the `1/z²`
   integral `integral_mul_cexp_Ioi`). So `H = L[h]` on `Re s > 1/2`; `H` is meromorphic on `H0`
   and analytic off `iβ, iβ̄`.
3. Consequences: `identityStep : IdentityStep` (unconditional, via
   `identityStep_of_expLaplaceMero`), and the fine chain is
   `hPsiKreinChain : HPsi → KreinDecomp → RiemannHypothesis`. `KreinDecomp`, `HPsi` untouched.

No converse claimed. H_ψ: OPEN. ARP: OPEN. RH: OPEN.
-/
import GppVerify.RiemannHypothesis.PoleMeroProof

namespace GppExpLaplaceMeroProof

open GppKreinBridge GppKreinHPsi GppKreinHPsiChain GppKreinPoleSplit GppKreinRepSplit
  GppSpectralMatchingSplit GppIdentityStepSplit GppPoleMeroProof ComplexConjugate MeasureTheory
  Set Filter Topology

/-! ## 1. Elementary facts (PROVED) -/

/-- `Re(iβ̄) = −Re(iβ)`. -/
theorem re_I_mul_conj (β : ℂ) : (Complex.I * conj β).re = -(Complex.I * β).re := by
  simp [Complex.mul_re]

/-- `‖(c₀ + c₁d) e^{wd}‖ = ‖c₀ + c₁d‖ e^{(Re w) d}`. -/
theorem norm_block (c₀ c₁ w : ℂ) (d : ℝ) :
    ‖(c₀ + c₁ * d) * Complex.exp (w * d)‖ = ‖c₀ + c₁ * d‖ * Real.exp (w.re * d) := by
  rw [norm_mul, Complex.norm_exp]
  simp [Complex.mul_re]

/-- A function bounded below by a positive constant on a half-line is not integrable on
`(0,∞)`. -/
theorem not_integrableOn_of_norm_ge {f : ℝ → ℂ} {δ T : ℝ} (hδ : 0 < δ)
    (hf : ∀ d : ℝ, T ≤ d → δ ≤ ‖f d‖) : ¬ IntegrableOn f (Ioi 0) := by
  intro hi
  have h1 := Integrable.measure_norm_ge_lt_top hi hδ
  rw [Measure.restrict_apply' measurableSet_Ioi] at h1
  have h2 : Ici (max T 1) ⊆ {x | δ ≤ ‖f x‖} ∩ Ioi 0 := fun x hx =>
    ⟨hf x (le_trans (le_max_left _ _) hx),
      lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) (mem_Ici.mp hx))⟩
  have h3 := measure_mono (μ := (volume : Measure ℝ)) h2
  rw [Real.volume_Ici] at h3
  exact lt_irrefl _ (lt_of_le_of_lt h3 h1)

/-- **Growth forces vanishing (PROVED).** If `Re w > 0` and `(c₀ + c₁d)e^{wd}` is integrable on
`(0,∞)`, then `c₀ = c₁ = 0`. -/
theorem grow_vanish {c₀ c₁ w : ℂ} (hε : 0 < w.re)
    (h : IntegrableOn (fun d : ℝ => (c₀ + c₁ * d) * Complex.exp (w * d)) (Ioi 0)) :
    c₀ = 0 ∧ c₁ = 0 := by
  have hc₁ : c₁ = 0 := by
    by_contra hc
    have hpos : 0 < ‖c₁‖ := norm_pos_iff.mpr hc
    refine not_integrableOn_of_norm_ge (δ := 1) (T := (1 + ‖c₀‖) / ‖c₁‖) one_pos ?_ h
    intro d hd
    have hT : 0 ≤ (1 + ‖c₀‖) / ‖c₁‖ := by positivity
    have hd0 : 0 ≤ d := le_trans hT hd
    rw [norm_block]
    have hd' : 1 + ‖c₀‖ ≤ ‖c₁‖ * d := by
      rw [div_le_iff₀ hpos] at hd; linarith
    have hn : ‖(c₁ : ℂ) * d‖ = ‖c₁‖ * d := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hd0]
    have htri : ‖(c₁ : ℂ) * d‖ ≤ ‖c₀ + c₁ * d‖ + ‖c₀‖ := by
      have := norm_sub_le (c₀ + c₁ * d) c₀
      simpa using this
    have h1 : 1 ≤ ‖c₀ + c₁ * d‖ := by linarith
    have h2 : 1 ≤ Real.exp (w.re * d) := Real.one_le_exp (mul_nonneg hε.le hd0)
    exact one_le_mul_of_one_le_of_one_le h1 h2
  subst hc₁
  refine ⟨?_, rfl⟩
  by_contra hc
  have hpos : 0 < ‖c₀‖ := norm_pos_iff.mpr hc
  refine not_integrableOn_of_norm_ge (δ := ‖c₀‖) (T := 0) hpos ?_ h
  intro d hd0
  rw [norm_block]
  simp only [zero_mul, add_zero]
  exact le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (mul_nonneg hε.le hd0))

/-- Rewriting a block against `e^{−sd}`. -/
theorem block_mul_exp (c₀ c₁ w s : ℂ) (d : ℝ) :
    (c₀ + c₁ * d) * Complex.exp (w * d) * Complex.exp (-s * d) =
      c₀ * Complex.exp ((w - s) * d) + c₁ * ((d : ℂ) * Complex.exp ((w - s) * d)) := by
  rw [mul_assoc, ← Complex.exp_add]
  have : w * d + -s * d = (w - s) * d := by ring
  rw [this]; ring

/-- A decaying block is integrable against `e^{−sd}` (PROVED). -/
theorem block_integrable {c₀ c₁ w s : ℂ} (hz : (w - s).re < 0) :
    IntegrableOn (fun d : ℝ =>
      (c₀ + c₁ * d) * Complex.exp (w * d) * Complex.exp (-s * d)) (Ioi 0) := by
  have h : IntegrableOn (fun d : ℝ =>
      c₀ * Complex.exp ((w - s) * d) + c₁ * ((d : ℂ) * Complex.exp ((w - s) * d))) (Ioi 0) :=
    ((integrableOn_exp_mul_complex_Ioi hz 0).const_mul c₀).add
      ((mul_cexp_integrable hz).const_mul c₁)
  exact IntegrableOn.congr_fun h (fun d _ => (block_mul_exp c₀ c₁ w s d).symm) measurableSet_Ioi

/-- **Laplace transform of a decaying block (PROVED).**
`∫_{(0,∞)} (c₀ + c₁d)e^{wd}e^{−sd} dd = c₀/(s − w) + c₁/(s − w)²` for `Re(w − s) < 0`. -/
theorem block_laplace_of_re {c₀ c₁ w s : ℂ} (hz : (w - s).re < 0) :
    ∫ d : ℝ in Ioi 0, (c₀ + c₁ * d) * Complex.exp (w * d) * Complex.exp (-s * d) =
      c₀ / (s - w) + c₁ / (s - w) ^ 2 := by
  have hz0 : w - s ≠ 0 := fun h => by simp [h] at hz
  simp_rw [block_mul_exp]
  rw [integral_add ((integrableOn_exp_mul_complex_Ioi hz 0).const_mul c₀)
    ((mul_cexp_integrable hz).const_mul c₁), integral_const_mul, integral_const_mul,
    integral_exp_mul_complex_Ioi hz 0, integral_mul_cexp_Ioi hz]
  have hs0 : s - w ≠ 0 := fun h => hz0 (by rw [← neg_sub, h, neg_zero])
  have e1 : -Complex.exp ((w - s) * ((0 : ℝ) : ℂ)) / (w - s) = 1 / (s - w) := by
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, ← neg_sub s w, div_neg, neg_div,
      neg_neg]
  have e2 : (1 : ℂ) / (w - s) ^ 2 = 1 / (s - w) ^ 2 := by
    rw [← neg_sub s w, neg_sq]
  rw [e1, e2]; ring

/-- A block that is either zero or has `Re w ≤ 1/2`, against `e^{−sd}` with `Re s > 1/2`. -/
theorem block_laplace {c₀ c₁ w s : ℂ} (hc : (c₀ = 0 ∧ c₁ = 0) ∨ w.re ≤ 1 / 2)
    (hs : 1 / 2 < s.re) :
    IntegrableOn (fun d : ℝ =>
      (c₀ + c₁ * d) * Complex.exp (w * d) * Complex.exp (-s * d)) (Ioi 0) ∧
    ∫ d : ℝ in Ioi 0, (c₀ + c₁ * d) * Complex.exp (w * d) * Complex.exp (-s * d) =
      c₀ / (s - w) + c₁ / (s - w) ^ 2 := by
  rcases hc with ⟨rfl, rfl⟩ | hw
  · simp
  · have hz : (w - s).re < 0 := by rw [Complex.sub_re]; linarith
    exact ⟨block_integrable hz, block_laplace_of_re hz⟩

/-! ## 2. `CoeffVanish` PROVED (as stated) -/

/-- **The growing block vanishes (PROVED).** If `Re w₂ = −Re w₁`, `Re w₁ > 1/2`, and the sum of
the two blocks is integrable against `e^{−sd}` for every `Re s > 1/2`, then `c₀ = c₁ = 0`. -/
theorem block_vanish {w₁ w₂ c₀ c₁ c₂ c₃ : ℂ} (hw : w₂.re = -w₁.re) (ha : 1 / 2 < w₁.re)
    (hint : ∀ s : ℂ, 1 / 2 < s.re → IntegrableOn (fun d : ℝ =>
      ((c₀ + c₁ * d) * Complex.exp (w₁ * d) +
        (c₂ + c₃ * d) * Complex.exp (w₂ * d)) * Complex.exp (-s * d)) (Ioi 0)) :
    c₀ = 0 ∧ c₁ = 0 := by
  set r : ℝ := (1 / 2 + w₁.re) / 2 with hr
  have hs : 1 / 2 < ((r : ℂ)).re := by rw [Complex.ofReal_re, hr]; linarith
  have hF := hint (r : ℂ) hs
  have hz₂ : (w₂ - (r : ℂ)).re < 0 := by
    rw [Complex.sub_re, Complex.ofReal_re, hw, hr]; linarith
  have hG := block_integrable (c₀ := c₂) (c₁ := c₃) hz₂
  have hε : 0 < (w₁ - (r : ℂ)).re := by
    rw [Complex.sub_re, Complex.ofReal_re, hr]; linarith
  refine grow_vanish hε ((hF.sub hG).congr_fun (fun d _ => ?_) measurableSet_Ioi)
  simp only [Pi.sub_apply]
  rw [add_mul, add_sub_cancel_right, mul_assoc, ← Complex.exp_add]
  congr 2; ring

/-- **`CoeffVanish` PROVED**, exactly as stated in `PoleMeroProof` (not widened). -/
theorem coeffVanish : CoeffVanish := by
  intro β c₀ c₁ c₂ c₃ hint
  have hre := re_I_mul_conj β
  refine ⟨fun ha => block_vanish hre ha hint, fun ha => ?_⟩
  refine block_vanish (w₁ := Complex.I * conj β) (w₂ := Complex.I * β) (c₂ := c₀) (c₃ := c₁)
    (by linarith) ha (fun s hs => (hint s hs).congr_fun (fun d _ => by ring) measurableSet_Ioi)

/-- Dichotomy for a block: vanishing coefficients, or `Re w ≤ 1/2`. -/
theorem block_dichotomy {c₀ c₁ w : ℂ} (h : 1 / 2 < w.re → c₀ = 0 ∧ c₁ = 0) :
    (c₀ = 0 ∧ c₁ = 0) ∨ w.re ≤ 1 / 2 :=
  (le_or_gt w.re (1 / 2)).elim Or.inr fun hw => Or.inl (h hw)

/-! ## 3. `ExpLaplaceMero` PROVED (as stated) -/

/-- The rational function `c₀/(s − w) + c₁/(s − w)²`. -/
noncomputable def ratBlock (c₀ c₁ w : ℂ) (s : ℂ) : ℂ := c₀ / (s - w) + c₁ / (s - w) ^ 2

theorem meromorphicAt_ratBlock (c₀ c₁ w z : ℂ) : MeromorphicAt (ratBlock c₀ c₁ w) z := by
  unfold ratBlock
  have h1 : MeromorphicAt (fun s : ℂ => s - w) z := (analyticAt_id.sub analyticAt_const).meromorphicAt
  exact ((MeromorphicAt.const c₀ z).div h1).add ((MeromorphicAt.const c₁ z).div (h1.pow 2))

theorem analyticAt_ratBlock (c₀ c₁ : ℂ) {w z : ℂ} (hz : z ≠ w) :
    AnalyticAt ℂ (ratBlock c₀ c₁ w) z := by
  unfold ratBlock
  have h1 : AnalyticAt ℂ (fun s : ℂ => s - w) z := analyticAt_id.sub analyticAt_const
  have h0 : z - w ≠ 0 := sub_ne_zero.mpr hz
  exact (analyticAt_const.div h1 h0).add (analyticAt_const.div (h1.pow 2) (pow_ne_zero 2 h0))

/-- **`ExpLaplaceMero` PROVED**, exactly as stated in `IdentityStepSplit` (not widened). -/
theorem expLaplaceMero : ExpLaplaceMero := by
  intro Q h hE hint
  rcases hE with rfl | ⟨β, hβ, c₀, c₁, c₂, c₃, hh⟩
  · refine ⟨fun _ => 0, fun z _ => MeromorphicAt.const 0 z, fun s _ => ?_,
      fun z _ _ => analyticAt_const⟩
    simp [laplace]
  · obtain rfl : h = _ := funext hh
    have hcv := coeffVanish β c₀ c₁ c₂ c₃ hint
    refine ⟨fun s => ratBlock c₀ c₁ (Complex.I * β) s + ratBlock c₂ c₃ (Complex.I * conj β) s,
      fun z _ => (meromorphicAt_ratBlock _ _ _ z).add (meromorphicAt_ratBlock _ _ _ z),
      fun s hs => ?_, fun z _ hz => ?_⟩
    · obtain ⟨hi₁, he₁⟩ := block_laplace (block_dichotomy hcv.1) hs
      obtain ⟨hi₂, he₂⟩ := block_laplace (block_dichotomy hcv.2) hs
      unfold ratBlock laplace
      beta_reduce
      rw [← he₁, ← he₂, ← integral_add hi₁ hi₂]
      congr 1; funext d; ring
    · obtain ⟨h1, h2⟩ := hz β hβ
      exact (analyticAt_ratBlock c₀ c₁ h1).add (analyticAt_ratBlock c₂ c₃ h2)

/-! ## 4. Consequences (PROVED) -/

/-- **`IdentityStep` PROVED** (unconditionally): `PoleMero`, `LaplaceHolo`, `ExpLaplaceMero` are
all discharged. -/
theorem identityStep : IdentityStep := identityStep_of_expLaplaceMero expLaplaceMero

/-- The fine chain is now two named premises: `HPsi` and `KreinDecomp`. -/
def HPsiKreinChain : Prop := HPsi → KreinDecomp → RiemannHypothesis

theorem hPsiKreinChain : HPsiKreinChain := fun h hD => hPsiExpChain h hD expLaplaceMero

end GppExpLaplaceMeroProof

#print axioms GppExpLaplaceMeroProof.re_I_mul_conj
#print axioms GppExpLaplaceMeroProof.norm_block
#print axioms GppExpLaplaceMeroProof.not_integrableOn_of_norm_ge
#print axioms GppExpLaplaceMeroProof.grow_vanish
#print axioms GppExpLaplaceMeroProof.block_mul_exp
#print axioms GppExpLaplaceMeroProof.block_integrable
#print axioms GppExpLaplaceMeroProof.block_laplace_of_re
#print axioms GppExpLaplaceMeroProof.block_laplace
#print axioms GppExpLaplaceMeroProof.block_vanish
#print axioms GppExpLaplaceMeroProof.coeffVanish
#print axioms GppExpLaplaceMeroProof.block_dichotomy
#print axioms GppExpLaplaceMeroProof.meromorphicAt_ratBlock
#print axioms GppExpLaplaceMeroProof.analyticAt_ratBlock
#print axioms GppExpLaplaceMeroProof.expLaplaceMero
#print axioms GppExpLaplaceMeroProof.identityStep
#print axioms GppExpLaplaceMeroProof.hPsiKreinChain
