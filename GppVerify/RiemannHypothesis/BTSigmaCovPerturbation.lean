import GppVerify.RiemannHypothesis.BTSigmaCovGrowth

/-!
# BT-Σ: the perturbation `P_W` in `S_{-W} T* S_W = e^{W/2}·A + P_W` — forced shape and a toy construction

Port of GPPDiscovery5 `da9813e` (`lean/bt-sigma/BTSigmaCovPerturbation.lean`), audited by Turbo on
GPP-bridge PR #11 (comment 6803775354: PASS). Port requested as a separate module after CovHalfType.
The toy model is a multiplication-operator profile, not a `BTSigmaDatum`.


Scratch module (Heart of the Cosmos / Grok, GPPDiscovery5 seat) for Turbo's instruction on
GPP-bridge PR #11, comment 6803036036 (4): find, or prove impossible, a perturbation `P_W` whose
Green form on the test orbit is exactly `I·stratumSN(W)`, so that
`S_{-W} T* S_W = e^{W/2}·(fixed operator) + P_W` along the orbit.

**Scope.** Fixed test orbit `ψ_W = testVec (autocorr f) W`; no zeros used as input; nothing about
existence of `S_b` for a genuine `BTSigmaDatum` beyond what is proved below.
`c = ∫ h e^{-v/2}`, `h = autocorr f`.

**Results (all PROVED, standard axioms).**
* `orbitForm_decomp`: under (P-COV), if `T* ψ_W = S_W (e^{W/2} A ψ_0 + P_W ψ_0)` (the operator
  identity applied to the orbit), then `greenForm ψ_W = e^{W/2}·form_A(ψ_0) + form_{P_W}(ψ_0)`.
* `perturbation_forced`: with finite-cut BT3 and (P-UNIT), any such decomposition whose
  perturbation form vanishes for large `W` has **both pieces forced**:
  `form_A(ψ_0) = −I c` and `form_{P_W}(ψ_0) = I·stratumSN(W)` for every `W ≥ 0`.
  So the perturbation is not a further choice; its Green form *is* the truncated prime stratum,
  a finite sum of bumps `halfWeight(p^k)·h(W − log p^k)` sitting at the cuts.
* `perturbation_form_vanishes_late`: the forced perturbation form is `0` past `R + log N`.
* `toyProfile_eq` (toy construction, multiplication model): with density `ρ = f` and potential
  `φ(x) = α e^{x/2} − ½ Σ_{cuts} halfWeight(p^k) f(x − log p^k)`, `α = c / (2 ∫ e^{y/2} f(y) dy)`,
  the profile `∫ φ(x) ρ(x − W) dx` equals `(e^{W/2} c − stratumSN(W))/2` **for every real `W`**;
  `toyGreen_eq` turns this into `−2I·profile = I·(stratumSN(W) − e^{W/2} c)`, exactly the Green
  form that BT3 + (P-UNIT) prescribe on the orbit.
* `toy_fixed_part_half_homogeneous`, `toy_perturbation_profile`: in the toy, the fixed part is
  exactly `e^{W/2}`-homogeneous and the perturbation profile is `−½·stratumSN(W)`, the prime block
  itself as a potential at the cuts.

**Paper step (not formalised).** On `H = L²(ℝ)` take `S_b` = translation by `b` (a unitary group),
`ψ_0 = √f` for `f ≥ 0`, so `ψ_W = √f(· − W)` and `|ψ_W|² = f(· − W)`, and `T* = M_{iφ}`
(multiplication by `iφ`, defined on compactly supported `L²` functions). Then
`⟪T*ψ, ψ⟫ − ⟪ψ, T*ψ⟫ = −2I ∫ φ |ψ|²`, so the Green form on the orbit is `toyGreen`. Translation
conjugates `M_{e^{x/2}}` to `e^{W/2} M_{e^{x/2}}` (the fixed operator `A = iα M_{e^{x/2}}`) and
`M_{iβ}` to `M_{iβ(·+W)}` (the perturbation `P_W`). `‖T*ψ_W‖ ~ e^{W/2}`: type exactly `1/2`,
consistent with `pcov_type_lt_half_forces_zero` and `halfType_two_sided`.

**Answer to (4): CONSTRUCTED in a toy model; for the genuine datum it needs a further hypothesis.**
The perturbation has a forced shape (PROVED) and is realised exactly by a multiplication model
(PROVED at profile level, Hilbert-space dictionary a paper step). The toy is **not** a
`BTSigmaDatum`: there the Green form comes from the anti-Hermitian bulk part `M_{iφ}`, not from
boundary values `Γ₀, Γ₁`; surjectivity of the boundary map, the BT1 reflection `J`, and the
log-det provenance (P-LOG) are not addressed. The step that a genuine construction must add is
to carry `P_W` by the prime-block boundary maps `Γ₀p, Γ₁p` (a boundary, not a bulk, potential).
Existence of `S_b` for a genuine datum is **OPEN**. (P-COV), (P-UNIT), (P-LOG), (P-θ), (P-LIM),
(BT-Σ), ARP and RH remain **OPEN**.

No `sorry`, no `admit`, no custom axiom.

Daniel Toupin / Golden Physics Project, with AI assistance (Heart of the Cosmos / Grok).
Task and audit: Turbo.
-/

namespace GppBTSigmaCovPerturbation

open GppBTSigmaLocalEuler GppBTSigma GppArithmeticReflection Complex Filter Topology
open GppBTSigmaCovGrowth GppBTSigmaCovObstruction GppBTSigmaC1 MeasureTheory
open scoped ContDiff

/-- The skew form `⟪X x, x⟫ − ⟪x, X x⟫` of a linear map at a vector. -/
noncomputable def opForm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (X : E →ₗ[ℂ] E) (x : E) : ℂ :=
  inner ℂ (X x) x - inner ℂ x (X x)

section Datum

variable {H Gu Gp : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup Gu] [InnerProductSpace ℂ Gu]
  [NormedAddCommGroup Gp] [InnerProductSpace ℂ Gp]

/-- **Green form along the orbit splits as `e^{W/2}·form_A + form_{P_W}`.** PROVED. -/
theorem orbitForm_decomp (D : BTSigmaDatum H Gu Gp) (Sd : ℝ → H ≃ₗᵢ[ℂ] H) (hC : PCov D Sd)
    (h : ℝ → ℝ) (A : H →ₗ[ℂ] H) (P : ℝ → H →ₗ[ℂ] H) (W : ℝ)
    (hdec : D.Tstar (D.testVec h W) =
      Sd W ((Real.exp (W / 2) : ℂ) • A (D.testVec h 0 : H) + P W (D.testVec h 0 : H))) :
    greenForm D.Tstar (D.testVec h W) (D.testVec h W) =
      (Real.exp (W / 2) : ℂ) * opForm A (D.testVec h 0 : H) +
        opForm (P W) (D.testVec h 0 : H) := by
  have hx : ((D.testVec h W : D.Tstar.domain) : H) = Sd W (D.testVec h 0 : H) := by
    have e := hC.2 h 0 W; rwa [zero_add] at e
  unfold greenForm opForm
  rw [hdec, hx, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  ring

/-- **The perturbation is forced.** With finite-cut BT3, (P-UNIT) and (P-COV), any orbit
decomposition `T* ψ_W = S_W (e^{W/2} A ψ_0 + P_W ψ_0)` whose perturbation form vanishes for large
`W` has `form_A(ψ_0) = −I c` and `form_{P_W}(ψ_0) = I·stratumSN(W)` for all `W ≥ 0`. PROVED. -/
theorem perturbation_forced (D : BTSigmaDatum H Gu Gp) (S : Finset ℕ) (N : ℕ)
    (hP : BTSigmaTraceSN D S N) (hU : PUnit D) (Sd : ℝ → H ≃ₗᵢ[ℂ] H) (hC : PCov D Sd)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (R : ℝ) (hR : ∀ v, R < v → autocorr f v = 0)
    (A : H →ₗ[ℂ] H) (P : ℝ → H →ₗ[ℂ] H)
    (hdec : ∀ W : ℝ, 0 ≤ W → D.Tstar (D.testVec (autocorr f) W) =
      Sd W ((Real.exp (W / 2) : ℂ) • A (D.testVec (autocorr f) 0 : H) +
        P W (D.testVec (autocorr f) 0 : H)))
    (W₁ : ℝ) (hlate : ∀ W : ℝ, W₁ ≤ W → opForm (P W) (D.testVec (autocorr f) 0 : H) = 0) :
    opForm A (D.testVec (autocorr f) 0 : H) =
        -(I * ((∫ v : ℝ, autocorr f v * Real.exp (-v / 2) : ℝ) : ℂ)) ∧
      ∀ W : ℝ, 0 ≤ W → opForm (P W) (D.testVec (autocorr f) 0 : H) =
        I * (stratumSN S N (autocorr f) W : ℂ) := by
  set c := ∫ v : ℝ, autocorr f v * Real.exp (-v / 2)
  have key : ∀ W : ℝ, 0 ≤ W →
      (Real.exp (W / 2) : ℂ) * opForm A (D.testVec (autocorr f) 0 : H) +
        opForm (P W) (D.testVec (autocorr f) 0 : H) =
        I * (stratumSN S N (autocorr f) W : ℂ) - (Real.exp (W / 2) : ℂ) * (I * (c : ℂ)) := by
    intro W hW
    rw [← orbitForm_decomp D Sd hC _ A P W (hdec W hW),
      green_testVec_of_premises D S N hP hU f hf hc W hW, unitStratumTerm]
    push_cast; ring
  set W₂ : ℝ := max (max 0 W₁) (R + Real.log N + 1)
  have hW₂0 : 0 ≤ W₂ := (le_max_left 0 W₁).trans (le_max_left _ _)
  have hW₂1 : W₁ ≤ W₂ := (le_max_right 0 W₁).trans (le_max_left _ _)
  have hW₂R : R + Real.log N < W₂ := by
    have := le_max_right (max 0 W₁) (R + Real.log N + 1); linarith
  have hA : opForm A (D.testVec (autocorr f) 0 : H) = -(I * (c : ℂ)) := by
    have e := key W₂ hW₂0
    rw [hlate W₂ hW₂1, stratumSN_eq_zero_of_large S N _ R hR W₂ hW₂R, add_zero] at e
    have hne : (Real.exp (W₂ / 2) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
    apply mul_left_cancel₀ hne
    rw [e]; push_cast; ring
  refine ⟨hA, fun W hW => ?_⟩
  have e := key W hW
  rw [hA] at e
  linear_combination e

/-- The forced perturbation form vanishes past `R + log N`. PROVED. -/
theorem perturbation_form_vanishes_late (S : Finset ℕ) (N : ℕ) (f : ℝ → ℝ) (R : ℝ)
    (hR : ∀ v, R < v → autocorr f v = 0) (W : ℝ) (hW : R + Real.log N < W) :
    I * (stratumSN S N (autocorr f) W : ℂ) = 0 := by
  rw [stratumSN_eq_zero_of_large S N _ R hR W hW]; simp

end Datum

/-! ## Toy construction: multiplication model on `L²(ℝ)`, profile level -/

/-- The toy potential `φ(x) = α e^{x/2} − ½ Σ_{cuts} halfWeight(p^k) f(x − log p^k)`. -/
noncomputable def toyPotential (S : Finset ℕ) (N : ℕ) (f : ℝ → ℝ) (α : ℝ) (x : ℝ) : ℝ :=
  α * Real.exp (x / 2) -
    (1 / 2) * ∑ c ∈ cutIndex S N, halfWeight (c.1 ^ c.2) * f (x - Real.log ((c.1 ^ c.2 : ℕ) : ℝ))

/-- The orbit profile `∫ φ(x) ρ(x − W) dx` of a potential against a translated density. -/
noncomputable def toyProfile (φ ρ : ℝ → ℝ) (W : ℝ) : ℝ := ∫ x : ℝ, φ x * ρ (x - W)

lemma integrable_shift_mul {g f : ℝ → ℝ} (hg : Continuous g) (hf : Continuous f)
    (hc : HasCompactSupport f) (W : ℝ) : Integrable (fun x => g x * f (x - W)) := by
  have hc' : HasCompactSupport (fun x => f (x - W)) :=
    hc.comp_homeomorph (Homeomorph.subRight W)
  exact (hg.mul (hf.comp (continuous_sub_right W))).integrable_of_hasCompactSupport
    (hc'.mul_left)

/-- The fixed part is exactly `e^{W/2}`-homogeneous. PROVED. -/
theorem toy_fixed_part_half_homogeneous (f : ℝ → ℝ) (α W : ℝ) :
    ∫ x : ℝ, α * Real.exp (x / 2) * f (x - W) =
      Real.exp (W / 2) * (α * ∫ y : ℝ, Real.exp (y / 2) * f y) := by
  rw [← integral_add_right_eq_self (fun x => α * Real.exp (x / 2) * f (x - W)) W]
  simp only [add_sub_cancel_right]
  rw [← integral_const_mul, ← integral_const_mul]
  congr 1; ext y
  rw [show (y + W) / 2 = y / 2 + W / 2 by ring, Real.exp_add]; ring

/-- A translated bump against a translated density gives the autocorrelation at the offset.
PROVED. -/
theorem toy_bump_profile (f : ℝ → ℝ) (L W : ℝ) :
    ∫ x : ℝ, f (x - L) * f (x - W) = autocorr f (W - L) := by
  rw [← integral_add_right_eq_self (fun x => f (x - L) * f (x - W)) L]
  unfold autocorr
  congr 1; ext y
  congr 2 <;> ring

/-- The perturbation profile is `−½·stratumSN(W)`: the prime block as a potential at the cuts.
PROVED. -/
theorem toy_perturbation_profile (S : Finset ℕ) (N : ℕ) (f : ℝ → ℝ) (hf : Continuous f)
    (hc : HasCompactSupport f) (W : ℝ) :
    ∫ x : ℝ, ((1 / 2) * ∑ c ∈ cutIndex S N,
        halfWeight (c.1 ^ c.2) * f (x - Real.log ((c.1 ^ c.2 : ℕ) : ℝ))) * f (x - W) =
      (1 / 2) * stratumSN S N (autocorr f) W := by
  simp_rw [mul_assoc, Finset.sum_mul]
  rw [integral_const_mul, integral_finsetSum]
  · unfold stratumSN
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    simp_rw [mul_assoc]
    rw [integral_const_mul, toy_bump_profile]
  · intro c _
    exact integrable_shift_mul
      (g := fun x => halfWeight (c.1 ^ c.2) * f (x - Real.log ((c.1 ^ c.2 : ℕ) : ℝ)))
      (continuous_const.mul (hf.comp (continuous_sub_right _))) hf hc W

/-- **Toy construction: the multiplication model reproduces the flux-defect profile exactly.**
For every real `W`, `∫ φ(x) f(x − W) dx = (e^{W/2} c − stratumSN(W)) / 2`. PROVED. -/
theorem toyProfile_eq (S : Finset ℕ) (N : ℕ) (f : ℝ → ℝ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hm : (∫ y : ℝ, Real.exp (y / 2) * f y) ≠ 0) (W : ℝ) :
    toyProfile (toyPotential S N f
        ((∫ v : ℝ, autocorr f v * Real.exp (-v / 2)) / (2 * ∫ y : ℝ, Real.exp (y / 2) * f y)))
        f W =
      (unitStratumTerm (autocorr f) W - stratumSN S N (autocorr f) W) / 2 := by
  set m := ∫ y : ℝ, Real.exp (y / 2) * f y
  set c := ∫ v : ℝ, autocorr f v * Real.exp (-v / 2)
  have hcont : Continuous fun x : ℝ => c / (2 * m) * Real.exp (x / 2) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_id.div_const 2))
  have hI1 : Integrable fun x => c / (2 * m) * Real.exp (x / 2) * f (x - W) :=
    integrable_shift_mul hcont hf hc W
  have hcont2 : Continuous fun x : ℝ => (1 / 2) * ∑ c ∈ cutIndex S N,
      halfWeight (c.1 ^ c.2) * f (x - Real.log ((c.1 ^ c.2 : ℕ) : ℝ)) := by
    refine continuous_const.mul (continuous_finsetSum _ fun c _ => ?_)
    exact continuous_const.mul (hf.comp (continuous_sub_right _))
  have hI2 := integrable_shift_mul hcont2 hf hc W
  unfold toyProfile toyPotential
  simp_rw [sub_mul]
  rw [integral_sub hI1 hI2, toy_fixed_part_half_homogeneous, toy_perturbation_profile S N f hf hc,
    unitStratumTerm]
  have hmm : c / (2 * m) * m = c / 2 := by field_simp
  rw [hmm]
  ring

/-- **Toy Green form.** `−2I·profile = I·(stratumSN(W) − e^{W/2} c)`, the Green form that
finite-cut BT3 + (P-UNIT) prescribe on the test orbit (`green_testVec_of_premises`). PROVED. -/
theorem toyGreen_eq (S : Finset ℕ) (N : ℕ) (f : ℝ → ℝ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hm : (∫ y : ℝ, Real.exp (y / 2) * f y) ≠ 0) (W : ℝ) :
    -(2 * I) * (toyProfile (toyPotential S N f
        ((∫ v : ℝ, autocorr f v * Real.exp (-v / 2)) / (2 * ∫ y : ℝ, Real.exp (y / 2) * f y)))
        f W : ℂ) =
      I * ((stratumSN S N (autocorr f) W - unitStratumTerm (autocorr f) W : ℝ) : ℂ) := by
  rw [toyProfile_eq S N f hf hc hm W]
  push_cast; ring

end GppBTSigmaCovPerturbation
