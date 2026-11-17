import GppVerify.RiemannHypothesis.BTSigmaCovGrowth

/-!
# BT-Σ: the type-`1/2` test for (P-COV) — what a type-`1/2` dilation would have to look like

Port of GPPDiscovery5 `4d34d24` (`lean/bt-sigma/BTSigmaCovHalfType.lean`), audited by Turbo on
GPP-bridge PR #11 (comment 6803036036: PASS, verdict agreed NEEDS A FURTHER HYPOTHESIS; exact
half-homogeneity refuted PROVED). Port requested as a separate module after CovGrowth.


Scratch module (Heart of the Cosmos / Grok, GPPDiscovery5 seat) for Turbo's instruction on
GPP-bridge PR #11, comment 6802830722 (4): is graph-norm type exactly `1/2` compatible with the
unit stratum being a genuine second block, i.e. can a group `Sd` with `‖T* ψ_W‖ ≲ e^{W/2}`
carry `Γ_u` bounded on the graph norm with `‖Γ₀u ψ_W‖ ‖Γ₁u ψ_W‖ ≥ e^{W/2}|c|/2` along the
test orbit?

**Scope.** Fixed test orbit `ψ_W = testVec (autocorr f) W`; no zeros used as input; nothing
about existence of `S_b` beyond what is proved below. `c = ∫ h e^{-v/2}`, `h = autocorr f`.

**Results (all PROVED, standard axioms).**
* `norm_blockForm_le`, `punit_unit_product_lower`: (P-UNIT) alone gives
  `e^{W/2}|c| ≤ 2 ‖Γ₀u ψ_W‖ ‖Γ₁u ψ_W‖` for every `W ≥ 0`. The product bound Turbo names is
  automatic; it is not an extra condition.
* `graphBounded_unit_product_upper`: if `Γ₀u, Γ₁u` are bounded on the graph norm
  (`‖Γ_iu x‖ ≤ K (‖x‖ + ‖T* x‖)`) and `‖T* ψ_W‖ ≤ M e^{W/2}`, then
  `‖Γ₀u ψ_W‖ ‖Γ₁u ψ_W‖ ≤ K² (‖ψ_0‖ + M e^{W/2})²`, of order `e^{W}`. Lower order `e^{W/2}`,
  upper order `e^{W}`: the two bounds do not conflict, with slack `e^{W/2}`. So at the level of
  norms, type `1/2` is **not excluded** (the test *holds*).
* `halfType_two_sided`, `halfType_alignment`: at type `1/2` with `c ≠ 0` the growth is
  saturated, `e^{W/2}|c|/(2‖ψ_0‖) ≤ ‖T* ψ_W‖ ≤ M e^{W/2}` past `R + log N`, and the Cauchy–Schwarz
  step is tight up to a constant: `|greenForm ψ_W| ≥ (|c| / (2 M ‖ψ_0‖)) · 2‖T*ψ_W‖‖ψ_W‖`.
  `T* ψ_W` must keep a fixed fraction of its norm along `i ψ_W`.
* `halfHomogeneous_forces_stratum_zero`: the natural way to get exactly type `1/2`, a group that
  scales the Green form exactly, `greenForm ψ_{W+b} = e^{b/2} greenForm ψ_W` (e.g.
  `S_{-b} T* S_b = e^{b/2} T*` on the orbit), **fails**: with finite-cut BT3 and (P-UNIT) it forces
  the truncated prime stratum to vanish on all of `W ≥ 0`. The step that breaks is BT3 at the
  cuts `W = log p^k ≤ log N`, where the prime block is a compactly supported bump that no
  `e^{b/2}`-homogeneous family can produce. (That the stratum is not identically zero, e.g.
  `stratumSN(log p^k) = halfWeight(p^k)·‖f‖² > 0` for `f ≠ 0` supported narrower than the
  minimal log gap of the cut set, is a paper step, not formalised here.)

**Answer to (4): needs a further hypothesis.** Norms allow type `1/2`; exact half-homogeneity is
refuted. A type-`1/2` group must be *asymptotically* half-homogeneous: the Green form along the
orbit is `e^{W/2}·(−I c)` plus the compactly supported correction `I·stratumSN(W)`, so
`S_{-W} T* S_W` must be `e^{W/2}` times a fixed operator plus a perturbation whose Green form is
exactly the prime stratum. Whether such an `S_b` exists is **OPEN**. (P-COV), (P-UNIT), (P-LOG),
(P-θ), (P-LIM), (BT-Σ), ARP and RH remain **OPEN**.

No `sorry`, no `admit`, no custom axiom.

Daniel Toupin / Golden Physics Project, with AI assistance (Heart of the Cosmos / Grok).
Task and audit: Turbo.
-/

namespace GppBTSigmaCovHalfType

open GppBTSigmaLocalEuler GppBTSigma GppArithmeticReflection Complex Filter Topology
open GppBTSigmaCovGrowth GppBTSigmaCovObstruction
open scoped ContDiff

/-- `|⟪b, a⟫ − ⟪a, b⟫| ≤ 2 ‖a‖ ‖b‖`. PROVED. -/
theorem norm_blockForm_le {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (a b : G) : ‖blockForm a b a b‖ ≤ 2 * (‖a‖ * ‖b‖) := by
  unfold blockForm
  have h1 := norm_inner_le_norm (𝕜 := ℂ) b a
  have h2 := norm_inner_le_norm (𝕜 := ℂ) a b
  calc ‖inner ℂ b a - inner ℂ a b‖ ≤ ‖inner ℂ b a‖ + ‖inner ℂ a b‖ := norm_sub_le _ _
    _ ≤ ‖b‖ * ‖a‖ + ‖a‖ * ‖b‖ := add_le_add h1 h2
    _ = 2 * (‖a‖ * ‖b‖) := by ring

section Datum

variable {H Gu Gp : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup Gu] [InnerProductSpace ℂ Gu]
  [NormedAddCommGroup Gp] [InnerProductSpace ℂ Gp]

/-- **(P-UNIT) gives the unit-block product bound on the whole orbit.** PROVED. -/
theorem punit_unit_product_lower (D : BTSigmaDatum H Gu Gp) (hU : PUnit D)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (W : ℝ) (hW : 0 ≤ W) :
    Real.exp (W / 2) * |∫ v : ℝ, autocorr f v * Real.exp (-v / 2)| ≤
      2 * (‖D.Γ₀u (D.testVec (autocorr f) W)‖ * ‖D.Γ₁u (D.testVec (autocorr f) W)‖) := by
  have e := hU f hf hc W hW
  have hle := norm_blockForm_le (D.Γ₀u (D.testVec (autocorr f) W))
    (D.Γ₁u (D.testVec (autocorr f) W))
  have : ‖blockForm (D.Γ₀u (D.testVec (autocorr f) W)) (D.Γ₁u (D.testVec (autocorr f) W))
      (D.Γ₀u (D.testVec (autocorr f) W)) (D.Γ₁u (D.testVec (autocorr f) W))‖ =
      Real.exp (W / 2) * |∫ v : ℝ, autocorr f v * Real.exp (-v / 2)| := by
    change ‖unitBlock D (autocorr f) W‖ = _
    rw [e, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      unitStratumTerm, abs_mul, abs_of_pos (Real.exp_pos _)]
  rw [this] at hle
  exact hle

/-- **Graph-norm-bounded `Γ_u` at type `1/2`: the upper bound is of order `e^{W}`.** PROVED. -/
theorem graphBounded_unit_product_upper (D : BTSigmaDatum H Gu Gp) (Sd : ℝ → H ≃ₗᵢ[ℂ] H)
    (hC : PCov D Sd) (h : ℝ → ℝ) (K M : ℝ) (hK : 0 ≤ K)
    (hK0 : ∀ x : D.Tstar.domain, ‖D.Γ₀u x‖ ≤ K * (‖(x : H)‖ + ‖D.Tstar x‖))
    (hK1 : ∀ x : D.Tstar.domain, ‖D.Γ₁u x‖ ≤ K * (‖(x : H)‖ + ‖D.Tstar x‖))
    (W : ℝ) (hM : ‖D.Tstar (D.testVec h W)‖ ≤ M * Real.exp (W / 2)) :
    ‖D.Γ₀u (D.testVec h W)‖ * ‖D.Γ₁u (D.testVec h W)‖ ≤
      K ^ 2 * (‖((D.testVec h 0 : D.Tstar.domain) : H)‖ + M * Real.exp (W / 2)) ^ 2 := by
  have hn := pcov_norm_const D Sd hC h W
  have hb : K * (‖((D.testVec h W : D.Tstar.domain) : H)‖ + ‖D.Tstar (D.testVec h W)‖) ≤
      K * (‖((D.testVec h 0 : D.Tstar.domain) : H)‖ + M * Real.exp (W / 2)) := by
    rw [hn]; gcongr
  have a0 := (hK0 (D.testVec h W)).trans hb
  have a1 := (hK1 (D.testVec h W)).trans hb
  calc ‖D.Γ₀u (D.testVec h W)‖ * ‖D.Γ₁u (D.testVec h W)‖
      ≤ (K * (‖((D.testVec h 0 : D.Tstar.domain) : H)‖ + M * Real.exp (W / 2))) *
        (K * (‖((D.testVec h 0 : D.Tstar.domain) : H)‖ + M * Real.exp (W / 2))) :=
        mul_le_mul a0 a1 (norm_nonneg _) ((norm_nonneg _).trans a0)
    _ = _ := by ring

/-- **At type `1/2` the growth is two-sided (saturated).** PROVED. -/
theorem halfType_two_sided (D : BTSigmaDatum H Gu Gp) (S : Finset ℕ) (N : ℕ)
    (hP : BTSigmaTraceSN D S N) (hU : PUnit D) (Sd : ℝ → H ≃ₗᵢ[ℂ] H) (hC : PCov D Sd)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (R : ℝ) (hR : ∀ v, R < v → autocorr f v = 0) (M : ℝ)
    (hM : ∀ W : ℝ, 0 ≤ W → ‖D.Tstar (D.testVec (autocorr f) W)‖ ≤ M * Real.exp (W / 2))
    (W : ℝ) (hW0 : 0 ≤ W) (hW : R + Real.log N < W) :
    Real.exp (W / 2) * |∫ v : ℝ, autocorr f v * Real.exp (-v / 2)| ≤
        2 * ‖((D.testVec (autocorr f) 0 : D.Tstar.domain) : H)‖ *
          ‖D.Tstar (D.testVec (autocorr f) W)‖ ∧
      ‖D.Tstar (D.testVec (autocorr f) W)‖ ≤ M * Real.exp (W / 2) := by
  refine ⟨?_, hM W hW0⟩
  have g := pcov_graph_growth D S N hP hU Sd hC f hf hc R hR W hW0 hW
  linarith

/-- **At type `1/2` the Cauchy–Schwarz step is tight up to a fixed constant.** PROVED. -/
theorem halfType_alignment (D : BTSigmaDatum H Gu Gp) (S : Finset ℕ) (N : ℕ)
    (hP : BTSigmaTraceSN D S N) (hU : PUnit D) (Sd : ℝ → H ≃ₗᵢ[ℂ] H) (hC : PCov D Sd)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (R : ℝ) (hR : ∀ v, R < v → autocorr f v = 0) (M : ℝ)
    (hM : ∀ W : ℝ, 0 ≤ W → ‖D.Tstar (D.testVec (autocorr f) W)‖ ≤ M * Real.exp (W / 2))
    (W : ℝ) (hW0 : 0 ≤ W) (hW : R + Real.log N < W) :
    |∫ v : ℝ, autocorr f v * Real.exp (-v / 2)| *
        (2 * (‖D.Tstar (D.testVec (autocorr f) W)‖ *
          ‖((D.testVec (autocorr f) W : D.Tstar.domain) : H)‖)) ≤
      (2 * M * ‖((D.testVec (autocorr f) 0 : D.Tstar.domain) : H)‖) *
        ‖greenForm D.Tstar (D.testVec (autocorr f) W) (D.testVec (autocorr f) W)‖ := by
  have e := green_testVec_of_premises D S N hP hU f hf hc W hW0
  rw [stratumSN_eq_zero_of_large S N _ R hR W hW, zero_sub] at e
  have hg : ‖greenForm D.Tstar (D.testVec (autocorr f) W) (D.testVec (autocorr f) W)‖ =
      Real.exp (W / 2) * |∫ v : ℝ, autocorr f v * Real.exp (-v / 2)| := by
    rw [e, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      unitStratumTerm, abs_mul, abs_of_pos (Real.exp_pos _)]
  rw [hg, pcov_norm_const D Sd hC]
  have hb := hM W hW0
  have hc0 : 0 ≤ |∫ v : ℝ, autocorr f v * Real.exp (-v / 2)| := abs_nonneg _
  have hn0 : 0 ≤ ‖((D.testVec (autocorr f) 0 : D.Tstar.domain) : H)‖ := norm_nonneg _
  have := mul_le_mul_of_nonneg_left hb (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hc0) hn0)
  nlinarith [this]

/-- The Green form scales exactly by `e^{b/2}` along the test orbit (exact half-homogeneity). -/
def HalfHomogeneousEdge (D : BTSigmaDatum H Gu Gp) (h : ℝ → ℝ) : Prop :=
  ∀ W b : ℝ, 0 ≤ W → 0 ≤ b →
    greenForm D.Tstar (D.testVec h (W + b)) (D.testVec h (W + b)) =
      (Real.exp (b / 2) : ℂ) * greenForm D.Tstar (D.testVec h W) (D.testVec h W)

/-- **Exact half-homogeneity kills the prime block.** With finite-cut BT3 and (P-UNIT), a test
orbit whose Green form scales exactly like `e^{b/2}` has truncated prime stratum identically zero
on `W ≥ 0`. PROVED. -/
theorem halfHomogeneous_forces_stratum_zero (D : BTSigmaDatum H Gu Gp) (S : Finset ℕ) (N : ℕ)
    (hP : BTSigmaTraceSN D S N) (hU : PUnit D)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (R : ℝ) (hR : ∀ v, R < v → autocorr f v = 0)
    (hhom : HalfHomogeneousEdge D (autocorr f)) :
    ∀ W : ℝ, 0 ≤ W → stratumSN S N (autocorr f) W = 0 := by
  set c := ∫ v : ℝ, autocorr f v * Real.exp (-v / 2)
  -- real Green profile g(W) = stratum − e^{W/2} c
  have hgreen : ∀ W : ℝ, 0 ≤ W →
      greenForm D.Tstar (D.testVec (autocorr f) W) (D.testVec (autocorr f) W) =
        I * ((stratumSN S N (autocorr f) W - Real.exp (W / 2) * c : ℝ) : ℂ) := by
    intro W hW
    rw [green_testVec_of_premises D S N hP hU f hf hc W hW, unitStratumTerm]
  -- scaling from W = 0, as real identity
  have hscale : ∀ b : ℝ, 0 ≤ b →
      stratumSN S N (autocorr f) b - Real.exp (b / 2) * c =
        Real.exp (b / 2) * (stratumSN S N (autocorr f) 0 - Real.exp (0 / 2) * c) := by
    intro b hb
    have e := hhom 0 b le_rfl hb
    rw [zero_add, hgreen b hb, hgreen 0 le_rfl] at e
    have e2 : ((stratumSN S N (autocorr f) b - Real.exp (b / 2) * c : ℝ) : ℂ) =
        ((Real.exp (b / 2) * (stratumSN S N (autocorr f) 0 - Real.exp (0 / 2) * c) : ℝ) : ℂ) := by
      have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
      apply mul_left_cancel₀ hI
      rw [e]; push_cast; ring
    exact_mod_cast e2
  -- large b: stratum vanishes, so stratum(0) = 0
  set b₀ : ℝ := max 0 (R + Real.log N + 1)
  have hb₀ : 0 ≤ b₀ := le_max_left _ _
  have hb₀R : R + Real.log N < b₀ := by
    have := le_max_right 0 (R + Real.log N + 1); linarith
  have h0 : stratumSN S N (autocorr f) 0 = 0 := by
    have e := hscale b₀ hb₀
    rw [stratumSN_eq_zero_of_large S N _ R hR b₀ hb₀R] at e
    simp only [zero_div, Real.exp_zero, one_mul] at e
    have hpos := Real.exp_pos (b₀ / 2)
    have : Real.exp (b₀ / 2) * stratumSN S N (autocorr f) 0 = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · exact h1
  intro W hW
  have e := hscale W hW
  rw [h0] at e
  simp only [zero_div, Real.exp_zero, one_mul, zero_sub] at e
  linarith

end Datum

end GppBTSigmaCovHalfType
