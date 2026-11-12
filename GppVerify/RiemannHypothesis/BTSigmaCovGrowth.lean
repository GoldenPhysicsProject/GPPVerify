import GppVerify.RiemannHypothesis.BTSigmaCovObstruction

/-!
# BT-Σ: what any (P-COV) dilation must do — exponential type at least `1/2` on the test orbit

Port of GPPDiscovery5 `3f349bf` (`lean/bt-sigma/BTSigmaCovGrowth.lean`), audited by Turbo on
GPP-bridge PR #11 (comment 6802830722: CovGrowth PROVED, `#print axioms` standard-three on
`pcov_norm_const`, `pcov_graph_growth`, `pcov_type_lt_half_forces_zero`; port requested as its
own module after FixedWWitness). Necessary condition only; type ≥ 1/2 and S_b existence stay OPEN.


Scratch module (Heart of the Cosmos / Grok, GPPDiscovery5 seat), first piece of Turbo's
open question on GPP-bridge PR #11, comment 6802501669 (3): is there any `S_b` meeting (P-COV)?

**Statement.** Let `D` satisfy finite-cut BT3 (`BTSigmaTraceSN D S N`) and (P-UNIT), and let
`Sd` meet (P-COV) (`PCov D Sd`). Fix a test `f` whose autocorrelation `h` vanishes beyond `R`,
and put `c = ∫ h e^{-v/2}`. Then
* `pcov_norm_const`: the test orbit has constant norm, `‖ψ_W‖ = ‖ψ_0‖` (unitarity);
* `pcov_graph_growth`: for all `W > max 0 (R + log N)`,
  `e^{W/2} |c| ≤ 2 ‖T* ψ_W‖ ‖ψ_0‖`;
* `pcov_type_lt_half_forces_zero`: if `‖T* ψ_W‖ ≤ M e^{a W}` for all `W ≥ 0` with `a < 1/2`,
  then `c = 0`.

So a (P-COV) dilation cannot be a symmetry of `T*` (that was `greenInvariant_forces_unit_zero`),
and it cannot even be a group of exponential type `< 1/2` on the graph norm of the orbit: the
unit-stratum pole forces `T*`-growth of rate at least `1/2` along `S_W`. For `f ≥ 0`, `f ≠ 0`,
`c = (∫ f e^{-x/2})(∫ f e^{x/2}) > 0` (paper step, CHECKED by Turbo at 50 dps, not formalised).

**Scope.** This is a necessary condition, not an impossibility: an `S_b` of graph-norm type
`≥ 1/2` is not excluded here. Whether any exists is still **OPEN**. (P-COV), (P-UNIT), (P-LOG),
(P-θ), (P-LIM), (BT-Σ), ARP and RH remain **OPEN**.

No `sorry`, no `admit`, no custom axiom.

Daniel Toupin / Golden Physics Project, with AI assistance (Heart of the Cosmos / Grok).
Task and audit: Turbo.
-/

namespace GppBTSigmaCovGrowth

open GppBTSigmaLocalEuler GppBTSigma GppArithmeticReflection Complex Filter Topology
open scoped ContDiff

/-- `|⟪Tx, x⟫ − ⟪x, Tx⟫| ≤ 2 ‖Tx‖ ‖x‖`. PROVED. -/
theorem norm_greenForm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ.[ℂ] E) (x : T.domain) :
    ‖greenForm T x x‖ ≤ 2 * (‖T x‖ * ‖(x : E)‖) := by
  unfold greenForm
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (T x) (x : E)
  have h2 := norm_inner_le_norm (𝕜 := ℂ) (x : E) (T x)
  calc ‖inner ℂ (T x) (x : E) - inner ℂ (x : E) (T x)‖
      ≤ ‖inner ℂ (T x) (x : E)‖ + ‖inner ℂ (x : E) (T x)‖ := norm_sub_le _ _
    _ ≤ ‖T x‖ * ‖(x : E)‖ + ‖(x : E)‖ * ‖T x‖ := add_le_add h1 h2
    _ = 2 * (‖T x‖ * ‖(x : E)‖) := by ring

section Datum

variable {H Gu Gp : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup Gu] [InnerProductSpace ℂ Gu]
  [NormedAddCommGroup Gp] [InnerProductSpace ℂ Gp]

/-- Under (P-COV) the test orbit has constant norm. PROVED. -/
theorem pcov_norm_const (D : BTSigmaDatum H Gu Gp) (Sd : ℝ → H ≃ₗᵢ[ℂ] H) (hC : PCov D Sd)
    (h : ℝ → ℝ) (W : ℝ) :
    ‖((D.testVec h W : D.Tstar.domain) : H)‖ = ‖((D.testVec h 0 : D.Tstar.domain) : H)‖ := by
  have e := hC.2 h 0 W
  rw [zero_add] at e
  rw [e, LinearIsometryEquiv.norm_map]

/-- **Graph-norm growth forced by (P-COV).** PROVED. -/
theorem pcov_graph_growth (D : BTSigmaDatum H Gu Gp) (S : Finset ℕ) (N : ℕ)
    (hP : BTSigmaTraceSN D S N) (hU : PUnit D) (Sd : ℝ → H ≃ₗᵢ[ℂ] H) (hC : PCov D Sd)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (R : ℝ) (hR : ∀ v, R < v → autocorr f v = 0) (W : ℝ) (hW0 : 0 ≤ W)
    (hW : R + Real.log N < W) :
    Real.exp (W / 2) * |∫ v : ℝ, autocorr f v * Real.exp (-v / 2)| ≤
      2 * (‖D.Tstar (D.testVec (autocorr f) W)‖ *
        ‖((D.testVec (autocorr f) 0 : D.Tstar.domain) : H)‖) := by
  have e := green_testVec_of_premises D S N hP hU f hf hc W hW0
  rw [GppBTSigmaCovObstruction.stratumSN_eq_zero_of_large S N _ R hR W hW, zero_sub] at e
  have hle := norm_greenForm_le D.Tstar (D.testVec (autocorr f) W)
  rw [e, pcov_norm_const D Sd hC] at hle
  have hn : ‖I * ((-unitStratumTerm (autocorr f) W : ℝ) : ℂ)‖ =
      Real.exp (W / 2) * |∫ v : ℝ, autocorr f v * Real.exp (-v / 2)| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      unitStratumTerm, abs_mul, abs_of_pos (Real.exp_pos _)]
  rw [hn] at hle
  exact hle

/-- **Type `< 1/2` is excluded.** If `‖T* ψ_W‖ ≤ M e^{aW}` on `W ≥ 0` with `a < 1/2`, the
unit-stratum integral vanishes. PROVED. -/
theorem pcov_type_lt_half_forces_zero (D : BTSigmaDatum H Gu Gp) (S : Finset ℕ) (N : ℕ)
    (hP : BTSigmaTraceSN D S N) (hU : PUnit D) (Sd : ℝ → H ≃ₗᵢ[ℂ] H) (hC : PCov D Sd)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (R : ℝ) (hR : ∀ v, R < v → autocorr f v = 0) (M a : ℝ) (ha : a < 1 / 2)
    (hM : ∀ W : ℝ, 0 ≤ W → ‖D.Tstar (D.testVec (autocorr f) W)‖ ≤ M * Real.exp (a * W)) :
    ∫ v : ℝ, autocorr f v * Real.exp (-v / 2) = 0 := by
  set c := |∫ v : ℝ, autocorr f v * Real.exp (-v / 2)|
  set n0 := ‖((D.testVec (autocorr f) 0 : D.Tstar.domain) : H)‖
  set W₀ : ℝ := max 0 (R + Real.log N + 1)
  have hW₀0 : 0 ≤ W₀ := le_max_left _ _
  have hW₀R : R + Real.log N < W₀ := by
    have := le_max_right 0 (R + Real.log N + 1); linarith
  -- for all W ≥ W₀ : c ≤ 2 M n0 e^{(a − 1/2) W}
  have key : ∀ W, W₀ ≤ W → c ≤ 2 * M * n0 * Real.exp ((a - 1 / 2) * W) := by
    intro W hW
    have g := pcov_graph_growth D S N hP hU Sd hC f hf hc R hR W (by linarith) (by linarith)
    have hb := hM W (by linarith)
    have hn0 : 0 ≤ n0 := norm_nonneg _
    have g2 : Real.exp (W / 2) * c ≤ 2 * (M * Real.exp (a * W) * n0) :=
      g.trans (by gcongr)
    have hpos := Real.exp_pos (W / 2)
    have hsplit : Real.exp (a * W) = Real.exp ((a - 1 / 2) * W) * Real.exp (W / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hsplit] at g2
    have : Real.exp (W / 2) * c ≤ Real.exp (W / 2) * (2 * M * n0 * Real.exp ((a - 1 / 2) * W)) := by
      linarith
    exact le_of_mul_le_mul_left this hpos
  have ht : Tendsto (fun W => 2 * M * n0 * Real.exp ((a - 1 / 2) * W)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun W : ℝ => (a - 1 / 2) * W) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by linarith)
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (2 * M * n0)
  have hc0 : c ≤ 0 :=
    ge_of_tendsto ht (eventually_atTop.mpr ⟨W₀, fun W hW => key W hW⟩)
  exact abs_nonpos_iff.mp hc0

end Datum

end GppBTSigmaCovGrowth
