import GppVerify.RiemannHypothesis.BTSigmaShiftedTheta

/-!
# BT-Σ: (P-θ) with BT3 and (P-UNIT) asserted only on `W > 0`: the forced graph-norm jump

Answer (Heart of the Cosmos / Grok, GPPDiscovery5 seat) to Turbo's queued question on
GPP-bridge PR #11 (comments 6809103492, 6813039478, 6815125311): the W > 0-only BT3/(P-UNIT)
variant "needs the orbit to jump in graph norm at the centre: name the jump or kill it".

**Statement.** `PLogThetaPos D J` is the tree's `PLogTheta` with finite-cut BT3 asserted only on
`W > 0` (`BTSigmaTraceSNPos`), and `PUnitPos` is (P-UNIT) on `W > 0` only. The reflection
`testVec h (−W) = J (testVec h W)` and the operator clauses are unchanged. Both are genuine
weakenings (`plogTheta_pos_of_plogTheta`, `punit_pos_of_punit`). The tree kill
(`ptheta_punit_kill`) used BT3/(P-UNIT) at the centre `W = 0` itself, which is no longer
asserted.

**What is PROVED (standard axioms).** Let `g(W)` be the Green form of the orbit vector
`testVec (f ⋆ f̃) W`, for the radius-`1/8` bump `f = bump8`.
1. *Odd orbit.* `g(−W) = −g(W)` for every `W` (`green_orbit_odd`), and `g(0) = 0`
   (`green_orbit_centre_zero`). This uses only the reflection and anticommutation clauses.
2. *Right of the centre.* For `0 < W < log 2 − 1/4` no cut is visible, so
   `g(W) = −I · u(W)` with `u(W) = e^{W/2} (∫ f e^{−y/2})(∫ f e^{y/2}) > 0`
   (`green_orbit_right`). By oddness, `g(−W) = +I · u(W)` (`green_orbit_left`).
3. *The jump, named.* `g → −I · u(0)` as `W → 0⁺` and `g → +I · u(0)` as `W → 0⁻`, with
   `g(0) = 0` and `u(0) > 0` (`green_orbit_tendsto_right`, `green_orbit_tendsto_left`,
   `green_orbit_jump`). The Green form of the orbit jumps by exactly `−2I · u(0)` across the
   centre: twice the unit-stratum pole term. On each side it misses its centre value by
   `I · u(0)`.
4. *Graph-norm discontinuity forced.* The Green form is continuous in the graph norm
   `(x, T* x)`, so `W ↦ (testVec W, T* testVec W)` cannot be right-continuous at `0`
   (`wpos_orbit_graph_jump`). The same holds from the left.
5. *Kill under graph continuity.* `¬ (PLogThetaPos D J ∧ PUnitPos (D S N) ∧
   GraphRightContAt0 (D S N) (bump8 ⋆ bump8~))` for every family, every `J` and every `(S, N)`
   (`wpos_ptheta_punit_kill_of_graph_cont`). This uses no ker Γ density, no (P-COV), and no
   property of `T` beyond the clauses.
6. *Shifted centre `c > 0`.* With BT3/(P-UNIT) on `W > 0` only, a centre `c > 0` is still
   inside the premise region, so the #580 kill carries over unchanged for every `c > 0` off the
   cuts (`shifted_wpos_kill`). Only the centre `c = 0` sits on the excluded boundary point.

**What stays OPEN.** Whether some genuine datum realises the jump: an orbit whose graph-norm
limit at `0⁺` differs from `testVec 0` enough to carry the Green-form jump `I · u(0)`, while
BT3 and (P-UNIT) hold for all `W > 0`. No such datum is constructed here, and none is excluded.
So the W > 0-only variant is not killed outright: it is killed exactly on graph-continuous
orbits, and any escape must carry the named jump. The `c > 0` on-cut case is not repeated here;
it is #581's width-scaling argument with `0 < c`. `c < 0` is a separate track. (BT-Σ), ARP,
CGC and RH remain OPEN.

Lean results PROVED, standard axioms. No `sorry`, no custom axiom, no cited theorem.

Daniel Toupin / Golden Physics Project, with AI assistance.
This seat: Heart of the Cosmos / Grok (GPPDiscovery5). Audit: Turbo.
-/

namespace GppBTSigmaWPosTheta

open GppBTSigmaShiftedTheta GppBTSigmaLocalEuler GppBTSigma GppArithmeticReflection
open Complex MeasureTheory Filter Topology Set
open scoped InnerProductSpace ContDiff

section Defs

variable {H Gu Gp : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup Gu] [InnerProductSpace ℂ Gu]
  [NormedAddCommGroup Gp] [InnerProductSpace ℂ Gp]

/-- Finite-cut BT3 asserted only on `W > 0`. -/
def BTSigmaTraceSNPos (D : BTSigmaDatum H Gu Gp) (S : Finset ℕ) (N : ℕ) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ∀ W : ℝ, 0 < W →
    primeBlock D (autocorr f) W = I * (stratumSN S N (autocorr f) W : ℂ)

/-- (P-UNIT) asserted only on `W > 0`. -/
def PUnitPos (D : BTSigmaDatum H Gu Gp) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ∀ W : ℝ, 0 < W →
    unitBlock D (autocorr f) W = -(I * (unitStratumTerm (autocorr f) W : ℂ))

/-- **(P-θ), W > 0-only variant.** `PLogTheta` with finite-cut BT3 only on `W > 0`; the
reflection `W ↦ −W` and the operator clauses unchanged. Named Prop, not asserted. -/
def PLogThetaPos (D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp) (J : H ≃ₗᵢ[ℂ] H) : Prop :=
  (∀ S N, BTSigmaTraceSNPos (D S N) S N) ∧
  (∀ x : H, J (J x) = x) ∧
  (∀ S N (x : (D S N).Tstar.domain), ∃ y : (D S N).Tstar.domain,
      (y : H) = J x ∧ (D S N).Tstar y = -J ((D S N).Tstar x)) ∧
  (∀ S N (h : ℝ → ℝ) (W : ℝ),
      (((D S N).testVec h (-W) : (D S N).Tstar.domain) : H) = J ((D S N).testVec h W))

/-- **Shifted centre, W > 0-only.** As `ShiftedPLogTheta` with BT3 only on `W > 0`. -/
def ShiftedPLogThetaPos (D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp) (J : H ≃ₗᵢ[ℂ] H) (c : ℝ) :
    Prop :=
  (∀ S N, BTSigmaTraceSNPos (D S N) S N) ∧
  (∀ x : H, J (J x) = x) ∧
  (∀ S N (x : (D S N).Tstar.domain), ∃ y : (D S N).Tstar.domain,
      (y : H) = J x ∧ (D S N).Tstar y = -J ((D S N).Tstar x)) ∧
  (∀ S N (h : ℝ → ℝ) (W : ℝ),
      (((D S N).testVec h (2 * c - W) : (D S N).Tstar.domain) : H) = J ((D S N).testVec h W))

/-- Graph-norm right-continuity of the orbit `W ↦ testVec h W` at the centre `W = 0`:
both `testVec h W → testVec h 0` and `T* testVec h W → T* testVec h 0` as `W → 0⁺`. -/
def GraphRightContAt0 (D : BTSigmaDatum H Gu Gp) (h : ℝ → ℝ) : Prop :=
  Tendsto (fun W => ((D.testVec h W : D.Tstar.domain) : H)) (𝓝[>] 0)
      (𝓝 ((D.testVec h 0 : D.Tstar.domain) : H)) ∧
    Tendsto (fun W => D.Tstar (D.testVec h W)) (𝓝[>] 0) (𝓝 (D.Tstar (D.testVec h 0)))

/-- Graph-norm left-continuity of the orbit at the centre. -/
def GraphLeftContAt0 (D : BTSigmaDatum H Gu Gp) (h : ℝ → ℝ) : Prop :=
  Tendsto (fun W => ((D.testVec h W : D.Tstar.domain) : H)) (𝓝[<] 0)
      (𝓝 ((D.testVec h 0 : D.Tstar.domain) : H)) ∧
    Tendsto (fun W => D.Tstar (D.testVec h W)) (𝓝[<] 0) (𝓝 (D.Tstar (D.testVec h 0)))

/-- The Green form along the orbit. -/
noncomputable def orbitGreen (D : BTSigmaDatum H Gu Gp) (h : ℝ → ℝ) (W : ℝ) : ℂ :=
  greenForm D.Tstar (D.testVec h W) (D.testVec h W)

/-- The W > 0-only BT3 is a weakening of finite-cut BT3. PROVED. -/
theorem traceSN_pos_of_traceSN {D : BTSigmaDatum H Gu Gp} {S : Finset ℕ} {N : ℕ}
    (h : BTSigmaTraceSN D S N) : BTSigmaTraceSNPos D S N :=
  fun f hf hc W hW => h f hf hc W hW.le

/-- The W > 0-only (P-UNIT) is a weakening of (P-UNIT). PROVED. -/
theorem punit_pos_of_punit {D : BTSigmaDatum H Gu Gp} (h : PUnit D) : PUnitPos D :=
  fun f hf hc W hW => h f hf hc W hW.le

/-- The W > 0-only (P-θ) is a weakening of the tree's `PLogTheta`. PROVED. -/
theorem plogTheta_pos_of_plogTheta {D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp}
    {J : H ≃ₗᵢ[ℂ] H} (h : PLogTheta D J) : PLogThetaPos D J :=
  ⟨fun S N => traceSN_pos_of_traceSN (h.1 S N), h.2.1, h.2.2.1, h.2.2.2⟩

/-- With W > 0-only BT3 and (P-UNIT), the Green form on test vectors at `W > 0` is
`I · (prime stratum − unit stratum)`. PROVED. -/
theorem green_testVec_of_premises_pos (D : BTSigmaDatum H Gu Gp) (S : Finset ℕ) (N : ℕ)
    (hP : BTSigmaTraceSNPos D S N) (hU : PUnitPos D)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (W : ℝ) (hW : 0 < W) :
    orbitGreen D (autocorr f) W =
      I * ((stratumSN S N (autocorr f) W - unitStratumTerm (autocorr f) W : ℝ) : ℂ) := by
  unfold orbitGreen
  rw [D.green]
  show unitBlock D (autocorr f) W + primeBlock D (autocorr f) W = _
  rw [hU f hf hc W hW, hP f hf hc W hW]
  push_cast
  ring

/-- **Odd orbit.** The reflection and anticommutation clauses make the orbit Green form odd in
`W`. PROVED. -/
theorem green_orbit_odd {D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp} {J : H ≃ₗᵢ[ℂ] H}
    (hθ : PLogThetaPos D J) (S : Finset ℕ) (N : ℕ) (h : ℝ → ℝ) (W : ℝ) :
    orbitGreen (D S N) h (-W) = -orbitGreen (D S N) h W := by
  obtain ⟨-, -, hanti, hrefl⟩ := hθ
  obtain ⟨y, hy, hTy⟩ := hanti S N ((D S N).testVec h W)
  have hyx : y = (D S N).testVec h (-W) := Subtype.ext (hy.trans (hrefl S N h W).symm)
  rw [hyx] at hy hTy
  exact greenForm_anticomm _ J _ _ _ _ hy hTy hy hTy

/-- **Centre value.** The orbit Green form vanishes at the centre `W = 0`. PROVED. -/
theorem green_orbit_centre_zero {D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp} {J : H ≃ₗᵢ[ℂ] H}
    (hθ : PLogThetaPos D J) (S : Finset ℕ) (N : ℕ) (h : ℝ → ℝ) :
    orbitGreen (D S N) h 0 = 0 := by
  have e := green_orbit_odd hθ S N h 0
  rw [neg_zero] at e
  have : (2 : ℂ) * orbitGreen (D S N) h 0 = 0 := by linear_combination e
  simpa using this

end Defs

section Bump

/-- The radius-`1/8` bump: its autocorrelation is supported in `[−1/4, 1/4]`. -/
noncomputable def bump8 : ContDiffBump (0 : ℝ) := bumpR (1 / 8) (by norm_num)

/-- The bump datum `h₈ = bump8 ⋆ bump8~`. -/
noncomputable def h8 : ℝ → ℝ := autocorr (bump8 : ℝ → ℝ)

/-- The pole term of the bump datum at the centre. -/
noncomputable def u0 : ℝ := unitStratumTerm h8 0

theorem u0_pos : 0 < u0 := unitStratumTerm_bumpR_pos (by norm_num) 0

theorem quarter_lt_log_two : (1 : ℝ) / 4 < Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

/-- No cut is visible to `h₈` for `W < log 2 − 1/4`. PROVED. -/
theorem stratumSN_h8_small (S : Finset ℕ) (N : ℕ) {W : ℝ}
    (hW : W + 1 / 4 < Real.log 2) : stratumSN S N h8 W = 0 := by
  refine stratumSN_bumpR_eq_zero (by norm_num) S N W fun x hx => ?_
  have hL := log_two_le_cut hx
  rw [abs_sub_comm, abs_of_pos (by linarith)]
  linarith

/-- `W ↦ u(W)` is continuous. PROVED. -/
theorem continuous_unit_h8 : Continuous fun W : ℝ => unitStratumTerm h8 W := by
  unfold unitStratumTerm; fun_prop

end Bump

section Jump

variable {H Gu Gp : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup Gu] [InnerProductSpace ℂ Gu]
  [NormedAddCommGroup Gp] [InnerProductSpace ℂ Gp]

/-- **Right of the centre.** For `0 < W < log 2 − 1/4`, `g(W) = −I · u(W)`. PROVED. -/
theorem green_orbit_right {D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp} {J : H ≃ₗᵢ[ℂ] H}
    (hθ : PLogThetaPos D J) (S : Finset ℕ) (N : ℕ) (hU : PUnitPos (D S N))
    {W : ℝ} (hW0 : 0 < W) (hW : W + 1 / 4 < Real.log 2) :
    orbitGreen (D S N) h8 W = -(I * (unitStratumTerm h8 W : ℂ)) := by
  have e := green_testVec_of_premises_pos (D S N) S N (hθ.1 S N) hU (bump8 : ℝ → ℝ)
    bump8.contDiff bump8.hasCompactSupport W hW0
  rw [show autocorr (bump8 : ℝ → ℝ) = h8 from rfl, stratumSN_h8_small S N hW] at e
  rw [e]; push_cast; ring

/-- **Left of the centre.** For `0 < W < log 2 − 1/4`, `g(−W) = +I · u(W)`. PROVED. -/
theorem green_orbit_left {D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp} {J : H ≃ₗᵢ[ℂ] H}
    (hθ : PLogThetaPos D J) (S : Finset ℕ) (N : ℕ) (hU : PUnitPos (D S N))
    {W : ℝ} (hW0 : 0 < W) (hW : W + 1 / 4 < Real.log 2) :
    orbitGreen (D S N) h8 (-W) = I * (unitStratumTerm h8 W : ℂ) := by
  rw [green_orbit_odd hθ, green_orbit_right hθ S N hU hW0 hW, neg_neg]

theorem eventually_right : ∀ᶠ W in 𝓝[>] (0 : ℝ), 0 < W ∧ W + 1 / 4 < Real.log 2 := by
  have hmem : Ioo (0 : ℝ) (Real.log 2 - 1 / 4) ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT (by have := quarter_lt_log_two; linarith)
  filter_upwards [hmem] with W hW
  exact ⟨hW.1, by linarith [hW.2]⟩

/-- **Right limit.** `g(W) → −I · u(0)` as `W → 0⁺`. PROVED. -/
theorem green_orbit_tendsto_right {D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp} {J : H ≃ₗᵢ[ℂ] H}
    (hθ : PLogThetaPos D J) (S : Finset ℕ) (N : ℕ) (hU : PUnitPos (D S N)) :
    Tendsto (orbitGreen (D S N) h8) (𝓝[>] 0) (𝓝 (-(I * (u0 : ℂ)))) := by
  have hc : Tendsto (fun W : ℝ => -(I * (unitStratumTerm h8 W : ℂ))) (𝓝[>] 0)
      (𝓝 (-(I * (u0 : ℂ)))) := by
    have : Continuous fun W : ℝ => -(I * (unitStratumTerm h8 W : ℂ)) := by
      have := continuous_unit_h8; fun_prop
    exact (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine hc.congr' ?_
  filter_upwards [eventually_right] with W hW
  exact (green_orbit_right hθ S N hU hW.1 hW.2).symm

/-- **Left limit.** `g(W) → +I · u(0)` as `W → 0⁻`. PROVED. -/
theorem green_orbit_tendsto_left {D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp} {J : H ≃ₗᵢ[ℂ] H}
    (hθ : PLogThetaPos D J) (S : Finset ℕ) (N : ℕ) (hU : PUnitPos (D S N)) :
    Tendsto (orbitGreen (D S N) h8) (𝓝[<] 0) (𝓝 (I * (u0 : ℂ))) := by
  have hneg : Tendsto (fun W : ℝ => -W) (𝓝[<] 0) (𝓝[>] 0) := by
    simpa using (tendsto_neg_nhdsLT (a := (0 : ℝ)))
  have hr := (green_orbit_tendsto_right hθ S N hU).comp hneg
  have : Tendsto (fun W : ℝ => -orbitGreen (D S N) h8 (-W)) (𝓝[<] 0)
      (𝓝 (-(-(I * (u0 : ℂ))))) := hr.neg
  rw [neg_neg] at this
  refine this.congr fun W => ?_
  rw [green_orbit_odd hθ S N h8 W, neg_neg]

/-- **The jump, named.** Across the centre the orbit Green form jumps from `+I · u(0)` to
`−I · u(0)`, through the centre value `0`, with `u(0) > 0`: a jump of `−2I · u(0) ≠ 0`.
PROVED. -/
theorem green_orbit_jump {D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp} {J : H ≃ₗᵢ[ℂ] H}
    (hθ : PLogThetaPos D J) (S : Finset ℕ) (N : ℕ) (hU : PUnitPos (D S N)) :
    Tendsto (orbitGreen (D S N) h8) (𝓝[>] 0) (𝓝 (-(I * (u0 : ℂ)))) ∧
    Tendsto (orbitGreen (D S N) h8) (𝓝[<] 0) (𝓝 (I * (u0 : ℂ))) ∧
    orbitGreen (D S N) h8 0 = 0 ∧
    -(I * (u0 : ℂ)) - I * (u0 : ℂ) = -(2 * I * (u0 : ℂ)) ∧ -(2 * I * (u0 : ℂ)) ≠ 0 := by
  refine ⟨green_orbit_tendsto_right hθ S N hU, green_orbit_tendsto_left hθ S N hU,
    green_orbit_centre_zero hθ S N h8, by ring, ?_⟩
  have := u0_pos
  have h1 : (u0 : ℂ) ≠ 0 := by exact_mod_cast this.ne'
  simp [h1, Complex.I_ne_zero]

/-- The Green form is continuous along any filter in the graph norm `(x, T x)`. PROVED. -/
theorem tendsto_orbitGreen_of_graph {D : BTSigmaDatum H Gu Gp} {h : ℝ → ℝ} {l : Filter ℝ}
    (h1 : Tendsto (fun W => ((D.testVec h W : D.Tstar.domain) : H)) l
      (𝓝 ((D.testVec h 0 : D.Tstar.domain) : H)))
    (h2 : Tendsto (fun W => D.Tstar (D.testVec h W)) l (𝓝 (D.Tstar (D.testVec h 0)))) :
    Tendsto (orbitGreen D h) l (𝓝 (orbitGreen D h 0)) := by
  unfold orbitGreen greenForm
  exact (h2.inner h1).sub (h1.inner h2)

/-- **Graph-norm jump forced (right).** Under the W > 0-only (P-θ) and (P-UNIT), the orbit of
`h₈` is not graph-norm right-continuous at the centre. PROVED. -/
theorem wpos_orbit_graph_jump {D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp} {J : H ≃ₗᵢ[ℂ] H}
    (hθ : PLogThetaPos D J) (S : Finset ℕ) (N : ℕ) (hU : PUnitPos (D S N)) :
    ¬ GraphRightContAt0 (D S N) h8 := by
  rintro ⟨h1, h2⟩
  have hc := tendsto_orbitGreen_of_graph h1 h2
  rw [green_orbit_centre_zero hθ S N h8] at hc
  have e := tendsto_nhds_unique (green_orbit_tendsto_right hθ S N hU) hc
  have h1' : (u0 : ℂ) ≠ 0 := by exact_mod_cast u0_pos.ne'
  have : I * (u0 : ℂ) = 0 := neg_eq_zero.mp e
  exact (mul_ne_zero Complex.I_ne_zero h1') this

/-- **Graph-norm jump forced (left).** PROVED. -/
theorem wpos_orbit_graph_jump_left {D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp}
    {J : H ≃ₗᵢ[ℂ] H} (hθ : PLogThetaPos D J) (S : Finset ℕ) (N : ℕ) (hU : PUnitPos (D S N)) :
    ¬ GraphLeftContAt0 (D S N) h8 := by
  rintro ⟨h1, h2⟩
  have hc := tendsto_orbitGreen_of_graph h1 h2
  rw [green_orbit_centre_zero hθ S N h8] at hc
  have e := tendsto_nhds_unique (green_orbit_tendsto_left hθ S N hU) hc
  have h1' : (u0 : ℂ) ≠ 0 := by exact_mod_cast u0_pos.ne'
  exact (mul_ne_zero Complex.I_ne_zero h1') e

/-- **Kill under graph continuity.** No family carries the W > 0-only (P-θ), (P-UNIT) on
`W > 0` at `(S, N)`, and a graph-norm right-continuous orbit at the centre for `h₈`. PROVED. -/
theorem wpos_ptheta_punit_kill_of_graph_cont (D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp)
    (J : H ≃ₗᵢ[ℂ] H) (S : Finset ℕ) (N : ℕ) :
    ¬ (PLogThetaPos D J ∧ PUnitPos (D S N) ∧ GraphRightContAt0 (D S N) h8) :=
  fun ⟨hθ, hU, hg⟩ => wpos_orbit_graph_jump hθ S N hU hg

/-- **Kill, all-data form.** If the orbits of all smooth compactly supported autocorrelation
data are graph-norm right-continuous at the centre, the W > 0-only variant is killed. PROVED. -/
theorem wpos_ptheta_punit_kill_of_graph_cont_all (D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp)
    (J : H ≃ₗᵢ[ℂ] H) (S : Finset ℕ) (N : ℕ) :
    ¬ (PLogThetaPos D J ∧ PUnitPos (D S N) ∧
      ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
        GraphRightContAt0 (D S N) (autocorr f)) :=
  fun ⟨hθ, hU, hg⟩ => wpos_orbit_graph_jump hθ S N hU
    (hg _ bump8.contDiff bump8.hasCompactSupport)

end Jump

section Shifted

variable {H Gu Gp : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup Gu] [InnerProductSpace ℂ Gu]
  [NormedAddCommGroup Gp] [InnerProductSpace ℂ Gp]

/-- **Shifted centre balance, W > 0-only (needs `c > 0`).** PROVED. -/
theorem shifted_centre_balance_pos (D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp)
    (J : H ≃ₗᵢ[ℂ] H) {c : ℝ} (hc0 : 0 < c) (hθ : ShiftedPLogThetaPos D J c) (S : Finset ℕ)
    (N : ℕ) (hU : PUnitPos (D S N)) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    stratumSN S N (autocorr f) c = unitStratumTerm (autocorr f) c := by
  obtain ⟨hBT3, -, hanti, hrefl⟩ := hθ
  have hfix := hrefl S N (autocorr f) c
  rw [show 2 * c - c = c by ring] at hfix
  have hz := greenForm_eq_zero_of_fixed (D S N).Tstar J ((D S N).testVec (autocorr f) c)
    (hanti S N _) hfix
  have e := green_testVec_of_premises_pos (D S N) S N (hBT3 S N) hU f hf hc c hc0
  unfold orbitGreen at e
  rw [e] at hz
  have h2 := (mul_eq_zero.mp hz).resolve_left Complex.I_ne_zero
  have h3 : stratumSN S N (autocorr f) c - unitStratumTerm (autocorr f) c = 0 := by
    exact_mod_cast h2
  linarith

/-- **Shifted W > 0-only (P-θ) KILLED for every `c > 0` off the cuts.** PROVED. -/
theorem shifted_wpos_kill (D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp) (J : H ≃ₗᵢ[ℂ] H)
    (S : Finset ℕ) (N : ℕ) {c : ℝ} (hc0 : 0 < c)
    (hoff : ∀ x ∈ cutIndex S N, c ≠ Real.log ((x.1 ^ x.2 : ℕ) : ℝ)) :
    ¬ (ShiftedPLogThetaPos D J c ∧ PUnitPos (D S N)) := by
  rintro ⟨hθ, hU⟩
  obtain ⟨r, hr, hfar⟩ := exists_radius_off_cuts S N c hoff
  have e := shifted_centre_balance_pos D J hc0 hθ S N hU (bumpR r hr : ℝ → ℝ)
    (bumpR r hr).contDiff (bumpR r hr).hasCompactSupport
  rw [stratumSN_bumpR_eq_zero hr S N c hfar] at e
  have := unitStratumTerm_bumpR_pos hr c
  linarith

end Shifted

end GppBTSigmaWPosTheta
