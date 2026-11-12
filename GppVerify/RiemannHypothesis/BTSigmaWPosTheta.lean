import GppVerify.RiemannHypothesis.BTSigmaShiftedTheta

/-!
# BT-Σ: (P-θ) with BT3 and (P-UNIT) asserted only on `W > 0` — the forced graph-norm jump

Answer (Heart of the Cosmos / Grok, GPPDiscovery5 seat) to Turbo's question on GPP-bridge PR #11
(6809103492, 6813039478, 6815125311; spec sharpened in 6815444522): the W > 0-only BT3/(P-UNIT)
variant "needs the orbit to jump in graph norm at the centre: name the jump or kill it".

## 1. The hypotheses, exactly (definitions)

The datum is a family `D S N : BTSigmaDatum H Gu Gp` (genuine boundary triplet: Green's identity
and surjectivity are structure fields) with test vectors `ψ_{h,W} = (D S N).testVec h W`, a
field of the datum defined for every `W : ℝ`. `J : H ≃ₗᵢ[ℂ] H` is a unitary.

* `BTSigmaTraceSNPos D S N` — finite-cut BT3, `primeBlock D (f⋆f̃) W = I · stratumSN S N (f⋆f̃) W`,
  for smooth compactly supported `f` and **`W > 0` only**.
* `PUnitPos D` — (P-UNIT), `unitBlock D (f⋆f̃) W = −I · unitStratumTerm (f⋆f̃) W`, **`W > 0` only**.
* `PLogThetaPosStrict D J` — **every clause on `W > 0` only**: BT3 at `W > 0`; `J² = 1`;
  `T* J = −J T*` on the domain (an operator clause, no `W`); and the reflection
  `ψ_{h,−W} = J ψ_{h,W}` for **`W > 0`** only. The values `ψ_{h,W}` at `W < 0` are the datum's;
  the only constraint on them is the reflection from `W > 0`. **Nothing constrains `ψ_{h,0}`.**
* `PLogThetaPos D J` — the same, with the tree's reflection clause kept in its tree form, for
  every `W : ℝ`. Its only extra content beyond the strict form is the reflection at `W = 0`,
  that is `ψ_{h,0} = J ψ_{h,0}`. BT3 and (P-UNIT) are still `W > 0` only.
  `PLogTheta → PLogThetaPos → PLogThetaPosStrict` (`plogTheta_pos_of_plogTheta`,
  `plogThetaPosStrict_of_pos`).

Neither form uses BT3 or (P-UNIT) at any `W ≤ 0`. No zeros enter as input; `F_θ` is never given
an on-shell Gram. Write `g(W) = orbitGreen (D S N) h W = greenForm T* ψ_{h,W} ψ_{h,W}`
(a definition), `h₈ = bump8 ⋆ bump8~` (radius-`1/8` bump, a definition), and
`u(W) = unitStratumTerm h₈ W`, `u₀ = u(0)`.

## 2. Theorems (all PROVED, standard axioms)

*Oddness, proved from the clauses (not defined).* `green_orbit_odd_pos`: under the strict form,
`g(−W) = −g(W)` for every `W > 0`, from the `W > 0` reflection and anticommutation only.
`green_orbit_odd`: under `PLogThetaPos`, for every `W`.

*The centre, separated.* Under the strict form the value `g(0)` is not determined.
Under `PLogThetaPos` the **value** at the centre is `g(0) = 0` (`green_orbit_centre_zero`), while
the **right limit** is `−I · u₀ ≠ 0`. So "vanishing at the centre" is the value only, never the
limit.

*Right/left of the centre.* `green_orbit_right`: for `0 < W < log 2 − 1/4` no cut is visible and
`g(W) = −I · u(W)`; `green_orbit_left`: `g(−W) = +I · u(W)`. `u(W) ≥ u₀ > 0` for `W ≥ 0`
(`u0_le_unit`, `u0_pos`).

*The jump, as a number.* `green_orbit_tendsto_right`/`_left`: `g → −I·u₀` as `W ↓ 0` and
`g → +I·u₀` as `W ↑ 0`. `green_orbit_jump_strict`: the one-sided limits differ by exactly
`−2I·u₀`, with `u₀ > 0`.

*The graph-norm jump, with a positive lower bound.* `greenForm_sub_le` (operator inequality):
`‖g(x) − g(y)‖ ≤ 2(‖T*x − T*y‖‖x‖ + ‖T*y‖‖x − y‖)`. Hence:
* `orbit_graph_jump_across` (strict form): for all `W, W' ∈ (0, log 2 − 1/4)`,
  `u₀ ≤ ‖T*ψ_W − T*ψ_{−W'}‖ · ‖ψ_W‖ + ‖T*ψ_{−W'}‖ · ‖ψ_W − ψ_{−W'}‖`
  for `h = h₈`. The right branch and the left branch stay a fixed graph-norm-weighted distance
  apart, uniformly as `W, W' → 0`.
* `orbit_graph_jump_centre` (`PLogThetaPos`): for all `W ∈ (0, log 2 − 1/4)`,
  `u₀ ≤ 2(‖T*ψ_W − T*ψ_0‖ · ‖ψ_W‖ + ‖T*ψ_0‖ · ‖ψ_W − ψ_0‖)`: the right branch stays away
  from the centre vector `ψ_0` in graph norm (with the norm weights shown).

*Conditional kills (named hypotheses, in the statements).*
* `OrbitGraphLimAt0 D h`: the orbit `(ψ_{h,W}, T*ψ_{h,W})` has a graph-norm limit as
  `W → 0`, `W ≠ 0` (any limit, not required to be `ψ_{h,0}`).
  `wpos_strict_kill_of_graph_lim`:
  `¬ (PLogThetaPosStrict D J ∧ PUnitPos (D S N) ∧ OrbitGraphLimAt0 (D S N) h₈)`.
* `GraphRightContAt0 D h`: `(ψ_{h,W}, T*ψ_{h,W}) → (ψ_{h,0}, T*ψ_{h,0})` as `W ↓ 0`.
  `wpos_ptheta_punit_kill_of_graph_cont`:
  `¬ (PLogThetaPos D J ∧ PUnitPos (D S N) ∧ GraphRightContAt0 (D S N) h₈)`;
  `wpos_orbit_graph_jump`/`_left`: right/left continuity fails under `PLogThetaPos`.
These are **conditional** kills: continuity is not proved from the datum and is not claimed.

*Shifted centre `c > 0`.* The centre is inside the premise region, so #580's kill carries over
for every `c > 0` off the cuts (`shifted_wpos_kill`).

## 3. What stays OPEN

The W > 0-only variant is **not** killed unconditionally. An escape needs a genuine datum whose
orbit breaks graph-norm continuity at `W = 0` by at least the bound of
`orbit_graph_jump_across`: either `‖ψ_W‖` or `‖T*ψ_{−W'}‖` blows up as `W, W' → 0`, or the
graph-norm distance between the branches stays bounded below. No such datum is constructed here
(that needs BT3 and (P-UNIT) on all of `W > 0`, which no tree datum meets), and none is excluded.
The `c > 0` on-cut case (#581's width scaling, `0 < c`) is not repeated here; `c < 0` is a
separate track. (BT-Σ), ARP, CGC and RH remain OPEN.

Lean results PROVED, standard axioms. No `sorry`, no custom axiom, no cited theorem.

Daniel Toupin / Golden Physics Project, with AI assistance.
This seat: Heart of the Cosmos / Grok (GPPDiscovery5). Audit: Turbo.
-/

namespace GppBTSigmaWPosTheta

open GppBTSigmaShiftedTheta GppBTSigmaLocalEuler GppBTSigma GppArithmeticReflection
open Complex MeasureTheory Filter Topology Set
open scoped InnerProductSpace ContDiff

section Green

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Graph-norm continuity of the Green form, quantitative.**
`‖g(x) − g(y)‖ ≤ 2(‖Tx − Ty‖‖x‖ + ‖Ty‖‖x − y‖)`. PROVED. -/
theorem greenForm_sub_le (T : E →ₗ.[ℂ] E) (x y : T.domain) :
    ‖greenForm T x x - greenForm T y y‖ ≤
      2 * (‖T x - T y‖ * ‖(x : E)‖ + ‖T y‖ * ‖(x : E) - (y : E)‖) := by
  have e : greenForm T x x - greenForm T y y =
      (⟪T x - T y, (x : E)⟫_ℂ + ⟪T y, (x : E) - (y : E)⟫_ℂ) -
        (⟪(x : E), T x - T y⟫_ℂ + ⟪(x : E) - (y : E), T y⟫_ℂ) := by
    simp only [greenForm, inner_sub_left, inner_sub_right]; ring
  rw [e]
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (T x - T y) (x : E)
  have h2 := norm_inner_le_norm (𝕜 := ℂ) (T y) ((x : E) - (y : E))
  have h3 := norm_inner_le_norm (𝕜 := ℂ) (x : E) (T x - T y)
  have h4 := norm_inner_le_norm (𝕜 := ℂ) ((x : E) - (y : E)) (T y)
  calc _ ≤ ‖⟪T x - T y, (x : E)⟫_ℂ + ⟪T y, (x : E) - (y : E)⟫_ℂ‖ +
        ‖⟪(x : E), T x - T y⟫_ℂ + ⟪(x : E) - (y : E), T y⟫_ℂ‖ := norm_sub_le _ _
    _ ≤ (‖⟪T x - T y, (x : E)⟫_ℂ‖ + ‖⟪T y, (x : E) - (y : E)⟫_ℂ‖) +
        (‖⟪(x : E), T x - T y⟫_ℂ‖ + ‖⟪(x : E) - (y : E), T y⟫_ℂ‖) :=
          add_le_add (norm_add_le _ _) (norm_add_le _ _)
    _ ≤ _ := by nlinarith

end Green

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

/-- **(P-θ), strictly W > 0-only.** BT3 on `W > 0`; `J² = 1`; `T* J = −J T*` on the domain;
reflection `ψ_{h,−W} = J ψ_{h,W}` for `W > 0` only. Nothing constrains `ψ_{h,0}`.
Named Prop, not asserted. -/
def PLogThetaPosStrict (D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp) (J : H ≃ₗᵢ[ℂ] H) : Prop :=
  (∀ S N, BTSigmaTraceSNPos (D S N) S N) ∧
  (∀ x : H, J (J x) = x) ∧
  (∀ S N (x : (D S N).Tstar.domain), ∃ y : (D S N).Tstar.domain,
      (y : H) = J x ∧ (D S N).Tstar y = -J ((D S N).Tstar x)) ∧
  (∀ S N (h : ℝ → ℝ) (W : ℝ), 0 < W →
      (((D S N).testVec h (-W) : (D S N).Tstar.domain) : H) = J ((D S N).testVec h W))

/-- **(P-θ), W > 0-only BT3, tree reflection.** As `PLogThetaPosStrict`, with the reflection
clause in its tree form for every `W`; the extra content is `ψ_{h,0} = J ψ_{h,0}`.
Named Prop, not asserted. -/
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

/-- **Named continuity hypothesis (two-sided limit).** The orbit has a graph-norm limit
`(x₀, v₀)` as `W → 0`, `W ≠ 0`. Not asserted, not proved from the datum. -/
def OrbitGraphLimAt0 (D : BTSigmaDatum H Gu Gp) (h : ℝ → ℝ) : Prop :=
  ∃ x₀ v₀ : H, Tendsto (fun W => ((D.testVec h W : D.Tstar.domain) : H)) (𝓝[≠] 0) (𝓝 x₀) ∧
    Tendsto (fun W => D.Tstar (D.testVec h W)) (𝓝[≠] 0) (𝓝 v₀)

/-- **Named continuity hypothesis (right).** `(ψ_{h,W}, T*ψ_{h,W}) → (ψ_{h,0}, T*ψ_{h,0})` as
`W ↓ 0`. Not asserted, not proved from the datum. -/
def GraphRightContAt0 (D : BTSigmaDatum H Gu Gp) (h : ℝ → ℝ) : Prop :=
  Tendsto (fun W => ((D.testVec h W : D.Tstar.domain) : H)) (𝓝[>] 0)
      (𝓝 ((D.testVec h 0 : D.Tstar.domain) : H)) ∧
    Tendsto (fun W => D.Tstar (D.testVec h W)) (𝓝[>] 0) (𝓝 (D.Tstar (D.testVec h 0)))

/-- **Named continuity hypothesis (left).** As `GraphRightContAt0`, as `W ↑ 0`. -/
def GraphLeftContAt0 (D : BTSigmaDatum H Gu Gp) (h : ℝ → ℝ) : Prop :=
  Tendsto (fun W => ((D.testVec h W : D.Tstar.domain) : H)) (𝓝[<] 0)
      (𝓝 ((D.testVec h 0 : D.Tstar.domain) : H)) ∧
    Tendsto (fun W => D.Tstar (D.testVec h W)) (𝓝[<] 0) (𝓝 (D.Tstar (D.testVec h 0)))

/-- The Green form along the orbit (definition). -/
noncomputable def orbitGreen (D : BTSigmaDatum H Gu Gp) (h : ℝ → ℝ) (W : ℝ) : ℂ :=
  greenForm D.Tstar (D.testVec h W) (D.testVec h W)

/-- The W > 0-only BT3 is a weakening of finite-cut BT3. PROVED. -/
theorem traceSN_pos_of_traceSN {D : BTSigmaDatum H Gu Gp} {S : Finset ℕ} {N : ℕ}
    (h : BTSigmaTraceSN D S N) : BTSigmaTraceSNPos D S N :=
  fun f hf hc W hW => h f hf hc W hW.le

/-- The W > 0-only (P-UNIT) is a weakening of (P-UNIT). PROVED. -/
theorem punit_pos_of_punit {D : BTSigmaDatum H Gu Gp} (h : PUnit D) : PUnitPos D :=
  fun f hf hc W hW => h f hf hc W hW.le

/-- `PLogTheta → PLogThetaPos`. PROVED. -/
theorem plogTheta_pos_of_plogTheta {D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp}
    {J : H ≃ₗᵢ[ℂ] H} (h : PLogTheta D J) : PLogThetaPos D J :=
  ⟨fun S N => traceSN_pos_of_traceSN (h.1 S N), h.2.1, h.2.2.1, h.2.2.2⟩

/-- `PLogThetaPos → PLogThetaPosStrict`. PROVED. -/
theorem plogThetaPosStrict_of_pos {D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp}
    {J : H ≃ₗᵢ[ℂ] H} (h : PLogThetaPos D J) : PLogThetaPosStrict D J :=
  ⟨h.1, h.2.1, h.2.2.1, fun S N f W _ => h.2.2.2 S N f W⟩

/-- With W > 0-only BT3 and (P-UNIT), `g(W) = I · (prime stratum − unit stratum)` at `W > 0`.
PROVED. -/
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

/-- **Oddness on `W > 0`, from the strict clauses.** `g(−W) = −g(W)` for `W > 0`. PROVED. -/
theorem green_orbit_odd_pos {D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp} {J : H ≃ₗᵢ[ℂ] H}
    (hθ : PLogThetaPosStrict D J) (S : Finset ℕ) (N : ℕ) (h : ℝ → ℝ) {W : ℝ} (hW : 0 < W) :
    orbitGreen (D S N) h (-W) = -orbitGreen (D S N) h W := by
  obtain ⟨-, -, hanti, hrefl⟩ := hθ
  obtain ⟨y, hy, hTy⟩ := hanti S N ((D S N).testVec h W)
  have hyx : y = (D S N).testVec h (-W) := Subtype.ext (hy.trans (hrefl S N h W hW).symm)
  rw [hyx] at hy hTy
  exact greenForm_anticomm _ J _ _ _ _ hy hTy hy hTy

/-- **Oddness for every `W`, from `PLogThetaPos`.** PROVED. -/
theorem green_orbit_odd {D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp} {J : H ≃ₗᵢ[ℂ] H}
    (hθ : PLogThetaPos D J) (S : Finset ℕ) (N : ℕ) (h : ℝ → ℝ) (W : ℝ) :
    orbitGreen (D S N) h (-W) = -orbitGreen (D S N) h W := by
  obtain ⟨-, -, hanti, hrefl⟩ := hθ
  obtain ⟨y, hy, hTy⟩ := hanti S N ((D S N).testVec h W)
  have hyx : y = (D S N).testVec h (-W) := Subtype.ext (hy.trans (hrefl S N h W).symm)
  rw [hyx] at hy hTy
  exact greenForm_anticomm _ J _ _ _ _ hy hTy hy hTy

/-- **Centre value (not limit).** Under `PLogThetaPos`, `g(0) = 0`. PROVED. -/
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

/-- The pole term of `h₈` at the centre, `u₀ = unitStratumTerm h₈ 0`. -/
noncomputable def u0 : ℝ := unitStratumTerm h8 0

/-- `u₀ > 0`. PROVED. -/
theorem u0_pos : 0 < u0 := unitStratumTerm_bumpR_pos (by norm_num) 0

/-- `u(W) = e^{W/2} u₀ ≥ u₀` for `W ≥ 0`. PROVED. -/
theorem u0_le_unit {W : ℝ} (hW : 0 ≤ W) : u0 ≤ unitStratumTerm h8 W := by
  have hu := u0_pos
  unfold u0 unitStratumTerm at *
  simp only [zero_div, Real.exp_zero, one_mul] at *
  have : 1 ≤ Real.exp (W / 2) := Real.one_le_exp (by linarith)
  nlinarith

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

/-- **Right of the centre (strict form).** For `0 < W < log 2 − 1/4`, `g(W) = −I · u(W)`.
Uses BT3 and (P-UNIT) at this `W > 0` only. PROVED. -/
theorem green_orbit_right {D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp} {J : H ≃ₗᵢ[ℂ] H}
    (hθ : PLogThetaPosStrict D J) (S : Finset ℕ) (N : ℕ) (hU : PUnitPos (D S N))
    {W : ℝ} (hW0 : 0 < W) (hW : W + 1 / 4 < Real.log 2) :
    orbitGreen (D S N) h8 W = -(I * (unitStratumTerm h8 W : ℂ)) := by
  have e := green_testVec_of_premises_pos (D S N) S N (hθ.1 S N) hU (bump8 : ℝ → ℝ)
    bump8.contDiff bump8.hasCompactSupport W hW0
  rw [show autocorr (bump8 : ℝ → ℝ) = h8 from rfl, stratumSN_h8_small S N hW] at e
  rw [e]; push_cast; ring

/-- **Left of the centre (strict form).** For `0 < W < log 2 − 1/4`, `g(−W) = +I · u(W)`.
PROVED. -/
theorem green_orbit_left {D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp} {J : H ≃ₗᵢ[ℂ] H}
    (hθ : PLogThetaPosStrict D J) (S : Finset ℕ) (N : ℕ) (hU : PUnitPos (D S N))
    {W : ℝ} (hW0 : 0 < W) (hW : W + 1 / 4 < Real.log 2) :
    orbitGreen (D S N) h8 (-W) = I * (unitStratumTerm h8 W : ℂ) := by
  rw [green_orbit_odd_pos hθ S N h8 hW0, green_orbit_right hθ S N hU hW0 hW, neg_neg]

theorem eventually_right : ∀ᶠ W in 𝓝[>] (0 : ℝ), 0 < W ∧ W + 1 / 4 < Real.log 2 := by
  have hmem : Ioo (0 : ℝ) (Real.log 2 - 1 / 4) ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT (by have := quarter_lt_log_two; linarith)
  filter_upwards [hmem] with W hW
  exact ⟨hW.1, by linarith [hW.2]⟩

/-- **Right limit (strict form).** `g(W) → −I · u₀` as `W ↓ 0`. PROVED. -/
theorem green_orbit_tendsto_right {D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp} {J : H ≃ₗᵢ[ℂ] H}
    (hθ : PLogThetaPosStrict D J) (S : Finset ℕ) (N : ℕ) (hU : PUnitPos (D S N)) :
    Tendsto (orbitGreen (D S N) h8) (𝓝[>] 0) (𝓝 (-(I * (u0 : ℂ)))) := by
  have hc : Tendsto (fun W : ℝ => -(I * (unitStratumTerm h8 W : ℂ))) (𝓝[>] 0)
      (𝓝 (-(I * (u0 : ℂ)))) := by
    have : Continuous fun W : ℝ => -(I * (unitStratumTerm h8 W : ℂ)) := by
      have := continuous_unit_h8; fun_prop
    exact (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine hc.congr' ?_
  filter_upwards [eventually_right] with W hW
  exact (green_orbit_right hθ S N hU hW.1 hW.2).symm

/-- **Left limit (strict form).** `g(W) → +I · u₀` as `W ↑ 0`. PROVED. -/
theorem green_orbit_tendsto_left {D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp} {J : H ≃ₗᵢ[ℂ] H}
    (hθ : PLogThetaPosStrict D J) (S : Finset ℕ) (N : ℕ) (hU : PUnitPos (D S N)) :
    Tendsto (orbitGreen (D S N) h8) (𝓝[<] 0) (𝓝 (I * (u0 : ℂ))) := by
  have hneg : Tendsto (fun W : ℝ => -W) (𝓝[<] 0) (𝓝[>] 0) := by
    simpa using (tendsto_neg_nhdsLT (a := (0 : ℝ)))
  have hr := (green_orbit_tendsto_right hθ S N hU).comp hneg
  have : Tendsto (fun W : ℝ => -orbitGreen (D S N) h8 (-W)) (𝓝[<] 0)
      (𝓝 (-(-(I * (u0 : ℂ))))) := hr.neg
  rw [neg_neg] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with W (hW : W < 0)
  have hW' : 0 < -W := by linarith
  rw [← green_orbit_odd_pos hθ S N h8 hW', neg_neg]

/-- **The jump, as a number (strict form).** Right limit `−I·u₀`, left limit `+I·u₀`, difference
exactly `−2I·u₀`, and `u₀ > 0`. PROVED. -/
theorem green_orbit_jump_strict {D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp} {J : H ≃ₗᵢ[ℂ] H}
    (hθ : PLogThetaPosStrict D J) (S : Finset ℕ) (N : ℕ) (hU : PUnitPos (D S N)) :
    Tendsto (orbitGreen (D S N) h8) (𝓝[>] 0) (𝓝 (-(I * (u0 : ℂ)))) ∧
    Tendsto (orbitGreen (D S N) h8) (𝓝[<] 0) (𝓝 (I * (u0 : ℂ))) ∧
    -(I * (u0 : ℂ)) - I * (u0 : ℂ) = -(2 * I * (u0 : ℂ)) ∧ 0 < u0 :=
  ⟨green_orbit_tendsto_right hθ S N hU, green_orbit_tendsto_left hθ S N hU, by ring, u0_pos⟩

/-- **The jump with the centre value (`PLogThetaPos`).** Right limit `−I·u₀`, left limit `+I·u₀`,
value `g(0) = 0`. PROVED. -/
theorem green_orbit_jump {D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp} {J : H ≃ₗᵢ[ℂ] H}
    (hθ : PLogThetaPos D J) (S : Finset ℕ) (N : ℕ) (hU : PUnitPos (D S N)) :
    Tendsto (orbitGreen (D S N) h8) (𝓝[>] 0) (𝓝 (-(I * (u0 : ℂ)))) ∧
    Tendsto (orbitGreen (D S N) h8) (𝓝[<] 0) (𝓝 (I * (u0 : ℂ))) ∧
    orbitGreen (D S N) h8 0 = 0 ∧ 0 < u0 :=
  ⟨green_orbit_tendsto_right (plogThetaPosStrict_of_pos hθ) S N hU,
    green_orbit_tendsto_left (plogThetaPosStrict_of_pos hθ) S N hU,
    green_orbit_centre_zero hθ S N h8, u0_pos⟩

/-- **Graph-norm jump across the centre, lower bound (strict form).** For all
`W, W' ∈ (0, log 2 − 1/4)`:
`u₀ ≤ ‖T*ψ_W − T*ψ_{−W'}‖ · ‖ψ_W‖ + ‖T*ψ_{−W'}‖ · ‖ψ_W − ψ_{−W'}‖` (datum `h₈`). PROVED. -/
theorem orbit_graph_jump_across {D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp} {J : H ≃ₗᵢ[ℂ] H}
    (hθ : PLogThetaPosStrict D J) (S : Finset ℕ) (N : ℕ) (hU : PUnitPos (D S N))
    {W W' : ℝ} (hW0 : 0 < W) (hW : W + 1 / 4 < Real.log 2)
    (hW0' : 0 < W') (hW' : W' + 1 / 4 < Real.log 2) :
    u0 ≤ ‖(D S N).Tstar ((D S N).testVec h8 W) - (D S N).Tstar ((D S N).testVec h8 (-W'))‖ *
          ‖(((D S N).testVec h8 W : (D S N).Tstar.domain) : H)‖ +
        ‖(D S N).Tstar ((D S N).testVec h8 (-W'))‖ *
          ‖(((D S N).testVec h8 W : (D S N).Tstar.domain) : H) -
            (((D S N).testVec h8 (-W') : (D S N).Tstar.domain) : H)‖ := by
  have hb := greenForm_sub_le (D S N).Tstar ((D S N).testVec h8 W) ((D S N).testVec h8 (-W'))
  have e1 := green_orbit_right hθ S N hU hW0 hW
  have e2 := green_orbit_left hθ S N hU hW0' hW'
  unfold orbitGreen at e1 e2
  rw [e1, e2] at hb
  have hn : ‖-(I * (unitStratumTerm h8 W : ℂ)) - I * (unitStratumTerm h8 W' : ℂ)‖ =
      unitStratumTerm h8 W + unitStratumTerm h8 W' := by
    have h1 := u0_le_unit hW0.le
    have h2 := u0_le_unit hW0'.le
    have hu := u0_pos
    rw [show -(I * (unitStratumTerm h8 W : ℂ)) - I * (unitStratumTerm h8 W' : ℂ) =
      -I * ((unitStratumTerm h8 W + unitStratumTerm h8 W' : ℝ) : ℂ) by push_cast; ring,
      norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  rw [hn] at hb
  have h1 := u0_le_unit hW0.le
  have h2 := u0_le_unit hW0'.le
  linarith

/-- **Graph-norm jump from the centre vector, lower bound (`PLogThetaPos`).** For all
`W ∈ (0, log 2 − 1/4)`: `u₀ ≤ 2(‖T*ψ_W − T*ψ_0‖ · ‖ψ_W‖ + ‖T*ψ_0‖ · ‖ψ_W − ψ_0‖)`. PROVED. -/
theorem orbit_graph_jump_centre {D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp} {J : H ≃ₗᵢ[ℂ] H}
    (hθ : PLogThetaPos D J) (S : Finset ℕ) (N : ℕ) (hU : PUnitPos (D S N))
    {W : ℝ} (hW0 : 0 < W) (hW : W + 1 / 4 < Real.log 2) :
    u0 ≤ 2 * (‖(D S N).Tstar ((D S N).testVec h8 W) - (D S N).Tstar ((D S N).testVec h8 0)‖ *
          ‖(((D S N).testVec h8 W : (D S N).Tstar.domain) : H)‖ +
        ‖(D S N).Tstar ((D S N).testVec h8 0)‖ *
          ‖(((D S N).testVec h8 W : (D S N).Tstar.domain) : H) -
            (((D S N).testVec h8 0 : (D S N).Tstar.domain) : H)‖) := by
  have hb := greenForm_sub_le (D S N).Tstar ((D S N).testVec h8 W) ((D S N).testVec h8 0)
  have e1 := green_orbit_right (plogThetaPosStrict_of_pos hθ) S N hU hW0 hW
  have e0 := green_orbit_centre_zero hθ S N h8
  unfold orbitGreen at e1 e0
  rw [e1, e0, sub_zero, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs] at hb
  have h1 := u0_le_unit hW0.le
  have hu := u0_pos
  rw [abs_of_pos (by linarith)] at hb
  linarith

/-- The Green form is continuous along any filter in the graph norm. PROVED. -/
theorem tendsto_orbitGreen_of_graph {D : BTSigmaDatum H Gu Gp} {h : ℝ → ℝ} {l : Filter ℝ}
    {x₀ v₀ : H}
    (h1 : Tendsto (fun W => ((D.testVec h W : D.Tstar.domain) : H)) l (𝓝 x₀))
    (h2 : Tendsto (fun W => D.Tstar (D.testVec h W)) l (𝓝 v₀)) :
    Tendsto (orbitGreen D h) l (𝓝 (⟪v₀, x₀⟫_ℂ - ⟪x₀, v₀⟫_ℂ)) := by
  unfold orbitGreen greenForm
  exact (h2.inner h1).sub (h1.inner h2)

/-- **Conditional kill, strict form, named hypothesis `OrbitGraphLimAt0`.** PROVED. -/
theorem wpos_strict_kill_of_graph_lim (D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp)
    (J : H ≃ₗᵢ[ℂ] H) (S : Finset ℕ) (N : ℕ) :
    ¬ (PLogThetaPosStrict D J ∧ PUnitPos (D S N) ∧ OrbitGraphLimAt0 (D S N) h8) := by
  rintro ⟨hθ, hU, x₀, v₀, h1, h2⟩
  have hc := tendsto_orbitGreen_of_graph h1 h2
  have hR := tendsto_nhds_unique (green_orbit_tendsto_right hθ S N hU)
    (hc.mono_left (nhdsWithin_mono _ fun x (hx : 0 < x) => ne_of_gt hx))
  have hL := tendsto_nhds_unique (green_orbit_tendsto_left hθ S N hU)
    (hc.mono_left (nhdsWithin_mono _ fun x (hx : x < 0) => ne_of_lt hx))
  have h0 : (2 : ℂ) * (I * (u0 : ℂ)) = 0 := by linear_combination hL - hR
  have h1' : (u0 : ℂ) ≠ 0 := by exact_mod_cast u0_pos.ne'
  simp [h1', Complex.I_ne_zero] at h0

/-- **Right graph-norm continuity fails (`PLogThetaPos`).** PROVED. -/
theorem wpos_orbit_graph_jump {D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp} {J : H ≃ₗᵢ[ℂ] H}
    (hθ : PLogThetaPos D J) (S : Finset ℕ) (N : ℕ) (hU : PUnitPos (D S N)) :
    ¬ GraphRightContAt0 (D S N) h8 := by
  rintro ⟨h1, h2⟩
  have hc := tendsto_orbitGreen_of_graph h1 h2
  rw [show (⟪(D S N).Tstar ((D S N).testVec h8 0),
      (((D S N).testVec h8 0 : (D S N).Tstar.domain) : H)⟫_ℂ -
      ⟪(((D S N).testVec h8 0 : (D S N).Tstar.domain) : H),
        (D S N).Tstar ((D S N).testVec h8 0)⟫_ℂ) = orbitGreen (D S N) h8 0 from rfl,
    green_orbit_centre_zero hθ S N h8] at hc
  have e := tendsto_nhds_unique (green_orbit_tendsto_right (plogThetaPosStrict_of_pos hθ) S N hU) hc
  have h1' : (u0 : ℂ) ≠ 0 := by exact_mod_cast u0_pos.ne'
  exact (mul_ne_zero Complex.I_ne_zero h1') (neg_eq_zero.mp e)

/-- **Left graph-norm continuity fails (`PLogThetaPos`).** PROVED. -/
theorem wpos_orbit_graph_jump_left {D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp}
    {J : H ≃ₗᵢ[ℂ] H} (hθ : PLogThetaPos D J) (S : Finset ℕ) (N : ℕ) (hU : PUnitPos (D S N)) :
    ¬ GraphLeftContAt0 (D S N) h8 := by
  rintro ⟨h1, h2⟩
  have hc := tendsto_orbitGreen_of_graph h1 h2
  rw [show (⟪(D S N).Tstar ((D S N).testVec h8 0),
      (((D S N).testVec h8 0 : (D S N).Tstar.domain) : H)⟫_ℂ -
      ⟪(((D S N).testVec h8 0 : (D S N).Tstar.domain) : H),
        (D S N).Tstar ((D S N).testVec h8 0)⟫_ℂ) = orbitGreen (D S N) h8 0 from rfl,
    green_orbit_centre_zero hθ S N h8] at hc
  have e := tendsto_nhds_unique (green_orbit_tendsto_left (plogThetaPosStrict_of_pos hθ) S N hU) hc
  have h1' : (u0 : ℂ) ≠ 0 := by exact_mod_cast u0_pos.ne'
  exact (mul_ne_zero Complex.I_ne_zero h1') e

/-- **Conditional kill (`PLogThetaPos`), named hypothesis `GraphRightContAt0`.** PROVED. -/
theorem wpos_ptheta_punit_kill_of_graph_cont (D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp)
    (J : H ≃ₗᵢ[ℂ] H) (S : Finset ℕ) (N : ℕ) :
    ¬ (PLogThetaPos D J ∧ PUnitPos (D S N) ∧ GraphRightContAt0 (D S N) h8) :=
  fun ⟨hθ, hU, hg⟩ => wpos_orbit_graph_jump hθ S N hU hg

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
