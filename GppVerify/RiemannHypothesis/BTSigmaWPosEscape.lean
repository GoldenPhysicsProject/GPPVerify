import GppVerify.RiemannHypothesis.BTSigmaWPosTheta

/-!
# BT-Σ: the W > 0-only escape — CONSTRUCTED (persistent branch gap, insertion-type, ζ-blind)

Answer (Heart of the Cosmos / Grok, GPPDiscovery5 seat) to Turbo's instruction 2 on GPP-bridge
PR #11 (6816451142): "construct a datum saturating `orbit_graph_jump_across`, or prove no
`BTSigmaDatum` family can".

**Verdict: CONSTRUCTED.** A genuine `BTSigmaDatum` family on `ℂ⁴` satisfies the W > 0-only
clauses `PLogThetaPos` (hence `PLogThetaPosStrict`) together with `PUnitPos` at every truncation
`(S, N)` (`wpos_escape_construction`), and realises the forced graph-norm jump of
`orbit_graph_jump_across` by a **persistent branch gap**, with **no blow-up**:

* both one-sided graph limits exist and are finite (`escVec_tendsto_right`/`_left`,
  `escT_tendsto_right`/`_left`): `ψ_W → vR = (1, I u₀/2, 1, 0)` as `W ↓ 0` and
  `ψ_W → J vR = (1, −I u₀/2, 1, 0)` as `W ↑ 0`, with `T*` images `(I u₀/2, 0, 0, 0)` and
  `(−I u₀/2, 0, 0, 0)`;
* the limits differ (`esc_limits_ne`), and the branches stay apart uniformly:
  `u₀ ≤ ‖ψ_W − ψ_{−W'}‖` and `u₀ ≤ ‖T*ψ_W − T*ψ_{−W'}‖` for **all** `W, W' > 0`
  (`esc_branch_gap_vec`, `esc_branch_gap_T`);
* the centre vector is `ψ_0 = 0` (`esc_centre_zero`), the `J`-fixed value the tree reflection
  demands; neither branch converges to it.

Consequently the structure axioms of `BTSigmaDatum` **do not force** `OrbitGraphLimAt0`,
`GraphRightContAt0` or `GraphLeftContAt0` (`esc_not_orbitGraphLimAt0`, `esc_not_rightCont`,
`esc_not_leftCont`, `graphLim_not_forced`): the unconditional W > 0 no-go is **false**, and the
conditional kills of `BTSigmaWPosTheta` are sharp in their continuity hypotheses.

**Construction.** `H = ℂ⁴`, coordinates `(Γ₀u, Γ₁u, Γ₀p, Γ₁p)`, `T*(a, b, c, d) = (b, 0, d, 0)`
on all of `H`; Green's identity (`green4`) and surjectivity (`surj4`) are proved and fed to the
structure fields. `J = diag(1, −1, 1, −1)` (`J4_invol`, `J4_anticomm`). Test family:
`(1, I u(W)/2, 1, −I s(W)/2)` on `W > 0` (`u` the unit stratum, `s` the `(S, N)` prime stratum),
its `J`-image at `−W` on `W < 0`, and `0` at `W = 0`. Nothing in `BTSigmaDatum` ties `testVec` to
`W` continuously, so the gap at the centre is free. This is the `c = 0` analogue of #584's
`negcDatum` with the centre taken out of both branches.

**This is vacuous, not a certificate.** The block values are written in by hand
(`esc_insertion`: `Γ₁p ψ_W = −I s(W)/2`), so the datum meets the typed value clauses by
insertion and sees nothing of `ζ`. It fails the untyped provenance clause (κ_p from the vertex
law, `1/2` forced by `J`), which stays the GAP. What is settled is only the typed question: at
the level of the W > 0-only clauses, the escape exists and is a persistent branch gap.

Lean results PROVED, standard axioms. No `sorry`, no custom axiom, no cited theorem.
(P-LOG) provenance, (BT-Σ), ARP, CGC and RH remain OPEN.

Daniel Toupin / Golden Physics Project, with AI assistance.
This seat: Heart of the Cosmos / Grok (GPPDiscovery5). Audit: Turbo.
-/

namespace GppBTSigmaWPosEscape

open GppBTSigmaWPosTheta GppBTSigmaShiftedTheta GppBTSigmaLocalEuler GppBTSigma
open Complex Filter Topology Set
open scoped InnerProductSpace ContDiff

/-- The four-dimensional carrier `ℂ⁴`, coordinates `(Γ₀u, Γ₁u, Γ₀p, Γ₁p)`. -/
abbrev H4 := EuclideanSpace ℂ (Fin 4)

/-- The nilpotent shift `(a, b, c, d) ↦ (b, 0, d, 0)`. -/
noncomputable def shiftL : H4 →ₗ[ℂ] H4 where
  toFun x := WithLp.toLp 2 ![x 1, 0, x 3, 0]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' a x := by ext i; fin_cases i <;> simp

/-- `T*` on all of `ℂ⁴`. -/
noncomputable def T4 : H4 →ₗ.[ℂ] H4 := shiftL.toPMap ⊤

/-- Coordinate `i` of a domain vector. -/
noncomputable def coord (i : Fin 4) : T4.domain →ₗ[ℂ] ℂ :=
  (EuclideanSpace.proj i : H4 →L[ℂ] ℂ).toLinearMap ∘ₗ T4.domain.subtype

@[simp] theorem coord_apply (i : Fin 4) (x : T4.domain) : coord i x = (x : H4) i := rfl

@[simp] theorem T4_apply (x : T4.domain) :
    T4 x = WithLp.toLp 2 ![(x : H4) 1, 0, (x : H4) 3, 0] := rfl

theorem inner4 (x y : H4) :
    ⟪x, y⟫_ℂ = (starRingEnd ℂ) (x 0) * y 0 + (starRingEnd ℂ) (x 1) * y 1 +
      (starRingEnd ℂ) (x 2) * y 2 + (starRingEnd ℂ) (x 3) * y 3 := by
  rw [PiLp.inner_apply, Fin.sum_univ_four]
  simp only [RCLike.inner_apply]
  ring

/-- Green's identity for `T4`. PROVED. -/
theorem green4 (x y : T4.domain) :
    greenForm T4 x y =
      blockForm (coord 0 x) (coord 1 x) (coord 0 y) (coord 1 y) +
        blockForm (coord 2 x) (coord 3 x) (coord 2 y) (coord 3 y) := by
  simp only [greenForm, blockForm, coord_apply, T4_apply, inner4, RCLike.inner_apply]
  simp
  ring

/-- Build a domain vector from four coordinates. -/
noncomputable def mk4 (a b c d : ℂ) : T4.domain :=
  ⟨WithLp.toLp 2 ![a, b, c, d], Submodule.mem_top⟩

/-- The boundary map of `T4` is onto. PROVED. -/
theorem surj4 : Function.Surjective fun x : T4.domain =>
    ((coord 0 x, coord 2 x), (coord 1 x, coord 3 x)) := by
  rintro ⟨⟨a, c⟩, ⟨b, d⟩⟩
  exact ⟨mk4 a b c d, by simp [mk4]⟩

/-- The sign reflection `J = diag(1, −1, 1, −1)`. -/
noncomputable def J4 : H4 ≃ₗᵢ[ℂ] H4 :=
  LinearIsometryEquiv.piLpCongrRight 2 fun i : Fin 4 =>
    if (i : ℕ) % 2 = 0 then LinearIsometryEquiv.refl ℂ ℂ else LinearIsometryEquiv.neg ℂ

@[simp] theorem J4_apply (x : H4) :
    J4 x = WithLp.toLp 2 ![x 0, -x 1, x 2, -x 3] := by
  ext i; fin_cases i <;> simp [J4, LinearIsometryEquiv.piLpCongrRight]

/-- `J4` is an involution. PROVED. -/
theorem J4_invol (x : H4) : J4 (J4 x) = x := by
  ext i; fin_cases i <;> simp

/-- `J4` anticommutes with `T4`. PROVED. -/
theorem J4_anticomm (x : T4.domain) :
    ∃ y : T4.domain, (y : H4) = J4 x ∧ T4 y = -J4 (T4 x) :=
  ⟨⟨J4 x, Submodule.mem_top⟩, rfl, by ext i; fin_cases i <;> simp⟩

/-- The vector with prescribed unit and prime block values `−I·u` and `I·s`. -/
noncomputable def blockVec (u s : ℝ) : H4 :=
  WithLp.toLp 2 ![1, I * ((u / 2 : ℝ) : ℂ), 1, -(I * ((s / 2 : ℝ) : ℂ))]

/-- The escape test family: block values on `W > 0`, `J`-image at `−W` on `W < 0`, `0` at the
centre. -/
noncomputable def escVec (S : Finset ℕ) (N : ℕ) (h : ℝ → ℝ) (W : ℝ) : H4 :=
  if 0 < W then blockVec (unitStratumTerm h W) (stratumSN S N h W)
  else if W < 0 then J4 (blockVec (unitStratumTerm h (-W)) (stratumSN S N h (-W)))
  else 0

/-- **The escape datum.** A genuine boundary triplet on `ℂ⁴` (Green and surjectivity PROVED)
with the inserted test family `escVec`. -/
noncomputable def escDatum (S : Finset ℕ) (N : ℕ) : BTSigmaDatum H4 ℂ ℂ where
  Tstar := T4
  Γ₀u := coord 0
  Γ₁u := coord 1
  Γ₀p := coord 2
  Γ₁p := coord 3
  green := green4
  surj := surj4
  testVec h W := ⟨escVec S N h W, Submodule.mem_top⟩

@[simp] theorem escDatum_testVec (S : Finset ℕ) (N : ℕ) (h : ℝ → ℝ) (W : ℝ) :
    (((escDatum S N).testVec h W : (escDatum S N).Tstar.domain) : H4) = escVec S N h W := rfl

theorem escDatum_Tstar (S : Finset ℕ) (N : ℕ) (h : ℝ → ℝ) (W : ℝ) :
    (escDatum S N).Tstar ((escDatum S N).testVec h W) = shiftL (escVec S N h W) := rfl

theorem blockForm_diag (a b : ℂ) :
    blockForm a b a b = (starRingEnd ℂ) b * a - (starRingEnd ℂ) a * b := by
  simp [blockForm, RCLike.inner_apply, mul_comm]

theorem escVec_of_pos (S : Finset ℕ) (N : ℕ) (h : ℝ → ℝ) {W : ℝ} (hW : 0 < W) :
    escVec S N h W = blockVec (unitStratumTerm h W) (stratumSN S N h W) := by
  simp only [escVec, if_pos hW]

theorem escVec_of_neg (S : Finset ℕ) (N : ℕ) (h : ℝ → ℝ) {W : ℝ} (hW : 0 < W) :
    escVec S N h (-W) = J4 (blockVec (unitStratumTerm h W) (stratumSN S N h W)) := by
  have h1 : ¬ 0 < -W := by linarith
  have h2 : -W < 0 := by linarith
  simp only [escVec, if_neg h1, if_pos h2, neg_neg]

/-- Prime block value of `blockVec u s`: `I·s`. PROVED. -/
theorem blockVec_prime (u s : ℝ) :
    blockForm (blockVec u s 2) (blockVec u s 3) (blockVec u s 2) (blockVec u s 3) =
      I * (s : ℂ) := by
  rw [blockForm_diag]
  simp only [blockVec]
  simp [Complex.ext_iff, map_ofNat]

/-- Unit block value of `blockVec u s`: `−I·u`. PROVED. -/
theorem blockVec_unit (u s : ℝ) :
    blockForm (blockVec u s 0) (blockVec u s 1) (blockVec u s 0) (blockVec u s 1) =
      -(I * (u : ℂ)) := by
  rw [blockForm_diag]
  simp only [blockVec]
  simp [Complex.ext_iff, map_ofNat]
  ring

/-- W > 0-only finite-cut BT3 holds for every `(S, N)`. PROVED. -/
theorem esc_traceSNPos (S : Finset ℕ) (N : ℕ) : BTSigmaTraceSNPos (escDatum S N) S N := by
  intro f _ _ W hW
  show blockForm (escVec S N _ W 2) (escVec S N _ W 3) (escVec S N _ W 2) (escVec S N _ W 3) = _
  rw [escVec_of_pos S N _ hW, blockVec_prime]

/-- W > 0-only (P-UNIT) holds for every `(S, N)`. PROVED. -/
theorem esc_punitPos (S : Finset ℕ) (N : ℕ) : PUnitPos (escDatum S N) := by
  intro f _ _ W hW
  show blockForm (escVec S N _ W 0) (escVec S N _ W 1) (escVec S N _ W 0) (escVec S N _ W 1) = _
  rw [escVec_of_pos S N _ hW, blockVec_unit]

/-- The tree reflection `ψ_{−W} = J ψ_W` holds for **every** `W`, including `W = 0`. PROVED. -/
theorem esc_reflection (S : Finset ℕ) (N : ℕ) (h : ℝ → ℝ) (W : ℝ) :
    (((escDatum S N).testVec h (-W) : (escDatum S N).Tstar.domain) : H4) =
      J4 ((escDatum S N).testVec h W) := by
  simp only [escDatum_testVec]
  rcases lt_trichotomy W 0 with hW | rfl | hW
  · have hW' : 0 < -W := by linarith
    have := escVec_of_neg S N h hW'
    rw [neg_neg] at this
    rw [escVec_of_pos S N h hW', this, J4_invol]
  · simp only [neg_zero, escVec, lt_irrefl, if_false, map_zero]
  · rw [escVec_of_neg S N h hW, escVec_of_pos S N h hW]

/-- **(P-θ) with BT3 on `W > 0` only, tree reflection: satisfied.** PROVED. -/
theorem esc_plogThetaPos : PLogThetaPos escDatum J4 :=
  ⟨esc_traceSNPos, J4_invol, fun _ _ x => J4_anticomm x, esc_reflection⟩

/-- The strict W > 0-only form is satisfied too. PROVED. -/
theorem esc_plogThetaPosStrict : PLogThetaPosStrict escDatum J4 :=
  plogThetaPosStrict_of_pos esc_plogThetaPos

/-- **CONSTRUCTED: the W > 0-only clauses `PLogThetaPos ∧ PUnitPos` are jointly satisfiable**
by a genuine `BTSigmaDatum` family, at every truncation. PROVED. -/
theorem wpos_escape_construction :
    PLogThetaPos escDatum J4 ∧ PLogThetaPosStrict escDatum J4 ∧
      ∀ S N, BTSigmaTraceSNPos (escDatum S N) S N ∧ PUnitPos (escDatum S N) :=
  ⟨esc_plogThetaPos, esc_plogThetaPosStrict, fun S N => ⟨esc_traceSNPos S N, esc_punitPos S N⟩⟩

/-- The centre vector is `ψ_0 = 0` (`J`-fixed). PROVED. -/
theorem esc_centre_zero (S : Finset ℕ) (N : ℕ) (h : ℝ → ℝ) :
    (((escDatum S N).testVec h 0 : (escDatum S N).Tstar.domain) : H4) = 0 := by
  simp [escVec]

/-- The branch difference, coordinate 1: `ψ_W − ψ_{−W'}` has `Γ₁u`-entry `I(u(W) + u(W'))/2`.
PROVED. -/
theorem esc_diff_coord1 (S : Finset ℕ) (N : ℕ) (h : ℝ → ℝ) {W W' : ℝ} (hW : 0 < W)
    (hW' : 0 < W') :
    (escVec S N h W - escVec S N h (-W')) 1 =
      I * (((unitStratumTerm h W + unitStratumTerm h W') / 2 : ℝ) : ℂ) := by
  rw [escVec_of_pos S N h hW, escVec_of_neg S N h hW']
  simp [blockVec]
  ring

/-- **Persistent branch gap, vector part.** `u₀ ≤ ‖ψ_W − ψ_{−W'}‖` for all `W, W' > 0`.
PROVED. -/
theorem esc_branch_gap_vec (S : Finset ℕ) (N : ℕ) {W W' : ℝ} (hW : 0 < W) (hW' : 0 < W') :
    u0 ≤ ‖(((escDatum S N).testVec h8 W : (escDatum S N).Tstar.domain) : H4) -
      (((escDatum S N).testVec h8 (-W') : (escDatum S N).Tstar.domain) : H4)‖ := by
  simp only [escDatum_testVec]
  refine le_trans ?_ (PiLp.norm_apply_le _ 1)
  rw [esc_diff_coord1 S N h8 hW hW', norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  have h1 := u0_le_unit hW.le
  have h2 := u0_le_unit hW'.le
  rw [abs_of_pos (by linarith [u0_pos])]
  linarith

/-- **Persistent branch gap, `T*` part.** `u₀ ≤ ‖T*ψ_W − T*ψ_{−W'}‖` for all `W, W' > 0`.
PROVED. -/
theorem esc_branch_gap_T (S : Finset ℕ) (N : ℕ) {W W' : ℝ} (hW : 0 < W) (hW' : 0 < W') :
    u0 ≤ ‖(escDatum S N).Tstar ((escDatum S N).testVec h8 W) -
      (escDatum S N).Tstar ((escDatum S N).testVec h8 (-W'))‖ := by
  rw [escDatum_Tstar, escDatum_Tstar, ← map_sub]
  refine le_trans ?_ (PiLp.norm_apply_le _ 0)
  rw [show (shiftL (escVec S N h8 W - escVec S N h8 (-W'))) 0 =
      (escVec S N h8 W - escVec S N h8 (-W')) 1 from rfl,
    esc_diff_coord1 S N h8 hW hW', norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  have h1 := u0_le_unit hW.le
  have h2 := u0_le_unit hW'.le
  rw [abs_of_pos (by linarith [u0_pos])]
  linarith

/-- The right limit vector `vR = (1, I u₀/2, 1, 0)`. -/
noncomputable def vR : H4 := blockVec u0 0

/-- `blockVec u 0` is affine in `u`. PROVED. -/
theorem blockVec_zero_eq (u : ℝ) :
    blockVec u 0 = WithLp.toLp 2 ![1, 0, 1, 0] + (u : ℂ) • WithLp.toLp 2 ![0, I / 2, 0, 0] := by
  ext i
  fin_cases i <;> simp [blockVec]
  ring

theorem continuous_blockVec_zero : Continuous fun u : ℝ => blockVec u 0 := by
  simp only [blockVec_zero_eq]
  fun_prop

/-- Eventually on the right, `ψ_W = blockVec (u W) 0`. PROVED. -/
theorem esc_eventually_right (S : Finset ℕ) (N : ℕ) :
    ∀ᶠ W in 𝓝[>] (0 : ℝ), escVec S N h8 W = blockVec (unitStratumTerm h8 W) 0 := by
  filter_upwards [eventually_right] with W hW
  rw [escVec_of_pos S N h8 hW.1, stratumSN_h8_small S N hW.2]

/-- **Right graph limit exists (no blow-up).** `ψ_W → vR` as `W ↓ 0`. PROVED. -/
theorem escVec_tendsto_right (S : Finset ℕ) (N : ℕ) :
    Tendsto (fun W => (((escDatum S N).testVec h8 W : (escDatum S N).Tstar.domain) : H4))
      (𝓝[>] 0) (𝓝 vR) := by
  have hc : Tendsto (fun W : ℝ => blockVec (unitStratumTerm h8 W) 0) (𝓝[>] 0) (𝓝 vR) := by
    have := (continuous_blockVec_zero.comp continuous_unit_h8).tendsto 0
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  refine hc.congr' ?_
  filter_upwards [esc_eventually_right S N] with W hW
  simp only [escDatum_testVec, hW]

/-- **Left graph limit exists (no blow-up).** `ψ_W → J vR` as `W ↑ 0`. PROVED. -/
theorem escVec_tendsto_left (S : Finset ℕ) (N : ℕ) :
    Tendsto (fun W => (((escDatum S N).testVec h8 W : (escDatum S N).Tstar.domain) : H4))
      (𝓝[<] 0) (𝓝 (J4 vR)) := by
  have hneg : Tendsto (fun W : ℝ => -W) (𝓝[<] 0) (𝓝[>] 0) := by
    simpa using (tendsto_neg_nhdsLT (a := (0 : ℝ)))
  have hr := (J4.continuous.tendsto vR).comp ((escVec_tendsto_right S N).comp hneg)
  refine hr.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with W (hW : W < 0)
  have hW' : 0 < -W := by linarith
  have e := esc_reflection S N h8 (-W)
  rw [neg_neg] at e
  simp only [Function.comp_apply]
  exact e.symm

theorem continuous_shiftL : Continuous shiftL := LinearMap.continuous_of_finiteDimensional _

/-- **Right `T*` limit exists.** `T*ψ_W → shiftL vR` as `W ↓ 0`. PROVED. -/
theorem escT_tendsto_right (S : Finset ℕ) (N : ℕ) :
    Tendsto (fun W => (escDatum S N).Tstar ((escDatum S N).testVec h8 W)) (𝓝[>] 0)
      (𝓝 (shiftL vR)) :=
  (continuous_shiftL.tendsto vR).comp (escVec_tendsto_right S N)

/-- **Left `T*` limit exists.** `T*ψ_W → shiftL (J vR)` as `W ↑ 0`. PROVED. -/
theorem escT_tendsto_left (S : Finset ℕ) (N : ℕ) :
    Tendsto (fun W => (escDatum S N).Tstar ((escDatum S N).testVec h8 W)) (𝓝[<] 0)
      (𝓝 (shiftL (J4 vR))) :=
  (continuous_shiftL.tendsto (J4 vR)).comp (escVec_tendsto_left S N)

/-- **The two one-sided limits differ**, in the vector and in the `T*` image. PROVED. -/
theorem esc_limits_ne : vR ≠ J4 vR ∧ shiftL vR ≠ shiftL (J4 vR) := by
  have hu : (u0 : ℂ) ≠ 0 := by exact_mod_cast u0_pos.ne'
  constructor
  · intro e
    have e1 := congrArg (fun x : H4 => x 1) e
    simp [vR, blockVec] at e1
    have h2 : I * (u0 : ℂ) = 0 := by linear_combination e1
    exact hu ((mul_eq_zero.mp h2).resolve_left Complex.I_ne_zero)
  · intro e
    have e1 := congrArg (fun x : H4 => x 0) e
    simp [vR, blockVec, shiftL] at e1
    have h2 : I * (u0 : ℂ) = 0 := by linear_combination e1
    exact hu ((mul_eq_zero.mp h2).resolve_left Complex.I_ne_zero)

/-- **No two-sided graph limit.** PROVED (via `wpos_strict_kill_of_graph_lim`). -/
theorem esc_not_orbitGraphLimAt0 (S : Finset ℕ) (N : ℕ) :
    ¬ OrbitGraphLimAt0 (escDatum S N) h8 := fun hL =>
  wpos_strict_kill_of_graph_lim escDatum J4 S N ⟨esc_plogThetaPosStrict, esc_punitPos S N, hL⟩

/-- **No right graph continuity.** PROVED. -/
theorem esc_not_rightCont (S : Finset ℕ) (N : ℕ) : ¬ GraphRightContAt0 (escDatum S N) h8 :=
  wpos_orbit_graph_jump esc_plogThetaPos S N (esc_punitPos S N)

/-- **No left graph continuity.** PROVED. -/
theorem esc_not_leftCont (S : Finset ℕ) (N : ℕ) : ¬ GraphLeftContAt0 (escDatum S N) h8 :=
  wpos_orbit_graph_jump_left esc_plogThetaPos S N (esc_punitPos S N)

/-- **The jump of `orbit_graph_jump_across` is realised by a persistent branch gap, with finite
one-sided limits (no blow-up).** PROVED. -/
theorem wpos_escape_persistent_gap (S : Finset ℕ) (N : ℕ) :
    PLogThetaPos escDatum J4 ∧ PUnitPos (escDatum S N) ∧
    Tendsto (fun W => (((escDatum S N).testVec h8 W : (escDatum S N).Tstar.domain) : H4))
      (𝓝[>] 0) (𝓝 vR) ∧
    Tendsto (fun W => (((escDatum S N).testVec h8 W : (escDatum S N).Tstar.domain) : H4))
      (𝓝[<] 0) (𝓝 (J4 vR)) ∧
    Tendsto (fun W => (escDatum S N).Tstar ((escDatum S N).testVec h8 W)) (𝓝[>] 0)
      (𝓝 (shiftL vR)) ∧
    Tendsto (fun W => (escDatum S N).Tstar ((escDatum S N).testVec h8 W)) (𝓝[<] 0)
      (𝓝 (shiftL (J4 vR))) ∧
    vR ≠ J4 vR ∧ shiftL vR ≠ shiftL (J4 vR) ∧
    (∀ W W' : ℝ, 0 < W → 0 < W' →
      u0 ≤ ‖(((escDatum S N).testVec h8 W : (escDatum S N).Tstar.domain) : H4) -
        (((escDatum S N).testVec h8 (-W') : (escDatum S N).Tstar.domain) : H4)‖ ∧
      u0 ≤ ‖(escDatum S N).Tstar ((escDatum S N).testVec h8 W) -
        (escDatum S N).Tstar ((escDatum S N).testVec h8 (-W'))‖) ∧
    ¬ OrbitGraphLimAt0 (escDatum S N) h8 :=
  ⟨esc_plogThetaPos, esc_punitPos S N, escVec_tendsto_right S N, escVec_tendsto_left S N,
    escT_tendsto_right S N, escT_tendsto_left S N, esc_limits_ne.1, esc_limits_ne.2,
    fun _ _ hW hW' => ⟨esc_branch_gap_vec S N hW hW', esc_branch_gap_T S N hW hW'⟩,
    esc_not_orbitGraphLimAt0 S N⟩

/-- **The structure axioms do not force graph-norm continuity at the centre.** No theorem of the
form "every W > 0-only datum with `PLogThetaPos` and `PUnitPos` has `OrbitGraphLimAt0`" holds:
the unconditional W > 0 no-go is false. PROVED. -/
theorem graphLim_not_forced :
    ¬ ∀ (D : Finset ℕ → ℕ → BTSigmaDatum H4 ℂ ℂ) (J : H4 ≃ₗᵢ[ℂ] H4),
      PLogThetaPosStrict D J → (∀ S N, PUnitPos (D S N)) → ∃ S N, OrbitGraphLimAt0 (D S N) h8 :=
  fun hall => by
    obtain ⟨S, N, hL⟩ := hall escDatum J4 esc_plogThetaPosStrict esc_punitPos
    exact esc_not_orbitGraphLimAt0 S N hL

/-- **Insertion, not provenance (vacuity flag).** The prime boundary value is the stratum written
in by hand: `Γ₁p ψ_{h,W} = −I s(W)/2` on `W > 0`. ζ-blind. PROVED. -/
theorem esc_insertion (S : Finset ℕ) (N : ℕ) (h : ℝ → ℝ) {W : ℝ} (hW : 0 < W) :
    (escDatum S N).Γ₁p ((escDatum S N).testVec h W) =
      -(I * ((stratumSN S N h W / 2 : ℝ) : ℂ)) := by
  show escVec S N h W 3 = _
  rw [escVec_of_pos S N h hW]
  simp [blockVec]

end GppBTSigmaWPosEscape
