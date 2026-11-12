import GppVerify.RiemannHypothesis.BTSigmaShiftedTheta

/-!
# BT-Σ: shifted (P-θ) at a negative centre `c < 0` — CONSTRUCTED (insertion-type, ζ-blind)

Answer (Heart of the Cosmos / Grok, GPPDiscovery5 seat) to the `c < 0` case left OPEN by
`BTSigmaShiftedTheta` (GPPVerify #580) and `BTSigmaShiftedThetaOnCut` (#581): is
`ShiftedPLogTheta D J c ∧ PUnit (D S N)` killed, or satisfiable, for `c < 0`?

**Answer: satisfiable, at every `c < 0` and every truncation `(S, N)`** (`negc_construction`,
`negc_no_kill`). So the `c ≥ 0` kill of #580/#581 is sharp: it cannot be extended to any
negative centre from the typed clauses.

**Construction (all PROVED, standard axioms).**
* `H = ℂ⁴` with coordinates `(Γ₀u, Γ₁u, Γ₀p, Γ₁p)`, `Gu = Gp = ℂ`, and
  `T* (a, b, c, d) = (b, 0, d, 0)` on all of `H`. Green's identity (`green4`) and surjectivity of
  the boundary map (`surj4`) hold, so `negcDatum c S N` is a genuine `BTSigmaDatum`.
* `J = diag(1, −1, 1, −1)`: a unitary involution (`J4_invol`) with `T* J = −J T*`
  (`J4_anticomm`).
* Test family `rawVec`: on `W ≥ 0` the vector `(1, I u/2, 1, −I s/2)` with `u` the unit stratum
  and `s` the `(S, N)` prime stratum, so BT3 and (P-UNIT) hold (`negc_traceSN`, `negc_punit`);
  on `W ≤ 2c` its `J`-image reflected through `c`; zero on the gap `2c < W < 0`. Because
  `2c < 0`, the two regions are disjoint and the reflection `W ↦ 2c − W` holds for every `W`
  (`negc_reflection`).

**Why this is empty, stated as theorems.** The fixed point `W = c` lies in the gap, so the fixed
test vector is `0` (`negc_centre_vec_zero`): the centre-balance step of the `c ≥ 0` kill has
nothing to bite on. And the prime boundary value is the stratum itself, written in by hand
(`negc_insertion`), exactly the insertion that `amplitude_insertion_reproduces_weights` already
flags. So this datum meets the *typed value clauses only*. It fails the untyped provenance
clause of `PLogTheta` (κ_p produced by the vertex law, `1/2` forced by `J`), and nothing in it
sees `ζ`.

**Consequence.** For `c < 0`, shifted (P-θ) with (P-UNIT) is not a constraint at all at the typed
level; it cannot kill and cannot certify. The `c < 0` route is closed as *vacuous*, not as
killed. Any content there must come from the provenance clause, which stays untyped (GAP).

Lean results PROVED, standard axioms. No `sorry`, no custom axiom, no cited theorem.
(P-LOG) provenance, (BT-Σ), ARP, CGC and RH remain OPEN.

Daniel Toupin / Golden Physics Project, with AI assistance (Heart of the Cosmos / Grok,
GPPDiscovery5). Task and audit: Turbo.
-/

namespace GppBTSigmaShiftedThetaNeg

open GppBTSigmaShiftedTheta GppBTSigmaLocalEuler GppBTSigma Complex
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

@[simp] theorem T4_apply (x : T4.domain) : T4 x = WithLp.toLp 2 ![(x : H4) 1, 0, (x : H4) 3, 0] :=
  rfl

theorem inner4 (x y : H4) :
    ⟪x, y⟫_ℂ = (starRingEnd ℂ) (x 0) * y 0 + (starRingEnd ℂ) (x 1) * y 1 +
      (starRingEnd ℂ) (x 2) * y 2 + (starRingEnd ℂ) (x 3) * y 3 := by
  rw [PiLp.inner_apply, Fin.sum_univ_four]
  simp only [RCLike.inner_apply]
  ring

/-- Green's identity for `T4` with boundary coordinates `(x₀, x₁)` and `(x₂, x₃)`. PROVED. -/
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

@[simp] theorem mk4_coe (a b c d : ℂ) : ((mk4 a b c d : T4.domain) : H4) =
    WithLp.toLp 2 ![a, b, c, d] := rfl

/-- The boundary map of `T4` is onto `(ℂ × ℂ) × (ℂ × ℂ)`. PROVED. -/
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

/-- Raw test family: block values prescribed on `W ≥ 0`, reflected through `c` onto `W ≤ 2c`,
and zero on the gap `2c < W < 0`. -/
noncomputable def rawVec (S : Finset ℕ) (N : ℕ) (c : ℝ) (h : ℝ → ℝ) (W : ℝ) : H4 :=
  if 0 ≤ W then blockVec (unitStratumTerm h W) (stratumSN S N h W)
  else if W ≤ 2 * c then
    J4 (blockVec (unitStratumTerm h (2 * c - W)) (stratumSN S N h (2 * c - W)))
  else 0

/-- **The `c < 0` datum.** A genuine boundary triplet on `ℂ⁴` (Green and surjectivity PROVED),
with the inserted test family `rawVec`. -/
noncomputable def negcDatum (c : ℝ) (S : Finset ℕ) (N : ℕ) : BTSigmaDatum H4 ℂ ℂ where
  Tstar := T4
  Γ₀u := coord 0
  Γ₁u := coord 1
  Γ₀p := coord 2
  Γ₁p := coord 3
  green := green4
  surj := surj4
  testVec h W := ⟨rawVec S N c h W, Submodule.mem_top⟩

theorem blockForm_diag (a b : ℂ) : blockForm a b a b = (starRingEnd ℂ) b * a - (starRingEnd ℂ) a * b := by
  simp [blockForm, RCLike.inner_apply, mul_comm]

theorem rawVec_of_nonneg (S : Finset ℕ) (N : ℕ) (c : ℝ) (h : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W) :
    rawVec S N c h W = blockVec (unitStratumTerm h W) (stratumSN S N h W) := by
  simp only [rawVec, if_pos hW]

theorem primeBlock_negc (c : ℝ) (S : Finset ℕ) (N : ℕ) (h : ℝ → ℝ) (W : ℝ) :
    primeBlock (negcDatum c S N) h W =
      blockForm (rawVec S N c h W 2) (rawVec S N c h W 3) (rawVec S N c h W 2)
        (rawVec S N c h W 3) := rfl

theorem unitBlock_negc (c : ℝ) (S : Finset ℕ) (N : ℕ) (h : ℝ → ℝ) (W : ℝ) :
    unitBlock (negcDatum c S N) h W =
      blockForm (rawVec S N c h W 0) (rawVec S N c h W 1) (rawVec S N c h W 0)
        (rawVec S N c h W 1) := rfl

/-- The block values of `blockVec u s`: prime `I·s`. PROVED. -/
theorem blockVec_prime (u s : ℝ) :
    blockForm (blockVec u s 2) (blockVec u s 3) (blockVec u s 2) (blockVec u s 3) =
      I * (s : ℂ) := by
  rw [blockForm_diag]
  simp only [blockVec]
  simp [Complex.ext_iff, map_ofNat]

/-- The block values of `blockVec u s`: unit `−I·u`. PROVED. -/
theorem blockVec_unit (u s : ℝ) :
    blockForm (blockVec u s 0) (blockVec u s 1) (blockVec u s 0) (blockVec u s 1) =
      -(I * (u : ℂ)) := by
  rw [blockForm_diag]
  simp only [blockVec]
  simp [Complex.ext_iff, map_ofNat]
  ring

/-- Finite-cut BT3 holds for every `(S, N)`. PROVED. -/
theorem negc_traceSN (c : ℝ) (S : Finset ℕ) (N : ℕ) : BTSigmaTraceSN (negcDatum c S N) S N := by
  intro f _ _ W hW
  rw [primeBlock_negc, rawVec_of_nonneg S N c _ hW, blockVec_prime]

/-- (P-UNIT) holds for every `(S, N)`. PROVED. -/
theorem negc_punit (c : ℝ) (S : Finset ℕ) (N : ℕ) : PUnit (negcDatum c S N) := by
  intro f _ _ W hW
  rw [unitBlock_negc, rawVec_of_nonneg S N c _ hW, blockVec_unit]

/-- For `c < 0` the test family carries the shifted reflection `W ↦ 2c − W`. PROVED. -/
theorem negc_reflection {c : ℝ} (hc : c < 0) (S : Finset ℕ) (N : ℕ) (h : ℝ → ℝ) (W : ℝ) :
    (((negcDatum c S N).testVec h (2 * c - W) : (negcDatum c S N).Tstar.domain) : H4) =
      J4 ((negcDatum c S N).testVec h W) := by
  show rawVec S N c h (2 * c - W) = J4 (rawVec S N c h W)
  by_cases hW : 0 ≤ W
  · have h1 : ¬ 0 ≤ 2 * c - W := by linarith
    have h2 : 2 * c - W ≤ 2 * c := by linarith
    simp only [rawVec, if_neg h1, if_pos h2, if_pos hW, sub_sub_cancel]
  · by_cases hW2 : W ≤ 2 * c
    · have h1 : 0 ≤ 2 * c - W := by linarith
      simp only [rawVec, if_pos h1, if_neg hW, if_pos hW2, J4_invol]
    · have h1 : ¬ 0 ≤ 2 * c - W := by linarith
      have h2 : ¬ 2 * c - W ≤ 2 * c := by linarith
      simp only [rawVec, if_neg h1, if_neg h2, if_neg hW, if_neg hW2, map_zero]

/-- **CONSTRUCTED: shifted (P-θ) ∧ (P-UNIT) is satisfiable at every centre `c < 0`.** The family
`negcDatum c` satisfies `ShiftedPLogTheta · J4 c` and (P-UNIT) at every truncation. PROVED. -/
theorem negc_construction {c : ℝ} (hc : c < 0) :
    ShiftedPLogTheta (negcDatum c) J4 c ∧ ∀ S N, PUnit (negcDatum c S N) :=
  ⟨⟨fun S N => negc_traceSN c S N, J4_invol, fun _ _ x => J4_anticomm x,
    fun S N h W => negc_reflection hc S N h W⟩, fun S N => negc_punit c S N⟩

/-- **The `c ≥ 0` kill cannot extend to any `c < 0`.** PROVED. -/
theorem negc_no_kill {c : ℝ} (hc : c < 0) (S : Finset ℕ) (N : ℕ) :
    ∃ (D : Finset ℕ → ℕ → BTSigmaDatum H4 ℂ ℂ) (J : H4 ≃ₗᵢ[ℂ] H4),
      ShiftedPLogTheta D J c ∧ PUnit (D S N) :=
  ⟨negcDatum c, J4, (negc_construction hc).1, (negc_construction hc).2 S N⟩

/-- **Why it is empty: the centre sits in the gap.** For `c < 0` the fixed test vector at `W = c`
is zero, so the centre-balance step of the `c ≥ 0` kill carries no information. PROVED. -/
theorem negc_centre_vec_zero {c : ℝ} (hc : c < 0) (S : Finset ℕ) (N : ℕ) (h : ℝ → ℝ) :
    (((negcDatum c S N).testVec h c : (negcDatum c S N).Tstar.domain) : H4) = 0 := by
  show rawVec S N c h c = 0
  have h1 : ¬ 0 ≤ c := by linarith
  have h2 : ¬ c ≤ 2 * c := by linarith
  simp only [rawVec, if_neg h1, if_neg h2]

/-- **Insertion, not provenance.** The prime boundary value of the test vector is the stratum
itself, written in by hand: `Γ₁p ψ_{h,W} = −I s/2`. So the datum meets the value clauses by
insertion (cf. `amplitude_insertion_reproduces_weights`) and is ζ-blind. PROVED. -/
theorem negc_insertion (c : ℝ) (S : Finset ℕ) (N : ℕ) (h : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W) :
    (negcDatum c S N).Γ₁p ((negcDatum c S N).testVec h W) =
      -(I * ((stratumSN S N h W / 2 : ℝ) : ℂ)) := by
  show rawVec S N c h W 3 = _
  rw [rawVec_of_nonneg S N c h hW]
  simp [blockVec]

end GppBTSigmaShiftedThetaNeg
