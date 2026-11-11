import GppVerify.RiemannHypothesis.BTSigmaLocalEuler

/-!
# BT-Σ: a Green-form-preserving dilation cannot carry the window edge (P-COV obstruction)

Port of GPPDiscovery5 `072d19f` (`lean/bt-sigma/BTSigmaCovObstruction.lean`), audited by Turbo on
GPP-bridge PR #11 (comment 6802501669: obstruction PROVED, `#print axioms` standard-three on
`greenInvariant_forces_unit_zero`, `stratumSN_eq_zero_of_large`, and `const_exp_mul`; port
requested as a module after #571). Paper steps stay paper steps, not Lean claims.

Scratch module (Heart of the Cosmos / Grok, GPPDiscovery5 seat) for Turbo's question on
GPP-bridge PR #11, comment 6802112580 §4 / (c): embed the local Fock weights into the boundary
triplet compatibly with (P-COV)/(P-UNIT), or name the exact step that fails.

**Statement.** Suppose a boundary triplet `D` has finite-cut BT3 (`BTSigmaTraceSN D S N`) and
(P-UNIT), and the window edge moves in a way that **preserves the Green form on the test orbit**:
`greenForm (testVec h (W + b)) = greenForm (testVec h W)` for `W, b ≥ 0`. This holds whenever
`testVec h (W + b) = S_b (testVec h W)` with `S_b` commuting with `T*` on the domain; in
particular for `u`-translation, for any fibrewise unitary in `u`, and for every
number-diagonal unitary of the Fock model (`p^{-ibN}`). Then for every test `f` whose
autocorrelation `h = autocorr f` vanishes beyond some `R`, `∫ h(v) e^{-v/2} dv = 0`
(`greenInvariant_forces_unit_zero`). For `f ≥ 0`, `f ≠ 0` that integral is
`(∫ f e^{-x/2})(∫ f e^{x/2}) > 0` (paper step, not formalised here), so no such dilation exists.

**Consequence for the Fock embedding.** At fixed `W`, a piecewise path whose `p`-channel on the
`m`-th segment is `a_m · C_m^{1/2} Ψ̂_p` has trace jumps that are computed vector-state
expectations (`tfd_cut_jump`), so `hjump` can be met with the coupling produced by the state.
But the Fock data are `W`-independent diagonal weights, and every unitary they supply
preserves the Green form; the `W`-dependence then has to sit in the scalar samples
`a_m ∝ h(W − m log p)`, i.e. `τ_{W−u}` inside the vector, which (P-COV) forbids. The exact
failing step is therefore (P-COV): `S_b` must change the Green form at the rate
`d/dW (stratum − unit stratum)`, so it cannot be a symmetry of `T*`. (P-LOG), (P-COV),
(P-UNIT), (P-LIM), (BT-Σ), ARP and RH remain **OPEN**.

No `sorry`, no `admit`, no custom axiom.

Daniel Toupin / Golden Physics Project, with AI assistance (Heart of the Cosmos / Grok).
Task and audit: Turbo.
-/

namespace GppBTSigmaCovObstruction

open GppBTSigmaLocalEuler GppBTSigma GppArithmeticReflection Complex
open scoped ContDiff

/-- Beyond the support of `h` shifted by `log N`, the truncated prime stratum vanishes. PROVED. -/
theorem stratumSN_eq_zero_of_large (S : Finset ℕ) (N : ℕ) (h : ℝ → ℝ) (R : ℝ)
    (hR : ∀ v, R < v → h v = 0) (W : ℝ) (hW : R + Real.log N < W) :
    stratumSN S N h W = 0 := by
  unfold stratumSN
  refine Finset.sum_eq_zero fun c hc => ?_
  have hc' := hc
  simp only [cutIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hc'
  obtain ⟨⟨⟨_, hp⟩, hk1, _⟩, hle⟩ := hc'
  have hpos : (0 : ℝ) < ((c.1 ^ c.2 : ℕ) : ℝ) := by
    exact_mod_cast pow_pos hp.pos _
  have hlog : Real.log ((c.1 ^ c.2 : ℕ) : ℝ) ≤ Real.log N :=
    Real.log_le_log hpos (by exact_mod_cast hle)
  rw [hR _ (by linarith), mul_zero]

/-- If `e^{W/2} c` is constant for all large `W`, then `c = 0`. PROVED. -/
theorem const_exp_mul {c : ℝ} {W₀ : ℝ}
    (h : ∀ b : ℝ, 0 ≤ b → Real.exp ((W₀ + b) / 2) * c = Real.exp (W₀ / 2) * c) : c = 0 := by
  have h1 := h 2 (by norm_num)
  have hlt : Real.exp (W₀ / 2) < Real.exp ((W₀ + 2) / 2) := Real.exp_lt_exp.mpr (by linarith)
  have : (Real.exp ((W₀ + 2) / 2) - Real.exp (W₀ / 2)) * c = 0 := by linarith
  rcases mul_eq_zero.mp this with h2 | h2
  · linarith
  · exact h2

section Datum

variable {H Gu Gp : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup Gu] [InnerProductSpace ℂ Gu]
  [NormedAddCommGroup Gp] [InnerProductSpace ℂ Gp]

/-- The window edge moves by a Green-form-preserving map on the test orbit. -/
def GreenInvariantEdge (D : BTSigmaDatum H Gu Gp) (h : ℝ → ℝ) : Prop :=
  ∀ W b : ℝ, 0 ≤ W → 0 ≤ b →
    greenForm D.Tstar (D.testVec h (W + b)) (D.testVec h (W + b)) =
      greenForm D.Tstar (D.testVec h W) (D.testVec h W)

/-- **P-COV obstruction.** Finite-cut BT3 + (P-UNIT) + a Green-form-preserving edge motion force
the unit-stratum integral `∫ h e^{-v/2}` of every compactly supported autocorrelation test to
vanish. PROVED. -/
theorem greenInvariant_forces_unit_zero (D : BTSigmaDatum H Gu Gp) (S : Finset ℕ) (N : ℕ)
    (hP : BTSigmaTraceSN D S N) (hU : PUnit D)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (R : ℝ) (hR : ∀ v, R < v → autocorr f v = 0)
    (hinv : GreenInvariantEdge D (autocorr f)) :
    ∫ v : ℝ, autocorr f v * Real.exp (-v / 2) = 0 := by
  set W₀ : ℝ := max 0 (R + Real.log N + 1) with hW₀
  have hW₀0 : 0 ≤ W₀ := le_max_left _ _
  have hW₀R : R + Real.log N < W₀ := by
    have := le_max_right 0 (R + Real.log N + 1); linarith
  apply const_exp_mul (W₀ := W₀)
  intro b hb
  have e1 := green_testVec_of_premises D S N hP hU f hf hc (W₀ + b) (by linarith)
  have e0 := green_testVec_of_premises D S N hP hU f hf hc W₀ hW₀0
  have hi := hinv W₀ b hW₀0 hb
  rw [e1, e0, stratumSN_eq_zero_of_large S N _ R hR _ (by linarith),
    stratumSN_eq_zero_of_large S N _ R hR _ hW₀R] at hi
  have := mul_left_cancel₀ Complex.I_ne_zero hi
  have h2 : unitStratumTerm (autocorr f) (W₀ + b) = unitStratumTerm (autocorr f) W₀ := by
    have := congrArg Complex.re this
    simpa using this
  simpa [unitStratumTerm] using h2

end Datum

end GppBTSigmaCovObstruction

