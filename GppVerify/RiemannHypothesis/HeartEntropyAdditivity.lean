/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude; statements from Heart of the Cosmos / Grok)
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.EulerProduct.Basic
import GppVerify.RiemannHypothesis.ZetaGibbsEntropyDerivative

/-!
# Bost–Connes entropy additivity over primes (Heart claim #26, `HR21_bost_connes_entropy`)

For real `β > 1`, with `p_n = n^{−β}/ζ(β)` and `S(β) = −Σ_n p_n log p_n`:

* `shannon_eq_zetaEntropy`: `S(β) = log ζ(β) + β · U(β)` with `U = M₁/Z = −ζ′/ζ` (the project's
  `zetaEntropy`), so the Shannon entropy of the zeta Gibbs measure *is* the potential `zetaEntropy`;
* `entropy_additive`: `S(β) = Σ_p S_p(β)` with
  `S_p(β) = −log(1 − p^{−β}) − p^{−β} log(p^{−β}) / (1 − p^{−β})`
  (entropy additivity over primes, i.e. the Euler product);
* `shannonEntropy_tendsto_atTop`: `S(β) → +∞` as `β → 1⁺` (from `(β − 1) ζ(β) → 1` and `U ≥ 0`).

**Route.** Real Euler product (`EulerProduct.eulerProduct_completely_multiplicative_hasProd` for
`n ↦ n^{−β}`) gives `log Z = Σ_p −log(1 − p^{−β})`. Differentiating this identity termwise
(`hasDerivAt_tsum_of_isPreconnected`, locally uniform bound `2 log p · p^{−β₀}`) and using the
tree's `hasDerivAt_zetaLogPartition` (`(log Z)′ = −U`) gives
`U(β) = Σ_p p^{−β} log p / (1 − p^{−β})`. Hypotheses: `β > 1` only. No zeta zero is an input.
No `sorry`, no `axiom`.
-/

namespace GppEntropyAdditivity

open GppZetaGibbsFisher GppZetaGibbsSummability GppZetaGibbsThermodynamicDerivatives
  GppZetaGibbsEntropyDerivative Filter Topology

/-- `n ↦ n^{−β}` as a completely multiplicative function `ℕ →*₀ ℝ`. -/
noncomputable def powNeg (β : ℝ) (hβ : β ≠ 0) : ℕ →*₀ ℝ where
  toFun n := (n : ℝ) ^ (-β)
  map_zero' := by simp [Real.zero_rpow (neg_ne_zero.mpr hβ)]
  map_one' := by simp
  map_mul' m n := by
    simp [Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

theorem powNeg_succ {β : ℝ} (hβ : β ≠ 0) (n : ℕ) :
    powNeg β hβ (n + 1) = gibbsWeight β n := by
  simp [gibbsWeight, powNeg, Real.rpow_neg (Nat.cast_nonneg _), one_div]

theorem summable_powNeg {β : ℝ} (hβ : 1 < β) :
    Summable (fun n => powNeg β (by linarith) n) := by
  rw [← summable_nat_add_iff 1]
  simpa [powNeg_succ] using summable_gibbsWeight hβ

theorem Z_eq_tsum_powNeg {β : ℝ} (hβ : 1 < β) :
    Z β = ∑' n, powNeg β (by linarith) n := by
  unfold Z
  rw [(summable_powNeg hβ).tsum_eq_zero_add]
  have h0 : powNeg β (by linarith) 0 = 0 := map_zero _
  rw [h0, zero_add]
  exact tsum_congr fun n => (powNeg_succ _ n).symm

/-- Real Euler product `Z(β) = Π_p (1 − p^{−β})⁻¹`. -/
theorem hasProd_euler {β : ℝ} (hβ : 1 < β) :
    HasProd (fun p : Nat.Primes => (1 - (p : ℝ) ^ (-β))⁻¹) (Z β) := by
  rw [Z_eq_tsum_powNeg hβ]
  have hs : Summable (fun n => ‖powNeg β (by linarith) n‖) := by
    refine (summable_powNeg hβ).norm
  exact EulerProduct.eulerProduct_completely_multiplicative_hasProd hs


theorem rpow_neg_lt_one {β : ℝ} (hβ : 0 < β) (p : Nat.Primes) : (p : ℝ) ^ (-β) < 1 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  exact Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)

theorem rpow_neg_pos (β : ℝ) (p : Nat.Primes) : 0 < (p : ℝ) ^ (-β) :=
  Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _

/-- `log Z(β) = Σ_p −log(1 − p^{−β})`. -/
theorem hasSum_logEuler {β : ℝ} (hβ : 1 < β) :
    HasSum (fun p : Nat.Primes => -Real.log (1 - (p : ℝ) ^ (-β))) (Real.log (Z β)) := by
  have hZ : 0 < Z β := gibbsWeight_tsum_pos hβ
  have hp := hasProd_euler hβ
  have hpos : ∀ p : Nat.Primes, 0 < 1 - (p : ℝ) ^ (-β) := fun p => by
    linarith [rpow_neg_lt_one (by linarith : 0 < β) p]
  have hlim := ((Real.continuousAt_log hZ.ne').tendsto).comp hp
  refine hlim.congr fun s => ?_
  simp only [Function.comp]
  rw [Real.log_prod (fun p _ => (inv_pos.mpr (hpos p)).ne')]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Real.log_inv]


theorem zetaPartition_eq_Z {β : ℝ} (hβ : 1 < β) : zetaPartition β = Z β := by
  have h1 := riemannZeta_eq_ofReal_zetaPartition hβ
  have h2 := riemannZeta_eq_ofReal_gibbsWeight_tsum hβ
  rw [h1] at h2
  exact_mod_cast h2

/-- The termwise derivative. -/
noncomputable def logTermDeriv (p : Nat.Primes) (y : ℝ) : ℝ :=
  -(Real.log p * (p : ℝ) ^ (-y)) / (1 - (p : ℝ) ^ (-y))

theorem hasDerivAt_logTerm (p : Nat.Primes) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun z : ℝ => -Real.log (1 - (p : ℝ) ^ (-z))) (logTermDeriv p y) y := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have h1 : HasDerivAt (fun z : ℝ => (p : ℝ) ^ (-z)) ((p : ℝ) ^ (-y) * Real.log p * (-1)) y :=
    (Real.hasStrictDerivAt_const_rpow hp0 (-y)).hasDerivAt.comp y (hasDerivAt_neg y)
  have h2 : HasDerivAt (fun z : ℝ => 1 - (p : ℝ) ^ (-z)) (-((p : ℝ) ^ (-y) * Real.log p * (-1))) y :=
    h1.const_sub 1
  have hne : 1 - (p : ℝ) ^ (-y) ≠ 0 := (by linarith [rpow_neg_lt_one hy p])
  have h3 := (h2.log hne).neg
  refine h3.congr_deriv ?_
  unfold logTermDeriv
  ring

theorem abs_logTermDeriv_le {p : Nat.Primes} {β₀ y : ℝ} (hβ₀ : 1 < β₀) (hy : β₀ < y) :
    ‖logTermDeriv p y‖ ≤ 2 * (Real.log p * (p : ℝ) ^ (-β₀)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.2.two_le
  have hlog : 0 ≤ Real.log p := Real.log_nonneg hp1.le
  set q : ℝ := (p : ℝ) ^ (-y) with hq
  have hq0 : 0 < q := rpow_neg_pos y p
  have hqβ : q ≤ (p : ℝ) ^ (-β₀) :=
    Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
  have hqhalf : q ≤ 1 / 2 := by
    have h1 : (p : ℝ) ^ (-y) ≤ (p : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
    rw [Real.rpow_neg_one] at h1
    have : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) hp2
    linarith
  have hden : 1 / 2 ≤ 1 - q := by linarith
  unfold logTermDeriv
  rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg (by positivity : 0 ≤ Real.log p * q),
    abs_of_pos (by linarith : 0 < 1 - q)]
  rw [div_le_iff₀ (by linarith)]
  have hlq : Real.log p * q ≤ Real.log p * (p : ℝ) ^ (-β₀) :=
    mul_le_mul_of_nonneg_left hqβ hlog
  nlinarith [mul_nonneg hlog hq0.le]


theorem summable_logPrime {β₀ : ℝ} (h : 1 < β₀) :
    Summable (fun p : Nat.Primes => Real.log p * (p : ℝ) ^ (-β₀)) := by
  have hs := summable_gibbsWeight_mul_logEnergy h
  have hN : Summable (fun n : ℕ => Real.log n * (n : ℝ) ^ (-β₀)) := by
    rw [← summable_nat_add_iff 1]
    refine hs.congr fun n => ?_
    simp only [gibbsWeight, logEnergy]
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
    ring
  exact hN.comp_injective Nat.Primes.coe_nat_injective

/-- **The mean energy is a sum over primes:**
`−ζ′/ζ(β) = U(β) = Σ_p p^{−β} log p / (1 − p^{−β})`. -/
theorem hasSum_meanEnergy {β : ℝ} (hβ : 1 < β) :
    HasSum (fun p : Nat.Primes => (p : ℝ) ^ (-β) * Real.log p / (1 - (p : ℝ) ^ (-β)))
      (zetaMeanEnergy β) := by
  set β₀ : ℝ := (1 + β) / 2 with hβ₀
  have hβ₀1 : 1 < β₀ := by rw [hβ₀]; linarith
  have hβ₀β : β₀ < β := by rw [hβ₀]; linarith
  have hu : Summable (fun p : Nat.Primes => 2 * (Real.log p * (p : ℝ) ^ (-β₀))) :=
    (summable_logPrime hβ₀1).mul_left 2
  have hmem : β ∈ Set.Ioi β₀ := hβ₀β
  have hder := hasDerivAt_tsum_of_isPreconnected
    (g := fun (p : Nat.Primes) (z : ℝ) => -Real.log (1 - (p : ℝ) ^ (-z))) (g' := logTermDeriv)
    hu isOpen_Ioi isPreconnected_Ioi
    (fun p y hy => hasDerivAt_logTerm p (by simp only [Set.mem_Ioi] at hy; linarith))
    (fun p y hy => abs_logTermDeriv_le hβ₀1 hy) hmem (hasSum_logEuler hβ).summable hmem
  have hev : (fun z : ℝ => ∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-z)))
      =ᶠ[𝓝 β] zetaLogPartition := by
    filter_upwards [Ioi_mem_nhds hβ] with z hz
    have hz1 : 1 < z := hz
    rw [(hasSum_logEuler hz1).tsum_eq, zetaLogPartition, zetaPartition_eq_Z hz1]
  have hder2 : HasDerivAt zetaLogPartition (∑' p, logTermDeriv p β) β :=
    hder.congr_of_eventuallyEq hev.symm
  have huniq := (hasDerivAt_zetaLogPartition hβ).unique hder2
  have hsd : Summable (fun p : Nat.Primes => logTermDeriv p β) :=
    Summable.of_norm_bounded hu (fun p => abs_logTermDeriv_le hβ₀1 hβ₀β)
  have hneg := hsd.hasSum.neg
  have hE : zetaMeanEnergy β = -∑' p, logTermDeriv p β := by linarith
  rw [hE]
  have hfun : (fun p : Nat.Primes => (p : ℝ) ^ (-β) * Real.log p / (1 - (p : ℝ) ^ (-β)))
      = fun p => -logTermDeriv p β := by
    funext p
    unfold logTermDeriv
    ring
  rw [hfun]
  exact hneg


/-- Gibbs probabilities `p_{n+1} = (n+1)^{−β} / ζ(β)`. -/
noncomputable def gibbsProb (β : ℝ) (n : ℕ) : ℝ := gibbsWeight β n / Z β

/-- Shannon entropy `S(β) = −Σ_n p_n log p_n` of the zeta Gibbs measure. -/
noncomputable def shannonEntropy (β : ℝ) : ℝ := -∑' n, gibbsProb β n * Real.log (gibbsProb β n)

/-- Local entropy at the prime `p`:
`S_p(β) = −log(1 − p^{−β}) − p^{−β} log(p^{−β}) / (1 − p^{−β})`. -/
noncomputable def localEntropy (β : ℝ) (p : Nat.Primes) : ℝ :=
  -Real.log (1 - (p : ℝ) ^ (-β))
    - (p : ℝ) ^ (-β) * Real.log ((p : ℝ) ^ (-β)) / (1 - (p : ℝ) ^ (-β))

/-- The Shannon entropy of the zeta Gibbs measure is the project's `zetaEntropy`
`= log ζ(β) + β · (−ζ′/ζ)(β)`. -/
theorem shannon_eq_zetaEntropy {β : ℝ} (hβ : 1 < β) :
    shannonEntropy β = zetaEntropy β := by
  have hZ : 0 < Z β := gibbsWeight_tsum_pos hβ
  have hw : ∀ n, 0 < gibbsWeight β n := fun n => by
    unfold gibbsWeight; positivity
  have hterm : ∀ n, -(gibbsProb β n * Real.log (gibbsProb β n))
      = (β / Z β) * (gibbsWeight β n * logEnergy n) + (Real.log (Z β) / Z β) * gibbsWeight β n := by
    intro n
    have hlogw : Real.log (gibbsWeight β n) = -β * logEnergy n := by
      unfold gibbsWeight logEnergy
      rw [one_div, Real.log_inv, Real.log_rpow (by positivity)]
      ring
    unfold gibbsProb
    rw [Real.log_div (hw n).ne' hZ.ne', hlogw]
    field_simp
    ring
  have h1 : Summable (fun n => (β / Z β) * (gibbsWeight β n * logEnergy n)) :=
    (summable_gibbsWeight_mul_logEnergy hβ).mul_left _
  have h2 : Summable (fun n => (Real.log (Z β) / Z β) * gibbsWeight β n) :=
    (summable_gibbsWeight hβ).mul_left _
  unfold shannonEntropy
  rw [← tsum_neg]
  simp_rw [hterm]
  rw [h1.tsum_add h2, tsum_mul_left, tsum_mul_left]
  have hM : zetaMeanEnergy β = M1 β / Z β := zetaMeanEnergy_eq_M1_div_Z hβ
  unfold zetaEntropy zetaLogPartition
  rw [zetaPartition_eq_Z hβ, hM]
  have hZdef : ∑' n, gibbsWeight β n = Z β := rfl
  have hMdef : ∑' n, gibbsWeight β n * logEnergy n = M1 β := rfl
  rw [hZdef, hMdef]
  field_simp
  ring

/-- **Heart #26: entropy additivity over primes.** For `β > 1`, the Shannon entropy of the zeta
Gibbs measure is the sum of the local entropies: `S(β) = Σ_p S_p(β)`. -/
theorem entropy_additive {β : ℝ} (hβ : 1 < β) :
    HasSum (fun p : Nat.Primes => localEntropy β p) (shannonEntropy β) := by
  have h := (hasSum_logEuler hβ).add ((hasSum_meanEnergy hβ).mul_left β)
  have hfun : (fun p : Nat.Primes => localEntropy β p)
      = fun p : Nat.Primes => -Real.log (1 - (p : ℝ) ^ (-β))
        + β * ((p : ℝ) ^ (-β) * Real.log p / (1 - (p : ℝ) ^ (-β))) := by
    funext p
    unfold localEntropy
    rw [Real.log_rpow (by exact_mod_cast p.2.pos)]
    ring
  rw [hfun, shannon_eq_zetaEntropy hβ]
  unfold zetaEntropy zetaLogPartition
  rw [zetaPartition_eq_Z hβ]
  exact h

/-- Corollary: `S(β) = Σ_p S_p(β)` as a `tsum`. -/
theorem shannonEntropy_eq_tsum {β : ℝ} (hβ : 1 < β) :
    shannonEntropy β = ∑' p : Nat.Primes, localEntropy β p :=
  (entropy_additive hβ).tsum_eq.symm


/-! ### Blow-up as `β → 1⁺` -/

theorem tendsto_ofReal_nhdsGT_nhdsNE : Tendsto (fun β : ℝ => (β : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have := (Complex.continuous_ofReal.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with β hβ
    have : (1 : ℝ) < β := hβ
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact_mod_cast this.ne'

/-- `(β − 1) · ζ(β) → 1` as `β → 1⁺`, on the real axis. -/
theorem tendsto_sub_one_mul_Z : Tendsto (fun β : ℝ => (β - 1) * Z β) (𝓝[>] 1) (𝓝 1) := by
  have hc := riemannZeta_residue_one.comp tendsto_ofReal_nhdsGT_nhdsNE
  have hre := (Complex.continuous_re.tendsto 1).comp hc
  simp only [Complex.one_re] at hre
  refine hre.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with β hβ
  have hβ1 : (1 : ℝ) < β := hβ
  have hz := riemannZeta_eq_ofReal_gibbsWeight_tsum hβ1
  simp only [Function.comp]
  rw [hz]
  have : ((β : ℂ) - 1) * ((∑' n, gibbsWeight β n : ℝ) : ℂ) = (((β - 1) * Z β : ℝ) : ℂ) := by
    unfold Z; push_cast; ring
  rw [this, Complex.ofReal_re]

theorem tendsto_Z_atTop : Tendsto Z (𝓝[>] 1) atTop := by
  have hinv : Tendsto (fun β : ℝ => (β - 1)⁻¹) (𝓝[>] 1) atTop := by
    have h0 : Tendsto (fun β : ℝ => β - 1) (𝓝[>] 1) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hc : Continuous (fun β : ℝ => β - 1) := by fun_prop
        have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with β hβ
        have : (1 : ℝ) < β := hβ
        simpa using this
    exact tendsto_inv_nhdsGT_zero.comp h0
  have hprod := hinv.atTop_mul_pos one_pos tendsto_sub_one_mul_Z
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with β hβ
  have : (1 : ℝ) < β := hβ
  have hne : β - 1 ≠ 0 := by linarith
  field_simp

/-- **`S(β) → +∞` as `β → 1⁺`** (`zetaEntropy`, equivalently the Shannon entropy). -/
theorem zetaEntropy_tendsto_atTop : Tendsto zetaEntropy (𝓝[>] 1) atTop := by
  have hlog : Tendsto (fun β => Real.log (Z β)) (𝓝[>] 1) atTop :=
    Real.tendsto_log_atTop.comp tendsto_Z_atTop
  refine tendsto_atTop_mono' _ ?_ hlog
  filter_upwards [self_mem_nhdsWithin] with β hβ
  have hβ1 : (1 : ℝ) < β := hβ
  unfold zetaEntropy zetaLogPartition
  rw [zetaPartition_eq_Z hβ1]
  have := zetaMeanEnergy_nonneg hβ1
  nlinarith

theorem shannonEntropy_tendsto_atTop : Tendsto shannonEntropy (𝓝[>] 1) atTop := by
  refine zetaEntropy_tendsto_atTop.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact (shannon_eq_zetaEntropy (by exact hβ)).symm

end GppEntropyAdditivity

#print axioms GppEntropyAdditivity.hasSum_logEuler
#print axioms GppEntropyAdditivity.hasSum_meanEnergy
#print axioms GppEntropyAdditivity.shannon_eq_zetaEntropy
#print axioms GppEntropyAdditivity.entropy_additive
#print axioms GppEntropyAdditivity.shannonEntropy_tendsto_atTop
