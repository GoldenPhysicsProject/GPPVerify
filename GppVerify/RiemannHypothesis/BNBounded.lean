import GppVerify.RiemannHypothesis.BNBilinear
import GppVerify.RiemannHypothesis.ResolventBounds

/-!
# `C_N` as a bounded operator on the `B_N`-completion

Turbo's build-order step (3), second half (bridge `0518bf9`; GPT's Theorem 6). With `b_N` the bilinear form of
`BNBilinear.lean`, `H` its Hilbert completion (`exists_hilbert_bn`) and `ι : V_L → H`, this file:

* shows `f ↦ C_N f` is **linear** on `V_L` (`phiLin`, `CNlin`): the shift series and `toLp` are additive and
  homogeneous;
* proves the bound `‖C_N f‖² ≤ (t_N(0)/m) · b_N(f, f)` for `m = θ(N) + κ_L > 0` (`normSq_CNlin_le`), from
  `ResolventBounds.normSq_CN_le` (`‖C_N f‖² ≤ t_N(0)‖f‖²`) and coercivity (`bnBilin_self_ge`);
* extends `C_N` to a **bounded** operator `Cbar : H → ⊕_{p ≤ N} L²` with `Cbar (ι f) = C_N f` and
  `‖Cbar‖² ≤ t_N(0)/m` (`exists_bounded_extension`).

**Not here:** the per-vector ratio and the norm-one limit as `N → ∞` (steps (4)–(5)); contractivity
`‖Cbar‖ ≤ 1`, which is `OB6At L` — OPEN. No `sorry`, no axiom.
-/

open MeasureTheory
open GppArithmeticReflection
open scoped ContDiff

noncomputable section

namespace GppShiftPresentation

variable {q ℓ : ℝ}

/-! ### Linearity of the shift series and of `Φ_p` into `L²` -/

theorem summable_shiftTerms {g : ℝ → ℝ} (hg : Continuous g) (hc : HasCompactSupport g)
    (hq0 : 0 < q) (hq1 : q < 1) (y : ℝ) : Summable (fun m : ℕ => q ^ m * g (y - m * ℓ)) := by
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hc
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0.le hq1).mul_right B)
    (fun m => ?_)
  rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos hq0]
  have := hB (y - m * ℓ)
  simp only [Real.norm_eq_abs] at this
  exact mul_le_mul_of_nonneg_left this (by positivity)

theorem shiftSeries_add {f g : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hq0 : 0 < q) (hq1 : q < 1) :
    shiftSeries q ℓ (f + g) = shiftSeries q ℓ f + shiftSeries q ℓ g := by
  funext y
  simp only [shiftSeries, Pi.add_apply]
  rw [← (summable_shiftTerms (ℓ := ℓ) hf hfc hq0 hq1 y).tsum_add
    (summable_shiftTerms (ℓ := ℓ) hg hgc hq0 hq1 y)]
  refine tsum_congr fun m => ?_
  ring

theorem shiftSeries_smul (c : ℝ) (g : ℝ → ℝ) :
    shiftSeries q ℓ (c • g) = c • shiftSeries q ℓ g := by
  funext y
  simp only [shiftSeries, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  ring

theorem phi_add {p : ℕ} (hp : 2 ≤ p) {f g : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) : phi p (f + g) = phi p f + phi p g := by
  rw [phi_eq hp, phi_eq hp, phi_eq hp]
  exact shiftSeries_add hf hfc hg hgc (qOf_pos hp) (qOf_lt_one hp)

theorem phi_smul {p : ℕ} (hp : 2 ≤ p) (c : ℝ) (g : ℝ → ℝ) : phi p (c • g) = c • phi p g := by
  rw [phi_eq hp, phi_eq hp]
  exact shiftSeries_smul c g

/-- `Φ_p` as a **linear** map `V_L → L²(ℝ)`. -/
def phiLin {p : ℕ} (hp : 2 ≤ p) (L : ℝ) :
    windowSubmodule L →ₗ[ℝ] Lp ℝ 2 (volume : Measure ℝ) where
  toFun f := phiL2 hp f.2.1.1.continuous f.2.1.2
  map_add' f g := by
    apply Lp.ext
    have h1 := MemLp.coeFn_toLp (memLp_phi hp (f + g).2.1.1.continuous (f + g).2.1.2)
    have h2 := MemLp.coeFn_toLp (memLp_phi hp f.2.1.1.continuous f.2.1.2)
    have h3 := MemLp.coeFn_toLp (memLp_phi hp g.2.1.1.continuous g.2.1.2)
    filter_upwards [h1, h2, h3, Lp.coeFn_add (phiL2 hp f.2.1.1.continuous f.2.1.2)
      (phiL2 hp g.2.1.1.continuous g.2.1.2)] with y e1 e2 e3 e4
    show (phiL2 hp (f + g).2.1.1.continuous (f + g).2.1.2) y = _
    rw [e4]
    show (MemLp.toLp (phi p ((f + g : windowSubmodule L) : ℝ → ℝ)) _) y = _
    rw [e1]
    simp only [Pi.add_apply]
    rw [show ((f + g : windowSubmodule L) : ℝ → ℝ) = f.1 + g.1 from rfl,
      phi_add hp f.2.1.1.continuous f.2.1.2 g.2.1.1.continuous g.2.1.2]
    simp only [Pi.add_apply]
    exact congrArg₂ (· + ·) e2.symm e3.symm
  map_smul' c f := by
    apply Lp.ext
    have h1 := MemLp.coeFn_toLp (memLp_phi hp (c • f).2.1.1.continuous (c • f).2.1.2)
    have h2 := MemLp.coeFn_toLp (memLp_phi hp f.2.1.1.continuous f.2.1.2)
    filter_upwards [h1, h2, Lp.coeFn_smul c (phiL2 hp f.2.1.1.continuous f.2.1.2)] with y e1 e2 e4
    show (phiL2 hp (c • f).2.1.1.continuous (c • f).2.1.2) y = _
    rw [RingHom.id_apply, e4]
    show (MemLp.toLp (phi p ((c • f : windowSubmodule L) : ℝ → ℝ)) _) y = _
    rw [e1]
    rw [show ((c • f : windowSubmodule L) : ℝ → ℝ) = c • f.1 from rfl, phi_smul hp]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [e2.symm]; rfl

/-! ### `C_N` as a linear map, and its bound against `b_N` -/

/-- The target `⊕_{p ≤ N} L²(ℝ)`. -/
abbrev CNTarget (N : ℕ) : Type := PiLp 2 (fun _ : ↥(primesUpTo N) => Lp ℝ 2 (volume : Measure ℝ))

/-- **`C_N` as a linear map** `V_L → ⊕_{p≤N} L²`: `f ↦ (√((log p)(1 − p⁻¹)) Φ_p f)_p`. -/
def CNlin (N : ℕ) (L : ℝ) : windowSubmodule L →ₗ[ℝ] CNTarget N :=
  (WithLp.linearEquiv 2 ℝ (∀ _ : ↥(primesUpTo N), Lp ℝ 2 (volume : Measure ℝ))).symm.toLinearMap ∘ₗ
    LinearMap.pi (fun p : ↥(primesUpTo N) =>
      Real.sqrt (Real.log p * (1 - 1 / (p : ℝ))) • phiLin (two_le_of_mem_primesUpTo p) L)

theorem CNlin_eq (N : ℕ) (L : ℝ) (f : windowSubmodule L) :
    CNlin N L f = CN N f.2.1.1.continuous f.2.1.2 := rfl

/-- `‖C_N f‖² ≤ (t_N(0)/m) · b_N(f, f)` when `m = θ(N) + κ_L > 0`. -/
theorem normSq_CNlin_le (N : ℕ) {L : ℝ} (hL : 0 ≤ L) (hm : 0 < thetaN N + kappa L)
    (f : windowSubmodule L) :
    ‖CNlin N L f‖ ^ 2 ≤ tN0 N / (thetaN N + kappa L) * bnBilin N L f f := by
  rw [CNlin_eq]
  have h1 := normSq_CN_le N f.2.1.1 f.2.1.2
  have h2 := bnBilin_self_ge N hL f
  have ht : 0 ≤ tN0 N := by
    rw [tN0_eq]
    refine Finset.sum_nonneg fun p hp => ?_
    have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
    have hq0 := qOf_pos hp2
    have hq1 := qOf_lt_one hp2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
    exact mul_nonneg (Real.log_nonneg hp1.le) (div_nonneg (by linarith) (by linarith))
  have hA : autocorr f.1 0 ≤ bnBilin N L f f / (thetaN N + kappa L) := by
    rw [le_div_iff₀ hm]; linarith
  calc ‖CN N f.2.1.1.continuous f.2.1.2‖ ^ 2 ≤ tN0 N * autocorr f.1 0 := h1
    _ ≤ tN0 N * (bnBilin N L f f / (thetaN N + kappa L)) := mul_le_mul_of_nonneg_left hA ht
    _ = tN0 N / (thetaN N + kappa L) * bnBilin N L f f := by ring

/-- **`C_N` extends to a bounded operator on the `B_N`-completion** (GPT's Theorem 6, bounded part):
there are a real Hilbert space `H`, a dense linear `ι : V_L → H` with `b_N(f, g) = ⟪ι f, ι g⟫`, and a bounded
`Cbar : H → ⊕_{p≤N} L²` with `Cbar (ι f) = C_N f` and `‖Cbar‖² ≤ t_N(0)/(θ(N) + κ_L)`. -/
theorem exists_bounded_extension (N : ℕ) {L : ℝ} (hL : 0 ≤ L) (hm : 0 < thetaN N + kappa L) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
      (ι : windowSubmodule L →ₗ[ℝ] H) (Cb : H →L[ℝ] CNTarget N),
      (∀ f g, bnBilin N L f g = inner ℝ (ι f) (ι g)) ∧ DenseRange ι ∧
        (∀ f, Cb (ι f) = CNlin N L f) ∧ ‖Cb‖ ^ 2 ≤ tN0 N / (thetaN N + kappa L) := by
  have hpsd := psd_bnBilin N hL hm.le
  set K : ℝ := tN0 N / (thetaN N + kappa L) with hK
  have hK0 : 0 ≤ K := by
    have ht : 0 ≤ tN0 N := by
      rw [tN0_eq]
      refine Finset.sum_nonneg fun p hp => ?_
      have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
      have hq0 := qOf_pos hp2
      have hq1 := qOf_lt_one hp2
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
      exact mul_nonneg (Real.log_nonneg hp1.le) (div_nonneg (by linarith) (by linarith))
    exact div_nonneg ht hm.le
  have hdense := GppFormGNS.dense_range_vec hpsd
  have hnorm : ∀ f : windowSubmodule L,
      ‖CNlin N L f‖ ≤ Real.sqrt K * ‖GppFormGNS.vec hpsd f‖ := by
    intro f
    have h1 := normSq_CNlin_le N hL hm f
    have h2 : bnBilin N L f f = ‖GppFormGNS.vec hpsd f‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, GppFormGNS.inner_vec]
    rw [h2, ← hK] at h1
    calc ‖CNlin N L f‖ = Real.sqrt (‖CNlin N L f‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (K * ‖GppFormGNS.vec hpsd f‖ ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt K * ‖GppFormGNS.vec hpsd f‖ := by
          rw [Real.sqrt_mul hK0, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨GppFormGNS.Space hpsd, inferInstance, inferInstance, inferInstance,
    GppFormGNS.vec hpsd, (CNlin N L).extendOfNorm (GppFormGNS.vec hpsd), ?_, hdense, ?_, ?_⟩
  · intro f g; exact (GppFormGNS.inner_vec hpsd f g).symm
  · intro f
    exact LinearMap.extendOfNorm_eq hdense ⟨Real.sqrt K, hnorm⟩ f
  · have hop := LinearMap.opNorm_extendOfNorm_le (f := CNlin N L)
      (e := GppFormGNS.vec hpsd) hdense (Real.sqrt_nonneg K) hnorm
    calc ‖(CNlin N L).extendOfNorm (GppFormGNS.vec hpsd)‖ ^ 2 ≤ (Real.sqrt K) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hop 2
      _ = K := Real.sq_sqrt hK0

end GppShiftPresentation

#print axioms GppShiftPresentation.exists_bounded_extension
