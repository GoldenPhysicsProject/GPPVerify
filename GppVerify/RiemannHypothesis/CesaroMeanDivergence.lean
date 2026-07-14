import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Divergence of the inversion-invariant Cesàro mean away from `σ = 1/2`

Formalizes the divergence half of Lemma 3.1 of Toupin, *The Riemann Hypothesis as Haar
Self-Duality* (`riemann_haar_dtoupin_v3_1.tex`): on `G = ℝ_{>0}` with Haar measure
`d×r = dr/r`, the symmetric Cesàro mean of `f_σ(r) = r^{2σ-1}`,
`(1/(2 log R)) ∫_{1/R}^{R} f_σ(r) d×r`, tends to `+∞` as `R → ∞` for every `σ ≠ 1/2`.

Combined with the pre-existing `born_rule_cesaro` (`RHProofStructure.lean`), which already
proves the mean equals exactly `1` — for every `R > 1`, not just in a limit — at `σ = 1/2`,
this completes Lemma 3.1 in full: `σ = 1/2` is the unique value at which the
inversion-invariant Cesàro mean is both finite and nonzero, the paper's central
self-duality claim. `RHProofStructure.lean`'s own doc comment on `born_rule_cesaro`
explicitly flagged this divergence direction as "a genuine but separate analytic fact ...
not formalized here"; it is formalized here.

Not derived from ONON52.tex — a from-scratch formalization of an auxiliary paper's lemma,
built against Mathlib's asymptotic-analysis library (the "polynomial beats logarithm"
comparison `isLittleO_log_rpow_atTop`), since Mathlib does not package the ratio-tendsto
form of that growth-rate fact directly.
-/

namespace GppCesaroMean

open Filter Real

/-- `x ^ r` divided by a fixed positive constant times `log x` tends to `+∞`, for `r > 0`:
    the polynomial growth of `x ^ r` beats the logarithm at any fixed positive scale `k`.
    Proved directly from `isLittleO_log_rpow_atTop` via an explicit `ε`-`M` argument, since
    Mathlib does not package the ratio-tendsto form of this fact. -/
theorem tendsto_rpow_div_const_mul_log_atTop {r k : ℝ} (hr : 0 < r) (hk : 0 < k) :
    Tendsto (fun x : ℝ => x ^ r / (k * Real.log x)) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro M
  rcases le_or_lt M 0 with hM | hM
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hlog : 0 < Real.log x := Real.log_pos hx
    have hxr : 0 < x ^ r := Real.rpow_pos_of_pos (lt_trans one_pos hx) r
    have hden : 0 < k * Real.log x := mul_pos hk hlog
    have hnn : 0 ≤ x ^ r / (k * Real.log x) := le_of_lt (div_pos hxr hden)
    linarith
  · have hkne : k ≠ 0 := hk.ne'
    have hMne : M ≠ 0 := hM.ne'
    have hεpos : (0 : ℝ) < 1 / (k * M) := by positivity
    filter_upwards [(isLittleO_log_rpow_atTop hr).def hεpos, eventually_gt_atTop (1 : ℝ)]
      with x hxev hx1
    have hlog : 0 < Real.log x := Real.log_pos hx1
    have hxr : 0 < x ^ r := Real.rpow_pos_of_pos (lt_trans one_pos hx1) r
    have hden : 0 < k * Real.log x := mul_pos hk hlog
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlog, abs_of_pos hxr] at hxev
    rw [le_div_iff₀ hden]
    have step1 : k * Real.log x ≤ k * (1 / (k * M) * x ^ r) :=
      mul_le_mul_of_nonneg_left hxev hk.le
    have step2 : M * (k * Real.log x) ≤ M * (k * (1 / (k * M) * x ^ r)) :=
      mul_le_mul_of_nonneg_left step1 hM.le
    have step3 : M * (k * (1 / (k * M) * x ^ r)) = x ^ r := by field_simp
    linarith [step2, step3]

/-- Core divergence estimate for `c > 0`: `(R^c - R^{-c}) / (c · 2 log R) → +∞`. -/
theorem tendsto_cesaro_diff_div_log_atTop_pos {c : ℝ} (hc : 0 < c) :
    Tendsto (fun R : ℝ => (R ^ c - R ^ (-c)) / (c * (2 * Real.log R))) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro M
  rcases le_or_lt M 0 with hM | hM
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
    have hRpos : 0 < R := lt_trans one_pos hR
    have hlog : 0 < Real.log R := Real.log_pos hR
    have hRc1 : 1 ≤ R ^ c := Real.one_le_rpow hR.le hc.le
    have hRneg1 : R ^ (-c) ≤ 1 := by
      rw [Real.rpow_neg hRpos.le]
      exact inv_le_one_of_one_le₀ hRc1
    have hnum : 0 ≤ R ^ c - R ^ (-c) := by linarith
    have hden : 0 < c * (2 * Real.log R) := by positivity
    have hnn : 0 ≤ (R ^ c - R ^ (-c)) / (c * (2 * Real.log R)) := div_nonneg hnum hden.le
    linarith
  · have hMne : M ≠ 0 := hM.ne'
    have hcne0 : c ≠ 0 := hc.ne'
    set ε : ℝ := 1 / (4 * M * c) with hεdef
    have hεpos : 0 < ε := by positivity
    have hRc2 : ∀ᶠ R : ℝ in atTop, (2 : ℝ) ≤ R ^ c :=
      Filter.tendsto_atTop.mp (tendsto_rpow_atTop hc) 2
    filter_upwards [(isLittleO_log_rpow_atTop hc).def hεpos, hRc2, eventually_gt_atTop (1 : ℝ)]
      with R hRev hRc2' hR1
    have hRpos : 0 < R := lt_trans one_pos hR1
    have hlog : 0 < Real.log R := Real.log_pos hR1
    have hRcpos : 0 < R ^ c := Real.rpow_pos_of_pos hRpos c
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlog, abs_of_pos hRcpos] at hRev
    have hRneg1 : R ^ (-c) ≤ 1 := by
      rw [Real.rpow_neg hRpos.le]
      exact inv_le_one_of_one_le₀ (by linarith : (1 : ℝ) ≤ R ^ c)
    have hnum : R ^ c - 1 ≤ R ^ c - R ^ (-c) := by linarith
    have hden : 0 < c * (2 * Real.log R) := by positivity
    rw [le_div_iff₀ hden]
    have hRc_ge : 4 * M * c * Real.log R ≤ R ^ c := by
      have h4Mc : (0 : ℝ) < 4 * M * c := by positivity
      have hmul := mul_le_mul_of_nonneg_left hRev h4Mc.le
      have heq2 : 4 * M * c * (ε * R ^ c) = R ^ c := by
        rw [hεdef]; field_simp
      linarith [hmul, heq2]
    calc M * (c * (2 * Real.log R))
        = (1 / 2) * (4 * M * c * Real.log R) := by ring
      _ ≤ (1 / 2) * R ^ c := by linarith [hRc_ge]
      _ = R ^ c / 2 := by ring
      _ ≤ R ^ c - 1 := by linarith [hRc2']
      _ ≤ R ^ c - R ^ (-c) := hnum

/-- General divergence estimate for any `c ≠ 0`, via the `c > 0` case applied to `-c` when
    `c < 0` — the expression is even in `c` (numerator and denominator both flip sign,
    leaving the ratio unchanged). -/
theorem tendsto_cesaro_diff_div_log_atTop {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun R : ℝ => (R ^ c - R ^ (-c)) / (c * (2 * Real.log R))) atTop atTop := by
  rcases hc.lt_or_lt with hneg | hpos
  · have hd : 0 < -c := by linarith
    have key := tendsto_cesaro_diff_div_log_atTop_pos hd
    have heq : ∀ R : ℝ, (R ^ (-c) - R ^ (-(-c))) / ((-c) * (2 * Real.log R)) =
        (R ^ c - R ^ (-c)) / (c * (2 * Real.log R)) := by
      intro R
      rw [neg_neg]
      rw [show R ^ (-c) - R ^ c = -(R ^ c - R ^ (-c)) by ring,
          show (-c) * (2 * Real.log R) = -(c * (2 * Real.log R)) by ring,
          neg_div_neg_eq]
    exact (Filter.tendsto_congr heq).mp key
  · exact tendsto_cesaro_diff_div_log_atTop_pos hpos

/-- **Lemma 3.1** (divergence direction): for `σ ≠ 1/2`, the symmetric Cesàro mean of
    `f_σ(r) = r^{2σ-1}` against Haar measure `d×r = dr/r` on `ℝ_{>0}` diverges to `+∞` as
    `R → ∞`. Together with `GppRHProofStructure.born_rule_cesaro` (which proves the mean
    equals exactly `1`, for every `R > 1`, at `σ = 1/2`), this gives the full content of
    Lemma 3.1: `σ = 1/2` is the unique value at which the inversion-invariant Cesàro mean is
    finite and nonzero. -/
theorem tendsto_cesaro_mean_atTop_of_ne {σ : ℝ} (hσ : σ ≠ 1 / 2) :
    Tendsto (fun R : ℝ => (∫ r in (1 / R)..R, r ^ (2 * σ - 2)) / (2 * Real.log R))
      atTop atTop := by
  have hcne : (2 : ℝ) * σ - 1 ≠ 0 := fun h => hσ (by linarith)
  have hrne : (2 : ℝ) * σ - 2 ≠ -1 := fun h => hcne (by linarith)
  have key := tendsto_cesaro_diff_div_log_atTop hcne
  have heq : (fun R : ℝ => (∫ r in (1 / R)..R, r ^ (2 * σ - 2)) / (2 * Real.log R)) =ᶠ[atTop]
      (fun R : ℝ => (R ^ (2 * σ - 1) - R ^ (-(2 * σ - 1))) /
        ((2 * σ - 1) * (2 * Real.log R))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hRinv : (0 : ℝ) < 1 / R := by positivity
    have h0 : (0 : ℝ) ∉ Set.uIcc (1 / R) R := Set.notMem_uIcc_of_lt hRinv hR
    rw [integral_rpow (Or.inr ⟨hrne, h0⟩),
        show (2 * σ - 2 + 1 : ℝ) = 2 * σ - 1 by ring,
        show (1 / R : ℝ) = R⁻¹ by rw [one_div],
        Real.inv_rpow hR.le, ← Real.rpow_neg hR.le,
        div_div]
  exact (Filter.tendsto_congr' heq).mpr key

end GppCesaroMean
