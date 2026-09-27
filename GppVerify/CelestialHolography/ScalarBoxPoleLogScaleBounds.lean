import GppVerify.CelestialHolography.ScalarBoxLogScaleBounds
import GppVerify.CelestialHolography.ScalarBoxPoleEndpointScale
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Logarithmic scale of the scalar-box pole-endpoint ratio

The exact pole displacement has the form

  t = q/a - 1 = η B,    η = m/S,

where `B` is a dimensionless product of factors uniformly close to one.  We use a
slightly coarser factorwise logarithmic bound than the discovery note because it is
simpler to formalize and is fully sufficient for the final `m log^2 m -> 0` remainder.
-/

namespace GppScalarBoxPoleLogScaleBounds

open GppScalarBoxRegulatorBounds
open GppScalarBoxLogScaleBounds

/-- Numerator normalization `N=(1+κ)/2`. -/
noncomputable def poleN (κ : ℝ) : ℝ := (1 + κ) / 2

/-- Product-channel normalization `D₂=(1+x)/2`, with `x=κR`. -/
noncomputable def poleD2 (x : ℝ) : ℝ := (1 + x) / 2

/-- Endpoint normalization `D₃=(1+R)/2`. -/
noncomputable def poleD3 (R : ℝ) : ℝ := (1 + R) / 2

/-- Rewrite the exact Badger-style pole normalization into unit-centered factors. -/
theorem B_eq_unit_centered
    {δ η κ x R B : ℝ}
    (hB : B = 2 * (1 + κ) /
      ((1 + δ) * (1 + x) * (1 + R) * (1 - η))) :
    B = poleN κ /
      ((1 + δ) * poleD2 x * poleD3 R * (1 - η)) := by
  rw [hB]
  unfold poleN poleD2 poleD3
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- If `R²=1/(1+δ)` and `0≤R≤1`, then the endpoint defect satisfies
`1-R≤δ/2`. -/
theorem one_sub_R_le_delta_half
    {δ R : ℝ}
    (hδ0 : 0 ≤ δ)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1)
    (hsq : R ^ 2 = 1 / (1 + δ)) :
    1 - R ≤ δ / 2 := by
  have hden : 0 < 1 + δ := by linarith
  have hsqMul : R ^ 2 * (1 + δ) = 1 := (eq_div_iff hden.ne').mp hsq
  have hid : (1 - R) * (1 + R) = δ * R ^ 2 := by
    nlinarith
  have hRfac : R ^ 2 ≤ (1 + R) / 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - R) (by linarith : 0 ≤ 2 * R + 1)]
  have hplus : 0 < 1 + R := by linarith
  have hscaled : δ * R ^ 2 ≤ δ * ((1 + R) / 2) :=
    mul_le_mul_of_nonneg_left hRfac hδ0
  have heq : 1 - R = δ * R ^ 2 / (1 + R) := by
    apply (eq_div_iff hplus.ne').2
    exact hid
  rw [heq]
  apply (div_le_iff₀ hplus).2
  nlinarith

/-- If `x²=1-δη/(1+δ)` and `x≥15/16`, the product-channel defect is bilinear:
`1-x ≤ (16/31)δη`. -/
theorem one_sub_product_le
    {δ η x : ℝ}
    (hδ0 : 0 ≤ δ) (hη0 : 0 ≤ η)
    (hxlo : 15 / 16 ≤ x) (hxhi : x ≤ 1)
    (hsq : x ^ 2 = 1 - δ * η / (1 + δ)) :
    1 - x ≤ (16 / 31 : ℝ) * (δ * η) := by
  have hden : 0 < 1 + δ := by linarith
  have hplus : (31 / 16 : ℝ) ≤ 1 + x := by linarith
  have hprod0 : 0 ≤ δ * η := mul_nonneg hδ0 hη0
  have hid : (1 - x) * (1 + x) = δ * η / (1 + δ) := by
    rw [show (1 - x) * (1 + x) = 1 - x ^ 2 by ring, hsq]
    ring
  have h1x0 : 0 ≤ 1 - x := by linarith
  have hfrac : δ * η / (1 + δ) ≤ δ * η := by
    exact div_le_self hprod0 (by linarith : 1 ≤ 1 + δ)
  have hmul : (1 - x) * (31 / 16 : ℝ) ≤ δ * η := by
    calc
      (1 - x) * (31 / 16 : ℝ) ≤ (1 - x) * (1 + x) :=
        mul_le_mul_of_nonneg_left hplus h1x0
      _ = δ * η / (1 + δ) := hid
      _ ≤ δ * η := hfrac
  nlinarith

/-- The `N` factor contributes at most `δ/4` to the logarithmic error. -/
theorem abs_log_poleN_le
    {δ η κ : ℝ}
    (hδ0 : 0 ≤ δ) (hη0 : 0 ≤ η)
    (hκlo : 1 ≤ κ)
    (hsq : κ ^ 2 = 1 + δ * (1 - η)) :
    |Real.log (poleN κ)| ≤ δ / 4 := by
  rcases kappa_sub_one_mem hδ0 hη0 hκlo hsq with ⟨_, he⟩
  have hN1 : 1 ≤ poleN κ := by unfold poleN; linarith
  have hNpos : 0 < poleN κ := lt_of_lt_of_le zero_lt_one hN1
  have hlog0 : 0 ≤ Real.log (poleN κ) := Real.log_nonneg hN1
  have hlog := Real.log_le_sub_one_of_pos hNpos
  rw [abs_of_nonneg hlog0]
  unfold poleN at hlog ⊢
  linarith

/-- The factor `1+δ` contributes at most `δ`. -/
theorem abs_log_one_add_delta_le
    {δ : ℝ} (hδ0 : 0 ≤ δ) :
    |Real.log (1 + δ)| ≤ δ := by
  have hpos : 0 < 1 + δ := by linarith
  have hlog0 : 0 ≤ Real.log (1 + δ) := Real.log_nonneg (by linarith)
  have hlog := Real.log_le_sub_one_of_pos hpos
  rw [abs_of_nonneg hlog0]
  linarith

/-- The product-channel factor contributes only `O(δη)`. -/
theorem abs_log_poleD2_le
    {δ η x : ℝ}
    (hδ0 : 0 ≤ δ) (hη0 : 0 ≤ η)
    (hxlo : 15 / 16 ≤ x) (hxhi : x ≤ 1)
    (hsq : x ^ 2 = 1 - δ * η / (1 + δ)) :
    |Real.log (poleD2 x)| ≤ (1 / 3 : ℝ) * (δ * η) := by
  have hDlo : (31 / 32 : ℝ) ≤ poleD2 x := by unfold poleD2; linarith
  have hDhi : poleD2 x ≤ 1 := by unfold poleD2; linarith
  have hlog := abs_log_le_one_sub_div_lower
    (c := (31 / 32 : ℝ)) (x := poleD2 x) (by norm_num) hDlo hDhi
  have hxdef := one_sub_product_le hδ0 hη0 hxlo hxhi hsq
  have hdef : 1 - poleD2 x ≤ (8 / 31 : ℝ) * (δ * η) := by
    unfold poleD2
    nlinarith
  have hscaled :
      (32 / 31 : ℝ) * (1 - poleD2 x) ≤
        (32 / 31 : ℝ) * ((8 / 31 : ℝ) * (δ * η)) :=
    mul_le_mul_of_nonneg_left hdef (by norm_num)
  calc
    |Real.log (poleD2 x)| ≤ (1 - poleD2 x) / (31 / 32 : ℝ) := hlog
    _ = (32 / 31 : ℝ) * (1 - poleD2 x) := by ring
    _ ≤ (32 / 31 : ℝ) * ((8 / 31 : ℝ) * (δ * η)) := hscaled
    _ ≤ (1 / 3 : ℝ) * (δ * η) := by
      have hp : 0 ≤ δ * η := mul_nonneg hδ0 hη0
      nlinarith

/-- The endpoint factor `D₃` contributes at most `(9/34)δ`. -/
theorem abs_log_poleD3_le
    {δ R : ℝ}
    (hδ0 : 0 ≤ δ)
    (hRlo : 8 / 9 ≤ R) (hRhi : R ≤ 1)
    (hsq : R ^ 2 = 1 / (1 + δ)) :
    |Real.log (poleD3 R)| ≤ (9 / 34 : ℝ) * δ := by
  have hR0 : 0 ≤ R := by linarith
  have hDlo : (17 / 18 : ℝ) ≤ poleD3 R := by unfold poleD3; linarith
  have hDhi : poleD3 R ≤ 1 := by unfold poleD3; linarith
  have hlog := abs_log_le_one_sub_div_lower
    (c := (17 / 18 : ℝ)) (x := poleD3 R) (by norm_num) hDlo hDhi
  have hRdef := one_sub_R_le_delta_half hδ0 hR0 hRhi hsq
  have hdef : 1 - poleD3 R ≤ δ / 4 := by
    unfold poleD3
    nlinarith
  calc
    |Real.log (poleD3 R)| ≤ (1 - poleD3 R) / (17 / 18 : ℝ) := hlog
    _ ≤ (9 / 34 : ℝ) * δ := by
      have hm := mul_le_mul_of_nonneg_left hdef (by norm_num : (0 : ℝ) ≤ 18 / 17)
      convert hm using 1 <;> ring

/-- The lower factor `1-η` contributes at most `(4/3)η` on `η≤1/4`. -/
theorem abs_log_one_sub_eta_le
    {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4) :
    |Real.log (1 - η)| ≤ (4 / 3 : ℝ) * η := by
  have hlo : (3 / 4 : ℝ) ≤ 1 - η := by linarith
  have hhi : 1 - η ≤ 1 := by linarith
  have hlog := abs_log_le_one_sub_div_lower
    (c := (3 / 4 : ℝ)) (x := 1 - η) (by norm_num) hlo hhi
  convert hlog using 1 <;> ring

/-- Five-term triangle inequality used for the logarithm of the normalized product. -/
theorem abs_sub_sub_sub_sub_le (a b c d e : ℝ) :
    |a - b - c - d - e| ≤ |a| + |b| + |c| + |d| + |e| := by
  calc
    |a - b - c - d - e| ≤ |a - b - c - d| + |e| := abs_sub _ _
    _ ≤ (|a - b - c| + |d|) + |e| := by gcongr; exact abs_sub _ _
    _ ≤ ((|a - b| + |c|) + |d|) + |e| := by gcongr; exact abs_sub _ _
    _ ≤ (((|a| + |b|) + |c|) + |d|) + |e| := by gcongr; exact abs_sub _ _
    _ = |a| + |b| + |c| + |d| + |e| := by ring

/-- Coarse but clean logarithmic normalization bound. -/
theorem abs_log_B_le
    {δ η κ x R B : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4)
    (hκlo : 1 ≤ κ) (hκhi : κ ≤ 9 / 8)
    (hxlo : 15 / 16 ≤ x) (hxhi : x ≤ 1)
    (hRlo : 8 / 9 ≤ R) (hRhi : R ≤ 1)
    (hκsq : κ ^ 2 = 1 + δ * (1 - η))
    (hxsq : x ^ 2 = 1 - δ * η / (1 + δ))
    (hRsq : R ^ 2 = 1 / (1 + δ))
    (hB : B = 2 * (1 + κ) /
      ((1 + δ) * (1 + x) * (1 + R) * (1 - η))) :
    |Real.log B| ≤
      (103 / 68 : ℝ) * δ + (1 / 3 : ℝ) * (δ * η) + (4 / 3 : ℝ) * η := by
  have hNorm := B_eq_unit_centered hB
  have hNpos : 0 < poleN κ := by unfold poleN; linarith
  have h1δ : 0 < 1 + δ := by linarith
  have hD2pos : 0 < poleD2 x := by unfold poleD2; linarith
  have hD3pos : 0 < poleD3 R := by unfold poleD3; linarith
  have h1η : 0 < 1 - η := by linarith
  have hdenpos : 0 < (1 + δ) * poleD2 x * poleD3 R * (1 - η) := by positivity
  have hlogDen :
      Real.log ((1 + δ) * poleD2 x * poleD3 R * (1 - η)) =
        Real.log (1 + δ) + Real.log (poleD2 x) +
          Real.log (poleD3 R) + Real.log (1 - η) := by
    rw [Real.log_mul (mul_ne_zero (mul_ne_zero h1δ.ne' hD2pos.ne') hD3pos.ne') h1η.ne']
    rw [Real.log_mul (mul_ne_zero h1δ.ne' hD2pos.ne') hD3pos.ne']
    rw [Real.log_mul h1δ.ne' hD2pos.ne']
  have hlogB :
      Real.log B = Real.log (poleN κ) - Real.log (1 + δ) -
        Real.log (poleD2 x) - Real.log (poleD3 R) - Real.log (1 - η) := by
    rw [hNorm, Real.log_div hNpos.ne' hdenpos.ne', hlogDen]
    ring
  have hN := abs_log_poleN_le hδ0 hη0 hκlo hκsq
  have hδlog := abs_log_one_add_delta_le hδ0
  have hD2 := abs_log_poleD2_le hδ0 hη0 hxlo hxhi hxsq
  have hD3 := abs_log_poleD3_le hδ0 hRlo hRhi hRsq
  have hηlog := abs_log_one_sub_eta_le hη0 hη
  rw [hlogB]
  calc
    |Real.log (poleN κ) - Real.log (1 + δ) - Real.log (poleD2 x) -
        Real.log (poleD3 R) - Real.log (1 - η)| ≤
      |Real.log (poleN κ)| + |Real.log (1 + δ)| + |Real.log (poleD2 x)| +
        |Real.log (poleD3 R)| + |Real.log (1 - η)| :=
      abs_sub_sub_sub_sub_le _ _ _ _ _
    _ ≤ (103 / 68 : ℝ) * δ + (1 / 3 : ℝ) * (δ * η) + (4 / 3 : ℝ) * η := by
      nlinarith

/-- Final logarithmic scale replacement for the moving pole endpoint. -/
theorem abs_log_t_sub_log_m_div_S_le
    {S m δ η κ x R B t : ℝ}
    (hS : 0 < S) (hm : 0 < m)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4)
    (hκlo : 1 ≤ κ) (hκhi : κ ≤ 9 / 8)
    (hxlo : 15 / 16 ≤ x) (hxhi : x ≤ 1)
    (hRlo : 8 / 9 ≤ R) (hRhi : R ≤ 1)
    (hκsq : κ ^ 2 = 1 + δ * (1 - η))
    (hxsq : x ^ 2 = 1 - δ * η / (1 + δ))
    (hRsq : R ^ 2 = 1 / (1 + δ))
    (hB : B = 2 * (1 + κ) /
      ((1 + δ) * (1 + x) * (1 + R) * (1 - η)))
    (hηdef : η = m / S)
    (ht : t = η * B) :
    |Real.log t - Real.log (m / S)| ≤
      (103 / 68 : ℝ) * δ + (1 / 3 : ℝ) * (δ * η) + (4 / 3 : ℝ) * η := by
  have hBpair := B_pos_and_le δ η κ x R B
    hδ0 hη0 hη hκlo hκhi hxlo hRlo hB
  have hBpos : 0 < B := hBpair.1
  have hηpos : 0 < η := by rw [hηdef]; exact div_pos hm hS
  have hlog := abs_log_B_le
    hδ0 hδ hη0 hη hκlo hκhi hxlo hxhi hRlo hRhi
    hκsq hxsq hRsq hB
  rw [ht, Real.log_mul hηpos.ne' hBpos.ne', hηdef]
  simp only [add_sub_cancel_left]
  simpa [hηdef] using hlog

end GppScalarBoxPoleLogScaleBounds

#print axioms GppScalarBoxPoleLogScaleBounds.one_sub_R_le_delta_half
#print axioms GppScalarBoxPoleLogScaleBounds.one_sub_product_le
#print axioms GppScalarBoxPoleLogScaleBounds.abs_log_B_le
#print axioms GppScalarBoxPoleLogScaleBounds.abs_log_t_sub_log_m_div_S_le
