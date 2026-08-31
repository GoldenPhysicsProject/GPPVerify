import GppVerify.QuantumGravity.StefanBoltzmannFamily
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Ladder convolution bound: `0 < 𝓜_L ≤ (1/8)^L`

`P(λ) = πλ/sinh(πλ)` is the two-particle massless phase-space weight of a celestial
unitarity cut (Toupin, "The Spectral Weight π λ / sinh π λ", 2026): the Mellin image of
two-particle phase space, restricted to the shadow locus, equals `Γ(1+iλ)Γ(1-iλ)`.

## The object

For `L ≥ 1`, `𝓜_L` is the `L`-fold chain convolution of `P` against itself

```
𝓜_L = (2π)^{-L} ∫_{ℝ_{>0}^L} [∏_{j=1}^L P(λ_j)] [∏_{j=1}^{L-1} P(|λ_j-λ_{j+1}|)] dλ_1⋯dλ_L
```

with `L` external factors of `P` and `L-1` internal "rung" factors coupling adjacent
integration variables. This is a statement about the convolution integral itself, not a
claim about any physical loop amplitude. This file encodes the object via its own recursive
description ("passing from `𝓜_{L-1}` to `𝓜_L` multiplies the integrand by one new
external factor and one new connecting rung"): a chain kernel `K n : ℝ → ℝ≥0∞`
(`n = L - 1`, so `K 0` is the one-loop weight `P`) with

```
K 0 λ       = P⁺(λ)
K (n+1) λ   = P⁺(λ) · ∫⁻ μ, K n μ · P⁺(|μ-λ|)
```

which is exactly Fubini/Tonelli's iterated-integral expansion of the `n+2`-loop `ℝ_{>0}^{n+2}`
integral, peeling off one loop variable at a time — the standard way to encode a chain
convolution without needing general `Fin L`-indexed product-measure machinery. `𝓜 n`
(`= 𝓜_{n+1}` in the paper's indexing) is then `(2π)^{-(n+1)} · ∫⁻ λ, K n λ`.

Everything is carried in `ℝ≥0∞` (Lebesgue's `lintegral`), which makes Tonelli's theorem
and monotonicity **unconditional** — no integrability side-conditions are needed anywhere
in the induction, since positivity is exactly what does the work in the paper's own proof
(bound each rung by 1, discard it; the remaining product integral factorizes). Finiteness
of `𝓜 n` (i.e. `𝓜 n < ⊤`, hence a genuine nonnegative real number) is part of what the
bound proves, not an assumption.

## Proof shape (matches the paper exactly)

* `P_le_one`/`P_pos`: `0 < P(λ) ≤ 1` for `λ > 0`, from `sinh(x) > x` (`x > 0`).
* `integral_P_eq`: `∫₀^∞ P(λ)dλ = π/4` (already proved in `StefanBoltzmannFamily`, at `s=1`).
* Induction on `n`: bounding each rung `P⁺(|μ-λ|) ≤ 1` lets the inner integral be dropped
  (`lintegral_mono`, unconditional), giving `K (n+1) λ ≤ P⁺(λ) · (∫⁻ K n)`; integrating and
  pulling the constant out (`lintegral_const_mul`, unconditional) and using the inductive
  bound on `∫⁻ K n` closes the `(1/8)^{n+2}` step exactly, matching the paper's power
  cancellation `(1/(2π))^{n+2}·(2π)^{n+1} = 1/(2π)`.
* Positivity is carried as a *pointwise-everywhere* invariant `∀ λ > 0, 0 < K n λ`
  (stronger than needed, but the clean invariant to induct on): the base case is `P_pos`;
  the step uses `lintegral_pos_iff_support` on the explicit λ-avoiding positive-measure
  subset `Ioi (λ+1) ⊆ Ioi 0 \ {λ}`, where the rung `P⁺(|μ-λ|) > 0` and `K n μ > 0` by IH.
-/

namespace GppAllLoopFiniteness

open MeasureTheory Real Set GppStefanBoltzmann
open scoped ENNReal

/-- `P` is bounded above by `1` on `[0,∞)`: `sinh(x) > x` for `x > 0` forces
    `P(λ) = πλ/sinh(πλ) < 1` for `λ > 0`, and `P(0) = 0 ≤ 1`. -/
theorem P_le_one {x : ℝ} (hx : 0 ≤ x) : P x ≤ 1 := by
  rcases hx.eq_or_lt with h0 | hpos
  · simp [P, ← h0]
  · have hπx : 0 < Real.pi * x := by positivity
    have hlt : Real.pi * x < Real.sinh (Real.pi * x) := Real.self_lt_sinh_iff.mpr hπx
    unfold P
    rw [div_le_one (by linarith)]
    linarith

/-- `P` is strictly positive on `(0,∞)`. -/
theorem P_pos {x : ℝ} (hx : 0 < x) : 0 < P x := by
  have hπx : 0 < Real.pi * x := by positivity
  have hlt : Real.pi * x < Real.sinh (Real.pi * x) := Real.self_lt_sinh_iff.mpr hπx
  unfold P
  exact div_pos hπx (by linarith)

/-- `P` is nonnegative on `[0,∞)`. -/
theorem P_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ P x := by
  rcases hx.eq_or_lt with h0 | hpos
  · simp [P, ← h0]
  · exact (P_pos hpos).le

/-- `P` is measurable (a quotient of continuous functions; the removable discontinuity at
    `0`, where our division convention gives `P 0 = 0` rather than the continuous limit
    `1`, does not affect measurability). -/
theorem P_measurable : Measurable P := by
  unfold P
  fun_prop

/-- `∫₀^∞ P(λ)dλ = π/4`, the `L=1` value of the Stefan–Boltzmann family
    (`m_one_eq` with the `λ^0 = 1` factor simplified away). -/
theorem integral_P_eq : ∫ lam in Ioi (0:ℝ), P lam = π / 4 := by
  have h := m_one_eq
  simp only [show (1:ℝ) - 1 = 0 by norm_num, Real.rpow_zero, one_mul] at h
  have hpi : (0:ℝ) < 2 * π := by positivity
  field_simp at h
  linarith

/-- The `ℝ≥0∞`-valued extension of `P`. -/
noncomputable def Pe (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (P x)

theorem Pe_le_one {x : ℝ} (hx : 0 ≤ x) : Pe x ≤ 1 := by
  unfold Pe
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (P_le_one hx)

theorem Pe_pos {x : ℝ} (hx : 0 < x) : 0 < Pe x :=
  ENNReal.ofReal_pos.mpr (P_pos hx)

theorem Pe_ne_top (x : ℝ) : Pe x ≠ ⊤ := ENNReal.ofReal_ne_top

theorem Pe_measurable : Measurable Pe := ENNReal.measurable_ofReal.comp P_measurable

/-- `P` is integrable on `(0,∞)`: since its Bochner integral there is `π/4 ≠ 0`, it cannot
    be the non-integrable junk value `0`. -/
theorem integrable_P : IntegrableOn P (Ioi (0:ℝ)) := by
  by_contra h
  have hz : ∫ lam in Ioi (0:ℝ), P lam = 0 := integral_undef h
  rw [integral_P_eq] at hz
  have : (0:ℝ) < π / 4 := by positivity
  linarith

theorem lintegral_Pe_eq : ∫⁻ lam in Ioi (0:ℝ), Pe lam = ENNReal.ofReal (π / 4) := by
  rw [← integral_P_eq]
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] P :=
    ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => P_nonneg hx.le)
  exact (ofReal_integral_eq_lintegral_ofReal integrable_P hnn).symm

/-! ## The chain kernel `K n` (`n = L - 1` loops beyond the first) and the loop measure `M n` -/

/-- The ladder chain kernel: `K 0 = P⁺`, and `K (n+1) λ = P⁺(λ) · ∫⁻ μ, K n μ · P⁺(|μ-λ|)`
    is Fubini's iterated-integral expansion of the `(n+2)`-loop measure, peeling off one
    loop variable (with its external weight and connecting rung) at a time. -/
noncomputable def K : ℕ → ℝ → ℝ≥0∞
  | 0, lam => Pe lam
  | (n+1), lam => Pe lam * ∫⁻ mu in Ioi (0:ℝ), K n mu * Pe (|mu - lam|)

theorem measurable_abs_sub_const (c : ℝ) : Measurable (fun x : ℝ => |x - c|) :=
  (continuous_abs.comp (continuous_id.sub continuous_const)).measurable

theorem K_measurable : ∀ n, Measurable (K n)
  | 0 => Pe_measurable
  | (n+1) => by
      have hjoint : Measurable (fun p : ℝ × ℝ => K n p.2 * Pe (|p.2 - p.1|)) :=
        ((K_measurable n).comp measurable_snd).mul
          (Pe_measurable.comp
            ((continuous_abs.comp (continuous_snd.sub continuous_fst)).measurable))
      have hinner : Measurable (fun lam => ∫⁻ mu in Ioi (0:ℝ), K n mu * Pe (|mu - lam|)) :=
        hjoint.lintegral_prod_right
      exact Pe_measurable.mul hinner

/-- **Strict positivity of the chain kernel** on `(0,∞)`, carried as the induction invariant
    (stronger than merely a.e.-positivity, and exactly what is needed to keep proving it one
    layer deeper). -/
theorem K_pos : ∀ n {lam : ℝ}, 0 < lam → 0 < K n lam
  | 0, lam, hlam => Pe_pos hlam
  | (n+1), lam, hlam => by
      have hPe : 0 < Pe lam := Pe_pos hlam
      have hjoint_meas : Measurable (fun mu => K n mu * Pe (|mu - lam|)) :=
        (K_measurable n).mul (Pe_measurable.comp (measurable_abs_sub_const lam))
      have hsub : Ioi (lam + 1) ⊆
          Function.support (fun mu => K n mu * Pe (|mu - lam|)) := by
        intro mu hmu
        simp only [mem_Ioi] at hmu
        have hmu0 : 0 < mu := by linarith
        have hKpos : 0 < K n mu := K_pos n hmu0
        have habs : 0 < |mu - lam| := by
          rw [abs_of_pos (by linarith : (0:ℝ) < mu - lam)]; linarith
        have hPepos : 0 < Pe (|mu - lam|) := Pe_pos habs
        exact (ENNReal.mul_pos hKpos.ne' hPepos.ne').ne'
      have hmeasIoi : (volume.restrict (Ioi (0:ℝ))) (Ioi (lam + 1)) = ⊤ := by
        rw [Measure.restrict_apply' measurableSet_Ioi,
          inter_eq_left.mpr (Ioi_subset_Ioi (by linarith)), Real.volume_Ioi]
      have hge := measure_mono (μ := volume.restrict (Ioi (0:ℝ))) hsub
      rw [hmeasIoi] at hge
      have hsupp_top : (volume.restrict (Ioi (0:ℝ)))
          (Function.support (fun mu => K n mu * Pe (|mu - lam|))) = ⊤ :=
        le_antisymm le_top hge
      have hlintpos : 0 < ∫⁻ mu in Ioi (0:ℝ), K n mu * Pe (|mu - lam|) := by
        rw [lintegral_pos_iff_support hjoint_meas, hsupp_top]
        exact ENNReal.zero_lt_top
      exact ENNReal.mul_pos hPe.ne' hlintpos.ne'

/-- **The finiteness bound on `∫⁻ K n`**: `∫⁻₀^∞ K n ≤ (π/4)^{n+1}`. -/
theorem lintegral_K_le : ∀ n, ∫⁻ lam in Ioi (0:ℝ), K n lam ≤ (ENNReal.ofReal (π / 4)) ^ (n + 1)
  | 0 => by rw [pow_one]; exact le_of_eq lintegral_Pe_eq
  | (n+1) => by
      set B : ℝ≥0∞ := (ENNReal.ofReal (π / 4)) ^ (n + 1) with hB
      have hIH : ∫⁻ mu in Ioi (0:ℝ), K n mu ≤ B := lintegral_K_le n
      have hinner : ∀ lam : ℝ, (∫⁻ mu in Ioi (0:ℝ), K n mu * Pe (|mu - lam|)) ≤ B := by
        intro lam
        calc ∫⁻ mu in Ioi (0:ℝ), K n mu * Pe (|mu - lam|)
            ≤ ∫⁻ mu in Ioi (0:ℝ), K n mu * 1 :=
              lintegral_mono (fun mu => mul_le_mul_right (Pe_le_one (abs_nonneg _)) (K n mu))
          _ = ∫⁻ mu in Ioi (0:ℝ), K n mu := by simp
          _ ≤ B := hIH
      have hstep : ∀ lam : ℝ, K (n+1) lam ≤ Pe lam * B := fun lam =>
        mul_le_mul_right (hinner lam) (Pe lam)
      calc ∫⁻ lam in Ioi (0:ℝ), K (n+1) lam
          ≤ ∫⁻ lam in Ioi (0:ℝ), Pe lam * B := lintegral_mono hstep
        _ = B * ∫⁻ lam in Ioi (0:ℝ), Pe lam := by
            rw [lintegral_mul_const B Pe_measurable, mul_comm]
        _ = B * ENNReal.ofReal (π / 4) := by rw [lintegral_Pe_eq]
        _ = (ENNReal.ofReal (π / 4)) ^ (n + 2) := by rw [hB, ← pow_succ]

/-- The `n`-th P-ladder chain measure (`n = L - 1`, so `n = 0` is `𝓜_1`). -/
noncomputable def M (n : ℕ) : ℝ≥0∞ :=
  (ENNReal.ofReal (2 * π))⁻¹ ^ (n + 1) * ∫⁻ lam in Ioi (0:ℝ), K n lam

theorem twoPiInv_mul_piOverFour :
    (ENNReal.ofReal (2 * π))⁻¹ * ENNReal.ofReal (π / 4) = ENNReal.ofReal (1 / 8) := by
  rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **All-loop finiteness** (`thm:finiteness`, `haar_qg_paper_v215.tex`): for every
    `n : ℕ` (i.e. every loop order `L = n+1 ≥ 1`), the P-ladder chain measure
    satisfies `0 < 𝓜_L ≤ (1/8)^L` — proved for every loop order at once, by induction on
    the ladder's own recursive construction, exactly matching the paper's proof (bound
    each rung by 1 and discard it, then factorize the remaining product integral). -/
theorem finiteness (n : ℕ) :
    0 < M n ∧ M n ≤ (ENNReal.ofReal (1 / 8)) ^ (n + 1) := by
  constructor
  · have hcoefpos : 0 < (ENNReal.ofReal (2 * π))⁻¹ := by
      rw [ENNReal.inv_pos]; exact ENNReal.ofReal_ne_top
    have hcoef : 0 < (ENNReal.ofReal (2 * π))⁻¹ ^ (n + 1) :=
      ENNReal.pow_pos hcoefpos (n + 1)
    have hlint : 0 < ∫⁻ lam in Ioi (0:ℝ), K n lam := by
      have hmeas : Measurable (K n) := K_measurable n
      have hsub : Ioi (0:ℝ) ⊆ Function.support (K n) :=
        fun lam hlam => (K_pos n hlam).ne'
      have hge := measure_mono (μ := volume.restrict (Ioi (0:ℝ))) hsub
      rw [Measure.restrict_apply' measurableSet_Ioi, inter_self, Real.volume_Ioi] at hge
      have hsupp_top : (volume.restrict (Ioi (0:ℝ))) (Function.support (K n)) = ⊤ :=
        le_antisymm le_top hge
      rw [lintegral_pos_iff_support hmeas, hsupp_top]
      exact ENNReal.zero_lt_top
    exact ENNReal.mul_pos_iff.mpr ⟨hcoef, hlint⟩
  · unfold M
    calc (ENNReal.ofReal (2 * π))⁻¹ ^ (n + 1) * ∫⁻ lam in Ioi (0:ℝ), K n lam
        ≤ (ENNReal.ofReal (2 * π))⁻¹ ^ (n + 1) * (ENNReal.ofReal (π / 4)) ^ (n + 1) :=
          mul_le_mul_right (lintegral_K_le n) _
      _ = ((ENNReal.ofReal (2 * π))⁻¹ * ENNReal.ofReal (π / 4)) ^ (n + 1) := by
          rw [mul_pow]
      _ = (ENNReal.ofReal (1 / 8)) ^ (n + 1) := by rw [twoPiInv_mul_piOverFour]

end GppAllLoopFiniteness
