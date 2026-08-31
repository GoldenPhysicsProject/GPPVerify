import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The zeta bridge: `∫₀^∞ t^{s−1}/sinh(t) dt = 2·(1−2^{−s})·Γ(s)·ζ(s)`

Thread S of `docs/FORMALIZATION_PLAN.md`, from `kinematic_block_v11.tex` (Proposition
"zetabridge") and `Toupin, "Modular Thermality of the Celestial Spectral Weight" (the first moment of P
`M₁ = 1/8`): the Riemann zeta function is the Mellin transform of the `1/sinh` thermal
kernel, through the odd Dirichlet factor `(1−2^{−s})`. The papers verify the bridge to
29 digits numerically; here it is a kernel-checked theorem for every real `s > 1`, with
`ζ(s)` in its defining Dirichlet-series form `∑ 1/n^s`.

The proof is `PlanckIntegral.lean`'s argument one level of generality up:

* `sinh_summand_eq` — the residue expansion
  `t^{s−1}/sinh t = Σ_{k≥0} 2·t^{s−1}·e^{−(2k+1)t}` pointwise for `t > 0`;
* `integral_term` — each term integrates to `(2k+1)^{−s}·Γ(s)`
  (`integral_rpow_mul_exp_neg_mul_rpow`, this time with a genuinely real exponent);
* `tsum_odd_inv_rpow` — the odd Dirichlet sum `Σ 1/(2k+1)^s = (1−2^{−s})·Σ 1/n^s`,
  by the even/odd splitting `tsum_even_add_odd` and `(2k)^s = 2^s·k^s`;
* `sinh_mellin_zeta` — the bridge, the sum–integral interchange justified by
  summability of the term norms (`integral_tsum_of_summable_integral_norm`).

Exact corollaries: `∫₀^∞ t/sinh t = π²/4` — the `haar_qg` paper's `M₁ = 1/8` in π-free
form (`plancherel_first_moment`) — and `∫₀^∞ t³/sinh t = π⁴/8`. The elementary
substitution `λ = t/π` carrying `π²/4` to the paper's normalization
`(1/2π)·∫ πλ/sinh(πλ) dλ = 1/8` is not formalized; the analytic content is the
integral itself.
-/

namespace GppZetaBridge

open MeasureTheory Real Set

/-- The pointwise residue expansion: for `t > 0`,
    `t^{s−1}/sinh t = Σ_{k≥0} 2·(t^{s−1}·e^{−(2k+1)t})`. -/
theorem sinh_summand_eq {t : ℝ} (ht : 0 < t) (s : ℝ) :
    t ^ (s-1) / Real.sinh t =
      ∑' k : ℕ, 2 * (t ^ (s-1) * Real.exp (-(2*(k:ℝ)+1)*t)) := by
  have hlt : Real.exp (-(2*t)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h0 : (0:ℝ) ≤ Real.exp (-(2*t)) := (Real.exp_pos _).le
  have hterm : ∀ k : ℕ, 2 * (t ^ (s-1) * Real.exp (-(2*(k:ℝ)+1)*t)) =
      (2 * (t ^ (s-1) * Real.exp (-t))) * (Real.exp (-(2*t))) ^ k := by
    intro k
    rw [show -(2*(k:ℝ)+1)*t = (k:ℝ) * -(2*t) + -t by ring, Real.exp_add,
      Real.exp_nat_mul]
    ring
  rw [tsum_congr hterm, tsum_mul_left, tsum_geometric_of_lt_one h0 hlt]
  have hgt : (1:ℝ) < Real.exp t := Real.one_lt_exp_iff.mpr ht
  have hexpne : Real.exp t ≠ 0 := Real.exp_ne_zero t
  have hXX : Real.exp t * Real.exp t - 1 ≠ 0 := by nlinarith
  have hXX' : 1 - Real.exp t * Real.exp t ≠ 0 := by nlinarith
  have hXsq : Real.exp t ^ 2 - 1 ≠ 0 := by nlinarith
  have hXsq' : 1 - Real.exp t ^ 2 ≠ 0 := by nlinarith
  rw [Real.sinh_eq, show -(2*t) = -t + -t by ring, Real.exp_add, Real.exp_neg]
  field_simp
  ring

/-- The term integral: `∫₀^∞ t^{s−1}·e^{−(2k+1)t} dt = (2k+1)^{−s}·Γ(s)`. -/
theorem integral_term {s : ℝ} (hs : 0 < s) (k : ℕ) :
    ∫ t in Ioi (0:ℝ), t ^ (s-1) * Real.exp (-(2*(k:ℝ)+1)*t) =
      1 / (2*(k:ℝ)+1) ^ s * Real.Gamma s := by
  have hb : (0:ℝ) < 2*(k:ℝ)+1 := by positivity
  have key := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := s - 1)
    (b := 2*(k:ℝ)+1) one_pos (by linarith) hb
  rw [show (-(s - 1 + 1) / 1 : ℝ) = -s by ring,
      show ((s - 1 + 1) / 1 : ℝ) = s by ring, Real.rpow_neg hb.le] at key
  simp_rw [Real.rpow_one] at key
  rw [key]
  ring

set_option maxHeartbeats 400000 in
/-- Each term is integrable on `(0,∞)`, dominated by twice the Euler Gamma integrand. -/
theorem integrable_term {s : ℝ} (hs : 1 < s) (k : ℕ) :
    IntegrableOn (fun t : ℝ => 2 * (t ^ (s-1) * Real.exp (-(2*(k:ℝ)+1)*t)))
      (Ioi (0:ℝ)) := by
  have hg : IntegrableOn (fun t : ℝ => 2 * (Real.exp (-t) * t ^ (s-1))) (Ioi (0:ℝ)) :=
    (Real.GammaIntegral_convergent (by linarith : (0:ℝ) < s)).const_mul 2
  refine hg.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul continuous_const
    apply Continuous.mul
    · exact continuous_id.rpow_const fun x => Or.inr (by linarith)
    · exact Real.continuous_exp.comp (continuous_const.mul continuous_id)
  · rw [ae_restrict_iff' measurableSet_Ioi]
    apply Filter.Eventually.of_forall
    intro t htt
    have ht' : (0:ℝ) < t := htt
    have hnn : (0:ℝ) ≤ t ^ (s-1) := Real.rpow_nonneg ht'.le _
    have hb : Real.exp (-(2*(k:ℝ)+1)*t) ≤ Real.exp (-t) := by
      apply Real.exp_le_exp.mpr
      have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      nlinarith
    have hnonneg : (0:ℝ) ≤ 2 * (t ^ (s-1) * Real.exp (-(2*(k:ℝ)+1)*t)) := by positivity
    have htwo : (0:ℝ) ≤ 2 := by norm_num
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    calc 2 * (t ^ (s-1) * Real.exp (-(2*(k:ℝ)+1)*t))
        ≤ 2 * (t ^ (s-1) * Real.exp (-t)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hnn) htwo
      _ = 2 * (Real.exp (-t) * t ^ (s-1)) := by ring

set_option maxHeartbeats 1600000 in
/-- **The odd Dirichlet factor**: `Σ_{k≥0} 1/(2k+1)^s = (1−2^{−s})·Σ_{n} 1/n^s`
    for `s > 1` (the `n = 0` term of the right sum vanishes since `0^s = 0`). -/
theorem tsum_odd_inv_rpow {s : ℝ} (hs : 1 < s) :
    ∑' k : ℕ, 1 / (2*(k:ℝ)+1) ^ s =
      (1 - 2^(-s)) * ∑' n : ℕ, 1 / (n:ℝ) ^ s := by
  have hζ : Summable (fun n : ℕ => 1 / (n:ℝ) ^ s) := summable_one_div_nat_rpow.mpr hs
  -- even terms: 1/(2k)^s = 2^{−s} · (1/k^s); stated in redex form so that
  -- `tsum_even_add_odd`'s implicit `f` unifies first-order.
  have heven : ∀ k : ℕ, (fun n : ℕ => 1 / (n:ℝ) ^ s) (2*k) =
      2^(-s) * (1 / (k:ℝ) ^ s) := by
    intro k
    show 1 / ((2*k : ℕ):ℝ) ^ s = 2^(-s) * (1 / (k:ℝ) ^ s)
    rw [show ((2*k : ℕ):ℝ) = 2 * (k:ℝ) by push_cast; ring,
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Nat.cast_nonneg k),
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    ring
  have he : Summable (fun k : ℕ => (fun n : ℕ => 1 / (n:ℝ) ^ s) (2*k)) :=
    hζ.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))
  -- odd terms: subseries of a summable series along the injection k ↦ 2k+1
  have hocast : ∀ k : ℕ, (fun n : ℕ => 1 / (n:ℝ) ^ s) (2*k+1) =
      1 / (2*(k:ℝ)+1) ^ s := by
    intro k
    show 1 / ((2*k+1 : ℕ):ℝ) ^ s = 1 / (2*(k:ℝ)+1) ^ s
    rw [show ((2*k+1 : ℕ):ℝ) = 2*(k:ℝ)+1 by push_cast; ring]
  have hinj : Function.Injective (fun k : ℕ => 2*k+1) :=
    (add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' ℕ))
  have ho : Summable (fun k : ℕ => (fun n : ℕ => 1 / (n:ℝ) ^ s) (2*k+1)) :=
    hζ.comp_injective hinj
  -- the even/odd split
  have hsplit := tsum_even_add_odd (f := fun n : ℕ => 1 / (n:ℝ) ^ s) he ho
  have e1 : ∑' k : ℕ, (fun n : ℕ => 1 / (n:ℝ) ^ s) (2*k) =
      2^(-s) * ∑' n : ℕ, 1 / (n:ℝ) ^ s := by
    rw [tsum_congr heven, tsum_mul_left]
  have e2 : ∑' k : ℕ, (fun n : ℕ => 1 / (n:ℝ) ^ s) (2*k+1) =
      ∑' k : ℕ, 1 / (2*(k:ℝ)+1) ^ s := tsum_congr hocast
  rw [e1, e2] at hsplit
  -- hsplit : 2^(-s) * S + (odd sum) = S; avoid linarith here — its preprocessing
  -- compares distinct tsum atoms up to defeq, unfolding tsum's classical choice.
  have hb := eq_sub_of_add_eq' hsplit
  rw [hb]
  ring

/-- **The zeta bridge** (`kinematic_block_v11` Prop. zetabridge, real form): for `s > 1`,
    `∫₀^∞ t^{s−1}/sinh t dt = 2·(1−2^{−s})·Γ(s)·Σ 1/n^s` — the Riemann zeta function is
    the Mellin transform of the `1/sinh` thermal kernel, exactly. -/
theorem sinh_mellin_zeta {s : ℝ} (hs : 1 < s) :
    ∫ t in Ioi (0:ℝ), t ^ (s-1) / Real.sinh t =
      2 * (1 - 2^(-s)) * Real.Gamma s * ∑' n : ℕ, 1 / (n:ℝ) ^ s := by
  have hterm_int : ∀ k : ℕ,
      ∫ t in Ioi (0:ℝ), 2 * (t ^ (s-1) * Real.exp (-(2*(k:ℝ)+1)*t)) =
        2 * (1 / (2*(k:ℝ)+1) ^ s) * Real.Gamma s := by
    intro k
    rw [integral_const_mul, integral_term (by linarith : (0:ℝ) < s) k]
    ring
  have hnorm : ∀ k : ℕ,
      (∫ t in Ioi (0:ℝ), ‖2 * (t ^ (s-1) * Real.exp (-(2*(k:ℝ)+1)*t))‖) =
        2 * (1 / (2*(k:ℝ)+1) ^ s) * Real.Gamma s := by
    intro k
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t : ℝ =>
        2 * (t ^ (s-1) * Real.exp (-(2*(k:ℝ)+1)*t))) (fun t htt => by
      have ht' : (0:ℝ) < t := htt
      have hnn : (0:ℝ) ≤ t ^ (s-1) := Real.rpow_nonneg ht'.le _
      have hnonneg : (0:ℝ) ≤ 2 * (t ^ (s-1) * Real.exp (-(2*(k:ℝ)+1)*t)) := by
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg])]
    exact hterm_int k
  -- summability of the term norms
  have hcomp : Summable (fun k : ℕ => 1 / (2*(k:ℝ)+1) ^ s) := by
    have hζ : Summable (fun n : ℕ => 1 / (n:ℝ) ^ s) := summable_one_div_nat_rpow.mpr hs
    have hinj : Function.Injective (fun k : ℕ => 2*k+1) :=
      (add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' ℕ))
    have ho : Summable (fun k : ℕ => (fun n : ℕ => 1 / (n:ℝ) ^ s) (2*k+1)) :=
      hζ.comp_injective hinj
    apply Summable.congr ho
    intro k
    show 1 / ((2*k+1 : ℕ):ℝ) ^ s = 1 / (2*(k:ℝ)+1) ^ s
    rw [show ((2*k+1 : ℕ):ℝ) = 2*(k:ℝ)+1 by push_cast; ring]
  have hsum : Summable (fun k : ℕ => 2 * (1 / (2*(k:ℝ)+1) ^ s) * Real.Gamma s) :=
    (hcomp.mul_left 2).mul_right _
  have hsum_norm : Summable (fun k : ℕ =>
      ∫ t in Ioi (0:ℝ), ‖2 * (t ^ (s-1) * Real.exp (-(2*(k:ℝ)+1)*t))‖) := by
    apply Summable.congr hsum
    intro k
    exact (hnorm k).symm
  have hswap := integral_tsum_of_summable_integral_norm
    (F := fun k : ℕ => fun t : ℝ => 2 * (t ^ (s-1) * Real.exp (-(2*(k:ℝ)+1)*t)))
    (μ := (volume : Measure ℝ).restrict (Ioi 0))
    (fun k => integrable_term hs k) hsum_norm
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun t htt => sinh_summand_eq (show (0:ℝ) < t from htt) s), ← hswap,
    tsum_congr (fun k => hterm_int k), tsum_mul_right, tsum_mul_left,
    tsum_odd_inv_rpow hs]
  ring

/-! ## Exact corollaries: the `M₁` family -/

/-- `∫₀^∞ t/sinh t dt = π²/4` — the odd Basel value, and the analytic content of the
    `haar_qg` paper's first moment of P. -/
theorem integral_id_div_sinh :
    ∫ t in Ioi (0:ℝ), t / Real.sinh t = π^2 / 4 := by
  have h := sinh_mellin_zeta (by norm_num : (1:ℝ) < 2)
  simp_rw [show ((2:ℝ)-1) = 1 by norm_num, Real.rpow_one] at h
  rw [h]
  have hg : Real.Gamma 2 = 1 := by
    rw [show (2:ℝ) = ((1:ℕ):ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  have h2 : (2:ℝ)^(-(2:ℝ)) = 1/4 := by
    rw [show (-(2:ℝ)) = -((2:ℕ):ℝ) by norm_num,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
    norm_num
  have hζ2 : ∑' n : ℕ, 1 / (n:ℝ) ^ (2:ℝ) = π^2/6 := by
    have hpow : ∀ n : ℕ, (1:ℝ) / (n:ℝ) ^ (2:ℝ) = 1 / (n:ℝ) ^ (2:ℕ) := fun n => by
      rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [tsum_congr hpow]
    exact hasSum_zeta_two.tsum_eq
  rw [hg, h2, hζ2]
  ring

/-- `∫₀^∞ t³/sinh t dt = π⁴/8` — the quartic member of the family. -/
theorem integral_cube_div_sinh :
    ∫ t in Ioi (0:ℝ), t ^ (3:ℕ) / Real.sinh t = π^4 / 8 := by
  have h := sinh_mellin_zeta (by norm_num : (1:ℝ) < 4)
  simp_rw [show ((4:ℝ)-1) = 3 by norm_num] at h
  have hpow3 : ∀ t : ℝ, t ^ (3:ℝ) = t ^ (3:ℕ) := fun t => by
    rw [show ((3:ℝ)) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  simp_rw [hpow3] at h
  rw [h]
  have hg : Real.Gamma 4 = 6 := by
    rw [show (4:ℝ) = ((3:ℕ):ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  have h2 : (2:ℝ)^(-(4:ℝ)) = 1/16 := by
    rw [show (-(4:ℝ)) = -((4:ℕ):ℝ) by norm_num,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
    norm_num
  have hζ4 : ∑' n : ℕ, 1 / (n:ℝ) ^ (4:ℝ) = π^4/90 := by
    have hpow : ∀ n : ℕ, (1:ℝ) / (n:ℝ) ^ (4:ℝ) = 1 / (n:ℝ) ^ (4:ℕ) := fun n => by
      rw [show ((4:ℝ)) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [tsum_congr hpow]
    exact hasSum_zeta_four.tsum_eq
  rw [hg, h2, hζ4]
  ring

/-- **The first moment of P `M₁ = 1/8`** (`haar_qg_paper_v2151`, eq. (M1)),
    in π-free normalization: `(1/2π²)·∫₀^∞ t/sinh t dt = 1/8`. The substitution
    `λ = t/π` to the paper's `(1/2π)·∫ πλ/sinh(πλ) dλ` is elementary and not
    formalized. -/
theorem plancherel_first_moment :
    1/(2*π^2) * ∫ t in Ioi (0:ℝ), t / Real.sinh t = 1/8 := by
  rw [integral_id_div_sinh, div_mul_div_comm, one_mul,
    show 2*π^2*4 = π^2 * 8 by ring, div_mul_eq_div_div,
    div_self (pow_ne_zero 2 Real.pi_ne_zero)]

end GppZetaBridge
