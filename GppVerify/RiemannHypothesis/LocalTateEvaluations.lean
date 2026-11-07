import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Step 1: the local Tate zeta integrals at the real place and at a prime

Step 1 of the full-construction brief (blueprint drafted by Gemini, relayed by Daniel
Toupin, audited by Turbo: bridge `MuseResearch/turbo-note-2026-11-06-step1-blueprint-revised.md`).

* **Archimedean.** For `Re s > 0`,
  `∫_ℝ e^{-π x²} |x|^{s-1} dx = π^{-s/2} Γ(s/2)` (`= Gammaℝ s`), via an even split
  (`integral_comp_abs'`, a vector-valued version of Mathlib's `integral_comp_abs`), the
  substitution `x = y^{1/2}` (`integral_comp_rpow_Ioi_of_pos`) and Mathlib's
  `integral_cpow_mul_exp_neg_mul_Ioi`.
* **Finite.** For a prime `p` and `Re s > 0`, `Σ_k (p^{-s})^k = (1 - p^{-s})⁻¹`, with the
  nonvanishing of `1 - p^{-s}` (`Re s > 0`) and of `1 - p^{s-1}` (`Re s < 1`), and the
  local functional-equation identity of the blueprint.

The blueprint's `sorry`s are all discharged. Audit notes applied: the norm bound
`‖p^{-s}‖ < 1` uses `norm_natCast_cpow_of_pos` (complex exponent), not `norm_cpow_real`;
the final archimedean cancellation is a `ring`-type step. The blueprint's separate
`GammaIntegral` step is unnecessary: `integral_cpow_mul_exp_neg_mul_Ioi` lands on `Gamma`
directly. Integrability of the archimedean integrand is not needed for these identities
and is not proved here. These are the local factors only; the global Tate integral and
Poisson summation on the adeles (Steps 2+) are not here. No claim about RH.

Daniel Toupin / Golden Physics Project, with AI assistance from Gemini (blueprint), Turbo
(audit) and Claude Code (Lean).
-/

open MeasureTheory Set Complex

namespace LocalTate

/-- Vector-valued even split: `∫ f |x| = 2 • ∫_{x>0} f x` (Mathlib has the real-valued case). -/
theorem integral_comp_abs' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} : ∫ x, f |x| = (2 : ℝ) • ∫ x in Ioi (0 : ℝ), f x := by
  have eq : ∫ (x : ℝ) in Ioi 0, f |x| = ∫ (x : ℝ) in Ioi 0, f x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
    rw [abs_eq_self.mpr (le_of_lt (by exact hx))]
  by_cases hf : IntegrableOn (fun x => f |x|) (Ioi 0)
  · have int_Iic : IntegrableOn (fun x ↦ f |x|) (Iic 0) := by
      rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
      let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
      rw [m.integrableOn_map_iff]
      simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
      exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf
    calc
      _ = (∫ x in Iic 0, f |x|) + ∫ x in Ioi 0, f |x| := by
        rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi int_Iic hf,
          Iic_union_Ioi, Measure.restrict_univ]
      _ = (2 : ℝ) • ∫ x in Ioi 0, f x := by
        rw [two_smul, eq]
        congr! 1
        rw [← neg_zero, ← integral_comp_neg_Iic, neg_zero]
        refine setIntegral_congr_fun measurableSet_Iic (fun _ hx => ?_)
        rw [abs_eq_neg_self.mpr (by exact hx)]
  · have : ¬ Integrable (fun x => f |x|) := by
      contrapose hf
      exact hf.integrableOn
    rw [← eq, integral_undef hf, integral_undef this, smul_zero]

namespace Archimedean

/-- The archimedean test function: the standard Gaussian. -/
noncomputable def gaussian (x : ℝ) : ℝ := Real.exp (-Real.pi * x ^ 2)

/-- The local archimedean zeta integral `∫_ℝ e^{-π x²} |x|^{s-1} dx`. -/
noncomputable def localZeta (s : ℂ) : ℂ :=
  ∫ x : ℝ, (gaussian x : ℂ) * ((|x| : ℝ) : ℂ) ^ (s - 1)

/-- Even split. -/
theorem localZeta_even_split (s : ℂ) :
    localZeta s = 2 * ∫ x in Ioi (0 : ℝ), (gaussian x : ℂ) * (x : ℂ) ^ (s - 1) := by
  have hg : ∀ x : ℝ, gaussian x = gaussian |x| := by
    intro x; unfold gaussian; rw [sq_abs]
  unfold localZeta
  have hfun : (fun x : ℝ => (gaussian x : ℂ) * ((|x| : ℝ) : ℂ) ^ (s - 1)) =
      fun x => (fun y : ℝ => (gaussian y : ℂ) * (y : ℂ) ^ (s - 1)) |x| := by
    funext x
    show (gaussian x : ℂ) * _ = (gaussian |x| : ℂ) * _
    rw [← hg x]
  rw [hfun, integral_comp_abs' (f := fun y : ℝ => (gaussian y : ℂ) * (y : ℂ) ^ (s - 1)),
    real_smul]
  push_cast
  ring

/-- Positive-real powers as exponentials. -/
theorem ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (x : ℂ) ^ w = Complex.exp ((Real.log x : ℂ) * w) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ofReal_log hx.le]

/-- Half-line Gaussian moment: `∫_{x>0} e^{-π x²} x^{s-1} dx = ½ π^{-s/2} Γ(s/2)`. -/
theorem localZeta_half_line {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (0 : ℝ), (gaussian x : ℂ) * (x : ℂ) ^ (s - 1)) =
      (1 / 2 : ℂ) * (Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) := by
  set G : ℝ → ℂ := fun y => (1 / 2 : ℂ) * ((y : ℂ) ^ (s / 2 - 1) *
    Complex.exp (-((Real.pi : ℂ) * y)))
  have hsub := integral_comp_rpow_Ioi_of_pos (g := G) (p := (2 : ℝ)) (by norm_num)
  have hlhs : ∫ x in Ioi (0 : ℝ), ((2 : ℝ) * x ^ ((2 : ℝ) - 1)) • G (x ^ (2 : ℝ)) =
      ∫ x in Ioi (0 : ℝ), (gaussian x : ℂ) * (x : ℂ) ^ (s - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx : (0 : ℝ) < x := hx
    have hx2 : (0 : ℝ) < x ^ (2 : ℝ) := Real.rpow_pos_of_pos hx _
    simp only [G, real_smul]
    rw [ofReal_cpow_eq_exp hx2, ofReal_cpow_eq_exp hx, Real.log_rpow hx]
    unfold gaussian
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two]
    have hC : Complex.exp ((Real.log x : ℂ) * (s - 1)) =
        (x : ℂ) * Complex.exp (((2 * Real.log x : ℝ) : ℂ) * (s / 2 - 1)) := by
      have hxc : (x : ℂ) = Complex.exp (Real.log x : ℂ) := by
        rw [← ofReal_exp, Real.exp_log hx]
      rw [hxc, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hC, ofReal_exp]
    push_cast
    ring_nf
  have hre : 0 < (s / 2).re := by
    have : (s / 2).re = s.re / 2 := by simp
    rw [this]; linarith
  have hpi : (1 / (Real.pi : ℂ)) ^ (s / 2) = (Real.pi : ℂ) ^ (-s / 2) := by
    rw [show (1 / (Real.pi : ℂ)) = ((1 / Real.pi : ℝ) : ℂ) by push_cast; ring,
      ofReal_cpow_eq_exp (by positivity), ofReal_cpow_eq_exp Real.pi_pos, one_div,
      Real.log_inv]
    congr 1
    push_cast
    ring
  rw [← hlhs, hsub]
  simp only [G]
  rw [integral_const_mul, integral_cpow_mul_exp_neg_mul_Ioi hre Real.pi_pos, hpi]
  ring

/-- **Archimedean evaluation:** `∫_ℝ e^{-π x²} |x|^{s-1} dx = π^{-s/2} Γ(s/2)` for `Re s > 0`. -/
theorem archimedean_evaluation {s : ℂ} (hs : 0 < s.re) :
    localZeta s = (Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) := by
  rw [localZeta_even_split, localZeta_half_line hs]
  ring

/-- The same, in Mathlib's notation: the local factor is `Gammaℝ s`. -/
theorem archimedean_evaluation_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    localZeta s = Gammaℝ s := by
  rw [archimedean_evaluation hs, Gammaℝ_def]

end Archimedean

namespace Finite

/-- The unramified local zeta integral at `p`, as the geometric series. -/
noncomputable def localZetaPrime (p : ℕ) (s : ℂ) : ℂ := ∑' k : ℕ, ((p : ℂ) ^ (-s)) ^ k

theorem norm_prime_cpow (p : ℕ) [hp : Fact p.Prime] (w : ℂ) :
    ‖(p : ℂ) ^ w‖ = (p : ℝ) ^ w.re :=
  norm_natCast_cpow_of_pos hp.out.pos w

/-- `‖p^{-s}‖ < 1` for `Re s > 0`. -/
theorem padic_norm_lt_one (p : ℕ) [hp : Fact p.Prime] {s : ℂ} (hs : 0 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_prime_cpow, neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.out.one_lt) (by linarith)

theorem padic_denom_ne_zero (p : ℕ) [Fact p.Prime] {s : ℂ} (hs : 0 < s.re) :
    1 - (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have := padic_norm_lt_one p hs
  rw [h1, norm_one] at this
  exact lt_irrefl _ this

theorem padic_shifted_denom_ne_zero (p : ℕ) [hp : Fact p.Prime] {s : ℂ} (hs : s.re < 1) :
    1 - (p : ℂ) ^ (s - 1) ≠ 0 := by
  intro h
  have h1 : (p : ℂ) ^ (s - 1) = 1 := (sub_eq_zero.mp h).symm
  have hn : ‖(p : ℂ) ^ (s - 1)‖ < 1 := by
    rw [norm_prime_cpow, sub_re, one_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.out.one_lt) (by linarith)
  rw [h1, norm_one] at hn
  exact lt_irrefl _ hn

/-- **Finite evaluation.** -/
theorem finite_evaluation (p : ℕ) [Fact p.Prime] {s : ℂ} (hs : 0 < s.re) :
    localZetaPrime p s = (1 - (p : ℂ) ^ (-s))⁻¹ :=
  tsum_geometric_of_norm_lt_one (padic_norm_lt_one p hs)

/-- **Local functional-equation identity at `p`** (blueprint form). -/
theorem local_functional_equation_p (p : ℕ) [Fact p.Prime] {s : ℂ}
    (hs_pos : 0 < s.re) (hs_lt_one : s.re < 1) :
    localZetaPrime p s =
      localZetaPrime p (1 - s) * ((1 - (p : ℂ) ^ (s - 1)) / (1 - (p : ℂ) ^ (-s))) := by
  have h1s : 0 < (1 - s).re := by simp; linarith
  rw [finite_evaluation p hs_pos, finite_evaluation p h1s, neg_sub]
  have a := padic_denom_ne_zero p hs_pos
  have b := padic_shifted_denom_ne_zero p hs_lt_one
  field_simp

end Finite

end LocalTate

#print axioms LocalTate.Archimedean.archimedean_evaluation_Gammaℝ
#print axioms LocalTate.Finite.local_functional_equation_p
