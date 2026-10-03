import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Critical zeta Gibbs ensemble: the escaping energy is an exponential boundary mode

Source: Codex, GPPDiscovery2 `research/2026-09-27_critical_zeta_gibbs_exponential_escape.md`,
§§1–2.

For `β = 1 + ε > 1` the zeta Gibbs ensemble puts weight `n^{-β}/ζ(β)` on the positive integer `n`;
the arithmetic Hamiltonian is `H = log N`, and the scaled escaping energy is `Y_ε = ε log N`.

* `laplace_term`, `laplace_tsum`: the exact Laplace transform
  `E[e^{-s Y_ε}] = ζ(1 + ε(1+s)) / ζ(1 + ε)`, i.e. the weighted sum
  `Σ_n n^{-(1+ε)} e^{-sε log n} / ζ(1+ε)`, for `ε > 0` and `Re s ≥ 0`;
* `tendsto_laplace`: as `ε ↓ 0` this converges to `1/(1+s)` for every `s` with `1 + s ≠ 0`
  (in particular for `Re s ≥ 0`). That is the Laplace transform of the `Exp(1)` law, so
  `ε log N ⇒ Exp(1)` in distribution. The only analytic input is Mathlib's pole statement
  `riemannZeta_residue_one`: `(s−1) ζ(s) → 1` at `s = 1`.

## Checks and scope

Both claims check; the limit holds locally uniformly in the note, here it is proved pointwise in
`s`, which is the form used above. **Not formalized:** the passage from convergence of Laplace
transforms to convergence in distribution (a probability-theory step); the joint limit with
finitely many prime occupations (§3); the fixed-frequency decay
`ζ(1+ε+it)/ζ(1+ε) → 0` and its consequences (§4). No RH claim and no zero data used.
-/

open Complex Filter Topology

namespace GppZetaGibbs

/-- The `n`-th Gibbs term factors as a Boltzmann weight times a Laplace factor. -/
theorem laplace_term (ε : ℝ) (s : ℂ) (n : ℕ) :
    1 / ((n + 1 : ℂ)) ^ (1 + (ε : ℂ) * (1 + s)) =
      1 / ((n + 1 : ℂ)) ^ (1 + (ε : ℂ)) * Complex.exp (-(s * ε) * Real.log (n + 1)) := by
  have hne : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast hne
  have h1 : (1 + (ε : ℂ) * (1 + s)) = (1 + (ε : ℂ)) + (s * ε) := by ring
  rw [h1, Complex.cpow_add _ _ hn, one_div, one_div, mul_inv]
  congr 1
  rw [Complex.cpow_def_of_ne_zero hn, ← Complex.exp_neg]
  congr 1
  have : Complex.log (n + 1 : ℂ) = (Real.log (n + 1) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
      ← Complex.ofReal_log (by positivity)]
  rw [this]
  ring

/-- **Exact Laplace transform of the scaled energy**, as a weighted sum. -/
theorem laplace_tsum (ε : ℝ) (hε : 0 < ε) (s : ℂ) (hs : 0 ≤ s.re) :
    riemannZeta (1 + (ε : ℂ) * (1 + s)) =
      ∑' n : ℕ, 1 / ((n + 1 : ℂ)) ^ (1 + (ε : ℂ)) * Complex.exp (-(s * ε) * Real.log (n + 1)) := by
  have hre : 1 < (1 + (ε : ℂ) * (1 + s)).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre]
  exact tsum_congr fun n => laplace_term ε s n

/-- The path `ε ↦ 1 + ε c` enters `𝓝[≠] 1` as `ε ↓ 0` when `c ≠ 0`. -/
theorem tendsto_path (c : ℂ) (hc : c ≠ 0) :
    Tendsto (fun ε : ℝ => 1 + (ε : ℂ) * c) (𝓝[>] 0) (𝓝[≠] 1) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have : Continuous fun ε : ℝ => 1 + (ε : ℂ) * c :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have h := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using h
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have : (ε : ℂ) ≠ 0 := by exact_mod_cast (Set.mem_Ioi.mp hε).ne'
    simp [this, hc]

/-- `ε · c · ζ(1 + ε c) → 1` as `ε ↓ 0` (the residue of `ζ` at `1`). -/
theorem tendsto_residue_path (c : ℂ) (hc : c ≠ 0) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * c * riemannZeta (1 + (ε : ℂ) * c)) (𝓝[>] 0) (𝓝 1) := by
  have h := riemannZeta_residue_one.comp (tendsto_path c hc)
  refine h.congr fun ε => ?_
  simp [Function.comp]

/-- **`ε log N ⇒ Exp(1)`, on the level of Laplace transforms.** -/
theorem tendsto_laplace (s : ℂ) (hs : 1 + s ≠ 0) :
    Tendsto (fun ε : ℝ => riemannZeta (1 + (ε : ℂ) * (1 + s)) / riemannZeta (1 + (ε : ℂ)))
      (𝓝[>] 0) (𝓝 (1 / (1 + s))) := by
  have h1 : (1 : ℂ) ≠ 0 := one_ne_zero
  have hnum := tendsto_residue_path (1 + s) hs
  have hden := tendsto_residue_path 1 h1
  have hlim : Tendsto (fun ε : ℝ => ((ε : ℂ) * (1 + s) * riemannZeta (1 + (ε : ℂ) * (1 + s))) /
      ((1 + s) * ((ε : ℂ) * 1 * riemannZeta (1 + (ε : ℂ) * 1)))) (𝓝[>] 0)
      (𝓝 (1 / ((1 + s) * 1))) :=
    hnum.div (tendsto_const_nhds.mul hden) (mul_ne_zero hs one_ne_zero)
  rw [mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast (Set.mem_Ioi.mp hε).ne'
  simp only [mul_one]
  by_cases hz : riemannZeta (1 + (ε : ℂ)) = 0
  · simp [hz]
  · field_simp

end GppZetaGibbs
