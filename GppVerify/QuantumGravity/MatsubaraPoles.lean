import GppVerify.QuantumGravity.StefanBoltzmannFamily
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Algebra.Field.Power

/-!
# Matsubara poles of the Plancherel weight

From `Modular_Thermality_of_the_Celestial_Spectral_Weight.tex`, Proposition "Equivalent
descriptions", item (iv): the meromorphic continuation of `P(λ) = πλ/sinh(πλ)` to complex
`λ` has simple poles exactly at `λ = in`, `n ∈ ℤ \ {0}`, with `Res_{λ=in} P(λ) = i(-1)ⁿn`.

## What this file proves

The complex-analytic continuation `Pc(z) := πz/sinh(πz)` of `GppStefanBoltzmann.P`, and the
residue statement in the same operational form the paper's own companion script
(`verify_modular_thermality.py`) certifies it numerically: `Res` is not invoked as a named
Mathlib operator (Mathlib has no general residue-calculus API at the pinned commit) but
computed directly as the defining limit of a simple pole,
```
Tendsto (fun ε => ε * Pc (I * n + ε)) (𝓝[≠] 0) (𝓝 (I * n * (-1) ^ n))
```
— exactly `lim_{ε→0} ε · P(in + ε)`, the same quantity the paper's script approximates by
evaluating at `ε = 10⁻²⁰`.

**Proof idea**: `sinh(π(in+ε)) = sinh(πin)cosh(πε) + cosh(πin)sinh(πε)` (`Complex.sinh_add`);
`sinh(πin) = sin(πn)·i = 0` (`Complex.sinh_mul_I` + `Complex.sin_int_mul_pi`); `cosh(πin) =
cos(πn) = (-1)ⁿ` (`Complex.cosh_mul_I`, then a real/complex cast of the standard real
identity). So `sinh(π(in+ε)) = (-1)ⁿ·sinh(πε)`, and `ε·Pc(in+ε) = (in+ε)·Pc(ε)/(-1)ⁿ` where
`Pc(ε) = πε/sinh(πε) → 1` as `ε → 0` — the elementary complex-analytic fact that `sinh` has
derivative `1` at `0` after the `π`-rescaling, proved here from `Complex.hasDerivAt_sinh` via
the chain rule rather than assumed. No axiom, no sorry.

## What this file does NOT do

Does not build any general residue-calculus machinery (contour integration, meromorphic
continuation as its own structure) — only this one specific limit, in the exact operational
form the paper's own numerics use.
-/

namespace GppMatsubara

open Complex Filter Topology Real

/-- The complex-analytic continuation of the Plancherel weight. -/
noncomputable def Pc (z : ℂ) : ℂ := (π : ℂ) * z / Complex.sinh ((π : ℂ) * z)

/-- `cos(nπ) = (-1)ⁿ` in `ℂ`, for `n : ℤ` — cast down from the standard real identity. -/
theorem cos_int_mul_pi (n : ℤ) : Complex.cos ((n : ℂ) * (π : ℂ)) = (-1) ^ n := by
  have hR : Real.cos ((n : ℝ) * Real.pi) = (-1) ^ n := by
    simpa using Real.cos_int_mul_pi_sub (0 : ℝ) n
  have hcast : ((n : ℂ) * (π : ℂ)) = (((n : ℝ) * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, ← Complex.ofReal_cos, hR]
  push_cast
  ring

/-- `sinh(π·in) = 0` for every integer `n`. -/
theorem sinh_pi_mul_I_mul_int (n : ℤ) :
    Complex.sinh ((π : ℂ) * (Complex.I * (n : ℂ))) = 0 := by
  have h : (π : ℂ) * (Complex.I * (n : ℂ)) = ((n : ℂ) * (π : ℂ)) * Complex.I := by ring
  rw [h, Complex.sinh_mul_I, Complex.sin_int_mul_pi]
  ring

/-- `cosh(π·in) = (-1)ⁿ` for every integer `n`. -/
theorem cosh_pi_mul_I_mul_int (n : ℤ) :
    Complex.cosh ((π : ℂ) * (Complex.I * (n : ℂ))) = (-1) ^ n := by
  have h : (π : ℂ) * (Complex.I * (n : ℂ)) = ((n : ℂ) * (π : ℂ)) * Complex.I := by ring
  rw [h, Complex.cosh_mul_I, cos_int_mul_pi]

/-- **The removable singularity at the origin**: `πε/sinh(πε) → 1` as `ε → 0` through
`ε ≠ 0` — the elementary fact that `Pc` extends continuously across `ε = 0` with value `1`
(matching `GppStefanBoltzmann.P`'s own real-variable behaviour, `P(λ) → 1` as `λ → 0`). -/
theorem tendsto_Pc_nhdsWithin_zero :
    Tendsto Pc (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
  have hderiv0 : HasDerivAt (fun ε : ℂ => Complex.sinh ((π : ℂ) * ε))
      (Complex.cosh ((π : ℂ) * 0) * ((π : ℂ) * 1)) 0 :=
    (Complex.hasDerivAt_sinh ((π : ℂ) * 0)).comp 0
      ((hasDerivAt_id' (x := (0 : ℂ))).const_mul (π : ℂ))
  have hderiv : HasDerivAt (fun ε : ℂ => Complex.sinh ((π : ℂ) * ε)) (π : ℂ) 0 := by
    simpa using hderiv0
  have hslope := hasDerivAt_iff_tendsto_slope.mp hderiv
  have hslope_eq : ∀ ε : ℂ, ε ≠ 0 →
      slope (fun ε : ℂ => Complex.sinh ((π : ℂ) * ε)) 0 ε
        = Complex.sinh ((π : ℂ) * ε) / ε := by
    intro ε hε
    simp [slope, mul_zero, Complex.sinh_zero, sub_zero, smul_eq_mul, div_eq_inv_mul]
  have hslope' : Tendsto (fun ε : ℂ => Complex.sinh ((π : ℂ) * ε) / ε) (𝓝[≠] (0 : ℂ))
      (𝓝 (π : ℂ)) := by
    refine hslope.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hslope_eq ε hε
  have hinv : Tendsto (fun ε : ℂ => ε / Complex.sinh ((π : ℂ) * ε)) (𝓝[≠] (0 : ℂ))
      (𝓝 ((π : ℂ)⁻¹)) := by
    have := hslope'.inv₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    simpa [inv_div] using this
  have := hinv.const_mul (π : ℂ)
  have heq : ∀ ε : ℂ, (π : ℂ) * (ε / Complex.sinh ((π : ℂ) * ε)) = Pc ε := by
    intro ε
    unfold Pc
    ring
  simpa [heq, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)] using this

/-- **The Matsubara-pole residue**: `lim_{ε→0} ε·Pc(in+ε) = i(-1)ⁿn`, for every integer `n`
(including `n = 0`, where the "residue" is trivially `0` since `Pc` is regular there). -/
theorem tendsto_residue_at_matsubara (n : ℤ) :
    Tendsto (fun ε : ℂ => ε * Pc (Complex.I * (n : ℂ) + ε)) (𝓝[≠] (0 : ℂ))
      (𝓝 (Complex.I * (n : ℂ) * (-1) ^ n)) := by
  have hfact : ∀ ε : ℂ, ε ≠ 0 →
      ε * Pc (Complex.I * (n : ℂ) + ε)
        = (Complex.I * (n : ℂ) + ε) * Pc ε * (-1) ^ n := by
    intro ε hε
    have hnegone : ((-1 : ℂ) ^ n) ≠ 0 := zpow_ne_zero n (by norm_num)
    unfold Pc
    have hadd : (π : ℂ) * (Complex.I * (n : ℂ) + ε)
        = (π : ℂ) * (Complex.I * (n : ℂ)) + (π : ℂ) * ε := by ring
    rw [hadd, Complex.sinh_add, sinh_pi_mul_I_mul_int, cosh_pi_mul_I_mul_int, zero_mul,
      zero_add]
    have hinv : ((-1 : ℂ) ^ n)⁻¹ = (-1 : ℂ) ^ n := by
      rcases Int.even_or_odd n with he | ho
      · rw [he.neg_one_zpow]; norm_num
      · rw [ho.neg_one_zpow]; norm_num
    rw [mul_comm ((-1 : ℂ) ^ n) (Complex.sinh ((π : ℂ) * ε)), ← div_div, div_eq_mul_inv, hinv]
    ring
  have htendsto : Tendsto (fun ε : ℂ => (Complex.I * (n : ℂ) + ε) * Pc ε * (-1) ^ n)
      (𝓝[≠] (0 : ℂ)) (𝓝 (Complex.I * (n : ℂ) * (-1) ^ n)) := by
    have h1 : Tendsto (fun ε : ℂ => Complex.I * (n : ℂ) + ε) (𝓝[≠] (0 : ℂ))
        (𝓝 (Complex.I * (n : ℂ))) := by
      have h0 : Tendsto (fun ε : ℂ => Complex.I * (n : ℂ) + ε) (𝓝 (0 : ℂ))
          (𝓝 (Complex.I * (n : ℂ) + 0)) := tendsto_const_nhds.add tendsto_id
      simpa using h0.mono_left nhdsWithin_le_nhds
    have h2 := (h1.mul tendsto_Pc_nhdsWithin_zero).mul_const ((-1 : ℂ) ^ n)
    simpa using h2
  refine htendsto.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hfact ε hε).symm

end GppMatsubara
