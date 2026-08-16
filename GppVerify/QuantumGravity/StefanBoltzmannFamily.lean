import GppVerify.QuantumGravity.SinhZetaBridge

/-!
# The Stefan–Boltzmann family `m_s = π^{-(s+1)}(1-2^{-(s+1)})Γ(s+1)ζ(s+1)`

From `blackbody_law_qg_dtoupin_v1.tex` (Test T7 of `verify_blackbody_capstone.py`) and
`haar_qg_paper_v215.tex`: the one-parameter family of "generalized Stefan–Boltzmann"
moments of the Planck spectral weight

```
  P(λ) := πλ / sinh(πλ)
  m_s   := (1/2π) · ∫₀^∞ λ^{s-1} · P(λ) dλ
```

has the closed form `m_s = π^{-(s+1)}·(1-2^{-(s+1)})·Γ(s+1)·ζ(s+1)` for every real `s > 0`
— generalizing `SinhZetaBridge.lean`'s fixed-exponent moments (`M₁ = 1/8` at `s=1`) to the
whole family, including the paper's `M₃ = 1/16` at `s=3` and every non-integer `s` the
companion script checks numerically (`s = 1.37`).

## Proof

`P(λ) = πλ/sinh(πλ)`, so `λ^{s-1}·P(λ) = π·λ^s/sinh(πλ)`. The substitution `t = πλ`
(`integral_comp_mul_left_Ioi`, unconditional on `(0,∞)`, `π > 0`) turns
`∫₀^∞ λ^{s-1}P(λ) dλ` into `π^{-s}·∫₀^∞ t^s/sinh(t) dt`, and the latter is exactly
`GppZetaBridge.sinh_mellin_zeta` at exponent `s+1` (needs `s+1 > 1`, i.e. `s > 0`):
`∫₀^∞ t^{(s+1)-1}/sinh t dt = 2(1-2^{-(s+1)})Γ(s+1)ζ(s+1)`. Multiplying by the `1/2π`
prefactor and collecting the powers of `π` gives the closed form exactly.
-/

namespace GppStefanBoltzmann

open MeasureTheory Real Set

/-- The Planck spectral weight `P(λ) = πλ/sinh(πλ)`. -/
noncomputable def P (lam : ℝ) : ℝ := π * lam / Real.sinh (π * lam)

/-- The auxiliary substituted integrand `g(t) = π^{1-s}·t^s/sinh(t)`, chosen so that
    `g(π·λ) = λ^{s-1}·P(λ)` on `(0,∞)`. -/
noncomputable def gAux (s t : ℝ) : ℝ := π ^ (1 - s) * t ^ s / Real.sinh t

theorem gAux_comp_pi_mul (s : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    gAux s (π * lam) = lam ^ (s - 1) * P lam := by
  have hl : (0:ℝ) ≤ lam := hlam.le
  have hp : (0:ℝ) < π := Real.pi_pos
  unfold gAux P
  rw [Real.mul_rpow hp.le hl]
  have hcomb : π ^ (1 - s) * (π ^ s * lam ^ s) = π * lam ^ s := by
    rw [show π ^ (1 - s) * (π ^ s * lam ^ s) = (π ^ (1 - s) * π ^ s) * lam ^ s by ring,
      ← Real.rpow_add hp, show (1 - s) + s = 1 by ring, Real.rpow_one]
  have hlams : lam ^ (s - 1) * lam = lam ^ s := by
    rw [← Real.rpow_add_one hlam.ne' (s - 1), show s - 1 + 1 = s by ring]
  rw [hcomb, mul_comm (lam ^ (s-1)) (π * lam / Real.sinh (π * lam))]
  rw [show π * lam / Real.sinh (π * lam) * lam ^ (s - 1)
      = π * (lam ^ (s-1) * lam) / Real.sinh (π * lam) by ring]
  rw [hlams]

/-- The substitution identity: `∫₀^∞ λ^{s-1}P(λ)dλ = π^{-s}·∫₀^∞ t^s/sinh(t) dt`. -/
theorem integral_rpow_mul_P_eq (s : ℝ) :
    ∫ lam in Ioi (0:ℝ), lam ^ (s - 1) * P lam
      = π ^ (-s) * ∫ t in Ioi (0:ℝ), t ^ s / Real.sinh t := by
  have hp : (0:ℝ) < π := Real.pi_pos
  have hcongr : ∫ lam in Ioi (0:ℝ), lam ^ (s - 1) * P lam
      = ∫ lam in Ioi (0:ℝ), gAux s (π * lam) :=
    setIntegral_congr_fun measurableSet_Ioi
      (fun lam hlam => (gAux_comp_pi_mul s hlam).symm)
  rw [hcongr, integral_comp_mul_left_Ioi (gAux s) 0 hp, mul_zero]
  have hconst : ∫ t in Ioi (0:ℝ), gAux s t
      = π ^ (1 - s) * ∫ t in Ioi (0:ℝ), t ^ s / Real.sinh t := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by
      unfold gAux; ring)
  rw [smul_eq_mul, hconst,
    show π⁻¹ * (π ^ (1 - s) * ∫ t in Ioi (0:ℝ), t ^ s / Real.sinh t)
      = (π⁻¹ * π ^ (1 - s)) * ∫ t in Ioi (0:ℝ), t ^ s / Real.sinh t by ring]
  congr 1
  rw [show π⁻¹ = π ^ (-(1:ℝ)) by
      rw [Real.rpow_neg hp.le, Real.rpow_one],
    ← Real.rpow_add hp, show -(1:ℝ) + (1 - s) = -s by ring]

/-- **The Stefan–Boltzmann family closed form** (T7 of `verify_blackbody_capstone.py`,
    general real `s > 0`, not merely the checked integer/rational sample points):
    `(1/2π)·∫₀^∞ λ^{s-1}P(λ)dλ = π^{-(s+1)}(1-2^{-(s+1)})Γ(s+1)ζ(s+1)`. -/
theorem stefan_boltzmann_family {s : ℝ} (hs : 0 < s) :
    (1 / (2 * π)) * ∫ lam in Ioi (0:ℝ), lam ^ (s - 1) * P lam
      = π ^ (-(s + 1)) * (1 - 2 ^ (-(s + 1))) * Real.Gamma (s + 1) *
          ∑' n : ℕ, 1 / (n:ℝ) ^ (s + 1) := by
  have hp : (0:ℝ) < π := Real.pi_pos
  rw [integral_rpow_mul_P_eq]
  have hmellin := GppZetaBridge.sinh_mellin_zeta (s := s + 1) (by linarith)
  rw [show s + 1 - 1 = s by ring] at hmellin
  rw [hmellin]
  rw [show (1:ℝ) / (2 * π) * (π ^ (-s) * (2 * (1 - 2 ^ (-(s+1))) * Real.Gamma (s+1) *
      ∑' n : ℕ, 1 / (n:ℝ) ^ (s+1)))
      = (π ^ (-s) / π) * (1 - 2 ^ (-(s+1))) * Real.Gamma (s+1) *
          ∑' n : ℕ, 1 / (n:ℝ) ^ (s+1) by ring]
  congr 2
  rw [div_eq_mul_inv, show π⁻¹ = π ^ (-(1:ℝ)) by rw [Real.rpow_neg hp.le, Real.rpow_one],
    ← Real.rpow_add hp, show -s + -(1:ℝ) = -(s+1) by ring]

/-- Special value `m₁ = 1/8` (the `haar_qg` paper's first Plancherel loop moment,
    already `SinhZetaBridge.plancherel_first_moment`; re-derived here as a special case
    of the general family for cross-verification). -/
theorem m_one_eq :
    (1 / (2 * π)) * ∫ lam in Ioi (0:ℝ), lam ^ ((1:ℝ) - 1) * P lam = 1 / 8 := by
  rw [stefan_boltzmann_family (s := 1) one_pos, show (1:ℝ) + 1 = 2 by norm_num]
  have hg2 : Real.Gamma (2:ℝ) = 1 := by
    rw [show (2:ℝ) = ((1:ℕ):ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  have h2 : (2:ℝ) ^ (-(2:ℝ)) = 1/4 := by
    rw [show -(2:ℝ) = -((2:ℕ):ℝ) by norm_num,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
    norm_num
  have hpi : π ^ (-(2:ℝ)) = π⁻¹^2 := by
    rw [show -(2:ℝ) = -((2:ℕ):ℝ) by norm_num,
      Real.rpow_neg Real.pi_pos.le, Real.rpow_natCast]
    ring
  have hζ2 : ∑' n : ℕ, 1 / (n:ℝ) ^ (2:ℝ) = π^2/6 := by
    have hpow : ∀ n : ℕ, (1:ℝ) / (n:ℝ) ^ (2:ℝ) = 1 / (n:ℝ) ^ (2:ℕ) := fun n => by
      rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [tsum_congr hpow]
    exact hasSum_zeta_two.tsum_eq
  rw [hg2, h2, hpi, hζ2]
  have hpine : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- Special value `m₃ = 1/16` (T7'' of `verify_blackbody_capstone.py`). -/
theorem m_three_eq :
    (1 / (2 * π)) * ∫ lam in Ioi (0:ℝ), lam ^ ((3:ℝ) - 1) * P lam = 1 / 16 := by
  rw [stefan_boltzmann_family (s := 3) (by norm_num), show (3:ℝ) + 1 = 4 by norm_num]
  have hg4 : Real.Gamma (4:ℝ) = 6 := by
    rw [show (4:ℝ) = ((3:ℕ):ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  have h2 : (2:ℝ) ^ (-(4:ℝ)) = 1/16 := by
    rw [show -(4:ℝ) = -((4:ℕ):ℝ) by norm_num,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
    norm_num
  have hpi : π ^ (-(4:ℝ)) = π⁻¹^4 := by
    rw [show -(4:ℝ) = -((4:ℕ):ℝ) by norm_num,
      Real.rpow_neg Real.pi_pos.le, Real.rpow_natCast]
    ring
  have hζ4 : ∑' n : ℕ, 1 / (n:ℝ) ^ (4:ℝ) = π^4/90 := by
    have hpow : ∀ n : ℕ, (1:ℝ) / (n:ℝ) ^ (4:ℝ) = 1 / (n:ℝ) ^ (4:ℕ) := fun n => by
      rw [show ((4:ℝ)) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [tsum_congr hpow]
    exact hasSum_zeta_four.tsum_eq
  rw [hg4, h2, hpi, hζ4]
  have hpine : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

end GppStefanBoltzmann
