import GppVerify.RiemannHypothesis.ArithmeticUnitaryDual
import GppVerify.RiemannHypothesis.CasimirRiemannHypothesis
import GppVerify.RiemannHypothesis.CelestialNodal

/-!
Exact scalar controls for Turbo's three 2026-11-07 PR11 audits.
The existing Ftheta is the actual theta=1/4 carrier, not a new test function.
Its zero-transfer control retains a genuine xi-zero hypothesis; no numerical zero,
Hardy existence theorem, representation construction or RH premise is smuggled in.
Daniel Toupin / Golden Physics Project; AI assistance from Principal series.
-/

set_option autoImplicit false

open Complex GppCasimirCriticalLine GppArithmeticUnitaryDual GppCelestialNodal

namespace CasimirGeographyRegression

example (s : ℂ) : Tempered s ↔ s.re = 1 / 2 := tempered_iff s

example (s : ℂ) : Complementary s ↔
    s.im = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1 / 2 := complementary_iff s

example (s : ℂ) : (casimir s).im ≠ 0 ↔ s.re ≠ 1 / 2 ∧ s.im ≠ 0 :=
  complex_casimir_iff s

example {s : ℂ} (h : (casimir s).im ≠ 0) : s.re ≠ 1 / 2 :=
  off_line_of_complex_casimir h

example (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    Tempered s ∨ Complementary s ∨ (casimir s).im ≠ 0 := strip_geography s h0 h1

-- Reuse the already-proved corrected sign, not a duplicate identity.
example (s : ℂ) : casimir s = 1 / 4 - (s - 1 / 2) ^ 2 := by
  simpa only [GppCasimirRH.centeredSq] using
    GppCasimirRH.casimir_eq_quarter_sub_centeredSq s

-- Exact countercontrol to the false plus sign.
example : casimir 0 ≠ (1 / 4 : ℂ) + (0 - 1 / 2) ^ 2 := by norm_num [casimir]

-- Entire line, including the zero-height threshold: no nonzero-height side condition.
example (γ : ℝ) : Tempered ((1 / 2 : ℂ) + γ * I) := by
  apply (tempered_iff _).mpr
  simp

example : casimir (1 / 2) = (1 / 4 : ℂ) := by norm_num [casimir]

example : Tempered (1 / 2 : ℂ) := by norm_num [Tempered, casimir]
example : ¬Complementary (1 / 2 : ℂ) := by norm_num [Complementary, casimir]
example : Complementary (1 / 4 : ℂ) := by norm_num [Complementary, casimir]
example : Complementary (3 / 4 : ℂ) := by norm_num [Complementary, casimir]
example : ¬Tempered (1 / 4 : ℂ) := by norm_num [Tempered, casimir]
example : ¬Complementary (0 : ℂ) := by norm_num [Complementary, casimir]
example : ¬Complementary (1 : ℂ) := by norm_num [Complementary, casimir]

-- General shifted parameter; theta=0 or gamma=0 must not be classified as complex.
example (θ γ : ℝ) : casimir ((1 / 2 : ℂ) + θ + γ * I) =
    1 / 4 + (γ : ℂ) ^ 2 - (θ : ℂ) ^ 2 - 2 * I * γ * θ :=
  casimir_shifted_principal θ γ

example (θ γ : ℝ) : (casimir ((1 / 2 : ℂ) + θ + γ * I)).im ≠ 0 ↔
    θ ≠ 0 ∧ γ ≠ 0 := casimir_shifted_nonreal_iff θ γ

-- Both theta signs at actual nonzero height; the real part alone is insufficient.
example : casimir (3 / 4 + I) = 19 / 16 - I / 2 := by
  apply Complex.ext <;> norm_num [casimir, Complex.mul_re, Complex.mul_im]
example : casimir (1 / 4 + I) = 19 / 16 + I / 2 := by
  apply Complex.ext <;> norm_num [casimir, Complex.mul_re, Complex.mul_im]
example : 1 / 4 < (casimir (3 / 4 + I)).re ∧
    ¬Tempered (3 / 4 + I) ∧ ¬Complementary (3 / 4 + I) := by
  norm_num [Tempered, Complementary, casimir, Complex.mul_re, Complex.mul_im]

-- Actual existing Ftheta zero carrier: both shifted zeros retain their nonzero height.
theorem Ftheta_nonzero_height_control {ρ : ℂ} (hρ : GppLogDerivZeroFree.xi ρ = 0)
    (hre : ρ.re = 1 / 2) (hγ : ρ.im ≠ 0) :
    Ftheta (ρ + 1 / 4) = 0 ∧ Ftheta (ρ - 1 / 4) = 0 ∧
    (casimir (ρ + 1 / 4)).im = -ρ.im / 2 ∧
    (casimir (ρ - 1 / 4)).im = ρ.im / 2 ∧
    (casimir (ρ + 1 / 4)).im ≠ 0 ∧ (casimir (ρ - 1 / 4)).im ≠ 0 ∧
    ¬Tempered (ρ + 1 / 4) ∧ ¬Tempered (ρ - 1 / 4) ∧
    ¬Complementary (ρ + 1 / 4) ∧ ¬Complementary (ρ - 1 / 4) := by
  obtain ⟨hp, hm, hpr, hmr⟩ := Ftheta_zeros_off_line hρ hre
  have hpi : (ρ + 1 / 4).im ≠ 0 := by simpa using hγ
  have hmi : (ρ - 1 / 4).im ≠ 0 := by simpa using hγ
  have hpc := off_line_nonreal_casimir (ρ + 1 / 4) (by rw [hpr]; norm_num) hpi
  have hmc := off_line_nonreal_casimir (ρ - 1 / 4) (by rw [hmr]; norm_num) hmi
  refine ⟨hp, hm, ?_, ?_, hpc, hmc, ?_, ?_, ?_, ?_⟩
  · rw [casimir_im, hpr]
    simp
    ring
  · rw [casimir_im, hmr]
    simp
    ring
  · exact fun h => hpc h.1
  · exact fun h => hmc h.1
  · exact fun h => hpc h.1
  · exact fun h => hmc h.1

end CasimirGeographyRegression

#print axioms CasimirGeographyRegression.Ftheta_nonzero_height_control
#print axioms GppArithmeticUnitaryDual.off_line_of_complex_casimir
#print axioms GppArithmeticUnitaryDual.tempered_iff
#print axioms GppArithmeticUnitaryDual.complementary_iff
#print axioms GppArithmeticUnitaryDual.complex_casimir_iff
#print axioms GppArithmeticUnitaryDual.strip_geography
#print axioms GppArithmeticUnitaryDual.casimir_shifted_principal
#print axioms GppArithmeticUnitaryDual.casimir_shifted_nonreal_iff
