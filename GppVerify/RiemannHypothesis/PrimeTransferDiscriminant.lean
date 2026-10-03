import GppVerify.RiemannHypothesis.SU11PrimeBlaschke
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# The SU(1,1) transfer discriminant as the finite-place mass coordinate

Source: Codex, GPPDiscovery2 `research/2026-09-27_su11_mass_discriminant_horizon_pair_cancellation.md`,
§§1–6, 8 (the conditional horizon interpretation of §7 is not formalized).

For `κ = artanh a` the real `SU(1,1)/SO(1,1)` transfer representative of the Blaschke automorphism
is `G(κ) = [[cosh κ, −sinh κ], [−sinh κ, cosh κ]]` (`Gk`).

* `Gk_det`, `Gk_mul`, `Gk_neg_mul`: `det G = 1`, `G(κ) G(κ') = G(κ + κ')`, `G(−κ) G(κ) = I`;
* `disc_eq`, `disc_prime`: the conjugacy discriminant `(Tr G)² − 4 = 4 sinh² κ = μ²`, and for
  `a = p^{-1/2}` it equals `4/(p − 1)`: the finite-place mass-square coordinate is the discriminant
  of the local transfer holonomy;
* `cov_eq`, `cov_det`: the completed two-mode covariance
  `Γ = [[sinh²κ + ½, sinh κ cosh κ], [sinh κ cosh κ, sinh²κ + ½]]` is `½ G(κ)^{-2} = ½ G(−2κ)`,
  with `det Γ = ¼`;
* `cayley_ratio`: `√(λ₋/λ₊) = e^{−2κ} = (1 − a)/(1 + a)`, the Cayley coordinate;
* `inversion_disc`, `pair_disc_zero`: orientation reversal `κ → −κ` preserves the discriminant, but
  the sewn two-sheet holonomy `G(−κ) G(κ) = I` has discriminant exactly `0`;
* `golden_prime`: for `p = 5`, `μ² = 1` and `e^{κ} = φ`, so the eigenvalues of `G` are `φ^{±1}`.

## Checks and scope

All claims check; they are exact `2 × 2` identities. **Not formalized:** the conditional horizon
interpretation of §7 (that the physical mass of a doubled pair is the discriminant of the
composed holonomy) and the global renormalized boost of §9. No claim about observed particle masses
and no RH claim.
-/

open Real Matrix

namespace GppPrimeTransferDiscriminant

/-- The hyperbolic transfer matrix `G(κ)`. -/
noncomputable def Gk (κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh κ, -Real.sinh κ; -Real.sinh κ, Real.cosh κ]

theorem Gk_det (κ : ℝ) : (Gk κ).det = 1 := by
  rw [Gk, Matrix.det_fin_two_of]
  nlinarith [Real.cosh_sq κ]

theorem Gk_trace (κ : ℝ) : (Gk κ).trace = 2 * Real.cosh κ := by
  rw [Gk, Matrix.trace_fin_two]
  simp
  ring

theorem Gk_mul (κ κ' : ℝ) : Gk κ * Gk κ' = Gk (κ + κ') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Gk, Matrix.mul_apply, Fin.sum_univ_two, Real.cosh_add, Real.sinh_add] <;> ring

theorem Gk_zero : Gk 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Gk]

theorem Gk_neg_mul (κ : ℝ) : Gk (-κ) * Gk κ = 1 := by
  rw [Gk_mul, neg_add_cancel, Gk_zero]

/-- The conjugacy discriminant is `4 sinh² κ = μ²`, `μ = 2 sinh κ`. -/
theorem disc_eq (κ : ℝ) : (Gk κ).trace ^ 2 - 4 = (2 * Real.sinh κ) ^ 2 := by
  rw [Gk_trace]
  nlinarith [Real.cosh_sq κ]

/-- **Finite-place mass square.** For `a = p^{-1/2}` and `κ = artanh a`,
`(Tr G)² − 4 = 4/(p − 1)`. -/
theorem disc_prime (p : ℝ) (hp : 1 < p) :
    (Gk (Real.artanh (1 / Real.sqrt p))).trace ^ 2 - 4 = 4 / (p - 1) := by
  have hp0 : 0 < p := by linarith
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hs1 : 1 < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) hp
  have ha : (1 / Real.sqrt p) ∈ Set.Ioo (-1 : ℝ) 1 := by
    refine ⟨by have : 0 < 1 / Real.sqrt p := by positivity
               linarith, ?_⟩
    rw [div_lt_one hs]; exact hs1
  have hsq : 1 - (1 / Real.sqrt p) ^ 2 = (p - 1) / p := by
    rw [div_pow, Real.sq_sqrt hp0.le]; field_simp
  rw [Gk_trace, Real.cosh_artanh ha, hsq]
  have : Real.sqrt ((p - 1) / p) ≠ 0 := by
    apply (Real.sqrt_pos.mpr _).ne'
    positivity
  rw [mul_pow, div_pow, one_pow, Real.sq_sqrt (by positivity)]
  have hp1 : p - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- The two-mode covariance. -/
noncomputable def Cov (κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.sinh κ ^ 2 + 1 / 2, Real.sinh κ * Real.cosh κ;
    Real.sinh κ * Real.cosh κ, Real.sinh κ ^ 2 + 1 / 2]

/-- **`Γ = ½ G^{-2}`.** -/
theorem cov_eq (κ : ℝ) : Cov κ = (1 / 2 : ℝ) • (Gk (-κ) * Gk (-κ)) := by
  rw [Gk_mul, show -κ + -κ = -(2 * κ) by ring]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Cov, Gk, Real.cosh_neg, Real.sinh_neg, Real.cosh_two_mul, Real.sinh_two_mul] <;>
    nlinarith [Real.cosh_sq κ]

theorem cov_det (κ : ℝ) : (Cov κ).det = 1 / 4 := by
  rw [Cov, Matrix.det_fin_two_of]
  nlinarith [Real.cosh_sq κ]

/-- **The Cayley coordinate is the squeezed eigenvalue ratio.** With eigenvalues
`λ_± = e^{±2κ}/2`: `√(λ₋/λ₊) = e^{−2κ} = (1 − a)/(1 + a)` for `κ = artanh a`. -/
theorem cayley_ratio (a : ℝ) (ha : |a| < 1) :
    Real.sqrt ((Real.exp (-(2 * Real.artanh a)) / 2) / (Real.exp (2 * Real.artanh a) / 2)) =
      (1 - a) / (1 + a) := by
  rw [GppSU11Prime.cayley_eq_exp a ha]
  have h : (Real.exp (-(2 * Real.artanh a)) / 2) / (Real.exp (2 * Real.artanh a) / 2) =
      Real.exp (-(2 * Real.artanh a)) ^ 2 := by
    rw [div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0), ← Real.exp_nat_mul,
      ← Real.exp_sub]
    congr 1
    push_cast
    ring
  rw [h, Real.sqrt_sq (Real.exp_pos _).le]

/-- Orientation reversal preserves the discriminant. -/
theorem inversion_disc (κ : ℝ) : (Gk (-κ)).trace ^ 2 - 4 = (Gk κ).trace ^ 2 - 4 := by
  rw [Gk_trace, Gk_trace, Real.cosh_neg]

/-- **The sewn two-sheet holonomy has zero discriminant.** -/
theorem pair_disc_zero (κ : ℝ) : (Gk (-κ) * Gk κ).trace ^ 2 - 4 = 0 := by
  rw [Gk_neg_mul]
  simp [Matrix.trace_one]
  norm_num

/-- **The prime `p = 5`**: discriminant `1` and `e^{κ} = φ`. -/
theorem golden_prime :
    (Gk (Real.artanh (1 / Real.sqrt 5))).trace ^ 2 - 4 = 1 ∧
      Real.exp (Real.artanh (1 / Real.sqrt 5)) = Real.goldenRatio := by
  refine ⟨?_, ?_⟩
  · rw [disc_prime 5 (by norm_num)]; norm_num
  · have hs5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
    have hs1 : 1 < Real.sqrt 5 := by
      nlinarith
    have ha : |1 / Real.sqrt 5| < 1 := by
      rw [abs_of_pos (by positivity), div_lt_one hs]; exact hs1
    have h2 := GppSU11Prime.exp_two_artanh (1 / Real.sqrt 5) ha
    have hφ : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
    have hφp : 0 < Real.goldenRatio := Real.goldenRatio_pos
    have hexp : Real.exp (Real.artanh (1 / Real.sqrt 5)) ^ 2 = Real.goldenRatio ^ 2 := by
      rw [← Real.exp_nat_mul]
      have : ((2 : ℕ) : ℝ) * Real.artanh (1 / Real.sqrt 5) = 2 * Real.artanh (1 / Real.sqrt 5) := by
        norm_num
      rw [this, h2]
      have hne : Real.sqrt 5 - 1 ≠ 0 := by linarith
      have hne' : Real.sqrt 5 ≠ 0 := hs.ne'
      rw [hφ, Real.goldenRatio]
      field_simp
      nlinarith [hs5]
    have := (sq_eq_sq₀ (Real.exp_pos _).le hφp.le).mp hexp
    exact this

end GppPrimeTransferDiscriminant
