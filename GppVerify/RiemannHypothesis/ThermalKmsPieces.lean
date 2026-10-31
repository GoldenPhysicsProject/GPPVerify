import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Exact pieces of the thermal/KMS prime–Archimedean identity

Source: Codex/Discovery2, GPP-bridge PR #11 comment 2026-10-31 ("exact all-scale completed
prime–Archimedean thermal/KMS identity", `discovery/complete_thermal_kms_global_identity.md`).
Daniel Toupin / Golden Physics Project, with AI assistance from Codex (statements) and Claude Code
(formalization).

Three exact, hypothesis-free pieces of that identity:

* `gamma_ladder`: for `y > 0`, `e^{y/2}/(2 sinh y) = Σ_{k≥0} e^{-(2k+1/2) y}` (the "odd half-integer
  thermal ladder", a geometric series).
* `gamma_split`: for `D = ‖f − T_y f‖²` and `q = 2N − D`,
  `(2N − e^{y/2} q)/(2 sinh y) = (e^{y/2}/(2 sinh y)) · D − 2N · (e^{y/2} − 1)/(2 sinh y)`.
* `prime_polarization`: for isometries `U_i`, weights `c_i`, a finite index set,
  `Σ c_i ‖f − U_i f‖² − 2 (Σ c_i) ‖f‖² = −2 Σ c_i Re⟪f, U_i f⟫`.
  (This is the finite-cutoff form of "`−S_prime = lim [K_X − 2Ψ(X)‖f‖²]`".)

**Scope.** These are the elementary identities only. Not formalized: the Bost–Connes algebra and its
KMS state (and so the midpoint identity `ω(B* σ_{i/2}(B)) = n^{-1/2}|f(x) − f(x+log n)|²`), the
value `∫₀^∞ r = ½ log 2 + π/4` and the constant `κ∞`, the stabilization of the cutoff limit on
compact supports, the signed pole, and any positivity of the completed form. Codex's CI receipts are
not checked here. The completed form `Q` is NOT a positive norm in this picture, as Codex states.
No claim about RH.
-/

set_option autoImplicit false

open Finset

namespace GppThermalKmsPieces

/-- The odd half-integer thermal ladder: `e^{y/2}/(2 sinh y) = Σ_k e^{-(2k+1/2) y}` for `y > 0`. -/
theorem gamma_ladder {y : ℝ} (hy : 0 < y) :
    HasSum (fun k : ℕ => Real.exp (-((2 * (k : ℝ) + 1 / 2) * y)))
      (Real.exp (y / 2) / (2 * Real.sinh y)) := by
  set u : ℝ := Real.exp (-(2 * y)) with hu
  have hu0 : 0 ≤ u := (Real.exp_pos _).le
  have hu1 : u < 1 := by
    rw [hu, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hg := (hasSum_geometric_of_lt_one hu0 hu1).mul_left (Real.exp (-(y / 2)))
  have hterm : ∀ k : ℕ, Real.exp (-(y / 2)) * u ^ k = Real.exp (-((2 * (k : ℝ) + 1 / 2) * y)) := by
    intro k
    rw [hu, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; ring
  have hsum : Real.exp (-(y / 2)) * (1 - u)⁻¹ = Real.exp (y / 2) / (2 * Real.sinh y) := by
    have h1 : 0 < 1 - u := by linarith
    have hs : 2 * Real.sinh y = Real.exp y - Real.exp (-y) := by rw [Real.sinh_eq]; ring
    have e1 : Real.exp y = Real.exp (y / 2) * Real.exp (y / 2) := by rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
    have e3 : Real.exp (-(y / 2)) * Real.exp (y / 2) = 1 := by rw [← Real.exp_add]; simp
    have e4 : u = Real.exp (-y) * Real.exp (-y) := by rw [hu, ← Real.exp_add]; congr 1; ring
    have hp : 0 < Real.exp (y / 2) := Real.exp_pos _
    have hpy : 0 < Real.exp y := Real.exp_pos _
    have hpn : 0 < Real.exp (-y) := Real.exp_pos _
    have hd : 0 < Real.exp y - Real.exp (-y) := by
      have : Real.exp (-y) < Real.exp y := Real.exp_lt_exp.mpr (by linarith)
      linarith
    rw [hs, inv_eq_one_div, ← mul_div_assoc, mul_one, div_eq_div_iff h1.ne' hd.ne']
    nlinarith [e1, e2, e3, e4, hp, hpy, hpn, mul_pos hp hp]
  rw [← hsum]
  simpa only [hterm] using hg

/-- The pointwise gamma split `(2N − e^{y/2} q)/(2 sinh y) = w D − 2N r` with `q = 2N − D`. -/
theorem gamma_split {y N D : ℝ} (hy : 0 < y) :
    (2 * N - Real.exp (y / 2) * (2 * N - D)) / (2 * Real.sinh y) =
      Real.exp (y / 2) / (2 * Real.sinh y) * D -
        2 * N * ((Real.exp (y / 2) - 1) / (2 * Real.sinh y)) := by
  have hs : Real.sinh y ≠ 0 := (Real.sinh_pos_iff.mpr hy).ne'
  field_simp
  ring

/-- Finite polarization of isometric shifts: the cutoff kinetic energy minus the diverging
counterterm equals the (negative twice) real part of the correlations. -/
theorem prime_polarization {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (s : Finset ι) (c : ι → ℝ) (U : ι → E → E)
    (hU : ∀ i x, ‖U i x‖ = ‖x‖) (f : E) :
    ∑ i ∈ s, c i * ‖f - U i f‖ ^ 2 - 2 * (∑ i ∈ s, c i) * ‖f‖ ^ 2 =
      -2 * ∑ i ∈ s, c i * RCLike.re (inner 𝕜 f (U i f)) := by
  have hterm : ∀ i, c i * ‖f - U i f‖ ^ 2 =
      c i * (2 * ‖f‖ ^ 2) - 2 * (c i * RCLike.re (inner 𝕜 f (U i f))) := by
    intro i
    rw [norm_sub_sq (𝕜 := 𝕜), hU i f]
    ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

end GppThermalKmsPieces
