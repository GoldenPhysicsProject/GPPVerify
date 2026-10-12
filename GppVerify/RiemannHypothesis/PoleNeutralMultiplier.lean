import GppVerify.NoGo.HermiteFourierIndefinite

/-!
# The pole-neutralizing operator `L₀ = d²/du² − ¼` keeps every nontrivial zero channel

Source: Codex, GPPDiscovery2 `research/2026-09-30_neutralization_preserves_zero_signature.md`
§§1–3.

* `fourier_L0`: **the Fourier multiplier of `L₀`.** For `g` with `g, g', g''` integrable,
  `𝓕(g'' − g/4)(w) = −(4π²w² + ¼)·𝓕g(w)`. In Codex's convention `ĝ(z) = ∫g e^{−izu}`,
  `z = 2πw`, this is `−(z² + ¼) = −s(1−s)` at `s = ½ + iz` (`one_sub_mul_eq`).
* `mul_one_sub_ne_zero`: `ρ(1−ρ) ≠ 0` for every `ρ` in the open critical strip. So `L₀` multiplies
  every nontrivial-zero channel by a **nonzero** scalar; it kills only the pole points `s = 0, 1`.
* `congr_preserves_negative`: an invertible congruence `D* H D` keeps a negative direction. So an
  off-line mirror pair stays indefinite after neutralization (Sylvester's step in the note).

Consequence (the note's §4, ARGUED here, since it needs Weil test-space interpolation): positivity of
the Weil form on the neutral subspace is RH-equivalent. A factorization `L₀* A L₀ = B*B` would be
an RH proof, not a lemma. **No RH claim.**
-/

namespace GppPoleNeutralMultiplier

open Real Complex MeasureTheory FourierTransform GppNoGo.HermiteFourierIndefinite Matrix

/-- **Fourier multiplier of `L₀ = d²/du² − ¼`.** -/
theorem fourier_L0 {g : ℝ → ℂ} (hg : Integrable g) (hd : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) (hd' : Differentiable ℝ (deriv g))
    (hg'' : Integrable (deriv (deriv g))) (w : ℝ) :
    𝓕 (fun x => deriv (deriv g) x - g x / 4) w = -(4 * π ^ 2 * w ^ 2 + 1 / 4) * 𝓕 g w := by
  have h1 := congrFun (fourier_deriv hg' hd' hg'') w
  have h0 := congrFun (fourier_deriv hg hd hg') w
  have hlin := fourier_lin hg hg'' (-1 / 4) w
  have hfun : (fun x => deriv (deriv g) x - g x / 4) = fun x => (-1 / 4 : ℂ) * g x + deriv (deriv g) x := by
    funext x; ring
  rw [hfun, hlin, h1]
  simp only [smul_eq_mul]
  rw [h0]
  simp only [smul_eq_mul]
  ring_nf
  rw [I_sq]
  ring

/-- `s(1−s) = z² + ¼` at `s = ½ + iz`. -/
theorem one_sub_mul_eq (z : ℂ) :
    (1 / 2 + I * z) * (1 - (1 / 2 + I * z)) = z ^ 2 + 1 / 4 := by
  ring_nf; rw [I_sq]; ring

/-- **`ρ(1−ρ) ≠ 0` in the open critical strip.** -/
theorem mul_one_sub_ne_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : ρ * (1 - ρ) ≠ 0 := by
  apply mul_ne_zero
  · intro h; rw [h] at h0; simp at h0
  · intro h
    have : ρ = 1 := by linear_combination -h
    rw [this] at h1; simp at h1

/-- **Invertible congruence preserves a negative direction.** If `⟪v, Hv⟫ < 0` for some `v` and `D`
is invertible, then `⟪w, D* H D w⟫ < 0` for `w = D⁻¹v`. -/
theorem congr_preserves_negative {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : IsUnit D.det) (v : Fin n → ℂ)
    (hv : (star v ⬝ᵥ (H *ᵥ v)).re < 0) :
    ∃ w : Fin n → ℂ, (star w ⬝ᵥ ((D.conjTranspose * H * D) *ᵥ w)).re < 0 := by
  refine ⟨D⁻¹ *ᵥ v, ?_⟩
  have hDD : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv D hD
  have hDv : D *ᵥ (D⁻¹ *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hDD, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hDv, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec, hDv]
  exact hv

end GppPoleNeutralMultiplier
