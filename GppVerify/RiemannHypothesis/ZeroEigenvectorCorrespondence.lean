import GppVerify.RiemannHypothesis.NymanBeurlingBoundStates

/-!
# Zeros of `ζ` are exactly the dilation-eigenstates orthogonal to the Beurling functions

For `0 < re ρ < 1` the state `x^{ρ-1}` on `(0, 1]` is a dilation eigenvector with eigenvalue
`θ^{ρ-1}`-scaling.  Its pairing with the Beurling function `ρ_θ` is the Mellin transform

  `∫_{(0,1]} x^{ρ-1} ρ_θ(x) dx = (θ^ρ - θ) · (-ζ(ρ)/ρ)`,

valid for every `ρ` in the strip (`integral_cpow_mul_beurling`).  Both directions of the
correspondence follow:

* `zeta_eq_zero_of_orthogonal` (eigenvector ⇒ zero): one vanishing pairing at a parameter
  `θ` with `θ^ρ ≠ θ` forces `ζ ρ = 0`.
* `zeta_eq_zero_iff_orthogonal_half`: the single test function `ρ_{1/2}` detects zeros:
  `ζ ρ = 0 ↔ ∫_{(0,1]} x^{ρ-1} ρ_{1/2}(x) dx = 0`.
* `zeta_eq_zero_iff_orthogonal`: `ζ ρ = 0` iff `x^{ρ-1}` is orthogonal to every `ρ_θ`.

Together with `beurling_orthogonal` (zero ⇒ eigenvector) this is the exact two-way dictionary
between the zeros in the strip and the dilation eigenstates of `N^⊥`.
-/

open Complex Set MeasureTheory

namespace GppZeroEigenvector

open GppNymanBeurling

/-- **The pairing is the Mellin symbol.** For `0 < re ρ < 1` and `0 < θ ≤ 1`,
`∫_{(0,1]} x^{ρ-1} ρ_θ(x) dx = (θ^ρ - θ)(-ζ(ρ)/ρ)`. -/
theorem integral_cpow_mul_beurling {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) {ρ : ℂ} (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) :
    ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (ρ - 1) * beurling θ x =
      ((θ : ℂ) ^ ρ - θ) * (-riemannZeta ρ / ρ) := by
  have hm := mellin_beurling hθ h0 h1
  have hconv : MellinConvergent (beurling θ) ρ := by
    have hA : MellinConvergent (fun t => fracInv (θ⁻¹ * t)) ρ :=
      (MellinConvergent.comp_mul_left (inv_pos.2 hθ)).2 (mellinConvergent_fracInv h0 h1)
    have hB : MellinConvergent (fun t => (θ : ℂ) * fracInv t) ρ := by
      have := (mellinConvergent_fracInv h0 h1).const_smul (θ : ℂ)
      simpa [smul_eq_mul] using this
    unfold MellinConvergent at hA hB ⊢
    refine (hA.sub hB).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [beurling, smul_eq_mul, Pi.sub_apply]; ring
  rw [← hm]
  unfold mellin
  unfold MellinConvergent at hconv
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hconv.mono_set (by rw [hsplit]; exact subset_union_left))
    (hconv.mono_set (by rw [hsplit]; exact subset_union_right))]
  have hz2 : ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (ρ - 1) • beurling θ t = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℂ))
      (fun t ht => by simp [beurling_eq_zero hθ hθ1 ht])]
    simp
  rw [hz2, add_zero]
  simp [smul_eq_mul]

/-- For `0 < θ < 1` and `re ρ < 1`, `θ^ρ ≠ θ`. -/
theorem cpow_ne_self {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) {ρ : ℂ} (h1 : ρ.re < 1) :
    (θ : ℂ) ^ ρ ≠ θ := by
  intro h
  have hn : ‖(θ : ℂ) ^ ρ‖ = ‖(θ : ℂ)‖ := by rw [h]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hθ, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hθ] at hn
  have : θ ^ ρ.re > θ ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_gt hθ hθ1 h1
  rw [Real.rpow_one] at this
  linarith

/-- **Eigenvector ⇒ zero.** A vanishing pairing of `x^{ρ-1}` with one `ρ_θ`, `0 < θ < 1`,
forces `ζ ρ = 0`. -/
theorem zeta_eq_zero_of_orthogonal {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) {ρ : ℂ} (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (h : ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (ρ - 1) * beurling θ x = 0) :
    riemannZeta ρ = 0 := by
  rw [integral_cpow_mul_beurling hθ hθ1.le h0 h1] at h
  have hne : (θ : ℂ) ^ ρ - θ ≠ 0 := sub_ne_zero.2 (cpow_ne_self hθ hθ1 h1)
  have hρ : ρ ≠ 0 := fun hρ0 => by simp [hρ0] at h0
  rcases mul_eq_zero.1 h with h | h
  · exact absurd h hne
  · have := (div_eq_zero_iff.1 h).resolve_right hρ
    simpa using this

/-- **The single test function `ρ_{1/2}` detects every zero in the strip.** -/
theorem zeta_eq_zero_iff_orthogonal_half {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    riemannZeta ρ = 0 ↔
      ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (ρ - 1) * beurling (1 / 2) x = 0 := by
  refine ⟨fun hz => beurling_orthogonal (by norm_num) (by norm_num) h0 h1 hz, fun h => ?_⟩
  exact zeta_eq_zero_of_orthogonal (by norm_num) (by norm_num) h0 h1 h

/-- **Zeros are exactly the eigenstates orthogonal to `N`.** -/
theorem zeta_eq_zero_iff_orthogonal {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    riemannZeta ρ = 0 ↔ ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (ρ - 1) * beurling θ x = 0 := by
  refine ⟨fun hz θ hθ hθ1 => beurling_orthogonal hθ hθ1 h0 h1 hz, fun h => ?_⟩
  exact zeta_eq_zero_of_orthogonal (by norm_num : (0:ℝ) < 1 / 2) (by norm_num) h0 h1
    (h (1 / 2) (by norm_num) (by norm_num))

end GppZeroEigenvector

#print axioms GppZeroEigenvector.integral_cpow_mul_beurling
#print axioms GppZeroEigenvector.zeta_eq_zero_of_orthogonal
#print axioms GppZeroEigenvector.zeta_eq_zero_iff_orthogonal_half
#print axioms GppZeroEigenvector.zeta_eq_zero_iff_orthogonal
