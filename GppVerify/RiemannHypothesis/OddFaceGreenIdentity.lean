import GppVerify.RiemannHypothesis.OddFaceSineAtoms

/-!
# OddFace(0.5): the Green identity behind `CCᵀ = Gram(k) − HHᵀ`

Heart's Round 10 (GPP-bridge PR #11, comment 6890476616; GPPDiscovery5 `84f8e45`) reduces the
Y–Z coupling of the 72/73 split to one exact Gram identity. Turbo's audit (6890691322) re-derived the
key step, and it is CHECKED there: for `h_a(y) = B(x_a, δ_y)` with `h_a(0) = 0` and
`k_a = −h_a''`, Green's formula twice on `[0, ℓ]` gives

  `⟨k_a, φ_j⟩ = h_a(ℓ) φ_j'(ℓ) + ω_j² ∫₀^ℓ h_a φ_j`,

which is `ω_j² B(x_a, ψ_j)` for `ψ_j = φ_j − w_j δ_ℓ` with `w_j = −φ_j'(ℓ)/ω_j²`.

**`green_phi`** proves this identity for any `C²` function `h` on `[0, ℓ]` with `h(0) = 0`. The form
`B` does not enter: the statement is about `h` alone. `phi_deriv_at_l` gives the closed form
`φ_j'(ℓ) = √(2/ℓ) ω_j (−1)^j`, so `w_j/ω_j² = −√(2/ℓ)(−1)^j/ω_j³`. That is the coefficient in
`rhoHat_eq`, sign included.

**Scope.**
 OddFace(0.5) is NUMERICAL; RH is OPEN. No `sorry`, no axioms.
-/

namespace GppOddFaceAtoms

open Real intervalIntegral

/-- `φ_j'(x) = √(2/ℓ) ω_j cos(ω_j x)`. -/
theorem hasDerivAt_phi (ℓ : ℝ) (j : ℕ) (x : ℝ) :
    HasDerivAt (phi ℓ j) (√(2 / ℓ) * (om ℓ j * cos (om ℓ j * x))) x :=
  (hasDerivAt_sin_mul (om ℓ j) x).const_mul _

/-- `φ_j'' = −ω_j² φ_j`. -/
theorem hasDerivAt_phi' (ℓ : ℝ) (j : ℕ) (x : ℝ) :
    HasDerivAt (fun x => √(2 / ℓ) * (om ℓ j * cos (om ℓ j * x))) (-(om ℓ j ^ 2) * phi ℓ j x) x := by
  have := ((hasDerivAt_cos_mul (om ℓ j) x).const_mul (om ℓ j)).const_mul (√(2 / ℓ))
  refine this.congr_deriv ?_
  unfold phi; ring

theorem phi_zero (ℓ : ℝ) (j : ℕ) : phi ℓ j 0 = 0 := by simp [phi]

theorem phi_l (ℓ : ℝ) (hℓ : 0 < ℓ) (j : ℕ) : phi ℓ j ℓ = 0 := by
  simp [phi, om_mul ℓ hℓ, Real.sin_nat_mul_pi]

/-- `φ_j'(ℓ) = √(2/ℓ) ω_j (−1)^j`. -/
theorem phi_deriv_at_l (ℓ : ℝ) (hℓ : 0 < ℓ) (j : ℕ) :
    √(2 / ℓ) * (om ℓ j * cos (om ℓ j * ℓ)) = √(2 / ℓ) * om ℓ j * (-1) ^ j := by
  rw [om_mul ℓ hℓ, Real.cos_nat_mul_pi]; ring

/-- **Green's identity on `[0, ℓ]` (Heart R10.1, Turbo-audited).** For `h` with continuous `h''` and
`h(0) = 0`: `∫₀^ℓ (−h'') φ_j = h(ℓ) φ_j'(ℓ) + ω_j² ∫₀^ℓ h φ_j`. -/
theorem green_phi (ℓ : ℝ) (hℓ : 0 < ℓ) (j : ℕ) {h h' h'' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt h (h' x) x) (hd' : ∀ x, HasDerivAt h' (h'' x) x)
    (hc : Continuous h'') (h0 : h 0 = 0) :
    ∫ x in (0 : ℝ)..ℓ, -h'' x * phi ℓ j x
      = h ℓ * (√(2 / ℓ) * om ℓ j * (-1) ^ j) + om ℓ j ^ 2 * ∫ x in (0 : ℝ)..ℓ, h x * phi ℓ j x := by
  have hcont : Continuous h := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  have hphic : Continuous (phi ℓ j) := by unfold phi; fun_prop
  -- `F = −h' φ + h φ'` has derivative `−h'' φ − ω² h φ`.
  have hF : ∀ x ∈ Set.uIcc (0 : ℝ) ℓ,
      HasDerivAt (fun x => -h' x * phi ℓ j x + h x * (√(2 / ℓ) * (om ℓ j * cos (om ℓ j * x))))
        (-h'' x * phi ℓ j x - om ℓ j ^ 2 * (h x * phi ℓ j x)) x := fun x _ => by
    have := (((hd' x).neg).mul (hasDerivAt_phi ℓ j x)).add ((hd x).mul (hasDerivAt_phi' ℓ j x))
    refine this.congr_deriv ?_
    simp only [Pi.neg_apply]
    ring
  have hint1 : IntervalIntegrable (fun x => -h'' x * phi ℓ j x) MeasureTheory.volume 0 ℓ :=
    ((hc.neg).mul hphic).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun x => om ℓ j ^ 2 * (h x * phi ℓ j x)) MeasureTheory.volume 0 ℓ :=
    (continuous_const.mul (hcont.mul hphic)).intervalIntegrable _ _
  have hftc := integral_eq_sub_of_hasDerivAt hF (hint1.sub hint2)
  rw [intervalIntegral.integral_sub hint1 hint2, intervalIntegral.integral_const_mul] at hftc
  simp only [phi_zero, phi_l ℓ hℓ, h0, mul_zero, zero_mul, add_zero, zero_add] at hftc
  rw [phi_deriv_at_l ℓ hℓ] at hftc
  linarith

end GppOddFaceAtoms

#print axioms GppOddFaceAtoms.green_phi
