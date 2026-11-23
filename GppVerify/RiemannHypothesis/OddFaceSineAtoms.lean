import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# OddFace(0.5): the sine atoms, their transforms, and the Cauchy–Schwarz mass majorant

Layer 2 of the OddFace(0.5) Lean architecture (bridge `CLAUDE_CODE_RESEARCH_NOTES.md`, 165b6ea):
the mode expansion that the bordered-Schur certificate is written in. The identities below are
Heart's Round 8 / 8b (GPP-bridge PR #11, comments 6890182093 and 6890206957; GPPDiscovery5
`dbccbfe`, `3a9987f`), audited by Turbo (6890250478: R8.1 CHECKED, R8b.1 CHECKED as an identity).
Here they are PROVED.

**Setting.** On `[0, ℓ]`, with `ℓ > 0` and `ω_j = jπ/ℓ` (so `ω_j ℓ = jπ`), the sine atoms are

  `φ_j(x) = √(2/ℓ) sin(ω_j x)`, `j ≥ 1`,

and their sine transform is `S_j(t) = ∫₀^ℓ φ_j(x) sin(t x) dx`.

* **`sineTransform_phi`** (Heart R8.1): for `t² ≠ ω_j²`,
  `S_j(t) = √(2/ℓ) ω_j (−1)^j sin(tℓ) / (t² − ω_j²)`.
* **`phi_orthonormal`**: `∫₀^ℓ φ_j φ_k = [j = k]` for `j, k ≥ 1`.
* **`rhoHat_eq`** (Heart R8.1, the `ψ̂ / ρ̂` split): with `ψ̂_j = (t/ω_j)² S_j`,
  `ψ̂_j(t) − (t/ω_j)⁴ S_j(t) = −√(2/ℓ) (−1)^j t² sin(tℓ) / ω_j³`, so the remainder
  `ρ̂_j = (t/ω_j)⁴ S_j` is exactly what is left after the boundary profile `∝ t² sin(tℓ)/ω_j³`
  (Heart's `(w_j/ω_j²) t² sin(tℓ)`, up to her sign convention for `w_j`) is removed. No fit.
* **`sineTransform_sum`**: for `g = Σ_{j∈s} c_j φ_j`,
  `ĝ(t) = √(2/ℓ) sin(tℓ) Σ_j c_j (−1)^j ω_j / (t² − ω_j²)`.
* **`sq_sineTransform_le`** (Heart R8b.3, the mass majorant):
  `ĝ(t)² ≤ (2/ℓ) sin²(tℓ) · ‖g‖²_{L²(0,ℓ)} · Σ_{j∈s} ω_j² / (t² − ω_j²)²`,
  with `‖g‖² = ∫₀^ℓ g²` (`integral_sq_sum_phi`: `= Σ c_j²`).

**Scope.** These are the atoms and the pointwise majorant only.
OddFace(0.5) is closed NUMERICALLY, not proved; corrected P2/P3, H_ψ,
WeilIsGram, KreinDecomp, ARP, RH: OPEN. No `sorry`, no axioms.
-/

namespace GppOddFaceAtoms

open Real intervalIntegral Finset

/-- The mode frequency `ω_j = jπ/ℓ`. -/
noncomputable def om (ℓ : ℝ) (j : ℕ) : ℝ := j * π / ℓ

/-- The sine atom `φ_j(x) = √(2/ℓ) sin(ω_j x)`. -/
noncomputable def phi (ℓ : ℝ) (j : ℕ) (x : ℝ) : ℝ := √(2 / ℓ) * sin (om ℓ j * x)

/-- The sine transform on `[0, ℓ]`. -/
noncomputable def sineT (ℓ : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x in (0 : ℝ)..ℓ, f x * sin (t * x)

theorem om_mul (ℓ : ℝ) (hℓ : 0 < ℓ) (j : ℕ) : om ℓ j * ℓ = j * π := by
  unfold om; field_simp

/-! ### The product-of-sines antiderivative -/

/-- An antiderivative of `sin(ωx) sin(tx)` for `t² ≠ ω²`. -/
noncomputable def F2 (ω t x : ℝ) : ℝ :=
  (ω * cos (ω * x) * sin (t * x) - t * sin (ω * x) * cos (t * x)) / (t ^ 2 - ω ^ 2)

theorem hasDerivAt_sin_mul (a x : ℝ) : HasDerivAt (fun x => sin (a * x)) (a * cos (a * x)) x := by
  have := ((hasDerivAt_id' x).const_mul a).sin
  simp only [mul_one] at this
  exact this.congr_deriv (mul_comm _ _)

theorem hasDerivAt_cos_mul (a x : ℝ) :
    HasDerivAt (fun x => cos (a * x)) (-(a * sin (a * x))) x := by
  have := ((hasDerivAt_id' x).const_mul a).cos
  simp only [mul_one] at this
  exact this.congr_deriv (by ring)

theorem hasDerivAt_F2 (ω t x : ℝ) (h : t ^ 2 - ω ^ 2 ≠ 0) :
    HasDerivAt (F2 ω t) (sin (ω * x) * sin (t * x)) x := by
  have h1 := (((hasDerivAt_cos_mul ω x).const_mul ω).mul (hasDerivAt_sin_mul t x)).sub
    (((hasDerivAt_sin_mul ω x).const_mul t).mul (hasDerivAt_cos_mul t x))
  have h2 := h1.div_const (t ^ 2 - ω ^ 2)
  refine h2.congr_deriv ?_
  field_simp
  ring

/-- `∫₀^ℓ sin(ω_j x) sin(t x) dx = (−1)^j ω_j sin(tℓ)/(t² − ω_j²)`. -/
theorem integral_sin_mul_sin (ℓ : ℝ) (hℓ : 0 < ℓ) (j : ℕ) (t : ℝ)
    (h : t ^ 2 - om ℓ j ^ 2 ≠ 0) :
    ∫ x in (0 : ℝ)..ℓ, sin (om ℓ j * x) * sin (t * x)
      = (-1) ^ j * om ℓ j * sin (t * ℓ) / (t ^ 2 - om ℓ j ^ 2) := by
  rw [integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_F2 (om ℓ j) t x h)
    ((by fun_prop : Continuous fun x => sin (om ℓ j * x) * sin (t * x)).intervalIntegrable _ _)]
  simp only [F2, om_mul ℓ hℓ, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi, mul_zero, Real.sin_zero,
    Real.cos_zero]
  ring

/-- **Heart R8.1.** `S_j(t) = √(2/ℓ) ω_j (−1)^j sin(tℓ)/(t² − ω_j²)`. -/
theorem sineTransform_phi (ℓ : ℝ) (hℓ : 0 < ℓ) (j : ℕ) (t : ℝ) (h : t ^ 2 - om ℓ j ^ 2 ≠ 0) :
    sineT ℓ (phi ℓ j) t = √(2 / ℓ) * om ℓ j * (-1) ^ j * sin (t * ℓ) / (t ^ 2 - om ℓ j ^ 2) := by
  unfold sineT phi
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul, integral_sin_mul_sin ℓ hℓ j t h]
  ring

/-! ### Orthonormality -/

theorem integral_sin_mul_sin_ne (ℓ : ℝ) (hℓ : 0 < ℓ) (j k : ℕ) (hj : 0 < j) (hk : 0 < k)
    (hjk : j ≠ k) : ∫ x in (0 : ℝ)..ℓ, sin (om ℓ j * x) * sin (om ℓ k * x) = 0 := by
  have hne : om ℓ k ^ 2 - om ℓ j ^ 2 ≠ 0 := by
    unfold om
    intro h0
    have hpi : (0 : ℝ) < π := Real.pi_pos
    have : ((k : ℝ) * π / ℓ) ^ 2 = ((j : ℝ) * π / ℓ) ^ 2 := by linarith
    have hpos : (0 : ℝ) ≤ (k : ℝ) * π / ℓ := by positivity
    have hpos' : (0 : ℝ) ≤ (j : ℝ) * π / ℓ := by positivity
    have := (sq_eq_sq₀ hpos hpos').1 this
    field_simp at this
    exact hjk (by exact_mod_cast this.symm)
  rw [integral_sin_mul_sin ℓ hℓ j _ hne, om_mul ℓ hℓ, Real.sin_nat_mul_pi]
  simp

theorem integral_sin_sq_om (ℓ : ℝ) (hℓ : 0 < ℓ) (j : ℕ) (hj : 0 < j) :
    ∫ x in (0 : ℝ)..ℓ, sin (om ℓ j * x) * sin (om ℓ j * x) = ℓ / 2 := by
  have hω : om ℓ j ≠ 0 := by unfold om; positivity
  have hd : ∀ x, HasDerivAt (fun x => x / 2 - sin (2 * om ℓ j * x) / (4 * om ℓ j))
      (sin (om ℓ j * x) * sin (om ℓ j * x)) x := fun x => by
    have := ((hasDerivAt_id x).div_const 2).sub ((hasDerivAt_sin_mul (2 * om ℓ j) x).div_const
      (4 * om ℓ j))
    refine this.congr_deriv ?_
    have hc : cos (2 * om ℓ j * x) = 1 - 2 * sin (om ℓ j * x) ^ 2 := by
      rw [mul_assoc, Real.cos_two_mul, Real.cos_sq']; ring
    rw [hc]; field_simp; ring
  rw [integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((by fun_prop : Continuous fun x => sin (om ℓ j * x) * sin (om ℓ j * x)).intervalIntegrable _ _)]
  have : 2 * om ℓ j * ℓ = ((2 * j : ℕ) : ℝ) * π := by
    rw [mul_assoc, om_mul ℓ hℓ]; push_cast; ring
  rw [this, Real.sin_nat_mul_pi]
  simp

/-- **Orthonormality** of the sine atoms on `[0, ℓ]`. -/
theorem phi_orthonormal (ℓ : ℝ) (hℓ : 0 < ℓ) (j k : ℕ) (hj : 0 < j) (hk : 0 < k) :
    ∫ x in (0 : ℝ)..ℓ, phi ℓ j x * phi ℓ k x = if j = k then 1 else 0 := by
  have e : ∀ x, phi ℓ j x * phi ℓ k x = (2 / ℓ) * (sin (om ℓ j * x) * sin (om ℓ k * x)) := by
    intro x
    unfold phi
    have h2 : √(2 / ℓ) * √(2 / ℓ) = 2 / ℓ := Real.mul_self_sqrt (by positivity)
    calc √(2 / ℓ) * sin (om ℓ j * x) * (√(2 / ℓ) * sin (om ℓ k * x))
        = (√(2 / ℓ) * √(2 / ℓ)) * (sin (om ℓ j * x) * sin (om ℓ k * x)) := by ring
      _ = _ := by rw [h2]
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul]
  split_ifs with hjk
  · subst hjk; rw [integral_sin_sq_om ℓ hℓ j hj]; field_simp
  · rw [integral_sin_mul_sin_ne ℓ hℓ j k hj hk hjk, mul_zero]

/-! ### The `ψ̂ / ρ̂` split -/

/-- **Heart R8.1.** `(t/ω)² S_j − (t/ω)⁴ S_j = −√(2/ℓ)(−1)^j t² sin(tℓ)/ω³`: removing the boundary
profile from `ψ̂_j = (t/ω_j)² S_j` leaves exactly `ρ̂_j = (t/ω_j)⁴ S_j`. -/
theorem rhoHat_eq (ℓ : ℝ) (hℓ : 0 < ℓ) (j : ℕ) (hj : 0 < j) (t : ℝ)
    (h : t ^ 2 - om ℓ j ^ 2 ≠ 0) :
    (t / om ℓ j) ^ 2 * sineT ℓ (phi ℓ j) t - (t / om ℓ j) ^ 4 * sineT ℓ (phi ℓ j) t
      = -(√(2 / ℓ) * (-1) ^ j * t ^ 2 * sin (t * ℓ) / om ℓ j ^ 3) := by
  have hω : om ℓ j ≠ 0 := by unfold om; positivity
  rw [sineTransform_phi ℓ hℓ j t h]
  field_simp
  ring

/-! ### Finite combinations and the mass majorant -/

/-- The sine transform of `g = Σ_{j∈s} c_j φ_j`. -/
theorem sineTransform_sum (ℓ : ℝ) (hℓ : 0 < ℓ) (s : Finset ℕ) (c : ℕ → ℝ) (t : ℝ)
    (h : ∀ j ∈ s, t ^ 2 - om ℓ j ^ 2 ≠ 0) :
    sineT ℓ (fun x => ∑ j ∈ s, c j * phi ℓ j x) t
      = √(2 / ℓ) * sin (t * ℓ) * ∑ j ∈ s, c j * ((-1) ^ j * om ℓ j / (t ^ 2 - om ℓ j ^ 2)) := by
  unfold sineT
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum (fun j _ => by
    unfold phi; exact (by fun_prop : Continuous fun x =>
      c j * (√(2 / ℓ) * sin (om ℓ j * x)) * sin (t * x)).intervalIntegrable _ _)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  have := sineTransform_phi ℓ hℓ j t (h j hj)
  unfold sineT at this
  simp_rw [mul_assoc] at this
  rw [this]
  ring

/-- `‖Σ c_j φ_j‖²_{L²(0,ℓ)} = Σ c_j²` (Parseval on the finite span). -/
theorem integral_sq_sum_phi (ℓ : ℝ) (hℓ : 0 < ℓ) (s : Finset ℕ) (hs : ∀ j ∈ s, 0 < j)
    (c : ℕ → ℝ) :
    ∫ x in (0 : ℝ)..ℓ, (∑ j ∈ s, c j * phi ℓ j x) ^ 2 = ∑ j ∈ s, c j ^ 2 := by
  have hint : ∀ j k, IntervalIntegrable (fun x => c j * phi ℓ j x * (c k * phi ℓ k x))
      MeasureTheory.volume 0 ℓ := fun j k => by
    unfold phi
    exact (by fun_prop : Continuous fun x =>
      c j * (√(2 / ℓ) * sin (om ℓ j * x)) * (c k * (√(2 / ℓ) * sin (om ℓ k * x)))).intervalIntegrable _ _
  simp_rw [sq, Finset.sum_mul_sum]
  rw [intervalIntegral.integral_finsetSum (fun j _ => by
    apply Continuous.intervalIntegrable; unfold phi; fun_prop)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [intervalIntegral.integral_finsetSum (fun k _ => hint j k)]
  have e : ∀ k ∈ s, ∫ x in (0 : ℝ)..ℓ, c j * phi ℓ j x * (c k * phi ℓ k x)
      = c j * c k * (if j = k then 1 else 0) := fun k hk => by
    rw [← phi_orthonormal ℓ hℓ j k (hs j hj) (hs k hk), ← intervalIntegral.integral_const_mul]
    congr 1; ext x; ring
  rw [Finset.sum_congr rfl e]
  simp [Finset.sum_ite_eq, hj]

/-- **Heart R8b.3, the Cauchy–Schwarz mass majorant.** For `g = Σ_{j∈s} c_j φ_j` and `t` off the
mode frequencies, `ĝ(t)² ≤ (2/ℓ) sin²(tℓ) ‖g‖² Σ_{j∈s} ω_j²/(t² − ω_j²)²`. -/
theorem sq_sineTransform_le (ℓ : ℝ) (hℓ : 0 < ℓ) (s : Finset ℕ) (hs : ∀ j ∈ s, 0 < j)
    (c : ℕ → ℝ) (t : ℝ) (h : ∀ j ∈ s, t ^ 2 - om ℓ j ^ 2 ≠ 0) :
    (sineT ℓ (fun x => ∑ j ∈ s, c j * phi ℓ j x) t) ^ 2
      ≤ (2 / ℓ) * sin (t * ℓ) ^ 2 * (∫ x in (0 : ℝ)..ℓ, (∑ j ∈ s, c j * phi ℓ j x) ^ 2)
        * ∑ j ∈ s, om ℓ j ^ 2 / (t ^ 2 - om ℓ j ^ 2) ^ 2 := by
  rw [sineTransform_sum ℓ hℓ s c t h, integral_sq_sum_phi ℓ hℓ s hs c]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq s c (fun j => (-1) ^ j * om ℓ j / (t ^ 2 - om ℓ j ^ 2))
  have hg : ∀ j ∈ s, ((-1 : ℝ) ^ j * om ℓ j / (t ^ 2 - om ℓ j ^ 2)) ^ 2
      = om ℓ j ^ 2 / (t ^ 2 - om ℓ j ^ 2) ^ 2 := fun j _ => by
    rw [div_pow, mul_pow, ← pow_mul, mul_comm j 2, pow_mul]; norm_num
  rw [Finset.sum_congr rfl hg] at cs
  have h2 : √(2 / ℓ) ^ 2 = 2 / ℓ := Real.sq_sqrt (by positivity)
  calc (√(2 / ℓ) * sin (t * ℓ) * ∑ j ∈ s, c j * ((-1) ^ j * om ℓ j / (t ^ 2 - om ℓ j ^ 2))) ^ 2
      = (2 / ℓ) * sin (t * ℓ) ^ 2
          * (∑ j ∈ s, c j * ((-1) ^ j * om ℓ j / (t ^ 2 - om ℓ j ^ 2))) ^ 2 := by
        rw [mul_pow, mul_pow, h2]
    _ ≤ (2 / ℓ) * sin (t * ℓ) ^ 2 * ((∑ j ∈ s, c j ^ 2)
          * ∑ j ∈ s, om ℓ j ^ 2 / (t ^ 2 - om ℓ j ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_left cs (by positivity)
    _ = _ := by ring

end GppOddFaceAtoms

#print axioms GppOddFaceAtoms.sineTransform_phi
#print axioms GppOddFaceAtoms.phi_orthonormal
#print axioms GppOddFaceAtoms.rhoHat_eq
#print axioms GppOddFaceAtoms.sq_sineTransform_le
