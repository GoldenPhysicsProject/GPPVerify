import Mathlib.Tactic
import GppVerify.StandardModel.OrientationMassTime

namespace GppOrientationMassTime

theorem fourth_power_eq_fourth_power_cases (z w : ℂ) (h : z ^ 4 = w ^ 4) :
    z = w ∨ z = -w ∨ z = Complex.I * w ∨ z = -Complex.I * w := by
  have hfac :
      (z - w) * (z + w) * (z - Complex.I * w) * (z + Complex.I * w) = 0 := by
    calc
      (z - w) * (z + w) * (z - Complex.I * w) * (z + Complex.I * w)
          = z ^ 4 - w ^ 4 := by
              ring_nf
              simp [Complex.I_mul_I]
              ring
      _ = 0 := sub_eq_zero.mpr h
  rcases mul_eq_zero.mp hfac with h123 | h4
  · rcases mul_eq_zero.mp h123 with h12 | h3
    · rcases mul_eq_zero.mp h12 with h1 | h2
      · exact Or.inl (sub_eq_zero.mp h1)
      · right; left
        linear_combination h2
    · right; right; left
      exact sub_eq_zero.mp h3
  · right; right; right
    linear_combination h4

theorem norm_eq_of_fourth_power_eq (z w : ℂ) (h : z ^ 4 = w ^ 4) :
    ‖z‖ = ‖w‖ := by
  rcases fourth_power_eq_fourth_power_cases z w h with hz | hz | hz | hz
  · simpa [hz]
  · simpa [hz]
  · rw [hz, norm_mul]
    simp
  · rw [hz, norm_mul]
    simp

theorem eigenvalue_fourth_root_classification
    (M : Matrix (Fin 4) (Fin 4) ℂ) (D λ : ℂ) (v : Fin 4 → ℂ)
    (hM4 : M * M * (M * M) = D ^ 4 • (1 : Matrix (Fin 4) (Fin 4) ℂ))
    (hv : v ≠ 0)
    (heig : M *ᵥ v = λ • v) :
    λ = D ∨ λ = -D ∨ λ = Complex.I * D ∨ λ = -Complex.I * D := by
  apply fourth_power_eq_fourth_power_cases
  exact jacobianNumerator_eigenvalue_fourth_power M D λ v hM4 hv heig

theorem eigenvalue_norm_eq_det_norm
    (M : Matrix (Fin 4) (Fin 4) ℂ) (D λ : ℂ) (v : Fin 4 → ℂ)
    (hM4 : M * M * (M * M) = D ^ 4 • (1 : Matrix (Fin 4) (Fin 4) ℂ))
    (hv : v ≠ 0)
    (heig : M *ᵥ v = λ • v) :
    ‖λ‖ = ‖D‖ := by
  apply norm_eq_of_fourth_power_eq
  exact jacobianNumerator_eigenvalue_fourth_power M D λ v hM4 hv heig

def universalLC (p : ℂ × ℂ × ℂ × ℂ) : ℂ × ℂ × ℂ × ℂ :=
  (-p.2.1, -p.2.2.2, p.1, p.2.2.1)

theorem universalLC_four (p : ℂ × ℂ × ℂ × ℂ) :
    universalLC (universalLC (universalLC (universalLC p))) = p := by
  rcases p with ⟨x1,x2,x3,x4⟩
  rfl

theorem universalLC_mode_one :
    universalLC ((1 : ℂ), -1, 1, 1) = ((1 : ℂ), -1, 1, 1) := by
  norm_num [universalLC]

theorem universalLC_mode_neg_one :
    universalLC ((1 : ℂ), 1, -1, 1) = ((-1 : ℂ), -1, 1, -1) := by
  norm_num [universalLC]

theorem universalLC_mode_I :
    universalLC ((1 : ℂ), -Complex.I, -Complex.I, -1)
      = (Complex.I, 1, 1, -Complex.I) := by
  simp [universalLC]

theorem universalLC_mode_neg_I :
    universalLC ((1 : ℂ), Complex.I, Complex.I, -1)
      = (-Complex.I, 1, 1, Complex.I) := by
  simp [universalLC]

end GppOrientationMassTime
