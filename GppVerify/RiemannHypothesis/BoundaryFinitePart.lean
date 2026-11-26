import GppVerify.RiemannHypothesis.KreinHPsi
import Mathlib.Tactic

/-!
# Two-point boundary finite part for `Kpsi`

Status labels:

* `pole_kform_eq`: **PROVED**. The pole kernel is a cosh square minus a sinh
  square for every finite configuration.
* `pole_two_point`: **PROVED**. On `x = (0, a)`, `c = (1, -sech (a / 2))`,
  the pole finite part is `-A * tanh (a / 2) ^ 2` with
  `A = 2 * bigPsiI2 ^ 2`.
* `two_point_nonneg_iff`: **PROVED**. Two-point nonnegativity of `Kpsi` is
  equivalent to prime-carrying domination of that boundary square.
* `TwoPointPrimeDomination`: **OPEN**. This file does not prove domination.
  Turbo's D6-2 audit records arch-alone domination as false at two-point
  configurations, so the prime term is load-bearing already at the boundary.
-/

namespace GppBoundaryFinitePart

open GppKreinBridge GppKreinHPsi

noncomputable section

/-- The pole coefficient `A = 2 Ψ(i/2)²`. -/
def poleCoeff : ℝ := 2 * bigPsiI2 ^ 2

theorem poleCoeff_nonneg : 0 ≤ poleCoeff := by
  unfold poleCoeff bigPsiI2
  positivity

theorem sq_sum_eq_sum_sum {n : ℕ} (c a : Fin n → ℝ) :
    (∑ i, c i * a i) ^ 2 = ∑ i, ∑ j, c i * c j * (a i * a j) := by
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **PROVED**: the pole kernel is exactly a cosh square minus a sinh square. -/
theorem pole_kform_eq {n : ℕ} (x c : Fin n → ℝ) :
    kform poleTerm x c =
      poleCoeff *
        ((∑ i, c i * Real.cosh (x i / 2)) ^ 2 -
          (∑ i, c i * Real.sinh (x i / 2)) ^ 2) := by
  have hcosh : ∀ i j : Fin n,
      Real.cosh ((x i - x j) / 2) =
        Real.cosh (x i / 2) * Real.cosh (x j / 2) -
          Real.sinh (x i / 2) * Real.sinh (x j / 2) := by
    intro i j
    have h : (x i - x j) / 2 = x i / 2 - x j / 2 := by ring
    rw [h, Real.cosh_sub]
  have h1 := sq_sum_eq_sum_sum c (fun i => Real.cosh (x i / 2))
  have h2 := sq_sum_eq_sum_sum c (fun i => Real.sinh (x i / 2))
  have hexpand :
      kform poleTerm x c =
        poleCoeff *
          (∑ i, ∑ j,
            c i * c j *
              (Real.cosh (x i / 2) * Real.cosh (x j / 2) -
                Real.sinh (x i / 2) * Real.sinh (x j / 2))) := by
    rw [kform, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [poleTerm, poleCoeff, hcosh]
    ring
  rw [hexpand, h1, h2]
  congr 1
  simp [mul_sub, Finset.sum_sub_distrib]

/-- **PROVED**: on the cosh hyperplane, the pole channel is the negative sinh square. -/
theorem pole_kform_on_hyperplane {n : ℕ} (x c : Fin n → ℝ)
    (hker : ∑ i, c i * Real.cosh (x i / 2) = 0) :
    kform poleTerm x c =
      -poleCoeff * (∑ i, c i * Real.sinh (x i / 2)) ^ 2 := by
  rw [pole_kform_eq, hker]
  ring

/-- The two-point configuration `x = (0, a)`. -/
def twoX (a : ℝ) : Fin 2 → ℝ := ![0, a]

/-- The two-point coefficient vector on the cosh hyperplane. -/
def twoC (a : ℝ) : Fin 2 → ℝ := ![1, -(Real.cosh (a / 2))⁻¹]

theorem twoC_cosh_sum (a : ℝ) :
    ∑ i, twoC a i * Real.cosh (twoX a i / 2) = 0 := by
  have h : Real.cosh (a / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  simp [twoX, twoC, Fin.sum_univ_two, h]

theorem twoC_sinh_sum (a : ℝ) :
    ∑ i, twoC a i * Real.sinh (twoX a i / 2) = -Real.tanh (a / 2) := by
  have h : Real.cosh (a / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  simp [twoX, twoC, Fin.sum_univ_two, Real.tanh_eq_sinh_div_cosh]
  ring

/-- **PROVED**: the two-point pole finite part is `-A tanh²(a/2)`. -/
theorem pole_two_point (a : ℝ) :
    kform poleTerm (twoX a) (twoC a) =
      -poleCoeff * (Real.tanh (a / 2)) ^ 2 := by
  rw [pole_kform_on_hyperplane _ _ (twoC_cosh_sum a), twoC_sinh_sum]
  ring

theorem pole_two_point_nonpos (a : ℝ) :
    kform poleTerm (twoX a) (twoC a) ≤ 0 := by
  rw [pole_two_point]
  nlinarith [poleCoeff_nonneg, sq_nonneg (Real.tanh (a / 2))]

theorem kform_Kpsi {n : ℕ} (x c : Fin n → ℝ) :
    kform Kpsi x c =
      kform poleTerm x c - kform primeTerm x c + kform archTerm x c := by
  simp [kform, Kpsi, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_add, mul_sub]

/-- **PROVED**: two-point nonnegativity of `Kpsi` is exactly prime-carrying
domination of the boundary square. -/
theorem two_point_nonneg_iff (a : ℝ) :
    0 ≤ kform Kpsi (twoX a) (twoC a) ↔
      poleCoeff * (Real.tanh (a / 2)) ^ 2 ≤
        kform archTerm (twoX a) (twoC a) - kform primeTerm (twoX a) (twoC a) := by
  rw [kform_Kpsi, pole_two_point]
  constructor <;> intro h <;> linarith

/-- **OPEN**: the remaining arithmetic hypothesis at two-point configurations. -/
def TwoPointPrimeDomination : Prop :=
  ∀ a : ℝ,
    poleCoeff * (Real.tanh (a / 2)) ^ 2 ≤
      kform archTerm (twoX a) (twoC a) - kform primeTerm (twoX a) (twoC a)

theorem two_point_nonneg_of_prime_domination
    (h : TwoPointPrimeDomination) (a : ℝ) :
    0 ≤ kform Kpsi (twoX a) (twoC a) :=
  (two_point_nonneg_iff a).2 (h a)

end

end GppBoundaryFinitePart

#print axioms GppBoundaryFinitePart.pole_kform_eq
#print axioms GppBoundaryFinitePart.pole_two_point
#print axioms GppBoundaryFinitePart.two_point_nonneg_iff
