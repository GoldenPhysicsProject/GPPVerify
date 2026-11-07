import GppVerify.Upstream.TwoVectorProjection
import GppVerify.RiemannHypothesis.SpectralOrbitals
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open scoped InnerProductSpace
open Submodule

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v x : E) (h : ⟪u,u⟫_ℝ * ⟪v,v⟫_ℝ - ⟪u,v⟫_ℝ ^ 2 ≠ 0) :
    letI := FiniteDimensional.span_of_finite ℝ (Set.toFinite ({u,v} : Set E))
    ‖x - (span ℝ ({u,v} : Set E)).starProjection x‖ ^ 2 =
      ‖x‖ ^ 2 - (⟪v,v⟫_ℝ * ⟪u,x⟫_ℝ ^ 2 -
        2 * ⟪u,v⟫_ℝ * ⟪u,x⟫_ℝ * ⟪v,x⟫_ℝ + ⟪u,u⟫_ℝ * ⟪v,x⟫_ℝ ^ 2) /
        (⟪u,u⟫_ℝ * ⟪v,v⟫_ℝ - ⟪u,v⟫_ℝ ^ 2) :=
  InnerProductSpace.norm_sub_starProjection_span_pair_sq u v x h

-- A nonorthogonal frame: u=(1,0,0), v=(1,1,0), x=(3,2,1).
-- det G=1, coefficients=(1,2), residual=(0,0,1), squared norm=1.
example :
    let u : EuclideanSpace ℝ (Fin 3) := !₂[1, 0, 0]
    let v : EuclideanSpace ℝ (Fin 3) := !₂[1, 1, 0]
    let x : EuclideanSpace ℝ (Fin 3) := !₂[3, 2, 1]
    ‖x - (span ℝ ({u,v} : Set (EuclideanSpace ℝ (Fin 3)))).starProjection x‖ ^ 2 = 1 := by
  dsimp only
  rw [InnerProductSpace.norm_sub_starProjection_span_pair_sq]
  · norm_num [PiLp.inner_apply, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  · norm_num [PiLp.inner_apply, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]

-- Check the projected vector as well as its residual energy.
example :
    let u : EuclideanSpace ℝ (Fin 3) := !₂[1, 0, 0]
    let v : EuclideanSpace ℝ (Fin 3) := !₂[1, 1, 0]
    let x : EuclideanSpace ℝ (Fin 3) := !₂[3, 2, 1]
    (span ℝ ({u,v} : Set (EuclideanSpace ℝ (Fin 3)))).starProjection x = !₂[3, 2, 0] := by
  dsimp only
  rw [InnerProductSpace.starProjection_span_pair]
  · norm_num [PiLp.inner_apply, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
    ext i
    fin_cases i <;> norm_num
  · norm_num [PiLp.inner_apply, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]

-- An orthogonal frame, with a nonunit second vector.
example :
    let u : EuclideanSpace ℝ (Fin 3) := !₂[1, 0, 0]
    let v : EuclideanSpace ℝ (Fin 3) := !₂[0, 2, 0]
    let x : EuclideanSpace ℝ (Fin 3) := !₂[3, 2, 1]
    ‖x - (span ℝ ({u,v} : Set (EuclideanSpace ℝ (Fin 3)))).starProjection x‖ ^ 2 = 1 := by
  dsimp only
  rw [InnerProductSpace.norm_sub_starProjection_span_pair_sq]
  · norm_num [PiLp.inner_apply, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  · norm_num [PiLp.inner_apply, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]

-- Singular control: the true projection is nonzero while Cramer's expression
-- with totalized division by zero is zero. The determinant guard is essential.
example :
    let u : EuclideanSpace ℝ (Fin 2) := !₂[1, 0]
    (span ℝ ({u,u} : Set (EuclideanSpace ℝ (Fin 2)))).starProjection u ≠
      ((⟪u,u⟫_ℝ * ⟪u,u⟫_ℝ - ⟪u,u⟫_ℝ * ⟪u,u⟫_ℝ) /
        (⟪u,u⟫_ℝ * ⟪u,u⟫_ℝ - ⟪u,u⟫_ℝ ^ 2)) • u +
      ((⟪u,u⟫_ℝ * ⟪u,u⟫_ℝ - ⟪u,u⟫_ℝ * ⟪u,u⟫_ℝ) /
        (⟪u,u⟫_ℝ * ⟪u,u⟫_ℝ - ⟪u,u⟫_ℝ ^ 2)) • u := by
  dsimp only
  simp only [Set.pair_eq_singleton, sub_self, zero_div, zero_smul, add_zero]
  rw [Submodule.starProjection_eq_self_iff.mpr (subset_span (Set.mem_singleton _))]
  intro h
  have := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) h
  norm_num at this

-- Type-level integration with the exact SpectralOrbitals parity convention.
-- No evaluation or approximation of its transcendental amplitudes is assumed.
example (K : ℕ) (W : Submodule ℝ (EuclideanSpace ℝ (Fin K × Fin K)))
    (D : EuclideanSpace ℝ (Fin K × Fin K)) (γ₁ γ₂ : ℝ)
    (h : let u := Wᗮ.starProjection (GppSpectralOrbitals.parityVec K
           (GppSpectralOrbitals.Pminus K γ₁))
         let v := Wᗮ.starProjection (GppSpectralOrbitals.parityVec K
           (GppSpectralOrbitals.Pminus K γ₂))
         ⟪u,u⟫_ℝ * ⟪v,v⟫_ℝ - ⟪u,v⟫_ℝ ^ 2 ≠ 0) :
    let u := Wᗮ.starProjection (GppSpectralOrbitals.parityVec K
      (GppSpectralOrbitals.Pminus K γ₁))
    let v := Wᗮ.starProjection (GppSpectralOrbitals.parityVec K
      (GppSpectralOrbitals.Pminus K γ₂))
    ‖D - (span ℝ ({u,v} : Set (EuclideanSpace ℝ (Fin K × Fin K)))).starProjection D‖ ^ 2 =
      ‖D‖ ^ 2 - (⟪v,v⟫_ℝ * ⟪u,D⟫_ℝ ^ 2 -
        2 * ⟪u,v⟫_ℝ * ⟪u,D⟫_ℝ * ⟪v,D⟫_ℝ + ⟪u,u⟫_ℝ * ⟪v,D⟫_ℝ ^ 2) /
        (⟪u,u⟫_ℝ * ⟪v,v⟫_ℝ - ⟪u,v⟫_ℝ ^ 2) := by
  exact InnerProductSpace.norm_sub_starProjection_span_pair_sq _ _ D h

#print axioms InnerProductSpace.starProjection_span_pair
#print axioms InnerProductSpace.norm_sub_starProjection_span_pair_sq
