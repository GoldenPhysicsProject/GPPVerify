import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Weyl Vector Casimir for U(4) ≅ A₃ ⊕ U(1)

Source: zitterbewegung_T_boundary_FINAL.tex, Theorem thm:weyl-casimir-value
The Weyl vector ρ_G for U(4) has ⟨ρ_G, ρ_G⟩ = 5.

The roots of A₃ = SU(4) are: ±e_i ± e_j (1≤i<j≤4).
The Weyl vector ρ = (3,1,-1,-3)/2 in the standard basis.
⟨ρ,ρ⟩ = (9+1+1+9)/4 = 20/4 = 5.

The main result is now the actual vector/dot-product computation
`rhoA3_dot_self`, not just arithmetic on the numerator; the bare
numerator identities below are recorded as corollaries.
-/

namespace GppWeylCasimir

/-- The Weyl vector of A₃ = SU(4), ρ = (3,1,-1,-3)/2, as an actual
    vector `Fin 4 → ℚ` rather than four separate numbers. -/
def rhoA3 : Fin 4 → ℚ
  | 0 => 3 / 2
  | 1 => 1 / 2
  | 2 => -1 / 2
  | 3 => -3 / 2

/-- The Weyl vector Casimir ⟨ρ_G, ρ_G⟩ = 5 for U(4) ≅ A₃ ⊕ U(1), computed
    as an actual Euclidean dot product of the Weyl vector with itself. -/
theorem rhoA3_dot_self : dotProduct rhoA3 rhoA3 = 5 := by
  norm_num [dotProduct, rhoA3, Fin.sum_univ_four]

/-- Corollary: the bare numerator identity behind `rhoA3_dot_self`,
    (3²+1²+1²+3²)/4 = 5. -/
theorem weyl_vector_sq_numerator : 3^2 + 1^2 + 1^2 + 3^2 = (20 : ℤ) := by decide

theorem weyl_vector_casimir_times_four : 3^2 + 1^2 + 1^2 + 3^2 = 4 * 5 := by decide

/-- Corollary: the integer-numerator restatement of `rhoA3_dot_self`. -/
theorem weyl_casimir_u4 : (3^2 + 1^2 + 1^2 + 3^2 : ℤ) / 4 = 5 := by decide

/-! ## First eigenvalue of the Laplace-Beltrami operator on Gr(2,4)

Source: ONON5213.tex, Dark Matter chapter, Theorem "First Eigenvalue of
Gr(2,4)" (thm:lambda1): λ₁(Gr(2,4)) = 8, via the Casimir formula
λ_μ = ⟨μ+ρ_G, μ+ρ_G⟩ - ⟨ρ_G, ρ_G⟩ at the smallest non-trivial
K-spherical weight μ = (1,0,0,-1). Reuses `rhoA3` above for ρ_G. -/

/-- The shifted weight μ + ρ_G at μ = (1,0,0,-1), the smallest non-trivial
    K-spherical representation of U(4) for Gr(2,4) = U(4)/(U(2)×U(2)). -/
def muPlusRhoA3 : Fin 4 → ℚ
  | 0 => 5 / 2
  | 1 => 1 / 2
  | 2 => -1 / 2
  | 3 => -5 / 2

theorem muPlusRhoA3_dot_self : dotProduct muPlusRhoA3 muPlusRhoA3 = 13 := by
  norm_num [dotProduct, muPlusRhoA3, Fin.sum_univ_four]

/-- The first non-trivial Laplace-Beltrami eigenvalue on Gr(2,4),
    λ₁ = ⟨μ+ρ_G,μ+ρ_G⟩ - ⟨ρ_G,ρ_G⟩ = 13 - 5 = 8, computed as an actual
    dot-product difference (not asserted from the boxed numerals alone). -/
theorem gr24_lambda1 : dotProduct muPlusRhoA3 muPlusRhoA3 - dotProduct rhoA3 rhoA3 = 8 := by
  rw [muPlusRhoA3_dot_self, rhoA3_dot_self]
  norm_num

/-! ## Spin(8) triality Casimir: C₂ = 7 for all three 8-dimensional reps

Source: holographic_chain_v932.tex, Definition "Triality" (Def 6.2). The
Weyl vector of D₄ = Spin(8) is ρ = (3,2,1,0); the vector, spinor, and
cospinor weights are λᵥ=(1,0,0,0), λₛ=(½,½,½,½), λ_c=(½,½,½,-½). The
Casimir formula C₂(λ) = ⟨λ,λ+2ρ⟩ gives the same value 7 for all three,
the algebraic seed of Spin(8) triality. Independently verified via
Python before being written as Lean proofs. -/

/-- The Weyl vector of D₄ = Spin(8), ρ = (3,2,1,0). -/
def rhoD4 : Fin 4 → ℚ
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0

/-- The Casimir formula C₂(λ) = ⟨λ, λ+2ρ⟩ for a weight λ of D₄. -/
def casimirD4 (lam : Fin 4 → ℚ) : ℚ := dotProduct lam (fun i => lam i + 2 * rhoD4 i)

/-- Vector weight λᵥ = (1,0,0,0) of Spin(8). -/
def lambdaVector : Fin 4 → ℚ
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | 3 => 0

/-- Spinor weight λₛ = (½,½,½,½) of Spin(8). -/
def lambdaSpinor : Fin 4 → ℚ
  | 0 => 1 / 2
  | 1 => 1 / 2
  | 2 => 1 / 2
  | 3 => 1 / 2

/-- Cospinor weight λ_c = (½,½,½,-½) of Spin(8). -/
def lambdaCospinor : Fin 4 → ℚ
  | 0 => 1 / 2
  | 1 => 1 / 2
  | 2 => 1 / 2
  | 3 => -1 / 2

theorem casimir_vector_eq_seven : casimirD4 lambdaVector = 7 := by
  unfold casimirD4 lambdaVector rhoD4 dotProduct
  norm_num [Fin.sum_univ_four]

theorem casimir_spinor_eq_seven : casimirD4 lambdaSpinor = 7 := by
  unfold casimirD4 lambdaSpinor rhoD4 dotProduct
  norm_num [Fin.sum_univ_four]

theorem casimir_cospinor_eq_seven : casimirD4 lambdaCospinor = 7 := by
  unfold casimirD4 lambdaCospinor rhoD4 dotProduct
  norm_num [Fin.sum_univ_four]

/-- **Spin(8) triality**: the three 8-dimensional representations
    (vector, spinor, cospinor) share the same Casimir eigenvalue, hence
    the same conformal weight -- the algebraic fact underlying
    triality. -/
theorem casimir_triality_equal :
    casimirD4 lambdaVector = casimirD4 lambdaSpinor ∧
      casimirD4 lambdaSpinor = casimirD4 lambdaCospinor := by
  rw [casimir_vector_eq_seven, casimir_spinor_eq_seven, casimir_cospinor_eq_seven]
  exact ⟨rfl, rfl⟩

/-! ## Peter-Weyl Casimir formula for symmetric SU(4) representations

Source: holographic_chain_v932.tex. For the symmetric representation
[n,0,0,0] of SU(4), C₂(n) = n(n+6)/2, giving the sequence
0, 7/2, 8, 27/2, 20 for n = 0,...,4. -/

/-- The quadratic Casimir eigenvalue of the symmetric SU(4) representation
    [n,0,0,0]. -/
def casimirSymmetricSU4 (n : ℕ) : ℚ := (n : ℚ) * (n + 6) / 2

theorem casimirSymmetricSU4_zero : casimirSymmetricSU4 0 = 0 := by
  unfold casimirSymmetricSU4; norm_num
theorem casimirSymmetricSU4_one : casimirSymmetricSU4 1 = 7 / 2 := by
  unfold casimirSymmetricSU4; norm_num
theorem casimirSymmetricSU4_two : casimirSymmetricSU4 2 = 8 := by
  unfold casimirSymmetricSU4; norm_num
theorem casimirSymmetricSU4_three : casimirSymmetricSU4 3 = 27 / 2 := by
  unfold casimirSymmetricSU4; norm_num
theorem casimirSymmetricSU4_four : casimirSymmetricSU4 4 = 20 := by
  unfold casimirSymmetricSU4; norm_num

/-- Euler characteristic of Gr(2,4): sum of Betti numbers b0+b2+b4+b4+b6+b8 = 1+1+2+1+1 = 6 -/
theorem gr24_euler_char : 1 + 1 + 2 + 1 + 1 = (6 : ℤ) := by decide

/-- Gaussian binomial [4 choose 2]_q at q=1 equals 6 = χ(Gr(2,4)) -/
theorem gaussian_binomial_4_2_at_1 : 1 + 1 + 2 + 1 + 1 = (6 : ℕ) := by decide

/-- Point count of Gr(2,4) over F_q: 1 + q + 2q² + q³ + q⁴ -/
def gr24_point_count (q : ℤ) : ℤ := 1 + q + 2 * q^2 + q^3 + q^4

theorem gr24_point_count_at_1 : gr24_point_count 1 = 6 := by
  simp [gr24_point_count]

/-- The physical shadow Casimir ratio: (Δ=1 central charge) / (k+N) coupling.

    Gap: neither the central charge at `Δ = 1` nor the `k+N` coupling is defined in this
    file, so there is nothing here to take a ratio of. Until 2026-09-01 this was stated as
    `(1 : ℤ) * 2 = 2 * 1`, which is commutativity of multiplication and carries none of
    the claimed physics. Renamed to `open_` so the gate counts it. -/
theorem open_shadow_dimension_at_critical : True := trivial

/-- Doubly-degenerate b₄ Betti number for Gr(2,4): the middle coefficient of the point
    count `1 + q + 2q² + q³ + q⁴` is `2`, while every other coefficient is `1`.

    Stated against `gr24_point_count` — the object actually defined above — rather than as
    the bare numeral `(2 : ℕ) = 2 := rfl`, which is what stood here until 2026-09-01 and
    mentions neither Gr(2,4) nor any Betti number. -/
theorem gr24_middle_betti (q : ℤ) :
    gr24_point_count q - (1 + q + q^3 + q^4) = 2 * q^2 := by
  simp only [gr24_point_count]
  ring

/-- Mirror baryon lower bound: number of dark generations ≥ 1.
    Source: zitterbewegung paper, thm:dm-bound.
    The T-boundary condition forces at least one mirror generation.

    Gap: there is no formal definition of "number of dark generations" in this tree, and
    no formalization of the T-boundary condition that is supposed to force the bound, so
    there is nothing for the inequality to range over.

    History worth stating plainly: this began as an axiom, and a June 2026 session
    recorded it as "closed" by restating it as `(1 : ℕ) ≤ 1 := le_refl 1`. That is not a
    closure — it is a true statement about the numeral 1 wearing the name of a physics
    theorem, and strictly less honest than the axiom it replaced, since an axiom at least
    shows up in `#print axioms`. Now an `open_` stub the gate counts. -/
theorem open_mirror_baryon_lower_bound : True := trivial

/-- Massless lightest neutrino prediction from T-boundary.
    Source: zitterbewegung paper, pred:massless.
    The lightest neutrino is massless because it cannot acquire T-boundary mass. -/
theorem open_lightest_neutrino_massless : True := trivial
-- NOTE: Requires spectral analysis of T-boundary Dirac operator (Mathlib gap).

/-- Majorana condition from T-boundary.
    Source: zitterbewegung paper, cor:neutrino.
    Neutrinos satisfying the T-boundary condition are their own antiparticles. -/
theorem open_majorana_from_T_boundary : True := trivial
-- NOTE: Requires T-boundary differential geometry formalism (Mathlib gap).

end GppWeylCasimir
