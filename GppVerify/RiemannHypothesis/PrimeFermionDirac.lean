import GppVerify.RiemannHypothesis.EulerFactorLogDeriv
import Mathlib.Tactic

/-!
# The local Euler factor as a two-state fermionic Hodge--Dirac system

The fermion/spinor analogy can be made exact at one prime.  The exterior algebra on one
generator has an even vacuum state and an odd occupied state.  In that basis, exterior
multiplication (`create`) and contraction (`annihilate`) are `2 × 2` matrices satisfying
the canonical anticommutation relations (CAR):

`create² = annihilate² = 0`,
`create * annihilate + annihilate * create = I`.

For a complex holonomy `z`, the rank-one Koszul supercharge is `d=z·create`, and its
Hodge--Dirac operator is

`D(z)=d+d† = [[0,conj z],[z,0]]`.

This file proves that `D(z)` is self-adjoint, odd under the grading, and

`D(z)² = |z|² I`.

Taking `z=1-p^{-s}`, the inverse holonomy is exactly the previously defined local Euler
factor `zetaP p s`.  On the critical line and for `p>1`, `1-p^{-s}` never vanishes, so the
local Dirac energy is strictly positive.  Hence an isolated prime channel has no local
zero mode: any physical zero must arise from collective prime--Archimedean boundary
coupling, as suggested by the completed Möbius--Koszul program.

This is a genuine local Clifford/Koszul theorem, but not the completed infinite-prime
Dirac operator, a determinant formula for `Xi`, the global no-ghost theorem, or RH.
-/

namespace GppPrimeFermion

open Complex

/-- Exterior multiplication by the one prime generator. -/
def create : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

/-- Contraction by the one prime generator. -/
def annihilate : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- Fermion parity: `+1` on the vacuum and `-1` on the occupied state. -/
def grading : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem grading_sq : grading * grading = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [grading, Matrix.mul_apply]

theorem create_sq : create * create = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [create, Matrix.mul_apply]

theorem annihilate_sq : annihilate * annihilate = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [annihilate, Matrix.mul_apply]

/-- The one-generator canonical anticommutation relation. -/
theorem car : create * annihilate + annihilate * create = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [create, annihilate, Matrix.mul_apply]

theorem create_adjoint : Matrix.conjTranspose create = annihilate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [create, annihilate, Matrix.conjTranspose_apply]

/-- The rank-one Koszul differential with holonomy `z`. -/
noncomputable def supercharge (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  z • create

/-- Nilpotence of the local Koszul differential. -/
theorem supercharge_sq (z : ℂ) : supercharge z * supercharge z = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [supercharge, create, Matrix.mul_apply]

theorem supercharge_adjoint (z : ℂ) :
    Matrix.conjTranspose (supercharge z) = star z • annihilate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [supercharge, create, annihilate, Matrix.conjTranspose_apply]

/-- The one-prime Hodge--Dirac operator `d+d†`. -/
noncomputable def dirac (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  z • create + star z • annihilate

theorem dirac_eq_supercharge_add_adjoint (z : ℂ) :
    dirac z = supercharge z + Matrix.conjTranspose (supercharge z) := by
  rw [supercharge_adjoint]
  rfl

theorem dirac_eq (z : ℂ) : dirac z = !![0, star z; z, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dirac, create, annihilate]

theorem dirac_selfAdjoint (z : ℂ) : Matrix.conjTranspose (dirac z) = dirac z := by
  rw [dirac_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dirac, Matrix.conjTranspose_apply]

/-- The local Dirac square is the nonnegative scalar energy `normSq z`. -/
theorem dirac_sq (z : ℂ) :
    dirac z * dirac z = (Complex.normSq z : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [dirac_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply]
  · exact Complex.normSq_eq_conj_mul_self.symm
  · exact Complex.mul_conj z

/-- The Hodge--Dirac operator is odd under fermion parity. -/
theorem grading_anticommutes (z : ℂ) :
    grading * dirac z + dirac z * grading = 0 := by
  rw [dirac_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [grading, Matrix.mul_apply]

/-- The Euler holonomy whose inverse is the local Euler factor. -/
noncomputable def eulerHolonomy (p : ℝ) (s : ℂ) : ℂ :=
  1 - Complex.exp (-s * Complex.log p)

/-- The one-prime Hodge--Dirac operator. -/
noncomputable def primeDirac (p : ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  dirac (eulerHolonomy p s)

theorem zetaP_eq_eulerHolonomy_inv (p : ℝ) (s : ℂ) :
    GppCutkoskyWeil.zetaP p s = (eulerHolonomy p s)⁻¹ := by
  rfl

/-- On the critical line, the local Euler holonomy cannot vanish for `p>1`: its
exponential term has norm `p^{-1/2}<1`, whereas `1` has norm one. -/
theorem eulerHolonomy_critical_ne_zero {p : ℝ} (hp : 1 < p) (t : ℝ) :
    eulerHolonomy p (1 / 2 + t * Complex.I) ≠ 0 := by
  have hp0 : 0 < p := lt_trans one_pos hp
  have hlogpC : Complex.log (p : ℂ) = (Real.log p : ℂ) :=
    (Complex.ofReal_log hp0.le).symm
  intro hzero
  have hexp :
      Complex.exp (-(1 / 2 + t * Complex.I) * Complex.log p) = 1 := by
    exact (sub_eq_zero.mp hzero).symm
  have hnorm :
      ‖Complex.exp (-(1 / 2 + t * Complex.I) * Complex.log p)‖ = 1 := by
    rw [hexp]
    norm_num
  rw [Complex.norm_exp] at hnorm
  have hre :
      (-(1 / 2 + t * Complex.I) * Complex.log p).re =
        -(1 / 2 : ℝ) * Real.log p := by
    rw [hlogpC]
    simp [Complex.mul_re]
  rw [hre] at hnorm
  have hneg : -(1 / 2 : ℝ) * Real.log p < 0 := by
    nlinarith [Real.log_pos hp]
  have hlt : Real.exp (-(1 / 2 : ℝ) * Real.log p) < 1 :=
    Real.exp_lt_one_iff.mpr hneg
  linarith

/-- Strict positivity of the isolated prime's local Dirac energy on the critical line. -/
theorem primeDiracEnergy_critical_pos {p : ℝ} (hp : 1 < p) (t : ℝ) :
    0 < Complex.normSq (eulerHolonomy p (1 / 2 + t * Complex.I)) := by
  exact Complex.normSq_pos.mpr (eulerHolonomy_critical_ne_zero hp t)

theorem primeDirac_sq (p : ℝ) (s : ℂ) :
    primeDirac p s * primeDirac p s =
      (Complex.normSq (eulerHolonomy p s) : ℂ) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  exact dirac_sq _

end GppPrimeFermion
