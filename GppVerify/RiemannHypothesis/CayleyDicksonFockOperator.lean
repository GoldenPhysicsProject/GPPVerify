import GppVerify.RiemannHypothesis.CayleyDicksonFockBridge
import Mathlib.Tactic

/-!
# Abstract finite CAR/Koszul operator layer

This file isolates the exact algebraic hypotheses needed for the multi-channel Hodge--Dirac
identity. Rather than baking in one concrete Jordan--Wigner representation, we work with
finite matrix families satisfying the canonical anticommutation relations.

The concrete one-channel matrices are already proved in `PrimeFermionDirac.lean`;
`GPPDiscovery2/cayley_fock_multichannel.py` checks the standard Jordan--Wigner finite
realization numerically for several channel counts.

The proof is built in small kernel-checkable layers. The first structural theorem is finite
Koszul nilpotence: if the creation family anticommutes, then the weighted supercharge
`Q = Σ_i z_i c_i` satisfies `Q²=0`. The second is the full finite Hodge--Dirac square:
under the mixed CAR relation, `D = Q + Q†` obeys

`D² = (Σ_i |z_i|²) I`.
-/

namespace GppCayleyFockOperator

open Complex
open scoped BigOperators

/-- Pairing a coefficient with its conjugate produces twice its real norm-square. -/
theorem coeff_conj_pair (z : ℂ) :
    star z * z + z * star z = 2 * (Complex.normSq z : ℂ) := by
  simp only [RCLike.star_def]
  rw [mul_comm (starRingEnd ℂ z) z, Complex.mul_conj]
  ring

/-- The antisymmetric coefficient combination vanishes. -/
theorem coeff_swap_cancel (z w : ℂ) :
    z * w - w * z = 0 := by
  ring

/-- The weighted ordered-pair sum appearing after expanding a finite supercharge square. -/
noncomputable def pairSum {ι κ : Type} [Fintype ι] [Fintype κ]
    (c : ι → Matrix κ κ ℂ) (z : ι → ℂ) : Matrix κ κ ℂ :=
  ∑ i, ∑ j, (z i * z j) • (c i * c j)

/-- Swapping the two dummy indices leaves the weighted pair sum unchanged except for
swapping the operator order. -/
theorem pairSum_swap {ι κ : Type} [Fintype ι] [Fintype κ]
    (c : ι → Matrix κ κ ℂ) (z : ι → ℂ) :
    pairSum c z = ∑ i, ∑ j, (z i * z j) • (c j * c i) := by
  unfold pairSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_comm (z j) (z i)]

/-- Pairwise CAR in the creation sector makes the weighted pair sum equal to its negative. -/
theorem pairSum_eq_neg {ι κ : Type} [Fintype ι] [Fintype κ]
    (c : ι → Matrix κ κ ℂ) (z : ι → ℂ)
    (hcar : ∀ i j, c i * c j + c j * c i = 0) :
    pairSum c z = - pairSum c z := by
  nth_rewrite 1 [pairSum_swap]
  unfold pairSum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hij : c j * c i = -(c i * c j) := by
    have h := hcar j i
    exact eq_neg_of_add_eq_zero_left h
  rw [hij]
  simp

/-- **Finite creation-sector cancellation.** A weighted sum of pairwise-anticommuting
creation operators has zero quadratic pair sum. -/
theorem pairSum_eq_zero {ι κ : Type} [Fintype ι] [Fintype κ]
    (c : ι → Matrix κ κ ℂ) (z : ι → ℂ)
    (hcar : ∀ i j, c i * c j + c j * c i = 0) :
    pairSum c z = 0 := by
  have hneg := pairSum_eq_neg c z hcar
  have htwo : pairSum c z + pairSum c z = 0 := by
    nth_rewrite 1 [hneg]
    abel
  have h2 : (2 : ℂ) • pairSum c z = 0 := by
    rw [two_smul]; exact htwo
  have hscaled := congrArg (fun M : Matrix κ κ ℂ => (2 : ℂ)⁻¹ • M) h2
  simpa [smul_smul, inv_mul_cancel₀ (two_ne_zero (α := ℂ))] using hscaled

/-- Finite Koszul supercharge. -/
noncomputable def supercharge {ι κ : Type} [Fintype ι] [Fintype κ]
    (c : ι → Matrix κ κ ℂ) (z : ι → ℂ) : Matrix κ κ ℂ :=
  ∑ i, z i • c i

/-- Expanding the supercharge square gives exactly the weighted pair sum. -/
theorem supercharge_sq_eq_pairSum {ι κ : Type} [Fintype ι] [Fintype κ]
    (c : ι → Matrix κ κ ℂ) (z : ι → ℂ) :
    supercharge c z * supercharge c z = pairSum c z := by
  unfold supercharge pairSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

/-- **Finite Koszul nilpotence.** For any finite pairwise-anticommuting creation family,
`Q = Σ_i z_i c_i` satisfies `Q²=0`. -/
theorem supercharge_sq_zero {ι κ : Type} [Fintype ι] [Fintype κ]
    (c : ι → Matrix κ κ ℂ) (z : ι → ℂ)
    (hcar : ∀ i j, c i * c j + c j * c i = 0) :
    supercharge c z * supercharge c z = 0 := by
  rw [supercharge_sq_eq_pairSum]
  exact pairSum_eq_zero c z hcar

/-- The conjugate-weighted annihilation supercharge. -/
noncomputable def adjointSupercharge {ι κ : Type} [Fintype ι] [Fintype κ]
    (a : ι → Matrix κ κ ℂ) (z : ι → ℂ) : Matrix κ κ ℂ :=
  ∑ i, star (z i) • a i

/-- The finite Hodge--Dirac operator. -/
noncomputable def dirac {ι κ : Type} [Fintype ι] [Fintype κ]
    (c a : ι → Matrix κ κ ℂ) (z : ι → ℂ) : Matrix κ κ ℂ :=
  supercharge c z + adjointSupercharge a z

/-- The mixed part of `D²` can be collected with one common coefficient by swapping the
dummy indices in the second product. -/
theorem mixed_products_eq {ι κ : Type} [Fintype ι] [Fintype κ]
    (c a : ι → Matrix κ κ ℂ) (z : ι → ℂ) :
    supercharge c z * adjointSupercharge a z +
        adjointSupercharge a z * supercharge c z =
      ∑ i, ∑ j, (z i * star (z j)) • (c i * a j + a j * c i) := by
  unfold supercharge adjointSupercharge
  have e1 : (∑ i, z i • c i) * ∑ j, star (z j) • a j =
      ∑ i, ∑ j, (z i * star (z j)) • (c i * a j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have e2 : (∑ i, star (z i) • a i) * ∑ j, z j • c j =
      ∑ i, ∑ j, (z i * star (z j)) • (a j * c i) := by
    rw [Finset.sum_mul]
    have step : (∑ m, (star (z m) • a m) * ∑ n, z n • c n) =
        ∑ m, ∑ n, (star (z m) * z n) • (a m * c n) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [step, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm (star (z j)) (z i)]
  rw [e1, e2, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_add]

/-- Under the mixed CAR relation, the mixed product is the scalar Hodge energy times the
identity matrix. -/
theorem mixed_products_eq_energy {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (c a : ι → Matrix κ κ ℂ) (z : ι → ℂ)
    (hmixed : ∀ i j, c i * a j + a j * c i = if i = j then 1 else 0) :
    supercharge c z * adjointSupercharge a z +
        adjointSupercharge a z * supercharge c z =
      ((∑ i, Complex.normSq (z i) : ℝ) : ℂ) •
        (1 : Matrix κ κ ℂ) := by
  rw [mixed_products_eq]
  have hterm : ∀ i, (∑ j, (z i * star (z j)) • (c i * a j + a j * c i)) =
      (Complex.normSq (z i) : ℂ) • (1 : Matrix κ κ ℂ) := by
    intro i
    simp_rw [hmixed, smul_ite, smul_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    congr 1
    rw [RCLike.star_def]
    exact Complex.mul_conj (z i)
  simp_rw [hterm]
  rw [← Finset.sum_smul]
  norm_cast

/-- **Finite CAR/Koszul Hodge--Dirac square.** If creation and annihilation families each
anticommute and satisfy the mixed CAR relation, then the weighted Dirac square is exactly
the total nonnegative Hodge energy times the identity. -/
theorem dirac_sq_energy {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (c a : ι → Matrix κ κ ℂ) (z : ι → ℂ)
    (hcreate : ∀ i j, c i * c j + c j * c i = 0)
    (hannihilate : ∀ i j, a i * a j + a j * a i = 0)
    (hmixed : ∀ i j, c i * a j + a j * c i = if i = j then 1 else 0) :
    dirac c a z * dirac c a z =
      ((∑ i, Complex.normSq (z i) : ℝ) : ℂ) •
        (1 : Matrix κ κ ℂ) := by
  unfold dirac
  rw [add_mul, mul_add, mul_add]
  have hc := supercharge_sq_zero c z hcreate
  have ha := supercharge_sq_zero a (fun i => star (z i)) hannihilate
  have hadj :
      adjointSupercharge a z * adjointSupercharge a z = 0 := by
    simpa [adjointSupercharge, supercharge] using ha
  rw [hc, hadj, zero_add, add_zero]
  exact mixed_products_eq_energy c a z hmixed

/-- The dimension carried by an `n`-channel CAR representation is the same binary doubling
number appearing in the Cayley--Dickson bridge. -/
theorem operator_state_dimension (n : ℕ) :
    GppCayleyFock.fockDim n = GppCayleyFock.cayleyDicksonDim n :=
  GppCayleyFock.fockDim_eq_cayleyDicksonDim n

end GppCayleyFockOperator

#print axioms GppCayleyFockOperator.coeff_conj_pair
#print axioms GppCayleyFockOperator.coeff_swap_cancel
#print axioms GppCayleyFockOperator.pairSum_eq_zero
#print axioms GppCayleyFockOperator.supercharge_sq_zero
#print axioms GppCayleyFockOperator.mixed_products_eq_energy
#print axioms GppCayleyFockOperator.dirac_sq_energy
#print axioms GppCayleyFockOperator.operator_state_dimension
