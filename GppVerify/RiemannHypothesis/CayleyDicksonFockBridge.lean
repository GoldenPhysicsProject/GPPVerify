import GppVerify.RiemannHypothesis.PrimeFermionDirac
import GppVerify.StandardModel.ThreeGenerations
import Mathlib.Tactic

/-!
# Cayley--Dickson / finite-prime Fock bridge

The finite-prime fermionic construction and the Cayley--Dickson tower share one exact
structural operation: adjoining one new binary generator doubles the dimension.

For `n` fermionic prime channels, the exterior/Fock state count is `2^n`.  The
Cayley--Dickson vector-space dimension after `n` doublings is also `2^n`.  Hence their
dimension recursions agree exactly:

`1 -> 2 -> 4 -> 8 -> 16 -> ...`.

This file formalizes that common doubling skeleton and the finite-prime Hodge energy built
from the already-formalized one-prime Euler holonomies.  It deliberately does not identify
the Cayley--Dickson multiplication law with the exterior/CAR product: those are different
algebraic structures.  The next operator layer is the finite CAR/Koszul complex whose
Dirac square should realize the Hodge energy below.
-/

namespace GppCayleyFock

open Complex

/-- Number of basis states in the fermionic Fock space of `n` binary prime channels. -/
def fockDim (n : ℕ) : ℕ := 2 ^ n

/-- Real vector-space dimension after `n` Cayley--Dickson doublings. -/
def cayleyDicksonDim (n : ℕ) : ℕ := GppSM.cdDim n

/-- The two constructions have exactly the same dimension sequence. -/
theorem fockDim_eq_cayleyDicksonDim (n : ℕ) :
    fockDim n = cayleyDicksonDim n := by
  rfl

/-- Adding one fermionic channel doubles the Fock dimension. -/
theorem fockDim_succ (n : ℕ) : fockDim (n + 1) = 2 * fockDim n := by
  simp [fockDim, pow_succ']

/-- One Cayley--Dickson step doubles the vector-space dimension. -/
theorem cayleyDicksonDim_succ (n : ℕ) :
    cayleyDicksonDim (n + 1) = 2 * cayleyDicksonDim n := by
  simp [cayleyDicksonDim, GppSM.cdDim, pow_succ']

/-- Adding one channel doubles both constructions in exactly the same way. -/
theorem common_doubling_step (n : ℕ) :
    fockDim (n + 1) = 2 * fockDim n ∧
      cayleyDicksonDim (n + 1) = 2 * cayleyDicksonDim n := by
  exact ⟨fockDim_succ n, cayleyDicksonDim_succ n⟩

/-- The first four common dimensions are exactly `1,2,4,8`. -/
theorem first_four_common_dimensions :
    (fockDim 0, fockDim 1, fockDim 2, fockDim 3) = (1, 2, 4, 8) := by
  norm_num [fockDim]

/-- Three binary fermionic channels have eight Fock basis states, matching the octonionic
Cayley--Dickson stage at the level of real dimension. -/
theorem three_channel_dimension :
    fockDim 3 = 8 ∧ cayleyDicksonDim 3 = 8 := by
  norm_num [fockDim, cayleyDicksonDim, GppSM.cdDim]

/-- The fourth doubling produces dimension `16` on both sides.  On the Cayley--Dickson
side this is the sedenion stage and no longer lies in the normed-division-algebra dimension
set formalized in `ThreeGenerations.lean`; on the Fock side it remains an ordinary
four-channel state-space dimension. -/
theorem fourth_doubling_dimension :
    fockDim 4 = 16 ∧ cayleyDicksonDim 4 = 16 := by
  norm_num [fockDim, cayleyDicksonDim, GppSM.cdDim]

/-- A finite family of local holonomies has the canonical nonnegative Hodge energy: the
sum of the one-prime Dirac-square coefficients. -/
noncomputable def finiteHodgeEnergy {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ∑ i, Complex.normSq (z i)

/-- Finite multi-prime Hodge energy is nonnegative term by term. -/
theorem finiteHodgeEnergy_nonneg {n : ℕ} (z : Fin n → ℂ) :
    0 ≤ finiteHodgeEnergy z := by
  unfold finiteHodgeEnergy
  exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (z i)

/-- The Hodge energy vanishes exactly when every local holonomy vanishes. -/
theorem finiteHodgeEnergy_eq_zero_iff {n : ℕ} (z : Fin n → ℂ) :
    finiteHodgeEnergy z = 0 ↔ ∀ i, z i = 0 := by
  constructor
  · intro h i
    have hnonneg : ∀ j ∈ Finset.univ, 0 ≤ Complex.normSq (z j) := by
      intro j _
      exact Complex.normSq_nonneg (z j)
    have hi : Complex.normSq (z i) = 0 := by
      apply Finset.sum_eq_zero_iff_of_nonneg hnonneg |>.mp
      · simpa [finiteHodgeEnergy] using h
      · simp
    exact Complex.normSq_eq_zero.mp hi
  · intro h
    simp [finiteHodgeEnergy, h]

/-- For a concrete finite prime family, substitute the actual Euler holonomies
`1 - exp(-s log p)` into the same positive sum. -/
noncomputable def finitePrimeHodgeEnergy {n : ℕ} (p : Fin n → ℝ) (s : ℂ) : ℝ :=
  finiteHodgeEnergy (fun i => GppPrimeFermion.eulerHolonomy (p i) s)

/-- The finite-prime Hodge energy is nonnegative for every complex spectral parameter. -/
theorem finitePrimeHodgeEnergy_nonneg {n : ℕ} (p : Fin n → ℝ) (s : ℂ) :
    0 ≤ finitePrimeHodgeEnergy p s := by
  exact finiteHodgeEnergy_nonneg _

/-- The finite-prime Hodge energy can vanish only when every Euler holonomy in the family
vanishes simultaneously. -/
theorem finitePrimeHodgeEnergy_eq_zero_iff {n : ℕ} (p : Fin n → ℝ) (s : ℂ) :
    finitePrimeHodgeEnergy p s = 0 ↔
      ∀ i, GppPrimeFermion.eulerHolonomy (p i) s = 0 := by
  exact finiteHodgeEnergy_eq_zero_iff _

/-- On the critical line, any nonempty finite family of genuine prime-scale channels has
strictly positive Hodge energy provided every channel satisfies `p_i > 1`. -/
theorem finitePrimeHodgeEnergy_critical_pos {n : ℕ} [NeZero n]
    (p : Fin n → ℝ) (hp : ∀ i, 1 < p i) (t : ℝ) :
    0 < finitePrimeHodgeEnergy p (1 / 2 + t * Complex.I) := by
  have hne : finitePrimeHodgeEnergy p (1 / 2 + t * Complex.I) ≠ 0 := by
    intro hzero
    have hall := (finitePrimeHodgeEnergy_eq_zero_iff p _).mp hzero
    let i : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
    exact GppPrimeFermion.eulerHolonomy_critical_ne_zero (hp i) t (hall i)
  exact lt_of_le_of_ne (finitePrimeHodgeEnergy_nonneg p _) (Ne.symm hne)

end GppCayleyFock

#check @GppCayleyFock.fockDim_eq_cayleyDicksonDim
#check @GppCayleyFock.common_doubling_step
#check @GppCayleyFock.first_four_common_dimensions
#check @GppCayleyFock.finiteHodgeEnergy_nonneg
#check @GppCayleyFock.finiteHodgeEnergy_eq_zero_iff
#check @GppCayleyFock.finitePrimeHodgeEnergy_critical_pos
