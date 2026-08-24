import GppVerify.RiemannHypothesis.CayleyDicksonFockOperator
import Mathlib.Tactic

/-!
# Finite-prime Dirac specialization and a completion obstruction

This file specializes the abstract finite CAR/Koszul Hodge--Dirac theorem to the actual
Euler holonomies

  z_p(s) = 1 - exp(-s log p),

whose inverse is the local Euler factor.  It then isolates an exact obstruction for the
Archimedean/completed step: if the extra completion channel is merely Clifford-orthogonal
to the finite-prime Dirac operator and has a nonnegative scalar square, then the completed
square remains strictly positive whenever the finite-prime Hodge energy is positive.

Therefore a collective zero cannot be created by adjoining an independent positive
Clifford channel.  Any genuine completed zero mechanism must enter through a nontrivial
prime--Archimedean anticommutator/cross term, or through an infinite/renormalized limit not
captured by the finite positive scalar-square model.

No RH claim is made here.
-/

namespace GppFinitePrimeCompletion

open Complex
open scoped BigOperators

/-- The finite CAR/Koszul Dirac operator specialized to Euler holonomies. -/
noncomputable def finitePrimeDirac {n : ℕ} {κ : Type} [Fintype κ]
    (c a : Fin n → Matrix κ κ ℂ) (p : Fin n → ℝ) (s : ℂ) : Matrix κ κ ℂ :=
  GppCayleyFockOperator.dirac c a (fun i => GppPrimeFermion.eulerHolonomy (p i) s)

/-- **Exact Euler specialization.** Under the finite CAR relations, the square of the
finite-prime Dirac operator is exactly the finite Euler Hodge energy times the identity. -/
theorem finitePrimeDirac_sq {n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
    (c a : Fin n → Matrix κ κ ℂ) (p : Fin n → ℝ) (s : ℂ)
    (hcreate : ∀ i j, c i * c j + c j * c i = 0)
    (hannihilate : ∀ i j, a i * a j + a j * a i = 0)
    (hmixed : ∀ i j, c i * a j + a j * c i = if i = j then 1 else 0) :
    finitePrimeDirac c a p s * finitePrimeDirac c a p s =
      ((GppCayleyFock.finiteHodgeEnergy
          (fun i => GppPrimeFermion.eulerHolonomy (p i) s) : ℝ) : ℂ) •
        (1 : Matrix κ κ ℂ) := by
  unfold finitePrimeDirac
  simpa [GppCayleyFock.finiteHodgeEnergy] using
    (GppCayleyFockOperator.dirac_sq_energy c a
      (fun i => GppPrimeFermion.eulerHolonomy (p i) s)
      hcreate hannihilate hmixed)

/-- Adding an extra operator `A` to a Dirac operator `D`: if their anticommutator vanishes,
the square contains no prime--Archimedean cross term. -/
theorem add_sq_of_anticommute {κ : Type} [Fintype κ] [DecidableEq κ]
    (D A : Matrix κ κ ℂ) (hanti : D * A + A * D = 0) :
    (D + A) * (D + A) = D * D + A * A := by
  calc
    (D + A) * (D + A) = D * D + (D * A + A * D) + A * A := by noncomm_ring
    _ = D * D + A * A := by rw [hanti]; simp

/-- **Positive Clifford-channel obstruction.** If `D² = E I`, `A² = μ I`, and `D`
anticommutes with `A`, then `(D+A)² = (E+μ) I`.  Thus an independent Clifford completion
only adds its positive scalar energy; it cannot cancel the finite-prime energy. -/
theorem completed_sq_of_clifford_orthogonal {κ : Type} [Fintype κ] [DecidableEq κ]
    (D A : Matrix κ κ ℂ) (E μ : ℂ)
    (hD : D * D = E • (1 : Matrix κ κ ℂ))
    (hA : A * A = μ • (1 : Matrix κ κ ℂ))
    (hanti : D * A + A * D = 0) :
    (D + A) * (D + A) = (E + μ) • (1 : Matrix κ κ ℂ) := by
  rw [add_sq_of_anticommute D A hanti, hD, hA]
  exact (add_smul E μ (1 : Matrix κ κ ℂ)).symm

/-- If a completed zero occurs in the scalar-square model, the prime--Archimedean cross
term is not arbitrary: it is forced to cancel the sum of both diagonal energies exactly.
This is the algebraic target for any proposed Archimedean coupling. -/
theorem cross_term_forced_of_completed_zero {κ : Type} [Fintype κ] [DecidableEq κ]
    (D A : Matrix κ κ ℂ) (E μ : ℂ)
    (hD : D * D = E • (1 : Matrix κ κ ℂ))
    (hA : A * A = μ • (1 : Matrix κ κ ℂ))
    (hzero : (D + A) * (D + A) = 0) :
    D * A + A * D = -(E + μ) • (1 : Matrix κ κ ℂ) := by
  have hsum :
      E • (1 : Matrix κ κ ℂ) + (D * A + A * D) + μ • (1 : Matrix κ κ ℂ) = 0 := by
    calc
      E • (1 : Matrix κ κ ℂ) + (D * A + A * D) + μ • (1 : Matrix κ κ ℂ) =
          D * D + (D * A + A * D) + A * A := by rw [hD, hA]
      _ = (D + A) * (D + A) := by noncomm_ring
      _ = 0 := hzero
  have hreordered :
      (D * A + A * D) +
          (E • (1 : Matrix κ κ ℂ) + μ • (1 : Matrix κ κ ℂ)) = 0 := by
    simpa [add_assoc, add_left_comm, add_comm] using hsum
  have hcross :
      D * A + A * D =
        -(E • (1 : Matrix κ κ ℂ) + μ • (1 : Matrix κ κ ℂ)) :=
    eq_neg_of_add_eq_zero_left hreordered
  simpa [add_smul] using hcross

/-- If the scalar energies are real and the finite-prime contribution is strictly positive
while the independent completion contribution is nonnegative, their total scalar energy
cannot vanish. -/
theorem positive_energy_sum_ne_zero {E μ : ℝ} (hE : 0 < E) (hμ : 0 ≤ μ) :
    ((E + μ : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt (add_pos_of_pos_of_nonneg hE hμ)

/-- Consequently, in the scalar-square Clifford-orthogonal model, a strictly positive
finite-prime energy cannot be canceled by a nonnegative Archimedean energy. -/
theorem completed_square_nonzero_of_positive_orthogonal {κ : Type} [Fintype κ] [DecidableEq κ]
    [Nonempty κ]
    (D A : Matrix κ κ ℂ) (E μ : ℝ)
    (hE : 0 < E) (hμ : 0 ≤ μ)
    (hD : D * D = (E : ℂ) • (1 : Matrix κ κ ℂ))
    (hA : A * A = (μ : ℂ) • (1 : Matrix κ κ ℂ))
    (hanti : D * A + A * D = 0) :
    (D + A) * (D + A) ≠ 0 := by
  rw [completed_sq_of_clifford_orthogonal D A (E : ℂ) (μ : ℂ) hD hA hanti]
  intro hzero
  have hscalar : ((E + μ : ℝ) : ℂ) = 0 := by
    simpa using congrArg (fun M : Matrix κ κ ℂ => M (Classical.choice inferInstance) (Classical.choice inferInstance)) hzero
  exact positive_energy_sum_ne_zero hE hμ hscalar

end GppFinitePrimeCompletion

#print axioms GppFinitePrimeCompletion.finitePrimeDirac_sq
#print axioms GppFinitePrimeCompletion.add_sq_of_anticommute
#print axioms GppFinitePrimeCompletion.completed_sq_of_clifford_orthogonal
#print axioms GppFinitePrimeCompletion.cross_term_forced_of_completed_zero
#print axioms GppFinitePrimeCompletion.completed_square_nonzero_of_positive_orthogonal
