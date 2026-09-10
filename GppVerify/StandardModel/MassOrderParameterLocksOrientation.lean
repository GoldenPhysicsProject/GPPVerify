import Mathlib.Tactic
import GppVerify.StandardModel.FourOrientationGaugeProjection

/-!
# A nonzero signed mass/order parameter locks the two microscopic half flips

Work on the exact four-lift carrier `(++,+-,-+,--)` with relational grading

    chi = (+,-,-,+).

Define a first-order signed generator

    B_mu = mu * chi.

This is deliberately the signed generator, not the positive Hamiltonian.  Its square is

    B_mu^2 = mu^2 * 1,

so the sign/orientation disappears from the quadratic energy scale.  The relational grading
itself rectifies the signed generator:

    chi B_mu = mu * 1.

The symmetry pattern is the important point.  At `mu=0`, both microscopic half flips are
symmetries because the generator vanishes.  For nonzero fixed `mu`, either half flip sends
`B_mu -> -B_mu`, whereas the simultaneous diagonal reversal commutes with `B_mu` exactly.
Thus a nonzero order parameter reduces the discrete half-flip symmetry to the diagonal
subgroup.

This is the finite algebraic symmetry-locking mechanism sought by the orientation programme.
It does NOT yet prove that `mu` is the physical Standard-Model mass/Higgs condensate or that
the project's diagonal reversal is physical CPT.  Those identifications require the actual
spin/gauge bundle and field equations.
-/

namespace GppMassOrderParameterLocksOrientation

open GppFourOrientationGaugeProjection

/-- The relational grading squares to the identity. -/
theorem chi_sq (v : Orientation4) : chi (chi v) = v := by
  rcases v with ⟨a,b,c,d⟩
  simp [chi]

/-- `chi` is complex-linear on the finite carrier. -/
theorem chi_smul (z : ℂ) (v : Orientation4) :
    chi (z • v) = z • chi v := by
  rcases v with ⟨a,b,c,d⟩
  simp [chi]

/-- Signed first-order generator. -/
def signedGenerator (mu : ℂ) (v : Orientation4) : Orientation4 :=
  mu • chi v

/-- Squaring the signed generator removes the orientation grading. -/
theorem signedGenerator_sq (mu : ℂ) (v : Orientation4) :
    signedGenerator mu (signedGenerator mu v) = (mu*mu) • v := by
  rw [signedGenerator, chi_smul, signedGenerator, chi_sq]
  simp [smul_smul]

/-- Multiplication by the relational grading rectifies the signed generator to a scalar
    positive-energy candidate when `mu` is a nonnegative real mass scale. -/
theorem chi_rectifies_signedGenerator (mu : ℂ) (v : Orientation4) :
    chi (signedGenerator mu v) = mu • v := by
  rw [signedGenerator, chi_smul, chi_sq]

/-- The simultaneous diagonal reversal is an exact symmetry for every value of the order
    parameter. -/
theorem diagonal_reversal_commutes_generator (mu : ℂ) (v : Orientation4) :
    diagReverse (signedGenerator mu v) =
      signedGenerator mu (diagReverse v) := by
  rcases v with ⟨a,b,c,d⟩
  simp [signedGenerator, diagReverse, chi]

/-- Flipping only the representation-conjugacy orientation reverses the signed generator. -/
theorem representation_half_flip_anticommutes_generator (mu : ℂ) (v : Orientation4) :
    signedGenerator mu (chargeFlip v) =
      - chargeFlip (signedGenerator mu v) := by
  rcases v with ⟨a,b,c,d⟩
  simp [signedGenerator, chargeFlip, chi]

/-- Flipping only the microscopic temporal orientation does the same. -/
theorem temporal_half_flip_anticommutes_generator (mu : ℂ) (v : Orientation4) :
    signedGenerator mu (temporalFlip v) =
      - temporalFlip (signedGenerator mu v) := by
  rcases v with ⟨a,b,c,d⟩
  simp [signedGenerator, temporalFlip, chi]

/-- At the symmetric point `mu=0`, both half flips commute with the vanishing generator. -/
theorem zero_order_parameter_restores_half_flip_symmetry (v : Orientation4) :
    signedGenerator 0 (chargeFlip v) = chargeFlip (signedGenerator 0 v) ∧
    signedGenerator 0 (temporalFlip v) = temporalFlip (signedGenerator 0 v) := by
  rcases v with ⟨a,b,c,d⟩
  simp [signedGenerator, chargeFlip, temporalFlip, chi]

/-- For nonzero `mu`, the representation half flip cannot commute with the generator on all
    states. -/
theorem nonzero_mu_breaks_representation_half_flip
    (mu : ℂ) (hmu : mu ≠ 0) :
    ¬ (∀ v : Orientation4,
      signedGenerator mu (chargeFlip v) = chargeFlip (signedGenerator mu v)) := by
  intro h
  have hv := h matterLift
  have hc := congrArg (fun v : Orientation4 => v.2.1) hv
  simp [signedGenerator, chargeFlip, chi, matterLift] at hc
  have hsum := congrArg (fun z : ℂ => z + mu) hc
  have h2 : (2 : ℂ) * mu = 0 := by
    simpa [two_mul, add_comm] using hsum.symm
  exact hmu ((mul_eq_zero.mp h2).resolve_left (by norm_num))

/-- Likewise for the microscopic temporal half flip. -/
theorem nonzero_mu_breaks_temporal_half_flip
    (mu : ℂ) (hmu : mu ≠ 0) :
    ¬ (∀ v : Orientation4,
      signedGenerator mu (temporalFlip v) = temporalFlip (signedGenerator mu v)) := by
  intro h
  have hv := h matterLift
  have hc := congrArg (fun v : Orientation4 => v.2.1) hv
  simp [signedGenerator, temporalFlip, chi, matterLift] at hc
  have hsum := congrArg (fun z : ℂ => z + mu) hc
  have h2 : (2 : ℂ) * mu = 0 := by
    simpa [two_mul, add_comm] using hsum.symm
  exact hmu ((mul_eq_zero.mp h2).resolve_left (by norm_num))

/-- Capstone symmetry-breaking package: a nonzero order parameter preserves the diagonal
    reversal but breaks both individual half flips. -/
theorem nonzero_order_parameter_leaves_only_diagonal_pattern
    (mu : ℂ) (hmu : mu ≠ 0) :
    (∀ v : Orientation4,
      diagReverse (signedGenerator mu v) = signedGenerator mu (diagReverse v)) ∧
    ¬ (∀ v : Orientation4,
      signedGenerator mu (chargeFlip v) = chargeFlip (signedGenerator mu v)) ∧
    ¬ (∀ v : Orientation4,
      signedGenerator mu (temporalFlip v) = temporalFlip (signedGenerator mu v)) := by
  exact ⟨diagonal_reversal_commutes_generator mu,
    nonzero_mu_breaks_representation_half_flip mu hmu,
    nonzero_mu_breaks_temporal_half_flip mu hmu⟩

end GppMassOrderParameterLocksOrientation
