import GppVerify.CelestialHolography.ArithmeticDefectPositivity

/-!
# Completed arithmetic defect criterion

The finite prime-local AFT sector now has an explicit positive factor map, but the
completed explicit formula carries the prime contribution with the opposite sign.
This file isolates the exact non-circular theorem that would make such a signed
completion positive.

For an arithmetic test state `x`, let `Ainf x` denote an Archimedean/ambient
amplitude and `Aprime x` the assembled prime amplitude. If the prime channel is
contractively dominated,

  ||Aprime x|| <= ||Ainf x||,

then the signed completed quadratic quantity

  ||Ainf x||^2 - ||Aprime x||^2

is nonnegative. If, more strongly, this defect is the norm square of a physical
quotient amplitude, positivity is an exact no-ghost identity.

This file proves the abstract and factorized criteria. It does not yet construct
the actual arithmetic transfer operator, identify the resulting defect with the
full Weil form, or prove RH.
-/

namespace GppArithmeticCompletedDefectCriterion

open GppArithmeticDefectPositivity

/-- Signed completed quadratic form associated to ambient and prime amplitudes. -/
noncomputable def completedDefect
    {X E P : Type*} [NormedAddCommGroup E] [NormedAddCommGroup P]
    (Ainf : X → E) (Aprime : X → P) (x : X) : ℝ :=
  ‖Ainf x‖ ^ 2 - ‖Aprime x‖ ^ 2

/-- Pointwise prime-channel contractivity is sufficient for positivity of the
signed completed arithmetic defect. -/
theorem completedDefect_nonneg_of_contract
    {X E P : Type*} [NormedAddCommGroup E] [NormedAddCommGroup P]
    (Ainf : X → E) (Aprime : X → P) (x : X)
    (hcontract : ‖Aprime x‖ ≤ ‖Ainf x‖) :
    0 ≤ completedDefect Ainf Aprime x := by
  unfold completedDefect
  exact normSq_sub_normSq_nonneg (Ainf x) (Aprime x) hcontract

/-- Uniform contractivity gives positivity for every arithmetic test state. -/
theorem completedDefect_nonneg
    {X E P : Type*} [NormedAddCommGroup E] [NormedAddCommGroup P]
    (Ainf : X → E) (Aprime : X → P)
    (hcontract : ∀ x, ‖Aprime x‖ ≤ ‖Ainf x‖) :
    ∀ x, 0 ≤ completedDefect Ainf Aprime x := by
  intro x
  exact completedDefect_nonneg_of_contract Ainf Aprime x (hcontract x)

/-- **Contraction-factorization bridge.** If the prime amplitude factors through
the ambient amplitude by a norm-contractive transfer map `C`, then the signed
completed defect is nonnegative for every test state. This isolates the concrete
operator construction needed by the prime-plus-Archimedean assembly: construct
`C`, prove `Aprime = C ∘ Ainf`, and prove `C` contractive. -/
theorem completedDefect_nonneg_of_contraction_factorization
    {X E P : Type*} [NormedAddCommGroup E] [NormedAddCommGroup P]
    (Ainf : X → E) (Aprime : X → P) (C : E → P)
    (hfactor : ∀ x, Aprime x = C (Ainf x))
    (hC : ∀ y, ‖C y‖ ≤ ‖y‖) :
    ∀ x, 0 ≤ completedDefect Ainf Aprime x := by
  intro x
  apply completedDefect_nonneg_of_contract Ainf Aprime x
  rw [hfactor x]
  exact hC (Ainf x)

/-- Exact no-ghost form: if the signed ambient-minus-prime defect is the norm
square of a physical quotient amplitude, positivity follows without any separate
spectral assumption. -/
theorem completedDefect_nonneg_of_physical_factor
    {X E P H : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup P] [NormedAddCommGroup H]
    (Ainf : X → E) (Aprime : X → P) (Aphys : X → H) (x : X)
    (hfactor : completedDefect Ainf Aprime x = ‖Aphys x‖ ^ 2) :
    0 ≤ completedDefect Ainf Aprime x := by
  rw [hfactor]
  exact sq_nonneg ‖Aphys x‖

end GppArithmeticCompletedDefectCriterion

#print axioms GppArithmeticCompletedDefectCriterion.completedDefect_nonneg_of_contract
#print axioms GppArithmeticCompletedDefectCriterion.completedDefect_nonneg
#print axioms GppArithmeticCompletedDefectCriterion.completedDefect_nonneg_of_contraction_factorization
#print axioms GppArithmeticCompletedDefectCriterion.completedDefect_nonneg_of_physical_factor
