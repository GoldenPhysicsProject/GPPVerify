import Mathlib.Tactic

/-!
# Co-Poisson diagonal duality as an orientation template

The arithmetic-principal-series programme contains the exact co-Poisson intertwining

    I P = P C,

where `P` is arithmetic summation, `C` is the Archimedean Fourier/cosine involution and `I`
is multiplicative inversion.  Equivalently,

    P = I P C.

This has exactly the algebraic shape sought in the orientation programme: one half-operation
acts on the source representation, the other on the synthesized geometric/output variable,
and the *combined* transformation leaves the physical synthesis unchanged.

This module proves the abstract intertwiner consequences only.  The actual co-Poisson
identity is a theorem of harmonic analysis and is not reproved here.  The dictionary
`C <-> internal representation conjugation`, `I <-> microscopic temporal/scale inversion`
remains a hypothesis to test.
-/

namespace GppArithmeticCoPoissonOrientationTemplate

variable {X Y : Type}

/-- If source duality `C` is involutive and output inversion `I` intertwines a synthesis
    map `P` with `C`, then applying the two half operations together returns the original
    synthesized output. -/
theorem diagonal_duality_invariance
    (C : X → X) (I : Y → Y) (P : X → Y)
    (hC : ∀ x, C (C x) = x)
    (hinter : ∀ x, I (P x) = P (C x)) :
    ∀ x, I (P (C x)) = P x := by
  intro x
  rw [hinter, hC]

/-- A single output inversion is exactly equivalent, after synthesis, to a single source
    dualization. -/
theorem half_dualities_are_intertwined
    (C : X → X) (I : Y → Y) (P : X → Y)
    (hinter : ∀ x, I (P x) = P (C x)) :
    ∀ x, I (P x) = P (C x) := hinter

/-- If the synthesis is injective, an output fixed point under inversion corresponds to a
    source fixed point under duality. -/
theorem fixed_output_forces_fixed_source_of_injective
    (C : X → X) (I : Y → Y) (P : X → Y)
    (hinter : ∀ x, I (P x) = P (C x))
    (hPinj : Function.Injective P)
    (x : X) (hfix : I (P x) = P x) : C x = x := by
  apply hPinj
  rw [← hinter x, hfix]

end GppArithmeticCoPoissonOrientationTemplate
