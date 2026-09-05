import Mathlib.Tactic
import GppVerify.CelestialHolography.KleinPinReflectionDegeneration

/-!
# Clifford anticommutator and internal Pin-reflection conjugation

The previous modules proved separately that the epsilon/Klein bivector `p` acts on the
two chiral twistor modules by an odd Clifford operator `C(p)`, and that a non-null Klein
vector `v` defines the orthogonal reflection

  r_v(q) = q - B(q,v)/Q(v) v.

This file closes the finite-dimensional Pin bridge internally.

First, polarization gives the full Clifford relation

  C(p) C(q) + C(q) C(p) = - B_epsilon(p,q) id.

Then, for `Q(v) != 0`, the triple Clifford product satisfies

  (1/Q(v)) C(v) C(q) C(v) = C(r_v(q)).

Since `C(v)^{-1} = - C(v)/Q(v)`, the left-hand side is precisely

  - C(v) C(q) C(v)^{-1}.

Thus the same odd Clifford element which exchanges the two half-spinor modules implements
on the six-dimensional Klein module exactly the determinant-minus-one orthogonal
reflection already formalized in `KleinPinReflectionDegeneration`.

Everything in this file is coordinate algebra over the existing epsilon/Klein model; no
external Pin-group theorem is assumed.
-/

namespace GppKleinCliffordPinConjugation

open GppGrassmannianGooglyDecomposition
open GppAmbientFourDualitySpine
open GppKleinSpinorIncidence
open GppKleinPinReflectionDegeneration
open GppTwistorAnnihilatorIncidence

/-- Componentwise addition on the four-dimensional twistor carrier. -/
def addV4 (x y : V4) : V4 :=
  (x.1+y.1, x.2.1+y.2.1, x.2.2.1+y.2.2.1, x.2.2.2+y.2.2.2)

/-- Componentwise scaling on the Dirac sum of the two chiral twistor modules. -/
def scaleDirac (a : ℝ) (psi : DiracTwistor) : DiracTwistor :=
  (scale4 a psi.1, scale4 a psi.2)

/-- Componentwise addition on the Dirac sum. -/
def addDirac (psi chi : DiracTwistor) : DiracTwistor :=
  (addV4 psi.1 chi.1, addV4 psi.2 chi.2)

/-- Full polarized Clifford relation on the direct sum of the two chiral twistor modules. -/
theorem clifford_anticommutator
    (p q : P6) (psi : DiracTwistor) :
    addDirac
      (cliffordAction p (cliffordAction q psi))
      (cliffordAction q (cliffordAction p psi)) =
    scaleDirac (- epsilonPair p q) psi := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  rcases q with ⟨q01,q02,q03,q12,q13,q23⟩
  rcases psi with ⟨z,alpha⟩
  rcases z with ⟨z0,z1,z2,z3⟩
  rcases alpha with ⟨a0,a1,a2,a3⟩
  apply Prod.ext
  · apply Prod.ext
    · simp [addDirac, addV4, cliffordAction, cPlus, cMinus, scaleDirac,
        scale4, epsilonPair]
      ring
    · apply Prod.ext
      · simp [addDirac, addV4, cliffordAction, cPlus, cMinus, scaleDirac,
          scale4, epsilonPair]
        ring
      · apply Prod.ext
        · simp [addDirac, addV4, cliffordAction, cPlus, cMinus, scaleDirac,
            scale4, epsilonPair]
          ring
        · simp [addDirac, addV4, cliffordAction, cPlus, cMinus, scaleDirac,
            scale4, epsilonPair]
          ring
  · apply Prod.ext
    · simp [addDirac, addV4, cliffordAction, cPlus, cMinus, scaleDirac,
        scale4, epsilonPair]
      ring
    · apply Prod.ext
      · simp [addDirac, addV4, cliffordAction, cPlus, cMinus, scaleDirac,
          scale4, epsilonPair]
        ring
      · apply Prod.ext
        · simp [addDirac, addV4, cliffordAction, cPlus, cMinus, scaleDirac,
            scale4, epsilonPair]
          ring
        · simp [addDirac, addV4, cliffordAction, cPlus, cMinus, scaleDirac,
            scale4, epsilonPair]
          ring

/-- Triple-product form of the Pin adjoint action.  Scaling the triple Clifford product
by `1/Q(v)` gives exactly Clifford multiplication by the reflected Klein vector. -/
theorem pin_conjugation_implements_kleinReflection
    (v q : P6) (hv : kleinQ v ≠ 0) (psi : DiracTwistor) :
    scaleDirac (1 / kleinQ v)
      (cliffordAction v (cliffordAction q (cliffordAction v psi))) =
    cliffordAction (kleinReflection v q) psi := by
  rcases v with ⟨v01,v02,v03,v12,v13,v23⟩
  rcases q with ⟨q01,q02,q03,q12,q13,q23⟩
  rcases psi with ⟨z,alpha⟩
  rcases z with ⟨z0,z1,z2,z3⟩
  rcases alpha with ⟨a0,a1,a2,a3⟩
  apply Prod.ext
  · apply Prod.ext
    · simp [scaleDirac, scale4, cliffordAction, cPlus, cMinus,
        kleinReflection, subP6, scaleP6, epsilonPair, kleinQ] at hv ⊢
      field_simp [hv]
      ring
    · apply Prod.ext
      · simp [scaleDirac, scale4, cliffordAction, cPlus, cMinus,
          kleinReflection, subP6, scaleP6, epsilonPair, kleinQ] at hv ⊢
        field_simp [hv]
        ring
      · apply Prod.ext
        · simp [scaleDirac, scale4, cliffordAction, cPlus, cMinus,
            kleinReflection, subP6, scaleP6, epsilonPair, kleinQ] at hv ⊢
          field_simp [hv]
          ring
        · simp [scaleDirac, scale4, cliffordAction, cPlus, cMinus,
            kleinReflection, subP6, scaleP6, epsilonPair, kleinQ] at hv ⊢
          field_simp [hv]
          ring
  · apply Prod.ext
    · simp [scaleDirac, scale4, cliffordAction, cPlus, cMinus,
        kleinReflection, subP6, scaleP6, epsilonPair, kleinQ] at hv ⊢
      field_simp [hv]
      ring
    · apply Prod.ext
      · simp [scaleDirac, scale4, cliffordAction, cPlus, cMinus,
          kleinReflection, subP6, scaleP6, epsilonPair, kleinQ] at hv ⊢
        field_simp [hv]
        ring
      · apply Prod.ext
        · simp [scaleDirac, scale4, cliffordAction, cPlus, cMinus,
            kleinReflection, subP6, scaleP6, epsilonPair, kleinQ] at hv ⊢
          field_simp [hv]
          ring
        · simp [scaleDirac, scale4, cliffordAction, cPlus, cMinus,
            kleinReflection, subP6, scaleP6, epsilonPair, kleinQ] at hv ⊢
          field_simp [hv]
          ring

/-- Specialization to the nonzero-cosmological infinity twistor.  The same chiral bridge
`C(I_Lambda)` implements the disconnected Klein reflection by Pin conjugation. -/
theorem infinityTwistor_pin_conjugation
    (Lambda : ℝ) (hLambda : Lambda ≠ 0) (q : P6) (psi : DiracTwistor) :
    scaleDirac (1 / Lambda)
      (cliffordAction (GppEinsteinInfinityTwistorFamily.infinityTwistor Lambda)
        (cliffordAction q
          (cliffordAction (GppEinsteinInfinityTwistorFamily.infinityTwistor Lambda) psi))) =
    cliffordAction
      (kleinReflection (GppEinsteinInfinityTwistorFamily.infinityTwistor Lambda) q) psi := by
  have hQ : kleinQ (GppEinsteinInfinityTwistorFamily.infinityTwistor Lambda) ≠ 0 := by
    rw [GppEinsteinInfinityTwistorFamily.kleinQ_infinityTwistor]
    exact hLambda
  simpa [GppEinsteinInfinityTwistorFamily.kleinQ_infinityTwistor] using
    pin_conjugation_implements_kleinReflection
      (GppEinsteinInfinityTwistorFamily.infinityTwistor Lambda) q hQ psi

end GppKleinCliffordPinConjugation
