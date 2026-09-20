import Mathlib.Tactic

/-!
# Four microscopic orientation lifts and the diagonal fixed carrier

This file contains the linear four-label algebra

    ++, +-, -+, --

represented by amplitudes `(a,b,c,d)`.  The two independent half flips reverse
the microscopic q and t labels, their product is the simultaneous reversal `D`,
and the relational grading is `χ=q*t`.

The fixed space of `D` is exactly

    (a,b,b,a),

a two-complex-dimensional subspace for the ordinary ambient scalar structure.
The finite identities below are interpretation-neutral: they prove the fixed
subspace and the action of χ and the two half flips.

A later refinement, `OrientationComplexStructureDoubleCover.lean` together with
`OrientationCriticalRealStructureBridge.lean`, shows that when the underlying
real carrier is equipped with the microscopic complex structure `I_q`, `D`
anticommutes with `I_q` and is therefore an involutive REAL STRUCTURE.  Thus this
file's historical name should not be read as a claim that `D` is a finite
physical gauge group.  The label-space Haar average remains valid finite
representation theory, while the Hilbert-carrier fixed set is more naturally
interpreted as the real form of `D`.

The bare q and t sign operators are odd under `D`; their product χ is even.
-/

namespace GppFourOrientationGaugeProjection

abbrev Orientation4 := ℂ × ℂ × ℂ × ℂ

/-- Simultaneous reversal: `++ <-> --` and `+- <-> -+`. -/
def diagReverse (v : Orientation4) : Orientation4 :=
  (v.2.2.2, v.2.2.1, v.2.1, v.1)

/-- Flip the first (`q`) sign only. -/
def chargeFlip (v : Orientation4) : Orientation4 :=
  (v.2.2.1, v.2.2.2, v.1, v.2.1)

/-- Flip the second microscopic temporal sign only. -/
def temporalFlip (v : Orientation4) : Orientation4 :=
  (v.2.1, v.1, v.2.2.2, v.2.2.1)

/-- Bare q-sign observable: `(+,+,-,-)` in the chosen basis. -/
def bareQ (v : Orientation4) : Orientation4 :=
  (v.1, v.2.1, -v.2.2.1, -v.2.2.2)

/-- Bare microscopic temporal-sign observable: `(+,-,+,-)`. -/
def bareT (v : Orientation4) : Orientation4 :=
  (v.1, -v.2.1, v.2.2.1, -v.2.2.2)

/-- Relational alignment grading `q*t = (+,-,-,+)`. -/
def chi (v : Orientation4) : Orientation4 :=
  (v.1, -v.2.1, -v.2.2.1, v.2.2.2)

/-- All three flips are involutions. -/
theorem flip_involutions (v : Orientation4) :
    diagReverse (diagReverse v) = v ∧
    chargeFlip (chargeFlip v) = v ∧
    temporalFlip (temporalFlip v) = v := by
  rcases v with ⟨a,b,c,d⟩
  exact ⟨rfl,rfl,rfl⟩

/-- The two half flips commute and compose to the full diagonal reversal. -/
theorem half_flips_compose_to_diagonal (v : Orientation4) :
    chargeFlip (temporalFlip v) = diagReverse v ∧
    temporalFlip (chargeFlip v) = diagReverse v := by
  rcases v with ⟨a,b,c,d⟩
  exact ⟨rfl,rfl⟩

/-- The relational grading is literally the product of the two bare sign gradings. -/
theorem bareQ_bareT_eq_chi (v : Orientation4) :
    bareQ (bareT v) = chi v ∧ bareT (bareQ v) = chi v := by
  rcases v with ⟨a,b,c,d⟩
  simp [bareQ, bareT, chi]

/-- Bare q is odd under diagonal reversal. -/
theorem diag_anticommutes_bareQ (v : Orientation4) :
    diagReverse (bareQ v) = - bareQ (diagReverse v) := by
  rcases v with ⟨a,b,c,d⟩
  simp [diagReverse, bareQ]

/-- Bare microscopic t is likewise odd under diagonal reversal. -/
theorem diag_anticommutes_bareT (v : Orientation4) :
    diagReverse (bareT v) = - bareT (diagReverse v) := by
  rcases v with ⟨a,b,c,d⟩
  simp [diagReverse, bareT]

/-- Their product/alignment grading is even under diagonal reversal. -/
theorem diag_commutes_chi (v : Orientation4) :
    diagReverse (chi v) = chi (diagReverse v) := by
  rcases v with ⟨a,b,c,d⟩
  simp [diagReverse, chi]

/-- Canonical parameterization of the diagonal-fixed candidate subspace. -/
def physicalLift (matter antimatter : ℂ) : Orientation4 :=
  (matter, antimatter, antimatter, matter)

/-- Every canonical paired lift is diagonal-fixed. -/
theorem physicalLift_diag_even (a b : ℂ) :
    diagReverse (physicalLift a b) = physicalLift a b := by
  rfl

/-- Conversely every diagonal-fixed vector has exactly this paired form. -/
theorem diag_even_has_paired_form (v : Orientation4)
    (h : diagReverse v = v) :
    ∃ a b : ℂ, v = physicalLift a b := by
  rcases v with ⟨a,b,c,d⟩
  have hd : d = a := congrArg (fun x : Orientation4 => x.1) h
  have hc : c = b := congrArg (fun x : Orientation4 => x.2.1) h
  refine ⟨a,b,?_⟩
  subst d
  subst c
  rfl

/-- The two natural unnormalized physical basis states. -/
def matterLift : Orientation4 := (1,0,0,1)
def antimatterLift : Orientation4 := (0,1,1,0)

/-- Both relational sectors are diagonal-fixed. -/
theorem basis_lifts_diag_even :
    diagReverse matterLift = matterLift ∧
    diagReverse antimatterLift = antimatterLift := by
  exact ⟨rfl,rfl⟩

/-- `χ` assigns matter eigenvalue +1. -/
theorem chi_matter : chi matterLift = matterLift := by
  norm_num [chi, matterLift]

/-- `χ` assigns antimatter eigenvalue -1. -/
theorem chi_antimatter : chi antimatterLift = -antimatterLift := by
  norm_num [chi, antimatterLift]

/-- Either microscopic half flip sends the matter lift to the antimatter lift. -/
theorem half_flips_matter_to_antimatter :
    chargeFlip matterLift = antimatterLift ∧
    temporalFlip matterLift = antimatterLift := by
  exact ⟨rfl,rfl⟩

/-- Either half flip sends the antimatter lift back to matter. -/
theorem half_flips_antimatter_to_matter :
    chargeFlip antimatterLift = matterLift ∧
    temporalFlip antimatterLift = matterLift := by
  exact ⟨rfl,rfl⟩

/-- The bare q grading takes a diagonal-fixed vector to the diagonal-odd complement. -/
theorem bareQ_maps_even_to_odd (v : Orientation4)
    (h : diagReverse v = v) :
    diagReverse (bareQ v) = - bareQ v := by
  rw [diag_anticommutes_bareQ, h]

/-- The same is true of the bare microscopic temporal grading. -/
theorem bareT_maps_even_to_odd (v : Orientation4)
    (h : diagReverse v = v) :
    diagReverse (bareT v) = - bareT v := by
  rw [diag_anticommutes_bareT, h]

/-- In contrast the relational character preserves the diagonal-fixed subspace. -/
theorem chi_preserves_even (v : Orientation4)
    (h : diagReverse v = v) :
    diagReverse (chi v) = chi v := by
  rw [diag_commutes_chi, h]

/-- Capstone: restriction to the diagonal fixed carrier leaves exactly two amplitudes, and `χ`
acts on those as the ordinary relational matter/antimatter sign. -/
theorem physical_sector_capstone (v : Orientation4)
    (h : diagReverse v = v) :
    ∃ a b : ℂ,
      v = physicalLift a b ∧
      chi v = physicalLift a (-b) := by
  obtain ⟨a,b,hv⟩ := diag_even_has_paired_form v h
  refine ⟨a,b,hv,?_⟩
  rw [hv]
  simp [chi, physicalLift]

end GppFourOrientationGaugeProjection
