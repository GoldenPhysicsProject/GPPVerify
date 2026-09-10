import Mathlib.Tactic
import Mathlib.Data.Matrix.Notation

/-!
# Positivity/unitarity forces alignment of symplectic and frequency orientations

For a real bosonic phase space, a compatible complex structure `J` is not chosen by
`J^2=-1` alone.  The one-particle real inner product is schematically

    G(u,v) = Omega(u, J v),

and it must be positive.  Reversing `J` while holding the symplectic orientation `Omega`
fixed sends `G -> -G` and destroys positivity.  Reversing BOTH `Omega` and `J` leaves `G`
unchanged.

This file gives the exact 2-dimensional core.  Choose

    Omega = [[0,1],[-1,0]],
    J     = [[0,-1],[1,0]],

so `Omega J = +I`.  Give each an independent sign `c,t = +/-1`.  Then

    G_{c,t} = (c Omega)(t J) = (c t) I.

Hence a nonzero test vector has positive norm exactly in the aligned sectors `ct=+1`.
The two aligned lifts `++` and `--` are equally positive and are exchanged by simultaneous
reversal.  The anti-aligned lifts give the negative form.

This is potentially the missing selection principle in the orientation programme: the
product sign can be fixed by Hilbert-space positivity rather than by an arbitrary primordial
matter choice.  IMPORTANT: if this interpretation survives the full charged Dirac/CAR
construction, the anti-aligned `ct=-1` sector must NOT be identified with ordinary
antimatter, because observed antiparticles have positive norm.  Ordinary particle-to-
antiparticle conjugation would instead have to reverse the relevant internal and frequency
orientations together.  That field-theoretic identification remains to be proved.
-/

namespace GppUnitarityForcesOrientationAlignment

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ
abbrev V2R := Fin 2 → ℝ

/-- Canonical symplectic matrix. -/
def Omega : M2R := !![0,1;-1,0]

/-- Compatible positive-frequency complex structure. -/
def J : M2R := !![0,-1;1,0]

/-- Binary sign, with `false=+1`, `true=-1`. -/
def sgn (b : Bool) : ℝ := if b then -1 else 1

/-- Orient the symplectic form by one microscopic sign. -/
def OmegaOrient (c : Bool) : M2R := sgn c • Omega

/-- Orient the frequency complex structure by the other sign. -/
def JOrient (t : Bool) : M2R := sgn t • J

/-- Resulting real one-particle metric matrix. -/
def oneParticleMetric (c t : Bool) : M2R := OmegaOrient c * JOrient t

/-- The reference pair is compatible: Omega*J=+I. -/
theorem Omega_mul_J_one : Omega * J = (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Omega, J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- Exact product law: only the relative sign survives in the one-particle metric. -/
theorem metric_eq_relative_sign_identity (c t : Bool) :
    oneParticleMetric c t = (sgn c * sgn t) • (1 : M2R) := by
  rw [oneParticleMetric, OmegaOrient, JOrient]
  rw [smul_mul, mul_smul, smul_smul, Omega_mul_J_one]

/-- Simultaneously reversing both orientations leaves the Hilbert metric unchanged. -/
theorem diagonal_reversal_preserves_metric (c t : Bool) :
    oneParticleMetric (!c) (!t) = oneParticleMetric c t := by
  cases c <;> cases t <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [oneParticleMetric, OmegaOrient, JOrient, sgn,
        Omega, J, Matrix.mul_apply, Fin.sum_univ_two]

/-- The basis vector used as a positivity witness. -/
def e0 : V2R := ![1,0]

/-- Quadratic form associated with a matrix on the witness vector. -/
def witnessNorm (G : M2R) : ℝ :=
  e0 0 * (G 0 0 * e0 0 + G 0 1 * e0 1) +
  e0 1 * (G 1 0 * e0 0 + G 1 1 * e0 1)

/-- The witness norm is exactly the relative orientation sign. -/
theorem witnessNorm_eq_product_sign (c t : Bool) :
    witnessNorm (oneParticleMetric c t) = sgn c * sgn t := by
  rw [metric_eq_relative_sign_identity]
  cases c <;> cases t <;>
    norm_num [witnessNorm, e0, sgn, Matrix.one_apply]

/-- Positivity of even one nonzero canonical mode is equivalent to alignment `c=t`. -/
theorem positive_witness_iff_orientations_aligned (c t : Bool) :
    0 < witnessNorm (oneParticleMetric c t) ↔ c = t := by
  cases c <;> cases t <;>
    norm_num [witnessNorm_eq_product_sign, sgn]

/-- Both aligned sheets have positive norm. -/
theorem both_aligned_lifts_positive :
    0 < witnessNorm (oneParticleMetric false false) ∧
    0 < witnessNorm (oneParticleMetric true true) := by
  norm_num [witnessNorm_eq_product_sign, sgn]

/-- Both anti-aligned lifts have negative norm. -/
theorem anti_aligned_lifts_negative :
    witnessNorm (oneParticleMetric false true) < 0 ∧
    witnessNorm (oneParticleMetric true false) < 0 := by
  norm_num [witnessNorm_eq_product_sign, sgn]

/-- Capstone: positivity eliminates the two half-flipped orientation choices while retaining
    both simultaneously reversed lifts. -/
theorem positivity_selects_diagonal_pair (c t : Bool)
    (hpos : 0 < witnessNorm (oneParticleMetric c t)) :
    (c = false ∧ t = false) ∨ (c = true ∧ t = true) := by
  have hct := (positive_witness_iff_orientations_aligned c t).1 hpos
  subst t
  cases c <;> simp

end GppUnitarityForcesOrientationAlignment
