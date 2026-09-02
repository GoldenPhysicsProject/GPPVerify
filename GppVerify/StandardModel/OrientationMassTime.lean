import Mathlib.Tactic
import GppVerify.GrassmannianMass
import GppVerify.GrassmannianJacobian
import GppVerify.StandardModel.MassOrientationCoupling

/-!
# Orientation, mass, proper time, and the half flip

Finite/algebraic core of Toupin, *Which Way Is Forward?*

This module deliberately formalizes only statements that do not require a QFT
construction of observers, Wigner time reversal, or a microscopic worldline
ontology.  In particular:

* the Compton clock/ruler identities are exact algebra;
* the relational half-flip quotient is exact sign algebra;
* the universal order-four tangent operator adjacent to the Grassmannian chart
  transition is formalized as an explicit four-coordinate map;
* the already-proved Grassmannian `tau^2 = -id`, `tau^4 = id`, and Jacobian
  polynomial identity are re-exported through imports above.

The physical identification of a projective Grassmannian chart determinant
with a dimensionful measured mass remains a separate normalization theorem.
-/

namespace GppOrientationMassTime

/-- Reduced Compton wavelength `hbar/(m*c)`. -/
def comptonLength (m c hbar : ℝ) : ℝ := hbar / (m * c)

/-- Compton angular frequency `m*c^2/hbar`. -/
def comptonFrequency (m c hbar : ℝ) : ℝ := m * c ^ 2 / hbar

/-- Dirac zitterbewegung angular frequency `2 omega_C`. -/
def zitterFrequency (m c hbar : ℝ) : ℝ := 2 * comptonFrequency m c hbar

/-- Characteristic zitterbewegung length `lambda_C/2`. -/
def zitterLength (m c hbar : ℝ) : ℝ := comptonLength m c hbar / 2

/-- Exact clock-ruler bridge `lambda_C * omega_C = c`. -/
theorem compton_length_mul_frequency
    (m c hbar : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hh : hbar ≠ 0) :
    comptonLength m c hbar * comptonFrequency m c hbar = c := by
  simp [comptonLength, comptonFrequency]
  field_simp
  ring

/-- Exact reciprocal zitter pair `a_Z * omega_Z = c`. -/
theorem zitter_length_mul_frequency
    (m c hbar : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hh : hbar ≠ 0) :
    zitterLength m c hbar * zitterFrequency m c hbar = c := by
  rw [zitterLength, zitterFrequency]
  rw [show comptonLength m c hbar / 2 * (2 * comptonFrequency m c hbar)
      = comptonLength m c hbar * comptonFrequency m c hbar by ring]
  exact compton_length_mul_frequency m c hbar hm hc hh

/-- Mass recovered from the magnitude of a proper-time phase rate once
    `|d theta / d tau| = m*c^2/hbar` is supplied.  This theorem is the
    algebraic inversion, not a formal derivative theorem. -/
theorem mass_from_phaseRate
    (m c hbar rate : ℝ) (hc : c ≠ 0) (hh : hbar ≠ 0)
    (hrate : rate = m * c ^ 2 / hbar) :
    m = hbar / c ^ 2 * rate := by
  rw [hrate]
  field_simp
  ring

/-- Relational charge/orientation character.  No claim is made here that
    `t` is Wigner time reversal; it is simply an oriented-line sign/weight. -/
def relationalCharacter (q t : ℝ) : ℝ := q * t

/-- Full diagonal reversal is invisible to the relational character. -/
theorem diagonal_flip_invariant (q t : ℝ) :
    relationalCharacter (-q) (-t) = relationalCharacter q t := by
  simp [relationalCharacter]

/-- A charge-only half flip reverses the relational character. -/
theorem charge_half_flip (q t : ℝ) :
    relationalCharacter (-q) t = - relationalCharacter q t := by
  simp [relationalCharacter]

/-- An orientation-only half flip reverses the same relational character. -/
theorem orientation_half_flip (q t : ℝ) :
    relationalCharacter q (-t) = - relationalCharacter q t := by
  simp [relationalCharacter]

/-- The two half flips land in the same relational class. -/
theorem two_half_flips_agree (q t : ℝ) :
    relationalCharacter (-q) t = relationalCharacter q (-t) := by
  simp [relationalCharacter]

/-- Explicit four-coordinate universal tangent operator
    `L(X) = X*epsilon - epsilon*tr(X)` in row-major coordinates:
    `(x1,x2,x3,x4) -> (-x2,-x4,x1,x3)`.

    This is the point-independent order-four part of the differential of
    `tau(A)=A*epsilon/det(A)` after identifying tangent vectors by `H=A X`.
-/
def universalL (p : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (-p.2.1, -p.2.2.2, p.1, p.2.2.1)

/-- The universal tangent operator has fourth power exactly the identity. -/
theorem universalL_four (p : ℝ × ℝ × ℝ × ℝ) :
    universalL (universalL (universalL (universalL p))) = p := by
  rcases p with ⟨x1, x2, x3, x4⟩
  rfl

/-- The second power is not `-id` in general.  This explicit witness records
    the correction: nonlinear `tau^2=-id` implies by the chain rule
    `d tau_(tau A) ∘ d tau_A = -I`, not `(d tau_A)^2=-I` at one point. -/
theorem universalL_sq_not_neg_id :
    universalL (universalL ((1 : ℝ), 0, 0, 0)) ≠ (-1, 0, 0, 0) := by
  norm_num [universalL]

/-- Re-export of the already formalized exact Grassmannian order-four theorem. -/
theorem grassmannian_tau_four
    (a b c d : ℝ) (hD : a * d - b * c ≠ 0) :
    GppGrassmannian.tauMap^[4] (a, b, c, d) = (a, b, c, d) :=
  GppGrassmannian.tauMap_iterate_four a b c d hD

/-- Re-export of the formally proved denominator-cleared Jacobian identity
    `N^4 = D^4 I`. -/
theorem grassmannian_jacobian_four
    (a b c d : ℝ) :
    GppGrassmannianJacobian.N a b c d * GppGrassmannianJacobian.N a b c d *
        (GppGrassmannianJacobian.N a b c d * GppGrassmannianJacobian.N a b c d)
      = (a * d - b * c) ^ 4 • (1 : Matrix (Fin 4) (Fin 4) ℝ) :=
  GppGrassmannianJacobian.N_pow_four_eq_D_pow_four_smul_one a b c d

end GppOrientationMassTime
