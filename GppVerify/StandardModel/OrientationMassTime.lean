import Mathlib.Tactic
import GppVerify.GrassmannianMass
import GppVerify.GrassmannianJacobian
import GppVerify.StandardModel.MassOrientationCoupling

/-!
# Orientation, mass, proper time, and the half flip

Finite/algebraic core of Toupin, *Which Way Is Forward?*

This module deliberately formalizes only statements that do not require a QFT
construction of observers, Wigner time reversal, or a microscopic worldline
ontology.
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

/-- Algebraic inversion of the proper-time phase-rate formula. -/
theorem mass_from_phaseRate
    (m c hbar rate : ℝ) (hc : c ≠ 0) (hh : hbar ≠ 0)
    (hrate : rate = m * c ^ 2 / hbar) :
    m = hbar / c ^ 2 * rate := by
  rw [hrate]
  field_simp
  ring

/-- Relational charge/orientation character. `t` is an oriented-line weight,
not Wigner time reversal. -/
def relationalCharacter (q t : ℝ) : ℝ := q * t

theorem diagonal_flip_invariant (q t : ℝ) :
    relationalCharacter (-q) (-t) = relationalCharacter q t := by simp [relationalCharacter]
theorem charge_half_flip (q t : ℝ) :
    relationalCharacter (-q) t = - relationalCharacter q t := by simp [relationalCharacter]
theorem orientation_half_flip (q t : ℝ) :
    relationalCharacter q (-t) = - relationalCharacter q t := by simp [relationalCharacter]
theorem two_half_flips_agree (q t : ℝ) :
    relationalCharacter (-q) t = relationalCharacter q (-t) := by simp [relationalCharacter]

/-! ## Exact finite half-flip quotient

The four sign choices are represented by `Bool × Bool`.  The diagonal subgroup
has two elements `(0,0)` and `(1,1)`.  The invariant `xorCharacter` is constant
on diagonal orbits and separates them, so the quotient has exactly the two
classes encoded by `Bool`.  This is the finite theorem behind
`(Z₂ × Z₂)/diag(Z₂) ≅ Z₂`, without invoking any physical interpretation.
-/

def diagFlip (x : Bool × Bool) : Bool × Bool := (!x.1, !x.2)
def xorCharacter (x : Bool × Bool) : Bool := xor x.1 x.2

theorem diagFlip_involutive (x : Bool × Bool) : diagFlip (diagFlip x) = x := by
  rcases x with ⟨a,b⟩ <;> cases a <;> cases b <;> decide

theorem xorCharacter_diagFlip (x : Bool × Bool) :
    xorCharacter (diagFlip x) = xorCharacter x := by
  rcases x with ⟨a,b⟩ <;> cases a <;> cases b <;> decide

/-- Equality of the quotient invariant is exactly equality up to the diagonal flip. -/
theorem xorCharacter_eq_iff_diagOrbit (x y : Bool × Bool) :
    xorCharacter x = xorCharacter y ↔ y = x ∨ y = diagFlip x := by
  rcases x with ⟨a,b⟩ <;> rcases y with ⟨c,d⟩ <;>
    cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- Charge-only and orientation-only flips have the same quotient character. -/
theorem finite_two_half_flips_agree (q t : Bool) :
    xor (!q) t = xor q (!t) := by
  cases q <;> cases t <;> decide

/-- Either single half flip changes the quotient character. -/
theorem finite_half_flip_changes_class (q t : Bool) :
    xor (!q) t = !(xor q t) ∧ xor q (!t) = !(xor q t) := by
  cases q <;> cases t <;> decide

/-- Universal tangent operator `L(X)=X*epsilon-epsilon*tr(X)` in row-major
coordinates: `(x1,x2,x3,x4) -> (-x2,-x4,x1,x3)`. -/
def universalL (p : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (-p.2.1, -p.2.2.2, p.1, p.2.2.1)

theorem universalL_four (p : ℝ × ℝ × ℝ × ℝ) :
    universalL (universalL (universalL (universalL p))) = p := by
  rcases p with ⟨x1, x2, x3, x4⟩
  rfl

theorem universalL_sq_not_neg_id :
    universalL (universalL ((1 : ℝ), 0, 0, 0)) ≠ (-1, 0, 0, 0) := by
  norm_num [universalL]

/-- Re-export of the exact nonlinear Grassmannian order-four theorem. -/
theorem grassmannian_tau_four
    (a b c d : ℝ) (hD : a * d - b * c ≠ 0) :
    GppGrassmannian.tauMap^[4] (a, b, c, d) = (a, b, c, d) :=
  GppGrassmannian.tauMap_iterate_four a b c d hD

/-- Re-export of `N^4=D^4 I`. -/
theorem grassmannian_jacobian_four
    (a b c d : ℝ) :
    GppGrassmannianJacobian.N a b c d * GppGrassmannianJacobian.N a b c d *
        (GppGrassmannianJacobian.N a b c d * GppGrassmannianJacobian.N a b c d)
      = (a * d - b * c) ^ 4 • (1 : Matrix (Fin 4) (Fin 4) ℝ) :=
  GppGrassmannianJacobian.N_pow_four_eq_D_pow_four_smul_one a b c d

/-- Eigenvector-level spectral corollary of `N^4=D^4 I`, formalized without
requiring a global eigenvalue multiset API. If `v` is a nonzero complex
4-vector and `N v = lambda v`, then `lambda^4 = D^4`. -/
theorem jacobianNumerator_eigenvalue_fourth_power
    (N4 : Matrix (Fin 4) (Fin 4) ℂ) (D λ : ℂ) (v : Fin 4 → ℂ)
    (hN4 : N4 * N4 * (N4 * N4) = D ^ 4 • (1 : Matrix (Fin 4) (Fin 4) ℂ))
    (hv : v ≠ 0)
    (heig : N4 *ᵥ v = λ • v) :
    λ ^ 4 = D ^ 4 := by
  have h4 : (N4 * N4 * (N4 * N4)) *ᵥ v = λ ^ 4 • v := by
    simp only [Matrix.mulVec_mulVec, heig, Matrix.mulVec_smul]
    ext i
    simp
    ring
  rw [hN4] at h4
  have hscalar : D ^ 4 • v = λ ^ 4 • v := by
    simpa using h4
  by_contra hne
  have hcoeff : D ^ 4 - λ ^ 4 ≠ 0 := sub_ne_zero.mpr hne
  have hz : (D ^ 4 - λ ^ 4) • v = 0 := by
    ext i
    have hi := congrFun hscalar i
    simpa [sub_mul] using sub_eq_zero.mpr hi
  exact hv (smul_eq_zero.mp hz |>.resolve_left hcoeff)

end GppOrientationMassTime
