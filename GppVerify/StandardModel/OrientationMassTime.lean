import Mathlib.Tactic
import GppVerify.GrassmannianMass
import GppVerify.GrassmannianJacobian
import GppVerify.StandardModel.MassOrientationCoupling

namespace GppOrientationMassTime

def comptonLength (m c hbar : ℝ) : ℝ := hbar / (m * c)
def comptonFrequency (m c hbar : ℝ) : ℝ := m * c ^ 2 / hbar
def zitterFrequency (m c hbar : ℝ) : ℝ := 2 * comptonFrequency m c hbar
def zitterLength (m c hbar : ℝ) : ℝ := comptonLength m c hbar / 2

theorem compton_length_mul_frequency
    (m c hbar : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hh : hbar ≠ 0) :
    comptonLength m c hbar * comptonFrequency m c hbar = c := by
  simp [comptonLength, comptonFrequency]
  field_simp
  ring

theorem zitter_length_mul_frequency
    (m c hbar : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hh : hbar ≠ 0) :
    zitterLength m c hbar * zitterFrequency m c hbar = c := by
  rw [zitterLength, zitterFrequency]
  rw [show comptonLength m c hbar / 2 * (2 * comptonFrequency m c hbar)
      = comptonLength m c hbar * comptonFrequency m c hbar by ring]
  exact compton_length_mul_frequency m c hbar hm hc hh

theorem mass_from_phaseRate
    (m c hbar rate : ℝ) (hc : c ≠ 0) (hh : hbar ≠ 0)
    (hrate : rate = m * c ^ 2 / hbar) :
    m = hbar / c ^ 2 * rate := by
  rw [hrate]
  field_simp
  ring

def relationalCharacter (q t : ℝ) : ℝ := q * t

theorem diagonal_flip_invariant (q t : ℝ) :
    relationalCharacter (-q) (-t) = relationalCharacter q t := by simp [relationalCharacter]
theorem charge_half_flip (q t : ℝ) :
    relationalCharacter (-q) t = - relationalCharacter q t := by simp [relationalCharacter]
theorem orientation_half_flip (q t : ℝ) :
    relationalCharacter q (-t) = - relationalCharacter q t := by simp [relationalCharacter]
theorem two_half_flips_agree (q t : ℝ) :
    relationalCharacter (-q) t = relationalCharacter q (-t) := by simp [relationalCharacter]

def diagFlip (x : Bool × Bool) : Bool × Bool := (!x.1, !x.2)
def xorCharacter (x : Bool × Bool) : Bool := xor x.1 x.2

theorem diagFlip_involutive (x : Bool × Bool) : diagFlip (diagFlip x) = x := by
  rcases x with ⟨a,b⟩ <;> cases a <;> cases b <;> decide

theorem xorCharacter_diagFlip (x : Bool × Bool) :
    xorCharacter (diagFlip x) = xorCharacter x := by
  rcases x with ⟨a,b⟩ <;> cases a <;> cases b <;> decide

theorem xorCharacter_eq_iff_diagOrbit (x y : Bool × Bool) :
    xorCharacter x = xorCharacter y ↔ y = x ∨ y = diagFlip x := by
  rcases x with ⟨a,b⟩ <;> rcases y with ⟨c,d⟩ <;>
    cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem finite_two_half_flips_agree (q t : Bool) :
    xor (!q) t = xor q (!t) := by
  cases q <;> cases t <;> decide

theorem finite_half_flip_changes_class (q t : Bool) :
    xor (!q) t = !(xor q t) ∧ xor q (!t) = !(xor q t) := by
  cases q <;> cases t <;> decide

def universalL (p : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (-p.2.1, -p.2.2.2, p.1, p.2.2.1)

theorem universalL_four (p : ℝ × ℝ × ℝ × ℝ) :
    universalL (universalL (universalL (universalL p))) = p := by
  rcases p with ⟨x1, x2, x3, x4⟩
  rfl

theorem universalL_sq_not_neg_id :
    universalL (universalL ((1 : ℝ), 0, 0, 0)) ≠ (-1, 0, 0, 0) := by
  norm_num [universalL]

theorem grassmannian_tau_four
    (a b c d : ℝ) (hD : a * d - b * c ≠ 0) :
    GppGrassmannian.tauMap^[4] (a, b, c, d) = (a, b, c, d) :=
  GppGrassmannian.tauMap_iterate_four a b c d hD

theorem grassmannian_jacobian_four
    (a b c d : ℝ) :
    GppGrassmannianJacobian.N a b c d * GppGrassmannianJacobian.N a b c d *
        (GppGrassmannianJacobian.N a b c d * GppGrassmannianJacobian.N a b c d)
      = (a * d - b * c) ^ 4 • (1 : Matrix (Fin 4) (Fin 4) ℝ) :=
  GppGrassmannianJacobian.N_pow_four_eq_D_pow_four_smul_one a b c d

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
