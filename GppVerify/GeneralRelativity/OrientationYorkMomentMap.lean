import Mathlib.Tactic
import GppVerify.GeneralRelativity.YorkVolumeReduction
import GppVerify.GeneralRelativity.TimeReversalEntropyGravity

/-!
# Anti-symplectic time orientation and the even York volume moment map

Extract the *mathematical* common core between Toupin's September 2026
"Which Way Is Forward?" orientation carrier and the volume-constraint paper.

If a time-orientation reversal T acts anti-symplectically, its York
Hamiltonian vector Y is T-odd, and the contraction with the canonical
2-form is c*dV with c nonzero, then dV is T-even.

Crucial distinction: the first manuscript's microscopic sign t,
the diagonal charge/time lift D, the record arrow, and Wigner's
antiunitary T are NOT identified here. The present T is an abstract
anti-symplectic involution modeling ADM temporal orientation reversal.
The physical intertwiner linking that T to the four-lift carrier
remains to be established.

The second theorem provides an explicit continuum of volume changes
in an orientation-symmetric canonical phase space. Thus parity does
not impose the fixed-volume constraint by itself.
-/

namespace GppOrientationYorkMomentMap

section Abstract

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- An anti-symplectic time reversal and a time-odd York generator
force the York moment-map differential dV to be time-even. -/
theorem york_momentmap_differential_time_even
    (omega : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (T : E →ₗ[ℝ] E)
    (Y : E) (dV : E →ₗ[ℝ] ℝ) (c : ℝ)
    (hc : c ≠ 0)
    (hAnti : ∀ u v, omega (T u) (T v) = -omega u v)
    (hYorkOdd : T Y = -Y)
    (hMoment : ∀ x, omega Y x = c * dV x)
    (x : E) :
    dV (T x) = dV x := by
  have h := hAnti Y x
  rw [hYorkOdd, map_neg] at h
  have hEven : omega Y (T x) = omega Y x := by
    linarith
  rw [hMoment (T x), hMoment x] at hEven
  exact (mul_left_cancel₀ hc) hEven

/-- The invariant first derivative of a time-even entropy response
annihilates a time-odd York perturbation (already developed in the
time-reversal entropy module); this is compatible with, not proof of,
the independent nonzero fixed-volume moment-map on time-even modes. -/
theorem entropy_blind_to_odd_york
    (dS : E →ₗ[ℝ] ℝ) (T : E →ₗ[ℝ] E) (Y : E)
    (hinv : ∀ x, dS (T x) = dS x)
    (hodd : T Y = -Y) :
    dS Y = 0 :=
  GppTimeReversalVolume.time_even_entropy_response_vanishes_on_odd_mode
    dS T Y hinv hodd

end Abstract

section CanonicalToy

/-- ADM scalar time-orientation reversal on configuration/momentum data. -/
def reverse (z : ℝ × ℝ) : ℝ × ℝ := (z.1, -z.2)

/-- The canonical pairing on the reduced one-degree-of-freedom phase plane. -/
def omega (a b : ℝ × ℝ) : ℝ :=
    a.2 * b.1 - b.2 * a.1

/-- Local linear volume coordinate, varying independently of time orientation. -/
def volume (z : ℝ × ℝ) : ℝ := z.1

/-- York momentum translation leaves configuration data fixed. -/
def york (c : ℝ) : ℝ × ℝ := (0, c)

/-- Time reversal changes orientation of the symplectic form. -/
theorem anti_symplectic (a b : ℝ × ℝ) :
    omega (reverse a) (reverse b) = -omega a b := by
  rcases a with ⟨qa, pa⟩
  rcases b with ⟨qb, pb⟩
  simp [omega, reverse]
  ring

/-- The York direction is time-odd. -/
theorem york_odd (c : ℝ) :
    reverse (york c) = york (-c) := by
  simp [reverse, york]

/-- The spatial-volume coordinate is time-even. -/
theorem volume_even (z : ℝ × ℝ) :
    volume (reverse z) = volume z := by
  rfl

/-- An odd York generator pairs nontrivially with even metric/volume data. -/
theorem york_pairs_with_even_volume (c : ℝ) (z : ℝ × ℝ) :
    omega (york c) z = c * volume z := by
  simp [omega, york, volume]

/-- This pairing is not a null gauge direction when volume is allowed
to vary. -/
theorem york_pairing_detects_nonzero_volume (c : ℝ) (hc : c ≠ 0) :
    omega (york c) (1, 0) ≠ 0 := by
  simp [omega, york]
  exact hc

/-- Discrete orientation reversal does not collapse all spatial volumes. -/
theorem orientation_invariant_family_variable_volume :
    ∃ z₁ z₂ : ℝ × ℝ,
      volume (reverse z₁) = volume z₁ ∧
      volume (reverse z₂) = volume z₂ ∧
      volume z₁ ≠ volume z₂ := by
  refine ⟨(1, 1), (2, -1), rfl, rfl, ?_⟩
  norm_num [volume]

end CanonicalToy
end GppOrientationYorkMomentMap

#print axioms GppOrientationYorkMomentMap.york_momentmap_differential_time_even
#print axioms GppOrientationYorkMomentMap.entropy_blind_to_odd_york
#print axioms GppOrientationYorkMomentMap.anti_symplectic
#print axioms GppOrientationYorkMomentMap.orientation_invariant_family_variable_volume
