import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic

/-!
# Turbo Wave234 exact doubled-sector parity decomposition

For Wave234 same-sheet form Q and symmetric cross-sheet form C, the doubled
block [[Q,C],[C,Q]] splits into parity forms Q+C and Q-C. The theorem is
valid in an arbitrary real vector space, not only in numerical K truncations.

Source: Turbo MuseResearch/turbo-source-wave234-s1-schur-definitions.md,
GPP-bridge PR #11; Astra's 2026-10-28 doubled-strip algebra.
It does not prove either actual arithmetic parity form positive, or RH.
-/

namespace GppWave234SectorParity

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def doubledForm (Q C : LinearMap.BilinForm ℝ V) (u v : V) : ℝ :=
  Q u u + Q v v + 2 * C u v

theorem parity_diagonalization (Q C : LinearMap.BilinForm ℝ V)
    (hC : ∀ u v, C u v = C v u) (u v : V) :
    doubledForm Q C u v =
      (Q (u + v) (u + v) + C (u + v) (u + v)) / 2 +
      (Q (u - v) (u - v) - C (u - v) (u - v)) / 2 := by
  unfold doubledForm
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  rw [hC v u]
  ring

theorem doubled_nonneg_of_parity (Q C : LinearMap.BilinForm ℝ V)
    (hC : ∀ u v, C u v = C v u)
    (hplus : ∀ w, 0 ≤ Q w w + C w w)
    (hminus : ∀ w, 0 ≤ Q w w - C w w) (u v : V) :
    0 ≤ doubledForm Q C u v := by
  rw [parity_diagonalization Q C hC]
  exact add_nonneg
    (div_nonneg (hplus (u + v)) (by norm_num))
    (div_nonneg (hminus (u - v)) (by norm_num))

theorem even_nonneg_of_doubled (Q C : LinearMap.BilinForm ℝ V)
    (h : ∀ u v, 0 ≤ doubledForm Q C u v) (w : V) :
    0 ≤ Q w w + C w w := by
  have hw := h w w
  unfold doubledForm at hw
  linarith

theorem odd_nonneg_of_doubled (Q C : LinearMap.BilinForm ℝ V)
    (h : ∀ u v, 0 ≤ doubledForm Q C u v) (w : V) :
    0 ≤ Q w w - C w w := by
  have hw := h w (-w)
  unfold doubledForm at hw
  have hq : Q (-w) (-w) = Q w w := by simp
  have hc : C w (-w) = -(C w w) := by simp
  rw [hq, hc] at hw
  linarith

theorem doubled_nonneg_iff_parity (Q C : LinearMap.BilinForm ℝ V)
    (hC : ∀ u v, C u v = C v u) :
    (∀ u v, 0 ≤ doubledForm Q C u v) ↔
      (∀ w, 0 ≤ Q w w + C w w) ∧ (∀ w, 0 ≤ Q w w - C w w) := by
  constructor
  · intro h
    exact ⟨even_nonneg_of_doubled Q C h, odd_nonneg_of_doubled Q C h⟩
  · rintro ⟨hp, hm⟩
    exact doubled_nonneg_of_parity Q C hC hp hm

end GppWave234SectorParity

#print axioms GppWave234SectorParity.parity_diagonalization
#print axioms GppWave234SectorParity.doubled_nonneg_iff_parity
