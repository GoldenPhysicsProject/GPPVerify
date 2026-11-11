/-
  Weight-k shadow involution (Golden Eye, GPP BSD holography notes).
  Generalizes GppFE.critical_line_is_fixed_locus and GppDiagonalLift to weight k.

  These lemmas generalize the repo's weight-1 (Riemann) shadow dictionary
    s ↦ 1 - conj(s)    with fixed locus Re(s) = 1/2
  to weight k
    s ↦ k - conj(s)    with fixed locus Re(s) = k/2.
  For L(E, s) one has k = 2, so the critical line is Re(s) = 1 and the
  Birch–Swinnerton-Dyer centre is the self-dual point s = 1.

  Nothing here proves BSD. Labels: KERNEL-CHECKED algebraic identities only.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace GppWeightKShadow

open Complex

/-- Weight-`k` arithmetic shadow involution `s ↦ k - conj(s)`.
    Riemann zeta / `ξ` has `k = 1`; the Hasse–Weil L-function of an elliptic
    curve (weight 2) has `k = 2`. -/
def shadowK (k : ℝ) (s : ℂ) : ℂ := (k : ℂ) - starRingEnd ℂ s

/-- `shadowK k` is an involution for every real `k`. -/
theorem shadowK_involutive (k : ℝ) (s : ℂ) :
    shadowK k (shadowK k s) = s := by
  unfold shadowK
  simp [conj_ofReal]

/-- The fixed locus of `s ↦ k - conj(s)` is the vertical line `Re(s) = k/2`.
    This is the weight-`k` critical line. -/
theorem shadowK_fixed_locus (k : ℝ) (s : ℂ) :
    shadowK k s = s ↔ s.re = k / 2 := by
  unfold shadowK
  constructor
  · intro h
    have hre := congr_arg Complex.re h
    simp only [Complex.conj_re, Complex.sub_re, Complex.ofReal_re] at hre
    linarith
  · intro h
    apply Complex.ext
    · simp only [Complex.conj_re, Complex.sub_re, Complex.ofReal_re]
      linarith
    · simp only [Complex.conj_im, Complex.sub_im, Complex.ofReal_im]
      ring

/-- Specialization `k = 1`: recovers `GppFE.critical_line_is_fixed_locus`
    and `GppWeilCriterion.zetaInvolution_fixed_iff`. -/
theorem shadowK_fixed_locus_zeta (s : ℂ) :
    shadowK 1 s = s ↔ s.re = 1 / 2 := by
  simpa using shadowK_fixed_locus 1 s

/-- Specialization `k = 2`: the BSD central line `Re(s) = 1` is exactly
    the fixed locus of `s ↦ 2 - conj(s)`. -/
theorem shadowK_fixed_locus_ell (s : ℂ) :
    shadowK 2 s = s ↔ s.re = 1 := by
  simpa using shadowK_fixed_locus 2 s

/-- Holomorphic (no-conjugation) involution `s ↦ k - s`. Its only fixed
    *point* is the centre `s = k/2`, whereas `shadowK` fixes a whole line. -/
def shadowKHol (k : ℂ) (s : ℂ) : ℂ := k - s

theorem shadowKHol_involutive (k s : ℂ) :
    shadowKHol k (shadowKHol k s) = s := by
  unfold shadowKHol; ring

theorem shadowKHol_fixed_point (k s : ℂ) :
    shadowKHol k s = s ↔ s = k / 2 := by
  unfold shadowKHol
  constructor
  · intro h
    have hk : k = 2 * s := by
      rw [sub_eq_iff_eq_add] at h
      convert h using 1
      ring
    apply mul_left_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num)
    convert hk.symm using 1
    ring
  · intro h
    rw [h]
    ring

/-- Diagonal lift `D(s) = (s, s)` as in `GppDiagonalLift.D`, over `ℂ`. -/
def D (s : ℂ) : ℂ × ℂ := (s, s)

/-- Conformal dimension `Δ = h + h̄`. -/
def Delta (p : ℂ × ℂ) : ℂ := p.1 + p.2

/-- Weight-aware 2d shadow: each chiral weight reflects through `k/2`,
    i.e. `(h, h̄) ↦ (k - h, k - h̄)`. For `k = 1` this is
    `GppDiagonalLift.Shadow2`. -/
def ShadowK2 (k : ℂ) (p : ℂ × ℂ) : ℂ × ℂ := (k - p.1, k - p.2)

theorem delta_D (s : ℂ) : Delta (D s) = 2 * s := by
  unfold Delta D; ring

/-- The 1d shadow `s ↦ k - s` and the 2d shadow `ShadowK2 k` intertwine
    under the diagonal lift. -/
theorem D_shadow_intertwine (k s : ℂ) :
    D (k - s) = ShadowK2 k (D s) := by
  unfold D ShadowK2; rfl

/-- Consequently `Δ ↦ 2k - Δ`. Identifying this with the CFT_d pairing
    `Δ ↦ d - Δ` gives the dictionary value `d = 2k`.
    For zeta (`k = 1`) one recovers GPP's `d = 2`; for `L(E, s)` (`k = 2`)
    one obtains `d = 4`. This is an algebraic identification, not a theorem
    that the bulk dual of an elliptic curve is AdS_5. -/
theorem delta_shadowK2 (k s : ℂ) :
    Delta (ShadowK2 k (D s)) = 2 * k - Delta (D s) := by
  rw [← D_shadow_intertwine, delta_D, delta_D]
  ring

/-- Root-number parity at the centre. If a completed L-function satisfies
    `Λ(s) = -Λ(k - s)` (odd global root number), then `Λ(k/2) = 0`.
    For elliptic curves, `k = 2`, so an odd root number forces `L(E, 1) = 0`
    and therefore odd analytic rank. This is the functional equation, not BSD. -/
theorem root_number_odd_vanishes (Λ : ℂ → ℂ) (k : ℂ)
    (hFE : ∀ s, Λ s = -Λ (k - s)) :
    Λ (k / 2) = 0 := by
  have hk : k - k / 2 = k / 2 := by field_simp; ring
  have h := hFE (k / 2)
  rw [hk] at h
  -- h : Λ(k/2) = -Λ(k/2)
  rw [eq_neg_iff_add_eq_zero, ← two_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

end GppWeightKShadow
