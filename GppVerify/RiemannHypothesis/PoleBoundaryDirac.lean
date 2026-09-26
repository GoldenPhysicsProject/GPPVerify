import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# The completed pole plane as a first-order boundary Dirac block

For the CCM semilocal Weil matrix, the elementary s=0,1 term factors as

  W02 = (1/2) (|c><c| - |s><s|).

Writing p = 4*pi*n and absorbing the common finite-window normalization into K,
the two Fourier coefficients are

  c(p) = K L / (L^2 + p^2),
  s(p) = K p / (L^2 + p^2),

while the physical dilation frequency is d(p)=p/(2L).

The point of this file is that these coefficients satisfy an exact first-order
two-state system

  d c = s/2,
  d s = -c/2 + kappa,

where kappa=K/(2L) is independent of p.  Therefore the failure of the
(c,s)-plane to close under the first-order generator is rank one, entirely in
the constant boundary channel eta.

Entrywise this gives

  [D,W02]_{pq} = (kappa/2) (s(p)-s(q)),

i.e.

  [D,W02] = (kappa/2)(s eta^T - eta s^T).

This is the exact finite-cutoff algebra behind the elementary s=0,1 completion.
It does not prove RH.
-/

namespace GppPoleBoundaryDirac

noncomputable section

/-- Even pole coefficient, with common normalization K and window length L. -/
def poleEven (K L p : ℂ) : ℂ :=
  K * L / (L ^ 2 + p ^ 2)

/-- Odd pole coefficient. -/
def poleOdd (K L p : ℂ) : ℂ :=
  K * p / (L ^ 2 + p ^ 2)

/-- Physical first-order frequency when p=4*pi*n. -/
def poleFreq (L p : ℂ) : ℂ :=
  p / (2 * L)

/-- Momentum-independent boundary defect. -/
def poleKappa (K L : ℂ) : ℂ :=
  K / (2 * L)

/-- The first half of the pole Dirac system: d c = s/2. -/
theorem poleFreq_mul_even
    {K L p : ℂ}
    (hL : L ≠ 0)
    (hden : L ^ 2 + p ^ 2 ≠ 0) :
    poleFreq L p * poleEven K L p = poleOdd K L p / 2 := by
  unfold poleFreq poleEven poleOdd
  field_simp [hL, hden]
  ring

/-- The second half closes only modulo the constant boundary channel:
    d s = -c/2 + kappa. -/
theorem poleFreq_mul_odd
    {K L p : ℂ}
    (hL : L ≠ 0)
    (hden : L ^ 2 + p ^ 2 ≠ 0) :
    poleFreq L p * poleOdd K L p =
      -poleEven K L p / 2 + poleKappa K L := by
  unfold poleFreq poleEven poleOdd poleKappa
  field_simp [hL, hden]
  ring

/-- Entry of the rank-two pole matrix. -/
def poleMatrixEntry (K L p q : ℂ) : ℂ :=
  (poleEven K L p * poleEven K L q -
    poleOdd K L p * poleOdd K L q) / 2

/--
Exact entrywise commutator identity.  With a diagonal generator
D_pp = poleFreq(L,p), the left side is [D,W02]_{pq}; the right side is
the rank-two boundary form (kappa/2)(s eta^T - eta s^T)_{pq}.
-/
theorem pole_commutator_entry
    {K L p q : ℂ}
    (hL : L ≠ 0)
    (hp : L ^ 2 + p ^ 2 ≠ 0)
    (hq : L ^ 2 + q ^ 2 ≠ 0) :
    (poleFreq L p - poleFreq L q) * poleMatrixEntry K L p q =
      poleKappa K L / 2 * (poleOdd K L p - poleOdd K L q) := by
  unfold poleFreq poleMatrixEntry poleEven poleOdd poleKappa
  field_simp [hL, hp, hq]
  ring

/--
The rank-one coefficient 1/2 is exactly what turns scalar Krein feedback into
unit translation in the reciprocal response y=2/r.
-/
theorem half_rank_one_feedback_translation
    {r : ℂ} (hr : r ≠ 0) (hden : 1 + r / 2 ≠ 0) :
    2 / (r / (1 + r / 2)) = 2 / r + 1 := by
  field_simp [hr, hden]
  ring

/-- The negative pole channel gives the inverse unit translation. -/
theorem negative_half_feedback_translation
    {r : ℂ} (hr : r ≠ 0) (hden : 1 - r / 2 ≠ 0) :
    2 / (r / (1 - r / 2)) = 2 / r - 1 := by
  field_simp [hr, hden]
  ring

/--
Opposite Weyl boundary conditions act by m -> -1/m.  After the canonical
half-density normalization r=2 i m this is exactly r -> 4/r.
-/
theorem normalized_weyl_duality_is_four_over
    {m : ℂ} (hm : m ≠ 0) :
    2 * Complex.I * (-1 / m) = 4 / (2 * Complex.I * m) := by
  field_simp [hm, Complex.I_ne_zero]
  ring_nf
  simp [Complex.I_mul_I]

end

end GppPoleBoundaryDirac
