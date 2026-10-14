import GppVerify.RiemannHypothesis.TwoFacePoleSignature

/-!
# Four orientation lifts: the charge-time Klein group and its indefinite mirror

Source: Daniel Toupin, Golden Physics Project, Which Way Is Forward,
and GPP-bridge/work/codex/2026-10-14_four_sector_yakaboylu_metric_domain.md.

There are four independent (q,t) orientation labels (++),(+-),(-+),(--).
Charge and microscopic time flips commute and their product reverses both.
The resulting real reflection quadratic has precisely two positive and two
negative spectral channels. Reversal invariance of the OBSERVABLE chi=qt
does not assert that the full mirror pairing is a positive Hilbert metric.

Pure finite-dimensional algebra, no zeta zeros, no Weil positivity or RH.
-/

namespace GppFourOrientationMirror

/-- Coordinates in the order (q,t)=(++),(+-),(-+),(--). -/
structure Lifts where
  pp : ℝ
  pm : ℝ
  mp : ℝ
  mm : ℝ

/-- Reverse the charge orientation only. -/
def chargeFlip (v : Lifts) : Lifts :=
  ⟨v.mp, v.mm, v.pp, v.pm⟩

/-- Reverse the microscopic time orientation only. -/
def timeFlip (v : Lifts) : Lifts :=
  ⟨v.pm, v.pp, v.mm, v.mp⟩

/-- Simultaneous reversal (q,t) ↦ (-q,-t). -/
def mirror (v : Lifts) : Lifts :=
  ⟨v.mm, v.mp, v.pm, v.pp⟩

/-- The observable orientation chi=q*t acts as (+,-,-,+). -/
def chi (v : Lifts) : Lifts :=
  ⟨v.pp, -v.pm, -v.mp, v.mm⟩

theorem flips_commute (v : Lifts) :
    chargeFlip (timeFlip v) = timeFlip (chargeFlip v) := by
  rfl

theorem two_flips_eq_mirror (v : Lifts) :
    chargeFlip (timeFlip v) = mirror v := by
  rfl

theorem mirror_involution (v : Lifts) : mirror (mirror v) = v := by
  cases v
  rfl

theorem chi_mirror_commute (v : Lifts) : chi (mirror v) = mirror (chi v) := by
  rfl

/-- The bilinear form for the full simultaneous orientation reflection. -/
def mirrorForm (v : Lifts) : ℝ :=
  2 * (v.pp * v.mm + v.pm * v.mp)

/-- Signed symmetric/antisymmetric mirror decomposition. -/
theorem mirror_form_decomposition (a b c d : ℝ) :
    mirrorForm ⟨a,b,c,d⟩ =
      ((a+d)^2+(b+c)^2-(a-d)^2-(b-c)^2)/2 := by
  unfold mirrorForm
  ring

/-- For a mirror-even vector the form is positive semidefinite. -/
theorem even_form_nonneg (a b : ℝ) :
    0 ≤ mirrorForm ⟨a,b,b,a⟩ := by
  unfold mirrorForm
  nlinarith [sq_nonneg a, sq_nonneg b]

/-- For a mirror-odd vector the form is negative semidefinite. -/
theorem odd_form_nonpos (a b : ℝ) :
    mirrorForm ⟨a,b,-b,-a⟩ ≤ 0 := by
  unfold mirrorForm
  nlinarith [sq_nonneg a, sq_nonneg b]

theorem even_plus_strict : 0 < mirrorForm ⟨1,0,0,1⟩ := by
  norm_num [mirrorForm]

theorem even_minus_strict : 0 < mirrorForm ⟨0,1,1,0⟩ := by
  norm_num [mirrorForm]

theorem odd_plus_strict : mirrorForm ⟨1,0,0,-1⟩ < 0 := by
  norm_num [mirrorForm]

theorem odd_minus_strict : mirrorForm ⟨0,1,-1,0⟩ < 0 := by
  norm_num [mirrorForm]

/-- The physical observable chi survives simultaneous reversal. -/
theorem chi_invariant_pairing (v : Lifts) :
    mirrorForm (chi v) = mirrorForm v := by
  unfold mirrorForm chi
  ring

end GppFourOrientationMirror
