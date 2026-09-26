import Mathlib.Tactic

/-!
# Neutral-fermion portal for direct conjugacy half flips

A bilinear which mixes a fermionic field with its charge conjugate carries twice the
field's Abelian charge.  Schematically, if `psi -> exp(i q alpha) psi`, then a Majorana-type
term `psi^T C psi` transforms with phase `exp(2 i q alpha)`.

Hence an unbroken U(1) gauge symmetry permits such a direct local conjugacy-mixing term only
for a neutral field (or when an additional charge-`-2q` background/field participates).
This is the clean algebraic reason charged Dirac fermions cannot freely oscillate into their
antiparticles whereas neutral fermions can admit Majorana mixing.

In the orientation programme this makes neutral fermions a distinguished possible portal
for a microscopic *half flip* of representation-conjugacy orientation.  The physical claim
that neutrinos implement the cosmological sheet transition is not made here.
-/

namespace GppMajoranaHalfFlipNeutralPortal

/-- Abelian charge carried by a same-field conjugacy-mixing bilinear. -/
def mixingCharge (q : ℝ) : ℝ := 2*q

/-- The mixing bilinear is neutral exactly when the fermion itself is neutral. -/
theorem mixing_gauge_neutral_iff (q : ℝ) :
    mixingCharge q = 0 ↔ q = 0 := by
  simp [mixingCharge]

/-- A nonzero charged field cannot have a gauge-neutral bare Majorana mixing term. -/
theorem nonzero_charge_forbids_neutral_bare_mixing
    (q : ℝ) (hq : q ≠ 0) : mixingCharge q ≠ 0 := by
  intro h
  exact hq ((mixing_gauge_neutral_iff q).1 h)

/-- If a compensating background carries `-2q`, total Abelian charge is restored. -/
theorem compensating_double_charge_restores_neutrality (q : ℝ) :
    mixingCharge q + (-2*q) = 0 := by
  simp [mixingCharge]

/-- Changing an additive conjugacy-odd number `b` to its opposite changes the subsystem
    number by exactly `-2b`; this is the analogous selection rule for baryon/lepton-like
    charges even when electric charge happens to vanish. -/
theorem conjugacy_flip_changes_odd_charge_by_double (b : ℝ) :
    (-b) - b = -2*b := by ring

end GppMajoranaHalfFlipNeutralPortal
