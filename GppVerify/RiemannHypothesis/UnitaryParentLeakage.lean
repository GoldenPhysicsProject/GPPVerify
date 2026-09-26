import Mathlib.Tactic

/-!
# Lossless parent, contractive compression, and the no-leakage strengthening

Suppose a lossless parent channel splits every input x into an observed component T x and
a hidden/leakage component H x with the exact energy identity

    ||T x||^2 + ||H x||^2 = ||x||^2.

Then T is automatically contractive.  Therefore ordinary contractivity of such a
compression cannot by itself encode a deep spectral condition.

The genuinely stronger condition is isometry of T.  Under the same identity,

    ||T x|| = ||x|| for every x

holds exactly when

    H x = 0 for every x.

This is the abstract algebra behind the Hardy decomposition of a unitary boundary
multiplier into causal Toeplitz and anticausal Hankel components:

    T^*T + H^*H = I.

For the RH program the no-leakage statement H=0 is the meaningful target.
-/

namespace GppUnitaryParentLeakage

variable {X Y Z : Type*}
  [SeminormedAddCommGroup X]
  [SeminormedAddCommGroup Y]
  [SeminormedAddCommGroup Z]

/-- Exact lossless energy splitting. -/
def LosslessSplit (T : X → Y) (H : X → Z) : Prop :=
  ∀ x : X, ‖T x‖^2 + ‖H x‖^2 = ‖x‖^2

/-- A lossless observed compression is automatically contractive. -/
theorem contractive_of_lossless
    (T : X → Y) (H : X → Z)
    (hsplit : LosslessSplit T H) :
    ∀ x : X, ‖T x‖ ≤ ‖x‖ := by
  intro x
  have h := hsplit x
  have hT : 0 ≤ ‖T x‖ := norm_nonneg _
  have hH2 : 0 ≤ ‖H x‖^2 := sq_nonneg _
  have hx : 0 ≤ ‖x‖ := norm_nonneg _
  nlinarith

/-- If the hidden channel vanishes, the observed channel is isometric. -/
theorem isometric_of_lossless_of_noLeakage
    (T : X → Y) (H : X → Z)
    (hsplit : LosslessSplit T H)
    (hzero : ∀ x : X, H x = 0) :
    ∀ x : X, ‖T x‖ = ‖x‖ := by
  intro x
  have h := hsplit x
  rw [hzero x, norm_zero] at h
  have hT : 0 ≤ ‖T x‖ := norm_nonneg _
  have hx : 0 ≤ ‖x‖ := norm_nonneg _
  nlinarith

/-- Isometry of the observed channel forces zero leakage. -/
theorem noLeakage_of_lossless_of_isometric
    (T : X → Y) (H : X → Z)
    (hsplit : LosslessSplit T H)
    (hiso : ∀ x : X, ‖T x‖ = ‖x‖) :
    ∀ x : X, H x = 0 := by
  intro x
  have h := hsplit x
  rw [hiso x] at h
  have hn : ‖H x‖ = 0 := by
    have hnon : 0 ≤ ‖H x‖ := norm_nonneg _
    nlinarith
  exact norm_eq_zero.mp hn

/--
Capstone: for a lossless parent, no leakage is exactly the strengthening from
contractivity to isometry.
-/
theorem isometric_iff_noLeakage
    (T : X → Y) (H : X → Z)
    (hsplit : LosslessSplit T H) :
    (∀ x : X, ‖T x‖ = ‖x‖) ↔
      (∀ x : X, H x = 0) := by
  constructor
  · exact noLeakage_of_lossless_of_isometric T H hsplit
  · exact isometric_of_lossless_of_noLeakage T H hsplit

end GppUnitaryParentLeakage

#print axioms GppUnitaryParentLeakage.contractive_of_lossless
#print axioms GppUnitaryParentLeakage.isometric_iff_noLeakage
