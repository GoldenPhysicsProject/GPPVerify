import GppVerify.RiemannHypothesis.WeightedSuperadditivity

/-!
# The finite-rank variance Schur identity

Turbo relay `560639a`, formalisation queue item (d): for an idempotent `P` (the finite-rank projection onto
the first Legendre modes), `Q = 1 − P` and any `A`,

`P A Q A P = P A² P − (P A P)²`.

This is the "variance" `Z = H − F²` of GPP's canonical Schur test (`H = P A² P`, `F = P A P`). On a real
Hilbert space, for `P` an orthogonal projection and `A` self-adjoint, `Z` is positive semidefinite — indeed
`⟪x, Z x⟫ = ‖Q A P x‖² ≥ 0` — so the completed-square test `F − δ⁻¹ (H − F²) ⪰ 0` is a legitimate sufficient
certificate whenever the high-sector bound `W(h) ≥ δ ‖h‖²` holds.

**Scope.** The identity and its positivity only. The domain hypotheses (that the Weil form's symmetric
operator is bounded, or the quadratic-form version on the form domain), the high-sector coercivity bound, and
the verification of the test at any new width are **not** here: `Z ⪰ 0` is the easy half, and no positivity of
the Weil form follows. ARP, OB-6, RH are untouched.

No `sorry`, no axiom.
-/

noncomputable section

namespace GppVarianceSchur

/-- **Variance identity in any ring:** for `P² = P`, `P A (1 − P) A P = P A² P − (P A P)²`. -/
theorem variance_identity {R : Type*} [Ring R] (P A : R) (hP : P * P = P) :
    P * A * (1 - P) * A * P = P * A * A * P - (P * A * P) * (P * A * P) := by
  have h : (P * A * P) * (P * A * P) = P * A * P * A * P := by
    calc (P * A * P) * (P * A * P) = P * A * (P * P) * A * P := by noncomm_ring
      _ = P * A * P * A * P := by rw [hP]
  rw [h]
  noncomm_ring

open InnerProductSpace in
/-- **Positivity of the variance:** on a real Hilbert space, for `P` a self-adjoint idempotent and `A`
self-adjoint, `⟪x, (P A² P − (P A P)²) x⟫ = ‖(1 − P) A P x‖² ≥ 0`. -/
theorem variance_form {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P A : H →L[ℝ] H) (hP : P * P = P) (hPs : IsSelfAdjoint P) (hAs : IsSelfAdjoint A) (x : H) :
    inner ℝ x ((P * A * A * P - (P * A * P) * (P * A * P)) x) = ‖(1 - P) (A (P x))‖ ^ 2 := by
  have hid := variance_identity P A hP
  rw [← hid]
  have hsP : ∀ u v : H, inner ℝ (P u) v = inner ℝ u (P v) := fun u v => hPs.isSymmetric u v
  have hsA : ∀ u v : H, inner ℝ (A u) v = inner ℝ u (A v) := fun u v => hAs.isSymmetric u v
  have hPi : ∀ y : H, P (P y) = P y := fun y => by
    have := congrArg (fun T : H →L[ℝ] H => T y) hP
    simpa using this
  have hQi : ∀ y : H, (1 - P) ((1 - P) y) = (1 - P) y := fun y => by
    simp only [sub_apply, one_apply_eq_self, map_sub, hPi]
    abel
  have hsQ : ∀ u v : H, inner ℝ ((1 - P) u) v = inner ℝ u ((1 - P) v) := fun u v => by
    simp only [sub_apply, one_apply_eq_self, inner_sub_left,
      inner_sub_right, hsP]
  simp only [mul_apply_eq_comp]
  have e1 : inner ℝ x (P (A ((1 - P) (A (P x))))) = inner ℝ (P x) (A ((1 - P) (A (P x)))) :=
    (hsP x _).symm
  have e2 : inner ℝ (P x) (A ((1 - P) (A (P x)))) = inner ℝ (A (P x)) ((1 - P) (A (P x))) :=
    (hsA (P x) _).symm
  have e3 : inner ℝ (A (P x)) ((1 - P) (A (P x))) = ‖(1 - P) (A (P x))‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    have h1 : inner ℝ (A (P x)) ((1 - P) (A (P x))) =
        inner ℝ (A (P x)) ((1 - P) ((1 - P) (A (P x)))) := by rw [hQi]
    rw [h1, ← hsQ (A (P x)) ((1 - P) (A (P x)))]
  rw [e1, e2, e3]

theorem variance_nonneg {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P A : H →L[ℝ] H) (hP : P * P = P) (hPs : IsSelfAdjoint P) (hAs : IsSelfAdjoint A) (x : H) :
    0 ≤ inner ℝ x ((P * A * A * P - (P * A * P) * (P * A * P)) x) := by
  rw [variance_form P A hP hPs hAs x]; positivity

end GppVarianceSchur

#print axioms GppVarianceSchur.variance_identity
#print axioms GppVarianceSchur.variance_nonneg
