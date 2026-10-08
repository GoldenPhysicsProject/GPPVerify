import GppVerify.RiemannHypothesis.RankOneThresholdControls

/-!
# Parity threshold closure for the semilocal Weil form

This is the finite algebraic closure theorem suggested by the Oct. 3--4
semilocal passive-network experiments.

It does **not** prove the arithmetic hypotheses.  It proves that once the
even block has the Hodge-index-one threshold data

  cᵀ A_e⁻¹ c = -2

and is positive on c^⊥, while the odd block is positive definite with

  sᵀ A_o⁻¹ s = 2,

then the two rank-one pole corrections make the complete parity-split
quadratic form nonnegative.

Thus the remaining analytic RH target is isolated cleanly: establish those
block hypotheses for the actual semilocal prime--Archimedean operator on
every window.
-/

open Matrix

namespace GppArrowWeilHodgeClosure

variable {e o : Type*}
  [Fintype e] [DecidableEq e]
  [Fintype o] [DecidableEq o]

/-- The even and odd threshold mechanisms close simultaneously.

The even channel uses the +1/2 rank-one correction and the odd channel uses
the -1/2 rank-one correction.  Under the exact threshold identities, their
quadratic forms are separately nonnegative, hence so is their sum. -/
theorem paired_threshold_quadratic_nonneg
    (Ae : Matrix e e ℝ) (hAeSymm : Ae.IsSymm) (hAeDet : IsUnit Ae.det)
    (c : e → ℝ)
    (hc : c ⬝ᵥ (Ae⁻¹ *ᵥ c) = -2)
    (hAePerp :
      ∀ y : e → ℝ, y ⬝ᵥ c = 0 → y ≠ 0 → 0 < y ⬝ᵥ (Ae *ᵥ y))
    (Ao : Matrix o o ℝ) (hAoSymm : Ao.IsSymm) (hAoDet : IsUnit Ao.det)
    (s : o → ℝ)
    (hs : s ⬝ᵥ (Ao⁻¹ *ᵥ s) = 2)
    (hAoPos : ∀ y : o → ℝ, y ≠ 0 → 0 < y ⬝ᵥ (Ao *ᵥ y))
    (xe : e → ℝ) (xo : o → ℝ) :
    0 ≤
      xe ⬝ᵥ ((Ae + (1 / 2 : ℝ) • Matrix.vecMulVec c c) *ᵥ xe) +
      xo ⬝ᵥ ((Ao - (1 / 2 : ℝ) • Matrix.vecMulVec s s) *ᵥ xo) := by
  have he :
      0 ≤ xe ⬝ᵥ ((Ae + (1 / 2 : ℝ) • Matrix.vecMulVec c c) *ᵥ xe) :=
    (GppRankOneControls.pole_threshold_neg
      Ae hAeSymm hAeDet c hc hAePerp).1 xe
  have ho :
      0 ≤ xo ⬝ᵥ ((Ao - (1 / 2 : ℝ) • Matrix.vecMulVec s s) *ᵥ xo) :=
    (GppRankOneControls.pole_threshold_pos
      Ao hAoSymm hAoDet s hs hAoPos).1 xo
  linarith

/-- The same closure exposed channel-by-channel. -/
theorem paired_threshold_channels_nonneg
    (Ae : Matrix e e ℝ) (hAeSymm : Ae.IsSymm) (hAeDet : IsUnit Ae.det)
    (c : e → ℝ)
    (hc : c ⬝ᵥ (Ae⁻¹ *ᵥ c) = -2)
    (hAePerp :
      ∀ y : e → ℝ, y ⬝ᵥ c = 0 → y ≠ 0 → 0 < y ⬝ᵥ (Ae *ᵥ y))
    (Ao : Matrix o o ℝ) (hAoSymm : Ao.IsSymm) (hAoDet : IsUnit Ao.det)
    (s : o → ℝ)
    (hs : s ⬝ᵥ (Ao⁻¹ *ᵥ s) = 2)
    (hAoPos : ∀ y : o → ℝ, y ≠ 0 → 0 < y ⬝ᵥ (Ao *ᵥ y)) :
    (∀ xe : e → ℝ,
      0 ≤ xe ⬝ᵥ ((Ae + (1 / 2 : ℝ) • Matrix.vecMulVec c c) *ᵥ xe)) ∧
    (∀ xo : o → ℝ,
      0 ≤ xo ⬝ᵥ ((Ao - (1 / 2 : ℝ) • Matrix.vecMulVec s s) *ᵥ xo)) := by
  constructor
  · exact (GppRankOneControls.pole_threshold_neg
      Ae hAeSymm hAeDet c hc hAePerp).1
  · exact (GppRankOneControls.pole_threshold_pos
      Ao hAoSymm hAoDet s hs hAoPos).1

end GppArrowWeilHodgeClosure
