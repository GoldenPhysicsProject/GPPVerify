import GppVerify.RiemannHypothesis.RungOneReductionTwo
import GppVerify.Upstream.DigammaVerticalBounds

/-!
# An elementary lower bound for the window symbol

For every shift `M`, the window symbol `Ψ₂(r) - β₂(25)` (`GppRungOneReductionTwo.symbolTwo`,
`betaTwo`) is bounded below by an explicit elementary function `G_M(r)`:

  `G_M(r) = ½ log((M + ¾)² + r²/4) - (M + ¼)/((M + ¼)² + r²/4) - Σ_{k<M} (k + ¼)/((k + ¼)² + r²/4)
            - 1/(4((M + ¾)² + r²/4)) - log π - A₂ cos(r log 2) - β₂(25)`

(`GM_le`), from the staged vertical digamma bounds (`Complex.re_digamma_ge_asymp` after
`Complex.re_digamma_shift`). Only a logarithm, `M + 1` rational functions and one cosine appear, so a
piecewise-polynomial minorant of `G_M` can be certified in rational arithmetic, with no polygamma
values. Float scans (GPP-bridge `work/claude-code/rung1/b_route_scan.py`; evidence only) give
`max_r (Ψ₂ - β₂ - G_M) ≈ 0.28/M²` on `[0, 25]`.

Unconditional; no `sorry`, no axioms.
-/

namespace GppWindowGM

open Finset GppRungOneReductionTwo

/-- The elementary lower bound `G_M`. -/
noncomputable def GM (M : ℕ) (r : ℝ) : ℝ :=
  Real.log ((1 / 4 + (M : ℝ) + 1 / 2) ^ 2 + (r / 2) ^ 2) / 2
    - (1 / 4 + (M : ℝ)) / ((1 / 4 + (M : ℝ)) ^ 2 + (r / 2) ^ 2)
    - ∑ k ∈ range M, (1 / 4 + (k : ℝ)) / ((1 / 4 + (k : ℝ)) ^ 2 + (r / 2) ^ 2)
    - 1 / ((1 / 4 + (M : ℝ) + 1 / 2) ^ 2 + (r / 2) ^ 2) / 4
    - Real.log Real.pi - primeTwoCos r - betaTwo 25

/-- **`G_M` is below the window symbol.** -/
theorem GM_le (M : ℕ) (r : ℝ) : GM M r ≤ symbolTwo r - betaTwo 25 := by
  have ha : (0 : ℝ) < 1 / 4 := by norm_num
  have hshift := Complex.re_digamma_shift ha (r / 2) M
  have hM : (0 : ℝ) < 1 / 4 + M := by positivity
  have hlow := Complex.re_digamma_ge_asymp hM (r / 2)
  unfold Complex.DigammaGauss.logPot Complex.DigammaGauss.invQuad at hlow
  unfold GM symbolTwo
  linarith

end GppWindowGM

#print axioms GppWindowGM.GM_le
