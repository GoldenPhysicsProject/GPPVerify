import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Finite heat-semigroup Gram positivity

The arithmetic heat-trace criterion for RH asks for positivity of every matrix

    G_ij = K(t_i+t_j),   t_i>0.

Whenever a heat kernel has a positive finite spectral representation

    K(t) = sum_k w_k exp(-alpha_k t),
    w_k >= 0,

its Gram factorization is automatic: the feature attached to spectral mode `k` and time
`t_i` is `exp(-alpha_k t_i)`, and the corresponding quadratic form is

    sum_k w_k (sum_i c_i exp(-alpha_k t_i))^2 >= 0.

This file formalizes that sum-of-squares core.  It is deliberately zero-independent.  The
hard arithmetic theorem is to identify the completed prime--Archimedean heat trace with such
a positive spectral Gram representation without assuming RH.
-/

namespace GppFiniteHeatGramPositive

/-- One real heat-semigroup feature. -/
noncomputable def heatFeature (alpha t : ℝ) : ℝ := Real.exp (-alpha * t)

/-- Finite positive spectral heat kernel. -/
noncomputable def finiteHeatKernel {m : ℕ}
    (w alpha : Fin m → ℝ) (t : ℝ) : ℝ :=
  ∑ k, w k * heatFeature (alpha k) t

/-- The two-time Gram kernel coming from the same finite spectral features. -/
noncomputable def finiteHeatGramKernel {m : ℕ}
    (w alpha : Fin m → ℝ) (s t : ℝ) : ℝ :=
  ∑ k, w k * heatFeature (alpha k) s * heatFeature (alpha k) t

/-- Semigroup factorization: the two-time feature kernel is the heat kernel at `s+t`. -/
theorem finiteHeatGramKernel_eq_add {m : ℕ}
    (w alpha : Fin m → ℝ) (s t : ℝ) :
    finiteHeatGramKernel w alpha s t = finiteHeatKernel w alpha (s+t) := by
  classical
  unfold finiteHeatGramKernel finiteHeatKernel heatFeature
  apply Finset.sum_congr rfl
  intro k _
  rw [← Real.exp_add]
  congr 1
  ring

/-- Coefficient synthesis in spectral mode `k`. -/
noncomputable def heatSynthesis {m n : ℕ}
    (alpha : Fin m → ℝ) (t c : Fin n → ℝ) (k : Fin m) : ℝ :=
  ∑ i, c i * heatFeature (alpha k) (t i)

/-- The finite Gram quadratic form, already written in its spectral sum-of-squares form. -/
noncomputable def heatGramQuadratic {m n : ℕ}
    (w alpha : Fin m → ℝ) (t c : Fin n → ℝ) : ℝ :=
  ∑ k, w k * (heatSynthesis alpha t c k)^2

/-- Positive spectral weights make the heat Gram quadratic form nonnegative. -/
theorem heatGramQuadratic_nonneg {m n : ℕ}
    (w alpha : Fin m → ℝ) (t c : Fin n → ℝ)
    (hw : ∀ k, 0 ≤ w k) :
    0 ≤ heatGramQuadratic w alpha t c := by
  unfold heatGramQuadratic
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hw k) (sq_nonneg _))

/-- Strictly positive weight plus a nonzero synthesized mode gives strict positivity of
that individual spectral contribution. -/
theorem heatModeContribution_pos {m n : ℕ}
    (w alpha : Fin m → ℝ) (t c : Fin n → ℝ) (k : Fin m)
    (hw : 0 < w k) (hs : heatSynthesis alpha t c k ≠ 0) :
    0 < w k * (heatSynthesis alpha t c k)^2 := by
  exact mul_pos hw (sq_pos_of_ne_zero hs)

/-- The finite positive-spectrum package: additive heat-semigroup factorization together
with positivity of every coefficient synthesis. -/
theorem finite_heat_semigroup_gram_package {m n : ℕ}
    (w alpha : Fin m → ℝ) (t c : Fin n → ℝ)
    (hw : ∀ k, 0 ≤ w k) (s u : ℝ) :
    finiteHeatGramKernel w alpha s u = finiteHeatKernel w alpha (s+u) ∧
    0 ≤ heatGramQuadratic w alpha t c := by
  exact ⟨finiteHeatGramKernel_eq_add w alpha s u,
    heatGramQuadratic_nonneg w alpha t c hw⟩

end GppFiniteHeatGramPositive
