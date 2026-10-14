import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Intertwined metrics pick up `|c|²`: the BPY-to-seed `1/d` conformal covariance

Source: Codex, GPP-bridge `research/codex/2026-09-30_bpy_seed_conformal_metric.md`.

If `J U = c • T J` with `T` an isometry (`T† T = 1`), then the pulled-back metric `G = J† J`
satisfies `U† G U = |c|² G` (`metric_covariance`). For Codex's `J = C_θ C_B⁻¹`, with
`U = U_d` (BPY dilation isometry), `T = T_{log d}` (unitary translation) and `c = d^{−1/2}`, this
is `U_d† G U_d = d⁻¹ G` (`metric_covariance_real`, with `c` real). That is the `1/d` weight shared
with `Λ(d)/d` and the critical Bost–Connes expectation `ω₁(P_d) = 1/d`. The boundedness inputs on
`C_θ` and `C_B` are Codex's established maps and are taken as hypotheses here. The frame inequality
the note targets next is **not** proved. **No RH claim.**
-/

namespace GppBpySeedConformalMetric

open ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Conformal covariance of the pulled-back metric.** -/
theorem metric_covariance (J : E →L[ℂ] F) (U : E →L[ℂ] E) (T : F →L[ℂ] F) (c : ℂ)
    (hT : adjoint T ∘L T = 1) (hJ : J ∘L U = c • (T ∘L J)) :
    adjoint U ∘L (adjoint J ∘L J) ∘L U = ((starRingEnd ℂ) c * c) • (adjoint J ∘L J) := by
  have h1 : adjoint U ∘L (adjoint J ∘L J) ∘L U = adjoint (J ∘L U) ∘L (J ∘L U) := by
    rw [adjoint_comp]; rfl
  rw [h1, hJ, map_smulₛₗ, adjoint_comp]
  ext x
  simp only [comp_apply, smul_apply, map_smul, smul_smul]
  have : adjoint T (T (J x)) = J x := by
    simpa using congrArg (fun A : F →L[ℂ] F => A (J x)) hT
  rw [this, mul_comm]

/-- Real scale `c = d^{−1/2}`: `U† G U = c² G`. -/
theorem metric_covariance_real (J : E →L[ℂ] F) (U : E →L[ℂ] E) (T : F →L[ℂ] F) (c : ℝ)
    (hT : adjoint T ∘L T = 1) (hJ : J ∘L U = (c : ℂ) • (T ∘L J)) :
    adjoint U ∘L (adjoint J ∘L J) ∘L U = ((c ^ 2 : ℝ) : ℂ) • (adjoint J ∘L J) := by
  rw [metric_covariance J U T c hT hJ, Complex.conj_ofReal]
  push_cast; ring_nf

end GppBpySeedConformalMetric
