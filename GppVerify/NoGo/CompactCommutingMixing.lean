import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.Sequences

/-!
# A compact operator commuting with a weakly mixing isometric symmetry is zero

Source: Codex, GPP-bridge PR #11 comment 6123884605 (2026-10-12; note
`work/codex/2026-10-12_daniel_haar_peter_weyl_critical_line_discreteness.md`). It builds on Daniel
Toupin's observation that multiplicative Haar fixes the unitary critical line while Peter–Weyl
quantizes the compact part `K` of the idele class group.

Codex's no-go: a compact operator on `L²(ℝ)` that commutes with all scale translations is zero. So
compactness of `K` alone cannot quantize the continuous Mellin variable `τ` while full dilation
symmetry remains.

**This file proves the abstract core (`eq_zero`).** Let `U n` be isometries on a complex inner
product space that are **weakly mixing**, `⟪U n x, y⟫ → 0` for all `x, y`. If a compact `T` commutes
with every `U n`, then `T = 0`.

Proof: `T(U n x) = U n (T x)` has constant norm `‖Tx‖`. Since the `U n x` stay in a ball,
compactness gives a norm-convergent subsequence `→ y`. Weak mixing forces `⟪y, w⟫ = 0` for all `w`,
so `y = 0`, hence `‖Tx‖ = 0`.

**Instance (stated, not formalized).** On `L²(ℝ)` the translations `τ_n f = f(· − n)` are unitary
and weakly mixing: `⟪τ_n f, g⟫ → 0`, by density of compactly supported functions. Through
`x = e^t`, these are the scale translations of `L²(ℝ_+, dx/x)`. The density argument is not
formalized here. **No RH or Yang–Mills claim.**
-/

namespace GppNoGo.CompactCommutingMixing

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **A compact operator commuting with a weakly mixing family of isometries is zero.** -/
theorem eq_zero (T : H →L[ℂ] H) (hT : IsCompactOperator T) (U : ℕ → H →L[ℂ] H)
    (hU : ∀ n x, ‖U n x‖ = ‖x‖) (hcomm : ∀ n x, T (U n x) = U n (T x))
    (hmix : ∀ x y, Tendsto (fun n => inner ℂ (U n x) y) atTop (𝓝 0)) : T = 0 := by
  ext x
  simp only [zero_apply]
  have hK := hT.isCompact_closure_image_closedBall (‖x‖)
  have hmem : ∀ n, T (U n x) ∈ closure (T '' Metric.closedBall 0 ‖x‖) := fun n =>
    subset_closure ⟨U n x, by simp [hU], rfl⟩
  obtain ⟨y, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  -- the limit is weakly zero, hence zero
  have hy : y = 0 := by
    have hw : ∀ w, inner ℂ y w = 0 := by
      intro w
      have h1 : Tendsto (fun n => inner ℂ (T (U (φ n) x)) w) atTop (𝓝 (inner ℂ y w)) :=
        Filter.Tendsto.inner hlim tendsto_const_nhds
      have h2 : Tendsto (fun n => inner ℂ (T (U (φ n) x)) w) atTop (𝓝 0) := by
        simp_rw [hcomm]
        exact (hmix (T x) w).comp hφ.tendsto_atTop
      exact tendsto_nhds_unique h1 h2
    exact inner_self_eq_zero.mp (hw y)
  -- the norms are constant
  have hn : Tendsto (fun n => ‖T (U (φ n) x)‖) atTop (𝓝 ‖y‖) := Filter.Tendsto.norm hlim
  simp_rw [hcomm, hU] at hn
  rw [hy, norm_zero] at hn
  exact norm_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hn)

end GppNoGo.CompactCommutingMixing
