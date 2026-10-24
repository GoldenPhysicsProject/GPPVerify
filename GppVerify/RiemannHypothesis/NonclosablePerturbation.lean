import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# A sequence witness of nonclosability survives every bounded perturbation

Source: Codex, GPP-bridge `work/codex/2026-10-24_pr11_wave327_strategic_pivot_source_ward.md`
§"A precise domain no-go" (commit `5f5c9a3`). Daniel Toupin / Golden Physics Project, with AI
assistance from Codex (statement) and Claude Code (formalization).

For a densely defined (partial) linear map `B : D ⊂ E → F`:

* `not_isClosable_of_tendsto`: if test vectors `x_n ∈ D` satisfy `x_n → 0` but `B x_n → g ≠ 0`,
  then `(0, g)` lies in the closure of the graph, so `B` is not closable.
* `not_isClosable_vadd`: the same sequence then witnesses that `C + B` is not closable for every
  continuous linear `C : E → F`, because `C x_n → 0`. So no bounded correction, in the same source
  and target topologies, repairs the nonclosability.

**Scope.** Abstract operator theory only. It does not construct the GCD / critical-Möbius
packets that supply the sequence (that construction is Codex's, and the earlier nonclosability
results are `GppGcdPacketClosability` and `GppTFDGCDMobius`). As Codex notes, a bound proved
in a different coefficient topology does not by itself give a bounded `C` in this setting.
No claim about RH.
-/

open Filter Topology

namespace GppNonclosablePerturbation

variable {R E F : Type*} [CommRing R] [AddCommGroup E] [AddCommGroup F] [Module R E] [Module R F]
  [TopologicalSpace E] [TopologicalSpace F] [ContinuousAdd E] [ContinuousAdd F]
  [TopologicalSpace R] [ContinuousSMul R E] [ContinuousSMul R F]

/-- **Sequence witness of nonclosability.** `x_n → 0` with `B x_n → g ≠ 0` forbids closability. -/
theorem not_isClosable_of_tendsto (B : E →ₗ.[R] F) (x : ℕ → B.domain) {g : F} (hg : g ≠ 0)
    (h0 : Tendsto (fun n => (x n : E)) atTop (𝓝 0))
    (h1 : Tendsto (fun n => B (x n)) atTop (𝓝 g)) : ¬ B.IsClosable := by
  rintro ⟨B', hB'⟩
  have hmem : ((0 : E), g) ∈ B.graph.topologicalClosure := by
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    exact mem_closure_of_tendsto (h0.prodMk_nhds h1)
      (Eventually.of_forall fun n => B.mem_graph (x n))
  rw [hB', LinearPMap.mem_graph_iff] at hmem
  obtain ⟨y, hy1, hy2⟩ := hmem
  have hy : y = 0 := Subtype.ext hy1
  rw [hy, LinearPMap.map_zero] at hy2
  exact hg hy2.symm

/-- **Bounded corrections cannot repair it.** For every continuous linear `C`, the same sequence
shows `C + B` is not closable. -/
theorem not_isClosable_vadd (B : E →ₗ.[R] F) (C : E →L[R] F) (x : ℕ → B.domain) {g : F}
    (hg : g ≠ 0) (h0 : Tendsto (fun n => (x n : E)) atTop (𝓝 0))
    (h1 : Tendsto (fun n => B (x n)) atTop (𝓝 g)) :
    ¬ ((C : E →ₗ[R] F) +ᵥ B).IsClosable := by
  refine not_isClosable_of_tendsto ((C : E →ₗ[R] F) +ᵥ B) x hg h0 ?_
  have hC : Tendsto (fun n => C (x n : E)) atTop (𝓝 0) := by
    have h := (C.continuous.tendsto 0).comp h0
    rw [map_zero] at h
    exact h
  simpa [LinearPMap.vadd_apply] using hC.add h1

end GppNonclosablePerturbation
