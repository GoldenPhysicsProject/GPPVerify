import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Strict interlacing from positive residues: the abstract IVT core

`formalization_queue` item `9cc1e2f8` ("Positive residues imply strict parity
interlacing"), Weil-Parity thread — explicitly named in `CLAUDE.md` and
`docs/FORMALIZATION_PLAN.md` as the natural next target after the earlier cross-resolvent
work, since it needs genuine monotonicity/IVT reasoning, not just block-matrix algebra.

The queue item's own framing: with `f(z) = Σ_j c_j/(α_j - z)` for `α_0 < ... < α_n` and all
`c_j > 0`, `f` is strictly increasing on each interval `(α_j, α_{j+1})`, tends from `-∞` to
`+∞` there, and has exactly one zero — the interlacing eigenvalue `β_j` of the odd block.

## What this file proves

The fully general, self-contained real-analysis core, stripped of the specific rational-
function structure so it can be reused verbatim once the per-interval monotonicity and
boundary-blowup facts for `f = Σ c_j/(α_j - z)` are established (not attempted in this
file — see honest boundary below): a function continuous and strictly increasing on an
open interval `(a,b)`, tending to `-∞` approaching `a` and `+∞` approaching `b`, has
exactly one zero in `(a,b)`.

## What this file does NOT do

Does **not** construct `f = Σ_j c_j/(α_j - z)` from the matrix data (`A`, `B`, `η`, `e₀`)
at all, and does not verify that this specific `f` satisfies the three hypotheses
(`StrictMonoOn`, `ContinuousOn`, the two `Tendsto` boundary conditions) on each interval
`(α_k, α_{k+1})` — that per-term limit/monotonicity bookkeeping (one pole term dominating,
the rest bounded) is the remaining, still-open connecting step for a future pass. It also
does not construct the matrix data or eigenvector setup at all. No axiom, no sorry.
-/

namespace GppWeilParity

open Set Filter Topology

/-- **Unique zero from monotonicity plus boundary blow-up.** If `g` is continuous and
strictly increasing on the open interval `(a,b)`, tends to `-∞` approaching `a` from the
right, and to `+∞` approaching `b` from the left, then `g` has exactly one zero in
`(a,b)`. This is the fully general IVT+monotonicity core behind "the secular equation
`f(z)=0` has exactly one root in each gap `(α_j,α_{j+1})`," with no reference to what `g`
concretely is. -/
theorem existsUnique_zero_of_strictMonoOn_of_tendsto {a b : ℝ} (hab : a < b) {g : ℝ → ℝ}
    (hmono : StrictMonoOn g (Ioo a b)) (hcont : ContinuousOn g (Ioo a b))
    (hbot : Tendsto g (𝓝[>] a) atBot) (htop : Tendsto g (𝓝[<] b) atTop) :
    ∃! z, z ∈ Ioo a b ∧ g z = 0 := by
  have hpre : IsPreconnected (Ioo a b) := isPreconnected_Ioo
  haveI : NeBot (𝓝[Ioo a b] a) := left_nhdsWithin_Ioo_neBot hab
  haveI : NeBot (𝓝[Ioo a b] b) := right_nhdsWithin_Ioo_neBot hab
  have hle_a : (𝓝[Ioo a b] a) ≤ 𝓟 (Ioo a b) := inf_le_right
  have hle_b : (𝓝[Ioo a b] b) ≤ 𝓟 (Ioo a b) := inf_le_right
  have hbot' : Tendsto g (𝓝[Ioo a b] a) atBot := by
    rw [nhdsWithin_Ioo_eq_nhdsGT hab]; exact hbot
  have htop' : Tendsto g (𝓝[Ioo a b] b) atTop := by
    rw [nhdsWithin_Ioo_eq_nhdsLT hab]; exact htop
  have hex : (Set.univ : Set ℝ) ⊆ g '' (Ioo a b) :=
    hpre.intermediate_value_Iii hle_a hle_b hcont hbot' htop'
  obtain ⟨z, hz, hgz⟩ := hex (Set.mem_univ (0 : ℝ))
  refine ⟨z, ⟨hz, hgz⟩, ?_⟩
  rintro w ⟨hw, hgw⟩
  exact hmono.injOn hw hz (hgw.trans hgz.symm)

end GppWeilParity
