import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Removable-singularity limit: a bounded numerator over a blowing-up denominator

`formalization_queue` item `4d97d8eb` ("Singular Pick kernel gives barycentric extremal
interpolant and infinity value"), Weil-Parity thread. The item asks to show, for the
barycentric rational interpolant `qStar(z) = B(z)/A(z)` built from a Pick-kernel null
vector, that `qStar(x_i) = q_i` at each node — a removable-singularity statement, since
both `A` and `B` have poles at `x_i` that cancel in the ratio (the item's own words:
"by Laurent expansion and the kernel equations").

## What this file proves

The genuinely reusable real-analysis core behind that removable-singularity computation,
stripped of the specific `A`, `B`, `qStar` construction: if a numerator `N` tends to a
*finite* limit `L` approaching a punctured point `x`, while a denominator `D`'s norm blows
up (`‖D z‖ → ∞`) there, then the ratio `N/D` tends to `0` — precisely the fact needed once
`N := B - q_i·A` is shown to have the finite limit `d_i·v_i` at `x_i` (via the kernel
equation `Rv=0`, an elementary algebraic computation: the `k=i` term in
`B(z)-q_i A(z) = Σ_k v_k(q_k-q_i)/(z-x_k)` vanishes identically since `q_i-q_i=0`, leaving
a sum regular at `x_i`) while `‖A(z)‖ → ∞` there (since `v_i ≠ 0`).

## What this file does NOT do

Does **not** construct the Pick matrix `R`, the barycentric functions `A`, `B`, `qStar`,
or verify the specific finite-limit/blow-up hypotheses for them at each node `x_i` — that
remaining algebraic bookkeeping (the kernel-equation computation sketched above), the
derivative-matching claim `qStar'(x_i) = d_i` (a genuinely harder second-order Laurent
computation, not attempted at all), and the `qStar(∞)` limit are all left for a future
pass. The Nevanlinna-Pick bridge in the item's final sentence is untouched, as the item's
own text anticipates ("this bridge may remain an explicit hypothesis if Mathlib lacks
Pick-class infrastructure" — confirmed absent, see the Weil-Semiboundedness chapter). No
axiom, no sorry.
-/

namespace GppWeilParity

open Filter Topology

/-- **Removable-singularity core.** A numerator with a finite limit divided by a
denominator whose norm blows up tends to zero. -/
theorem tendsto_div_zero_of_tendsto_nhds_of_tendsto_norm_atTop {x L : ℝ} {N D : ℝ → ℝ}
    (hN : Tendsto N (𝓝[≠] x) (𝓝 L)) (hD : Tendsto (fun z => ‖D z‖) (𝓝[≠] x) atTop) :
    Tendsto (fun z => N z / D z) (𝓝[≠] x) (𝓝 0) := by
  have hDinv_norm : Tendsto (fun z => ‖D z‖⁻¹) (𝓝[≠] x) (𝓝 0) := tendsto_inv_atTop_zero.comp hD
  have hDinv : Tendsto (fun z => (D z)⁻¹) (𝓝[≠] x) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [norm_inv] using hDinv_norm
  have hprod : Tendsto (fun z => N z * (D z)⁻¹) (𝓝[≠] x) (𝓝 (L * 0)) := hN.mul hDinv
  simpa [div_eq_mul_inv] using hprod

end GppWeilParity
