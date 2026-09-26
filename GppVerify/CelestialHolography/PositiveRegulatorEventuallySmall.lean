import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

/-!
# Positive regulators are eventually below every positive scale

A number of one-sided regulator limits use explicit chamber assumptions such as
`m ≤ S/4` or `m ≤ U/16`.  For a positive fixed scale these are not independent
analytic hypotheses: they hold automatically as `m → 0⁺`.
-/

namespace GppPositiveRegulatorEventuallySmall

open Set Filter
open scoped Topology

/-- Along the punctured positive neighborhood of zero, the regulator is eventually
bounded above by every fixed positive real number. -/
theorem eventually_le_pos_const {c : ℝ} (hc : 0 < c) :
    ∀ᶠ m : ℝ in 𝓝[>] 0, m ≤ c := by
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds hc)] with m hm_pos hm_lt
  exact le_of_lt hm_lt

/-- The scalar-box `m ≤ S/4` chamber condition is automatic for `S>0`. -/
theorem eventually_le_quarter {S : ℝ} (hS : 0 < S) :
    ∀ᶠ m : ℝ in 𝓝[>] 0, m ≤ S / 4 := by
  apply eventually_le_pos_const
  positivity

/-- The scalar-box `m ≤ U/16` chamber condition is automatic for `U>0`. -/
theorem eventually_le_sixteenth {U : ℝ} (hU : 0 < U) :
    ∀ᶠ m : ℝ in 𝓝[>] 0, m ≤ U / 16 := by
  apply eventually_le_pos_const
  positivity

end GppPositiveRegulatorEventuallySmall

#print axioms GppPositiveRegulatorEventuallySmall.eventually_le_pos_const
#print axioms GppPositiveRegulatorEventuallySmall.eventually_le_quarter
#print axioms GppPositiveRegulatorEventuallySmall.eventually_le_sixteenth
