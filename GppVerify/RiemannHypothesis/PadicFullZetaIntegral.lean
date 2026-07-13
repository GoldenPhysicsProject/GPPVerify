import GppVerify.RiemannHypothesis.PadicShellNorm
import GppVerify.RiemannHypothesis.PadicOriginMeasure

/-!
# The p-adic shell partition of `ℤ_p`

Continuing toward the full geometric-series zeta integral (Tate's-thesis lecture notes,
Example 4.10). Not sourced from a specific Golden Physics Project paper.

Every `x ≠ 0` lies in exactly one shell `pⁿ ℤ_p \ pⁿ⁺¹ ℤ_p` (namely `n = x.valuation`), so
`ℤ_p \ {0} = ⋃ n, shell n` is a disjoint, measurable, countable partition — the
decomposition needed to evaluate `∫_{ℤ_p} ‖x‖ˢ dμ` via `MeasureTheory.lintegral_iUnion`.
The closed-form evaluation itself (combining this partition with the already-proven shell
measure, shell norm, and origin-measure-zero facts, plus `ENNReal.tsum_geometric`) is left
for a follow-up file once every remaining `rpow` identity is independently verified.
-/

namespace GppPadicFullZeta

open MeasureTheory
open scoped ENNReal

variable (p : ℕ) [Fact p.Prime]

/-- The shell `pⁿ ℤ_p \ pⁿ⁺¹ ℤ_p`. -/
def shell (n : ℕ) : Set (PadicInt p) :=
  (Ideal.span {(p : PadicInt p) ^ n} : Set (PadicInt p)) \
    (Ideal.span {(p : PadicInt p) ^ (n + 1)} : Set (PadicInt p))

theorem measurableSet_shell (n : ℕ) : MeasurableSet (shell p n) :=
  (GppPadicShell.measurableSet_span_pow p n).diff (GppPadicShell.measurableSet_span_pow p (n + 1))

/-- Every nonzero `x` lies in the shell indexed by its own valuation. -/
theorem mem_shell_valuation {x : PadicInt p} (hx : x ≠ 0) : x ∈ shell p x.valuation := by
  refine ⟨(PadicInt.mem_span_pow_iff_le_valuation x hx x.valuation).mpr le_rfl, ?_⟩
  intro hmem
  have := (PadicInt.mem_span_pow_iff_le_valuation x hx (x.valuation + 1)).mp hmem
  omega

/-- Distinct shells are disjoint. -/
theorem shell_pairwise_disjoint : Pairwise (Function.onFun Disjoint (shell p)) := by
  intro m n hmn
  simp only [Function.onFun, Set.disjoint_left]
  intro x hxm hxn
  have hxne : x ≠ 0 := by
    intro h
    apply hxm.2
    rw [h]
    exact (Ideal.span {(p : PadicInt p) ^ (m + 1)}).zero_mem
  have hm1 : m ≤ x.valuation := (PadicInt.mem_span_pow_iff_le_valuation x hxne m).mp hxm.1
  have hm2 : ¬ (m + 1 ≤ x.valuation) := fun h =>
    hxm.2 ((PadicInt.mem_span_pow_iff_le_valuation x hxne (m + 1)).mpr h)
  have hn1 : n ≤ x.valuation := (PadicInt.mem_span_pow_iff_le_valuation x hxne n).mp hxn.1
  have hn2 : ¬ (n + 1 ≤ x.valuation) := fun h =>
    hxn.2 ((PadicInt.mem_span_pow_iff_le_valuation x hxne (n + 1)).mpr h)
  omega

/-- `ℤ_p` is the disjoint union of the origin and all the shells. -/
theorem univ_eq_shells : (Set.univ : Set (PadicInt p)) = {0} ∪ ⋃ n : ℕ, shell p n := by
  ext x
  simp only [Set.mem_univ, Set.mem_union, Set.mem_singleton_iff, Set.mem_iUnion, true_iff]
  by_cases hx : x = 0
  · exact Or.inl hx
  · exact Or.inr ⟨x.valuation, mem_shell_valuation p hx⟩

/-- The origin is disjoint from every shell (it lies in every `pⁿ⁺¹ ℤ_p`). -/
theorem singleton_disjoint_shells :
    Disjoint ({0} : Set (PadicInt p)) (⋃ n : ℕ, shell p n) := by
  rw [Set.disjoint_left]
  rintro x hx0 hxs
  simp only [Set.mem_singleton_iff] at hx0
  simp only [Set.mem_iUnion] at hxs
  obtain ⟨n, hxn⟩ := hxs
  apply hxn.2
  rw [hx0]
  exact (Ideal.span {(p : PadicInt p) ^ (n + 1)}).zero_mem

/-- The shell union is measurable. -/
theorem measurableSet_shell_iUnion : MeasurableSet (⋃ n : ℕ, shell p n) :=
  MeasurableSet.iUnion (measurableSet_shell p)

end GppPadicFullZeta
