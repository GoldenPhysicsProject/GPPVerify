import GppVerify.RiemannHypothesis.PadicShellMeasure

/-!
# The exact norm value on a p-adic shell

Real infrastructure continuing the p-adic zeta integral thread (Tate's-thesis lecture
notes, Example 4.10): every `x` in the shell `pⁿ ℤ_p \ pⁿ⁺¹ ℤ_p` has `‖x‖ = p⁻ⁿ` exactly
(not just bounded above/below by it). This pins down the integrand `‖x‖ˢ` as a genuine
constant on each shell, the last ingredient (together with the already-proven shell
measure) needed to evaluate `∫_{ℤ_p} ‖x‖ˢ dμ` as a geometric series. Not sourced from a
specific Golden Physics Project paper.
-/

namespace GppPadicShellNorm

variable (p : ℕ) [Fact p.Prime]

/-- **Exact norm on a shell**: every `x` with `n ≤ x.valuation < n+1` (equivalently,
    `x` in the shell `pⁿ ℤ_p \ pⁿ⁺¹ ℤ_p`) has `‖x‖ = p⁻ⁿ` exactly. -/
theorem norm_eq_of_mem_shell {n : ℕ} {x : PadicInt p}
    (hx : x ∈ (Ideal.span {(p : PadicInt p) ^ n} : Set (PadicInt p)) \
             (Ideal.span {(p : PadicInt p) ^ (n + 1)} : Set (PadicInt p))) :
    ‖x‖ = (p : ℝ) ^ (-(n : ℤ)) := by
  obtain ⟨hx1, hx2⟩ := hx
  have hxne : x ≠ 0 := by
    intro h
    apply hx2
    rw [h]
    exact (Ideal.span {(p : PadicInt p) ^ (n + 1)}).zero_mem
  have hval1 : n ≤ x.valuation := (PadicInt.mem_span_pow_iff_le_valuation x hxne n).mp hx1
  have hval2 : ¬ (n + 1 ≤ x.valuation) := fun h =>
    hx2 ((PadicInt.mem_span_pow_iff_le_valuation x hxne (n + 1)).mpr h)
  have hveq : x.valuation = n := by omega
  rw [PadicInt.norm_eq_zpow_neg_valuation hxne, hveq]

end GppPadicShellNorm
