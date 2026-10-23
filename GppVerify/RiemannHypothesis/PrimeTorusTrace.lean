import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Order.Filter.Cofinite

/-!
# The prime-torus heat trace: finite Gram positivity and divergence of the full trace

Source: Astra, `work/2026-10-22_astra_prime_torus_trace_audit.md` (GPP-bridge), auditing a proposed
Peter–Weyl heat trace `Tr exp(−t D²)` on the product prime torus, with
`D = −i ∑_j (log p_j) ∂_{θ_j}`. Daniel Toupin / Golden Physics Project, with AI assistance from
Astra (statements and proofs) and Claude Code (formalization).

* `gram_eq_sum_sq`: for any finite set of energies `E_k`, the Gram form of
  `K_B(t) = ∑_{k ∈ B} e^{−t E_k}` is a sum of squares,
  `∑_{i,j} c_i c_j K_B(t_i + t_j) = ∑_k (∑_i c_i e^{−t_i E_k})²`. No arithmetic is used.
* `not_summable_heat`: for `a > 0`, any `b` and `t > 0`, the two-frequency trace
  `∑_{(n,m) ∈ ℤ²} e^{−t (n a + m b)²}` diverges. For each `m`, the nearest integer `n` to `−m b / a`
  gives `|n a + m b| ≤ a/2`, so infinitely many distinct terms are at least `e^{−t a²/4}`.
* `not_summable_prime_heat`: in particular with `a = log 2`, `b = log 3`. Setting the other
  coordinates to zero gives the same divergence on the full product torus, so `exp(−t D²)` is not
  trace class there. `D²` is a directional derivative squared, not an elliptic Laplacian.

**Scope.** Astra's remarks on the Haar transform, the functional-equation involution and the
norm-one idele group are not formalized. This rules out one proposed trace normalization. It says
nothing about the zeros of ζ. No claim about RH.
-/

open Filter

namespace GppPrimeTorusTrace

/-- **Finite Gram positivity.** The Gram form of a finite heat trace is a sum of squares. -/
theorem gram_eq_sum_sq {ι κ : Type*} (B : Finset κ) (E : κ → ℝ) (s : Finset ι)
    (c t : ι → ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, c i * c j * ∑ k ∈ B, Real.exp (-(t i + t j) * E k) =
      ∑ k ∈ B, (∑ i ∈ s, c i * Real.exp (-t i * E k)) ^ 2 := by
  have hk : ∀ k, (∑ i ∈ s, c i * Real.exp (-t i * E k)) ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j * Real.exp (-(t i + t j) * E k) := fun k => by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show -(t i + t j) * E k = -t i * E k + -t j * E k by ring, Real.exp_add]
    ring
  calc ∑ i ∈ s, ∑ j ∈ s, c i * c j * ∑ k ∈ B, Real.exp (-(t i + t j) * E k)
      = ∑ i ∈ s, ∑ k ∈ B, ∑ j ∈ s, c i * c j * Real.exp (-(t i + t j) * E k) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
    _ = ∑ k ∈ B, ∑ i ∈ s, ∑ j ∈ s, c i * c j * Real.exp (-(t i + t j) * E k) :=
        Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun k _ => (hk k).symm

/-- **The two-frequency heat trace diverges.** -/
theorem not_summable_heat (a b t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    ¬ Summable (fun k : ℤ × ℤ => Real.exp (-t * ((k.1 : ℝ) * a + (k.2 : ℝ) * b) ^ 2)) := by
  intro hs
  set f := fun k : ℤ × ℤ => Real.exp (-t * ((k.1 : ℝ) * a + (k.2 : ℝ) * b) ^ 2)
  let φ : ℤ → ℤ × ℤ := fun m => (round (-(m : ℝ) * b / a), m)
  have hφ : Function.Injective φ := fun m m' h => (Prod.ext_iff.mp h).2
  have hlim : Tendsto (f ∘ φ) cofinite (nhds 0) :=
    hs.tendsto_cofinite_zero.comp hφ.tendsto_cofinite
  have hlow : ∀ m : ℤ, Real.exp (-t * (a ^ 2 / 4)) ≤ (f ∘ φ) m := by
    intro m
    simp only [Function.comp, f, φ]
    apply Real.exp_le_exp.mpr
    have hr := abs_sub_round (-(m : ℝ) * b / a)
    have heq : (round (-(m : ℝ) * b / a) : ℝ) * a + m * b =
        a * ((round (-(m : ℝ) * b / a) : ℝ) - -(m : ℝ) * b / a) := by
      field_simp; ring
    rw [heq, mul_pow]
    have h2 : ((round (-(m : ℝ) * b / a) : ℝ) - -(m : ℝ) * b / a) ^ 2 ≤ 1 / 4 := by
      rw [abs_sub_comm] at hr
      nlinarith [abs_le.mp hr, sq_abs ((round (-(m : ℝ) * b / a) : ℝ) - -(m : ℝ) * b / a)]
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ t * a ^ 2)]
  have hpos : 0 < Real.exp (-t * (a ^ 2 / 4)) := Real.exp_pos _
  have hev := hlim.eventually (gt_mem_nhds hpos)
  obtain ⟨m, hm⟩ := hev.exists
  exact absurd (hlow m) (not_le.mpr hm)

/-- **The prime-torus trace diverges** (frequencies `log 2`, `log 3`). -/
theorem not_summable_prime_heat (t : ℝ) (ht : 0 < t) :
    ¬ Summable (fun k : ℤ × ℤ =>
      Real.exp (-t * ((k.1 : ℝ) * Real.log 2 + (k.2 : ℝ) * Real.log 3) ^ 2)) :=
  not_summable_heat _ _ t (Real.log_pos one_lt_two) ht

end GppPrimeTorusTrace
