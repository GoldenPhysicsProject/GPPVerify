import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

/-!
# Compact-uniform convergence of the odd-lattice logarithmic-derivative series

This module isolates the M-test step needed to pass from the finite odd/even
Weierstrass quotient to the `tanh` partial-fraction identity.

For

  f_n(x) = 2 x / ((2n+1)^2 + x^2),

the partial sums converge uniformly on every compact symmetric interval
`[-T,T]`.  The proof uses the explicit summable majorant

  |f_n(x)| <= 2T/(n+1)^2.

It also records the exact finite logarithmic-derivative identity term by term:
`d/dx log(1 + x^2/(2n+1)^2) = f_n(x)`.  This is the finite calculus input for
the subsequent derivative-limit theorem identifying the infinite sum with `tanh`.
-/

namespace GppOddLatticeDerivativeUniform

open Filter Set Topology
open scoped BigOperators

/-- The odd-lattice logarithmic-derivative summand. -/
noncomputable def oddDerivativeTerm (n : ℕ) (x : ℝ) : ℝ :=
  2 * x / ((2 * (n : ℝ) + 1) ^ 2 + x ^ 2)

/-- The logarithm of the corresponding positive odd Weierstrass factor. -/
noncomputable def oddLogTerm (n : ℕ) (x : ℝ) : ℝ :=
  Real.log (1 + x ^ 2 / ((2 * (n : ℝ) + 1) ^ 2))

/-- Each finite odd-factor logarithm has exactly the expected rational derivative. -/
theorem hasDerivAt_oddLogTerm (n : ℕ) (x : ℝ) :
    HasDerivAt (oddLogTerm n) (oddDerivativeTerm n x) x := by
  have hc : 0 < (2 * (n : ℝ) + 1) ^ 2 := by positivity
  have hx2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hinner :
      HasDerivAt
        (fun y : ℝ => 1 + y ^ 2 / ((2 * (n : ℝ) + 1) ^ 2))
        (2 * x / ((2 * (n : ℝ) + 1) ^ 2)) x := by
    exact ((hasDerivAt_const x (1 : ℝ)).add
      (hx2.div_const ((2 * (n : ℝ) + 1) ^ 2))).congr_deriv (by ring)
  have hpos : 0 < 1 + x ^ 2 / ((2 * (n : ℝ) + 1) ^ 2) := by positivity
  have hlog := hinner.log hpos.ne'
  unfold oddLogTerm oddDerivativeTerm
  refine hlog.congr_deriv ?_
  field_simp

/-- Finite sums of odd-factor logarithms differentiate to the corresponding
finite odd-lattice rational sum. -/
theorem hasDerivAt_oddLogPartialSum (N : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => ∑ n ∈ Finset.range N, oddLogTerm n y)
      (∑ n ∈ Finset.range N, oddDerivativeTerm n x) x := by
  exact HasDerivAt.fun_sum (u := Finset.range N)
    (fun n _ => hasDerivAt_oddLogTerm n x)

/-- The standard p-series majorant used on `[-T,T]`. -/
noncomputable def oddDerivativeMajorant (T : ℝ) (n : ℕ) : ℝ :=
  2 * T / ((n : ℝ) + 1) ^ 2

/-- For nonnegative `T`, the compact majorant is summable. -/
theorem summable_oddDerivativeMajorant (T : ℝ) :
    Summable (oddDerivativeMajorant T) := by
  have hf : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := hasSum_zeta_two.summable
  have hshift : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 1).mpr hf
  have hbase : Summable (fun n : ℕ => 1 / (((n : ℝ) + 1) ^ 2)) := by
    convert hshift using 1 with n
    norm_num
  exact (hbase.mul_left (2 * T)).congr (fun n => by
    simp [oddDerivativeMajorant, div_eq_mul_inv])

/-- On a compact symmetric interval, every odd-lattice term is bounded by the
summable p-series majorant. -/
theorem norm_oddDerivativeTerm_le_majorant
    (T : ℝ) (hT : 0 ≤ T) (n : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (-T) T) :
    ‖oddDerivativeTerm n x‖ ≤ oddDerivativeMajorant T n := by
  have hxabs : |x| ≤ T := by
    rw [abs_le]
    exact ⟨hx.1, hx.2⟩
  have hdenpos : 0 < (2 * (n : ℝ) + 1) ^ 2 + x ^ 2 := by
    positivity
  have hsmallpos : 0 < ((n : ℝ) + 1) ^ 2 := by
    positivity
  have hden : ((n : ℝ) + 1) ^ 2 ≤ (2 * (n : ℝ) + 1) ^ 2 + x ^ 2 := by
    have hn : 0 ≤ (n : ℝ) := by positivity
    nlinarith [sq_nonneg x]
  have hnum : |2 * x| ≤ 2 * T := by
    rw [abs_mul]
    norm_num
    nlinarith [abs_nonneg x]
  rw [oddDerivativeTerm, oddDerivativeMajorant, Real.norm_eq_abs, abs_div,
      abs_of_pos hdenpos]
  calc
    |2 * x| / ((2 * (n : ℝ) + 1) ^ 2 + x ^ 2)
        ≤ (2 * T) / ((2 * (n : ℝ) + 1) ^ 2 + x ^ 2) := by
          exact div_le_div_of_nonneg_right hnum hdenpos.le
    _ ≤ (2 * T) / ((n : ℝ) + 1) ^ 2 := by
          exact div_le_div_of_nonneg_left (by positivity) hsmallpos hden

/-- The partial sums of the odd logarithmic-derivative series converge uniformly
on every compact symmetric interval `[-T,T]`. -/
theorem tendstoUniformlyOn_oddDerivativeTerm
    (T : ℝ) (hT : 0 ≤ T) :
    TendstoUniformlyOn
      (fun N : ℕ => fun x : ℝ => ∑ n ∈ Finset.range N, oddDerivativeTerm n x)
      (fun x : ℝ => ∑' n : ℕ, oddDerivativeTerm n x)
      Filter.atTop (Set.Icc (-T) T) := by
  exact tendstoUniformlyOn_tsum_nat
    (summable_oddDerivativeMajorant T)
    (fun n x hx => norm_oddDerivativeTerm_le_majorant T hT n x hx)

end GppOddLatticeDerivativeUniform

#print axioms GppOddLatticeDerivativeUniform.hasDerivAt_oddLogTerm
#print axioms GppOddLatticeDerivativeUniform.hasDerivAt_oddLogPartialSum
#print axioms GppOddLatticeDerivativeUniform.summable_oddDerivativeMajorant
#print axioms GppOddLatticeDerivativeUniform.norm_oddDerivativeTerm_le_majorant
#print axioms GppOddLatticeDerivativeUniform.tendstoUniformlyOn_oddDerivativeTerm
