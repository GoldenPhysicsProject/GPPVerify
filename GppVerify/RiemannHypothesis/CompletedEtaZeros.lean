import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# The periodic zeros of the eta factor `1 - 2^{1-s}`

Formalizes the elementary content of Definition 2.1 / eq. (2) of Yakaboylu, *Nontrivial
Riemann Zeros as Spectrum* (arXiv:2408.15135v14): the completed eta function
`Υ(s) = Γ(s+1) η(s)` with `η(s) = (1 - 2^{1-s}) ζ(s)` has, besides the nontrivial Riemann
zeros, a lattice of *periodic Dirichlet eta zeros* coming from the elementary factor
`1 - 2^{1-s}`, located exactly at `s = 1 - 2πik/log 2` (`k ∈ ℤ`):

* `eta_factor_zero_iff` — the complete characterization `2^{1-s} = 1 ↔ ∃ k, s = 1 - 2πik/log 2`,
  from `Complex.exp_eq_one_iff` (periodicity of the complex exponential);
* `eta_periodic_zero_re` — every such zero has real part exactly `1`: the periodic zeros
  sit on the line `Re s = 1`, *not* in the interior of the critical strip, so they never
  contaminate the RH-relevant zero set (this is why Yakaboylu's spectrum decomposes cleanly
  as `Z = Z_D ∪ Z_R`).

Also included, as `omega_eq_cosh`: the weight identity `t e^t/(1+e^t)² = t/(4 cosh²(t/2))`,
which is the bridge between the Yakaboylu paper's convention for the Mellin weight
`ω(t)` (eq. (1) there) and the `sech²` convention used in the companion Abel-Cesàro paper
(`rh_cesaro_v2.tex`, §2 and Theorem 5.1) — pure exponential algebra, but load-bearing for
any future work tying the two formalizations together.
-/

namespace GppCompletedEta

open Complex

/-- **Weight-convention bridge**: `ω(t) = t e^t/(1+e^t)² = t/(4 cosh²(t/2))`. Both forms
    appear in the source papers for the same Mellin weight; the identity is
    `4 cosh²(t/2) = e^{-t}(1+e^t)²`. -/
theorem omega_eq_cosh (t : ℝ) :
    t * Real.exp t / (1 + Real.exp t) ^ 2 = t / (4 * Real.cosh (t / 2) ^ 2) := by
  have hexp : Real.exp t = Real.exp (t / 2) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hcosh : Real.cosh (t / 2) = (Real.exp (t / 2) + Real.exp (-(t / 2))) / 2 :=
    Real.cosh_eq (t / 2)
  have hpos : 0 < Real.exp (t / 2) := Real.exp_pos _
  rw [hcosh, hexp, Real.exp_neg]
  field_simp
  ring

/-- **The periodic Dirichlet eta zeros** (Yakaboylu Definition 2.1, eq. (2)): the factor
    `2^{1-s}` equals `1` exactly at the lattice `s = 1 - k·2πi/log 2`, `k ∈ ℤ`. Follows
    from `exp z = 1 ↔ z ∈ 2πi·ℤ` after unfolding the complex power. -/
theorem eta_factor_zero_iff (s : ℂ) :
    (2 : ℂ) ^ ((1 : ℂ) - s) = 1 ↔
      ∃ k : ℤ, s = 1 - (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / (Real.log 2 : ℂ) := by
  have hlog2 : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [show ((2 : ℂ)) = ((2 : ℝ) : ℂ) by norm_num, Complex.ofReal_log (by norm_num : (0:ℝ) ≤ 2)]
  have hne : ((Real.log 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos one_lt_two).ne'
  rw [Complex.cpow_def_of_ne_zero two_ne_zero, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    rw [hlog2] at hk
    refine ⟨k, ?_⟩
    field_simp
    linear_combination -hk
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    rw [hlog2]
    field_simp
    ring

/-- **The periodic zeros live on `Re s = 1`** — outside the open critical strip, so they
    never mix with the nontrivial Riemann zeros: the `Z = Z_D ∪ Z_R` decomposition of the
    completed eta function's zero set is clean. -/
theorem eta_periodic_zero_re (k : ℤ) :
    ((1 : ℂ) - (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / (Real.log 2 : ℂ)).re = 1 := by
  have hpure : (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / (Real.log 2 : ℂ) =
      ((2 * Real.pi * (k : ℝ) / Real.log 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hpure]
  simp

end GppCompletedEta
