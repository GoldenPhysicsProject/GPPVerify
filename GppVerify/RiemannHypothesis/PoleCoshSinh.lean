import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic

/-!
# Rank-one pole: `|Σ c cosh a|² − |Σ c sinh a|² = Σ c̄_i c_j cosh(a_i − a_j)`

Source: Codex / Discovery2, PR #11 comment 2026-10-31 ("exact completed semilocal Weil SOS"): the
pole term is `2|∫ f cosh((x−L/2)/2)|² − 2|∫ f sinh((x−L/2)/2)|²`. Daniel Toupin / Golden Physics
Project, with AI assistance from Codex (statement) and Claude Code (formalization).

For a finite family of complex weights `c_j` and real nodes `a_j` (a quadrature of the two moments),
`‖Σ c_j cosh a_j‖² − ‖Σ c_j sinh a_j‖² = Σ_{i,j} conj(c_i) c_j cosh(a_i − a_j)`
(the right side is real by symmetry of cosh). This is the discrete form of "the pole is the cosh-kernel form
`∫∫ f(x) f̄(y) cosh((x−y)/2)`"; it uses only `cosh a cosh b − sinh a sinh b = cosh(a − b)`.

**Scope.** The finite-sum identity only. The integral version (integrability, the `L`-dependent
shift `a = (x − L/2)/2`) and everything about the sign of the completed form are not formalized.
No claim about RH.
-/

set_option autoImplicit false

open Finset

namespace GppPoleCoshSinh

/-- `|Σ c cosh a|² − |Σ c sinh a|² = Σ_{i,j} conj(c_i) c_j cosh(a_i − a_j)` as an identity in `ℂ`. -/
theorem pole_identity {ι : Type*} (s : Finset ι) (c : ι → ℂ) (a : ι → ℝ) :
    (((‖∑ j ∈ s, c j * (Real.cosh (a j) : ℂ)‖ ^ 2 -
        ‖∑ j ∈ s, c j * (Real.sinh (a j) : ℂ)‖ ^ 2 : ℝ)) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, (starRingEnd ℂ) (c i) * c j * (Real.cosh (a i - a j) : ℂ) := by
  have hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
    intro z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, hn, hn]
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hc : ∀ x : ℝ, (starRingEnd ℂ) (Complex.cosh (x : ℂ)) = Complex.cosh (x : ℂ) := fun x => by
    rw [← Complex.cosh_conj, Complex.conj_ofReal]
  have hs : ∀ x : ℝ, (starRingEnd ℂ) (Complex.sinh (x : ℂ)) = Complex.sinh (x : ℂ) := fun x => by
    rw [← Complex.sinh_conj, Complex.conj_ofReal]
  rw [hc, hs, Complex.cosh_sub]
  ring

end GppPoleCoshSinh
