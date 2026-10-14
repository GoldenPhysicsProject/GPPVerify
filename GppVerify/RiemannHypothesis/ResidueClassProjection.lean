import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Character-sector projections of the arithmetic Hardy space are residue-class projections

Source: Grok, GPP-bridge `work/grok/2026-10-14_prime_gas_unitarity.md` (b7d94e6; PR #11 comment
6166348048), answering Claude Code's request to define `P_χ`.

The dual group of `(ℤ/q)^×` acts on `ℓ²(ℕ)` by multiplication, `M_ψ f(n) = ψ(n) f(n)`. Its isotypic
projections are `E_a = φ(q)⁻¹ Σ_ψ ψ(a)⁻¹ M_ψ`.
* `projection_eq_indicator`: for `a` a unit mod `q`, `φ(q)⁻¹ Σ_ψ ψ(a)⁻¹ ψ(n)` is `1` if
  `n ≡ a (mod q)` and `0` otherwise. So `E_a` is multiplication by `1_{n ≡ a}` (Mathlib character
  orthogonality).
* `class_sum`: for `Re s > 1`, the L-series of `1_{n ≡ a}` is `φ(q)⁻¹ Σ_ψ ψ(a)⁻¹ L(s, ψ)`. With
  `s = 1 + 2 Re z` this is Grok's `‖E_a e_z‖²` formula.

Grok's own correction stands: the class norms are **not** equal at finite `z` (at `q = 5`,
`s = 1.3` they are `1.44634, 0.82367, 0.63484, 0.54187`, reproduced independently). Only
`ε‖E_a e_z‖² → 1/q` as `ε → 0⁺` (not formalized). No positivity content. **No RH claim.**
-/

namespace GppResidueClassProjection

open DirichletCharacter

variable {q : ℕ} [NeZero q]

/-- **Isotypic projection = residue-class indicator.** -/
theorem projection_eq_indicator {a : ZMod q} (ha : IsUnit a) (n : ℕ) :
    (q.totient : ℂ)⁻¹ * ∑ ψ : DirichletCharacter ℂ q, ψ a⁻¹ * ψ n =
      if (n : ZMod q) = a then 1 else 0 := by
  have ht : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_neZero q)).ne'
  rw [sum_char_inv_mul_char_eq ℂ ha]
  by_cases h : (n : ZMod q) = a
  · rw [if_pos h.symm, if_pos h, inv_mul_cancel₀ ht]
  · rw [if_neg (Ne.symm h), if_neg h, mul_zero]

/-- **Class-sum identity**: `Σ_{n ≡ a} n^{−s} = φ(q)⁻¹ Σ_ψ ψ(a)⁻¹ L(s, ψ)` on `Re s > 1`. -/
theorem class_sum {a : ZMod q} (ha : IsUnit a) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => if (n : ZMod q) = a then 1 else 0) s =
      (q.totient : ℂ)⁻¹ * ∑ ψ : DirichletCharacter ℂ q, ψ a⁻¹ * LSeries (fun n => ψ n) s := by
  have hfun : (fun n : ℕ => if (n : ZMod q) = a then (1 : ℂ) else 0) =
      (q.totient : ℂ)⁻¹ • ∑ ψ : DirichletCharacter ℂ q, ψ a⁻¹ • (fun n : ℕ => ψ n) := by
    ext1 n
    rw [← projection_eq_indicator ha n]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [hfun, LSeries_smul, LSeries_sum fun ψ _ => (LSeriesSummable_of_one_lt_re ψ hs).smul _]
  simp_rw [LSeries_smul]

end GppResidueClassProjection
