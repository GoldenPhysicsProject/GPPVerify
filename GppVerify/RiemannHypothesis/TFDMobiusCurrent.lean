import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries

/-!
# The zeta current is the vacuum expectation of the Möbius connection in the global arithmetic TFD

Source: Codex, GPPDiscovery2 `research/2026-09-28_tfd_mobius_connection_zeta_current.md` §§2, 5.
The single-prime version is `GppPrimeTFD.tfd_correlator`.

Let `Ω_β = ζ(β)^{−1/2} Σ_{n≥1} n^{−β/2} |n, n⟩` (`β > 1`) and `V_d = S_d ⊗ S_d`, with
`S_d|n⟩ = |dn⟩`. On basis vectors the matrix coefficient is the diagonal sum
`⟨Ω_β, V_d Ω_β⟩ = ζ(β)^{−1} Σ_n (dn)^{−β/2} n^{−β/2}` (`tfdCoeff`).

* `tfdCoeff_eq`: **`⟨Ω_β, V_d Ω_β⟩ = d^{−β/2}`** for every `d`.
* `vacuum_current`: the Möbius connection `P(z) = Σ Λ(n) n^{−z} V_n` has vacuum expectation
  `Σ Λ(n) n^{−z} ⟨Ω_β, V_n Ω_β⟩ = −ζ'(z + β/2)/ζ(z + β/2)` for `Re z + β/2 > 1`. The half-density
  shift `β/2` comes from the thermofield state, not from `P`.

**Scope.** The Hilbert space `ℓ²(ℕ) ⊗ ℓ²(ℕ)` is not constructed. The matrix coefficient is its
basis expansion (a convergent real series), as in `GppPrimeTFD`. The critical limit `β → 1` exists
only for the finite-local coefficient `d^{−1/2}`, not for the vector. The Cayley rewriting of each
prime channel (note §6) is in `GppPrimeCayley`. **No RH claim.**
-/

namespace GppTFDMobiusCurrent

open ArithmeticFunction LSeries Complex

/-- The basis expansion of `⟨Ω_β, V_d Ω_β⟩`. -/
noncomputable def tfdCoeff (β : ℝ) (d : ℕ) : ℝ :=
  (∑' n : ℕ, ((d : ℝ) * (n + 1)) ^ (-β / 2) * ((n : ℝ) + 1) ^ (-β / 2)) /
    ∑' n : ℕ, ((n : ℝ) + 1) ^ (-β)

lemma summable_shift {β : ℝ} (hβ : 1 < β) : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-β)) := by
  have := (Real.summable_nat_rpow.mpr (by linarith : -β < -1))
  exact_mod_cast (summable_nat_add_iff 1).mpr this

/-- **The global TFD matrix coefficient is the half-density `d^{−β/2}`.** -/
theorem tfdCoeff_eq {β : ℝ} (hβ : 1 < β) (d : ℕ) :
    tfdCoeff β d = (d : ℝ) ^ (-β / 2) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hterm : ∀ n : ℕ, ((d : ℝ) * (n + 1)) ^ (-β / 2) * ((n : ℝ) + 1) ^ (-β / 2) =
      (d : ℝ) ^ (-β / 2) * ((n : ℝ) + 1) ^ (-β) := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [Real.mul_rpow hd0 hn.le, mul_assoc, ← Real.rpow_add hn]
    ring_nf
  have hpos : 0 < ∑' n : ℕ, ((n : ℝ) + 1) ^ (-β) :=
    (summable_shift hβ).tsum_pos (fun n => by positivity) 0 (by positivity)
  unfold tfdCoeff
  simp_rw [hterm]
  rw [tsum_mul_left, mul_div_assoc, div_self hpos.ne', mul_one]

/-- **The vacuum expectation of the Möbius connection is the shifted zeta current.** -/
theorem vacuum_current {β : ℝ} (hβ : 1 < β) {z : ℂ} (hz : 1 < z.re + β / 2) :
    ∑' n : ℕ, (Λ n : ℂ) * (n : ℂ) ^ (-z) * (tfdCoeff β n : ℂ) =
      -deriv riemannZeta (z + (β / 2 : ℝ)) / riemannZeta (z + (β / 2 : ℝ)) := by
  rw [← LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hz)]
  unfold LSeries
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero h.ne', tfdCoeff_eq hβ n]
    have hn : (n : ℂ) ≠ 0 := by exact_mod_cast h.ne'
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.cpow_add _ _ hn, Complex.cpow_neg,
      Complex.ofReal_natCast, show ((-β / 2 : ℝ) : ℂ) = -((β / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.cpow_neg]
    have h1 : (n : ℂ) ^ z ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hn)
    have h2 : (n : ℂ) ^ ((β / 2 : ℝ) : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hn)
    field_simp

end GppTFDMobiusCurrent
