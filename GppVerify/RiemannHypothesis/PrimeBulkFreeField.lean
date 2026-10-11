import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The prime bulk free field: exact finite identities

Source: Codex, 2026-10-11, "arithmetic prime bulk/boundary QFT" (GPP-bridge
`work/codex/2026-10-11_arithmetic_prime_bulk_boundary_qft_mass_gap.md`, commit 6780eda; PR #11
comment 6107739998). The construction gives one free Klein–Gordon field `φ_p` of mass `log p`
on a Neumann strip `[0, L]` for every prime `p`, with normal modes
`ω_{p,k} = √((log p)² + (πk/L)²)`.

This file certifies the exact elementary statements the construction rests on.

* `omega_ge_log_two`: every mode has `ω_{p,k} ≥ log 2`, with equality at `p = 2, k = 0`
  (`omega_two_zero`). This is the free-field one-particle gap.
* `omega_ge_split`: `c·log p + d·πk/L ≤ ω_{p,k}` whenever `c² + d² = 1`. This
  is the Cauchy–Schwarz step that makes the whole bulk Gibbs trace factor into
  `(Σ_p p^{−βc})(Σ_k e^{−βdπk/L})`.
* `green_transfer`: the Neumann Green function
  `G(x,y) = cosh(κ x_<) cosh(κ(L − x_>)) / (κ sinh κL)` satisfies
  `G(x,0) = (cosh(κ(L−x))/cosh(κL)) · G(0,0)` for `x ≥ 0`, with
  `G(0,0) = cosh(κL)/(κ sinh κL)`.
* `scale_invariant_no_gap`: if a set of energies is invariant under every dilation `E ↦ λE`
  (`λ > 0`) and contains a positive energy, it contains positive energies below every `δ > 0`.
  So exact scale invariance excludes a gap.
* `doubled_orientation_gapless`: the doubled-orientation generator `H₀ ⊗ 1 − 1 ⊗ H₀` has
  eigenvalues `log(n/m)` arbitrarily close to `0⁺`, so it has no gap.
* `smooth_family_gap_closes`: a correction to *On the Nature of Nature*, Theorem 10.21. The
  family `G_a(r) = e^{−ar}` is smooth (`C^∞`) in `a` at every fixed `r`, while its decay rate
  (gap) `a` tends to `0`. Smoothness of the correlators in the coupling at fixed separation does
  not prevent the gap from closing (Codex).

Scope: this is a **free** (noninteracting) field theory. Its gap `log 2` is the lightest prime
mass, put in by hand. It is not a Yang–Mills mass gap, not a QFT construction theorem in
Lean, and it says nothing about RH.
-/

namespace GppPrimeBulkFreeField

open Real

/-- The normal-mode frequency of the prime-`p` field on a Neumann strip of length `L`. -/
noncomputable def omega (p : ℕ) (k : ℕ) (L : ℝ) : ℝ := sqrt (log p ^ 2 + (π * k / L) ^ 2)

/-- Every prime mode has energy at least `log 2`. -/
theorem omega_ge_log_two {p : ℕ} (hp : p.Prime) (k : ℕ) (L : ℝ) : log 2 ≤ omega p k L := by
  unfold omega
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hl : log 2 ≤ log p := log_le_log (by norm_num) h2
  have hl0 : 0 ≤ log 2 := log_nonneg (by norm_num)
  calc log 2 ≤ log p := hl
    _ = sqrt (log p ^ 2) := (sqrt_sq (hl0.trans hl)).symm
    _ ≤ sqrt (log p ^ 2 + (π * k / L) ^ 2) := sqrt_le_sqrt (by nlinarith [sq_nonneg (π * k / L)])

/-- The gap is attained: the `p = 2`, `k = 0` mode has energy exactly `log 2`. -/
theorem omega_two_zero (L : ℝ) : omega 2 0 L = log 2 := by
  unfold omega
  simp [sqrt_sq (log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]

/-- Cauchy–Schwarz split of the mode energy, used to factor the bulk Gibbs trace. -/
theorem omega_ge_split {c d m q : ℝ} (hcd : c ^ 2 + d ^ 2 = 1) :
    c * m + d * q ≤ sqrt (m ^ 2 + q ^ 2) := by
  apply le_sqrt_of_sq_le
  nlinarith [sq_nonneg (c * q - d * m)]

/-- The Neumann Green function of `−∂ₓ² + κ²` on `[0, L]`. -/
noncomputable def green (κ L x y : ℝ) : ℝ :=
  cosh (κ * min x y) * cosh (κ * (L - max x y)) / (κ * sinh (κ * L))

theorem green_diag_zero (κ L : ℝ) : green κ L 0 0 = cosh (κ * L) / (κ * sinh (κ * L)) := by
  simp [green]

/-- **Boundary-to-bulk transfer.** `G(x,0) = (cosh(κ(L−x))/cosh(κL))·G(0,0)` for `x ≥ 0`. -/
theorem green_transfer (κ L x : ℝ) (hx : 0 ≤ x) :
    green κ L x 0 = cosh (κ * (L - x)) / cosh (κ * L) * green κ L 0 0 := by
  have hc : cosh (κ * L) ≠ 0 := (cosh_pos _).ne'
  rw [green_diag_zero]
  simp only [green, min_eq_right hx, max_eq_left hx, mul_zero, cosh_zero, one_mul]
  field_simp

/-- **Exact scale invariance excludes a gap.** -/
theorem scale_invariant_no_gap (S : Set ℝ) (hS : ∀ l > 0, ∀ E ∈ S, l * E ∈ S)
    {E₀ : ℝ} (hE₀ : E₀ ∈ S) (hpos : 0 < E₀) :
    ∀ δ > 0, ∃ E ∈ S, 0 < E ∧ E < δ := by
  intro δ hδ
  refine ⟨(δ / (2 * E₀)) * E₀, hS _ (by positivity) _ hE₀, by positivity, ?_⟩
  rw [div_mul_eq_mul_div, mul_comm 2 E₀, ← div_div, mul_div_assoc, div_self hpos.ne', mul_one]
  linarith

/-- **The doubled-orientation generator is gapless.** Its eigenvalues `log(n/m)` (`n, m ≥ 1`)
come arbitrarily close to `0` from above. -/
theorem doubled_orientation_gapless :
    ∀ ε > 0, ∃ n m : ℕ, 1 ≤ m ∧ 0 < log ((n : ℝ) / m) ∧ log ((n : ℝ) / m) < ε := by
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε)
  have hm0 : (0 : ℝ) < m := lt_trans (by positivity) hm
  have hm1 : 1 ≤ m := by exact_mod_cast hm0
  refine ⟨m + 1, m, hm1, ?_, ?_⟩
  · apply log_pos
    rw [one_lt_div hm0]; push_cast; linarith
  · have h1 : ((m + 1 : ℕ) : ℝ) / m = 1 + 1 / m := by push_cast; field_simp
    rw [h1]
    calc log (1 + 1 / m) ≤ 1 / m := by
          have := log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / m by positivity)
          linarith
      _ < ε := by rw [div_lt_iff₀ hm0]; rw [div_lt_iff₀ hε] at hm; linarith

/-- **Correction to *On the Nature of Nature*, Theorem 10.21 (Codex).** The correlator family
`G_a(r) = e^{−ar}` is smooth in the coupling `a` at every fixed separation `r`, yet its decay
rate is `a` itself, so the gap closes as `a → 0`. -/
theorem smooth_family_gap_closes :
    (∀ r : ℝ, ContDiff ℝ ⊤ (fun a : ℝ => exp (-(a * r)))) ∧
      (∀ a > (0 : ℝ), ∀ r : ℝ, exp (-(a * r)) = exp (-a) ^ r) ∧
      ∀ δ > (0 : ℝ), ∃ a, 0 < a ∧ a < δ := by
  refine ⟨fun r => ?_, fun a _ r => ?_, fun δ hδ => ⟨δ / 2, by positivity, by linarith⟩⟩
  · exact (contDiff_id.mul contDiff_const).neg.exp
  · rw [← exp_mul]; ring_nf

end GppPrimeBulkFreeField
