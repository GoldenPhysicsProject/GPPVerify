import GppVerify.QuantumGravity.SinhZetaBridge

/-!
# The kinematic block's zeta bridge: `∫₀^∞ t^{s-1}κ(t) dt = (1-2^{-s})Γ(s)ζ(s)`

From `kinematic_block_v1.tex`, Proposition `prop:zetabridge`(a): the kernel
`κ(t) := (2sinh t)⁻¹ = Σ_{n≥0} e^{-(2n+1)t}` — "the generating kernel of the exponential
series of `P` and the kernel that closes the proof of Theorem `thm:moment`" — has Mellin
transform `(1-2^{-s})Γ(s)ζ(s)` for real `s > 1`.

This is `SinhZetaBridge.sinh_mellin_zeta` restated at the paper's own normalization: since
`κ(t) = (1/2)·(1/sinh t)`, the factor of `2` in `sinh_mellin_zeta`'s conclusion cancels the
`1/2` exactly.
-/

namespace GppKinematicBlock

open MeasureTheory Real Set

/-- The kernel `κ(t) = (2sinh t)⁻¹` of `kinematic_block_v1.tex`, Proposition `prop:zetabridge`. -/
noncomputable def kappa (t : ℝ) : ℝ := (2 * Real.sinh t)⁻¹

/-- **Proposition `prop:zetabridge`(a)**: for every real `s > 1`,
    `∫₀^∞ t^{s-1}κ(t) dt = (1-2^{-s})Γ(s)ζ(s)`. -/
theorem zeta_bridge_kappa {s : ℝ} (hs : 1 < s) :
    ∫ t in Ioi (0:ℝ), t ^ (s - 1) * kappa t = (1 - 2 ^ (-s)) * Real.Gamma s *
      ∑' n : ℕ, 1 / (n:ℝ) ^ s := by
  have hcongr : ∀ t : ℝ, t ^ (s - 1) * kappa t = (1/2) * (t ^ (s - 1) / Real.sinh t) := by
    intro t
    unfold kappa
    ring
  simp_rw [hcongr]
  rw [integral_const_mul, GppZetaBridge.sinh_mellin_zeta hs]
  ring

end GppKinematicBlock
