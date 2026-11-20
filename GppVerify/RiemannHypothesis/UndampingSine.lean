/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude)
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import GppVerify.RiemannHypothesis.UndampingKernel

/-!
# Undamping package: the sine-eigenvalue relation for the Dirichlet Green kernel

Scope (routed 2026-11-20, D2's undamping correction; follows `UndampingKernel`): the calculus identity
behind "the three resolvents are simultaneously diagonal in the Dirichlet sines". For `b, L > 0`,
`0 ≤ x ≤ L`, `ω = nπ/L`:

`∫₀ᴸ G_D(x,y) sin(ωy) dy = sin(ωx)/(b²+ω²)`   (`greenD_sine`),

so `2b·G_D` multiplies the `n`-th Dirichlet sine by `2b/(b²+(nπ/L)²)` (`greenD_sine_eigen`).
Proof: split at `x`, explicit antiderivatives `F1`, `F2`, and the addition formula for `sinh`.

**Scope, exactly:** a pointwise-in-`x` integral identity. It is NOT the statement that `G_D` is the
inverse of `−∂²+b²_D` as an operator on `L²(0,L)`, NOT the operator norm of the discarded tail, and NOT
the inequality `R_M − ε_M I ≤ Q₀ ≤ R_M`. No `sorry`, no `axiom`.
-/

open Real MeasureTheory intervalIntegral

namespace GppUndampingKernel

section Antiderivs

variable (b ω : ℝ)

/-- `∫ sinh(b y) sin(ω y) dy`. -/
noncomputable def F1 (y : ℝ) : ℝ :=
  (b * cosh (b * y) * sin (ω * y) - ω * sinh (b * y) * cos (ω * y)) / (b ^ 2 + ω ^ 2)

theorem hasDerivAt_F1 (hpos : b ^ 2 + ω ^ 2 ≠ 0) (y : ℝ) :
    HasDerivAt (F1 b ω) (sinh (b * y) * sin (ω * y)) y := by
  have h1 : HasDerivAt (fun y : ℝ => b * y) b y := by simpa using (hasDerivAt_id y).const_mul b
  have h2 : HasDerivAt (fun y : ℝ => ω * y) ω y := by simpa using (hasDerivAt_id y).const_mul ω
  have hc := (h1.cosh)
  have hs := (h1.sinh)
  have hsin := (h2.sin)
  have hcos := (h2.cos)
  have := (((hc.const_mul b).mul hsin).sub (((hs.const_mul ω)).mul hcos)).div_const (b ^ 2 + ω ^ 2)
  unfold F1
  refine this.congr_deriv ?_
  field_simp
  ring

/-- `∫ sinh(b(L−y)) sin(ω y) dy`. -/
noncomputable def F2 (L y : ℝ) : ℝ :=
  (-(b * cosh (b * (L - y)) * sin (ω * y)) - ω * sinh (b * (L - y)) * cos (ω * y)) / (b ^ 2 + ω ^ 2)

theorem hasDerivAt_F2 (L : ℝ) (hpos : b ^ 2 + ω ^ 2 ≠ 0) (y : ℝ) :
    HasDerivAt (F2 b ω L) (sinh (b * (L - y)) * sin (ω * y)) y := by
  have h1 : HasDerivAt (fun y : ℝ => b * (L - y)) (-b) y := by
    simpa using ((hasDerivAt_id y).const_sub L).const_mul b
  have h2 : HasDerivAt (fun y : ℝ => ω * y) ω y := by simpa using (hasDerivAt_id y).const_mul ω
  have hc := h1.cosh
  have hs := h1.sinh
  have hsin := h2.sin
  have hcos := h2.cos
  have := (((hc.const_mul b).mul hsin).neg.sub ((hs.const_mul ω).mul hcos)).div_const (b ^ 2 + ω ^ 2)
  unfold F2
  refine this.congr_deriv ?_
  field_simp
  ring

end Antiderivs


theorem continuous_greenD_y (b L x : ℝ) : Continuous (fun y : ℝ => greenD b L x y) := by
  unfold greenD
  fun_prop

/-- **Sine-eigenvalue relation.** For `0 ≤ x ≤ L`, `b, L > 0` and `ω = nπ/L`:
`∫₀ᴸ G_D(x,y) sin(ωy) dy = sin(ωx)/(b²+ω²)`. Equivalently `2b·G_D` acts on the Dirichlet sine
mode `n` by the eigenvalue `2b/(b²+(nπ/L)²)`. Pointwise-in-`x` calculus; not an operator statement. -/
theorem greenD_sine {b L x : ℝ} (hb : 0 < b) (hL : 0 < L) (hx : 0 ≤ x) (hxL : x ≤ L) (n : ℕ) :
    ∫ y in (0 : ℝ)..L, greenD b L x y * sin ((n * π / L) * y)
      = sin ((n * π / L) * x) / (b ^ 2 + (n * π / L) ^ 2) := by
  set ω : ℝ := n * π / L with hω
  have hpos : b ^ 2 + ω ^ 2 ≠ 0 := by positivity
  have hsinL : sin (ω * L) = 0 := by
    have : ω * L = n * π := by rw [hω]; field_simp
    rw [this]; exact Real.sin_nat_mul_pi n
  have hsh : sinh (b * L) ≠ 0 := (Real.sinh_pos_iff.mpr (by positivity)).ne'
  have hcont : Continuous (fun y : ℝ => greenD b L x y * sin (ω * y)) :=
    (continuous_greenD_y b L x).mul (by fun_prop)
  rw [← integral_add_adjacent_intervals (hcont.intervalIntegrable 0 x) (hcont.intervalIntegrable x L)]
  -- left piece
  have hleft : ∫ y in (0 : ℝ)..x, greenD b L x y * sin (ω * y)
      = (sinh (b * (L - x)) / (b * sinh (b * L))) * (F1 b ω x - F1 b ω 0) := by
    have h1 : ∫ y in (0 : ℝ)..x, greenD b L x y * sin (ω * y)
        = ∫ y in (0 : ℝ)..x, (sinh (b * (L - x)) / (b * sinh (b * L))) * (sinh (b * y) * sin (ω * y)) := by
      refine integral_congr (fun y hy => ?_)
      rw [Set.uIcc_of_le hx] at hy
      simp only [greenD, min_eq_right hy.2, max_eq_left hy.2]
      ring
    rw [h1, intervalIntegral.integral_const_mul]
    congr 1
    exact integral_eq_sub_of_hasDerivAt (fun y _ => hasDerivAt_F1 b ω hpos y)
      ((by fun_prop : Continuous fun y : ℝ => sinh (b * y) * sin (ω * y)).intervalIntegrable _ _)
  have hright : ∫ y in x..L, greenD b L x y * sin (ω * y)
      = (sinh (b * x) / (b * sinh (b * L))) * (F2 b ω L L - F2 b ω L x) := by
    have h1 : ∫ y in x..L, greenD b L x y * sin (ω * y)
        = ∫ y in x..L, (sinh (b * x) / (b * sinh (b * L))) * (sinh (b * (L - y)) * sin (ω * y)) := by
      refine integral_congr (fun y hy => ?_)
      rw [Set.uIcc_of_le hxL] at hy
      simp only [greenD, min_eq_left hy.1, max_eq_right hy.1]
      ring
    rw [h1, intervalIntegral.integral_const_mul]
    congr 1
    exact integral_eq_sub_of_hasDerivAt (fun y _ => hasDerivAt_F2 b ω L hpos y)
      ((by fun_prop : Continuous fun y : ℝ => sinh (b * (L - y)) * sin (ω * y)).intervalIntegrable _ _)
  rw [hleft, hright]
  have hF10 : F1 b ω 0 = 0 := by simp [F1]
  have hF2L : F2 b ω L L = 0 := by simp [F2, hsinL]
  rw [hF10, hF2L]
  have hsplit : sinh (b * L) = sinh (b * x) * cosh (b * (L - x)) + cosh (b * x) * sinh (b * (L - x)) := by
    rw [← Real.sinh_add]; congr 1; ring
  unfold F1 F2
  rw [hsplit] at hsh ⊢
  have hbx : b * (L - 0) = b * L := by ring
  simp only [sub_zero]
  generalize sinh (b * x) = A at *
  generalize cosh (b * x) = B at *
  generalize sinh (b * (L - x)) = C at *
  generalize cosh (b * (L - x)) = D at *
  have hb0 : b ≠ 0 := hb.ne'
  have hS : C * B + A * D ≠ 0 := fun h => hsh (by linarith)
  have hinv : (C * B + A * D) * (C * B + A * D)⁻¹ = 1 := mul_inv_cancel₀ hS
  field_simp
  linear_combination (b * sin (ω * x)) * hinv

/-- The eigenvalue form: `∫₀ᴸ (2b·G_D)(x,y) sin(ωy) dy = (2b/(b²+ω²))·sin(ωx)`. -/
theorem greenD_sine_eigen {b L x : ℝ} (hb : 0 < b) (hL : 0 < L) (hx : 0 ≤ x) (hxL : x ≤ L) (n : ℕ) :
    ∫ y in (0 : ℝ)..L, (2 * b * greenD b L x y) * sin ((n * π / L) * y)
      = (2 * b / (b ^ 2 + (n * π / L) ^ 2)) * sin ((n * π / L) * x) := by
  have h := greenD_sine hb hL hx hxL n
  have : ∀ y : ℝ, (2 * b * greenD b L x y) * sin ((n * π / L) * y)
      = (2 * b) * (greenD b L x y * sin ((n * π / L) * y)) := fun y => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, h]
  ring

end GppUndampingKernel

#print axioms GppUndampingKernel.greenD_sine
#print axioms GppUndampingKernel.greenD_sine_eigen
