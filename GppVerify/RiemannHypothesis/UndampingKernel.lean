/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude)
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Undamping package, item (b): the pointwise kernel identity

Scope (routed 2026-11-20, D2's undamping correction): the **scalar kernel identity** behind the
resolvent split `K_b = 2b(−∂²+b²)_D⁻¹ + H_b`. Here `K_b` has kernel `e^{−b|x−y|}`, the Dirichlet
Green kernel of `−∂²+b²` on `[0,L]` is `G_D(x,y) = sinh(b·min)·sinh(b(L−max))/(b·sinh(bL))`, and
`H_b(x,y) = [sinh(b(L−x))e^{−by} + sinh(bx)e^{−b(L−y)}]/sinh(bL)` is a sum of two separated products
(rank ≤ 2).

`kernel_split` is the pointwise identity `e^{−b|x−y|} = 2b·G_D(x,y) + H_b(x,y)` for `b, L > 0`.
 No `sorry`, no `axiom`.
-/

open Real

namespace GppUndampingKernel

/-- Dirichlet Green kernel of `−∂² + b²` on `[0,L]`. -/
noncomputable def greenD (b L x y : ℝ) : ℝ :=
  sinh (b * min x y) * sinh (b * (L - max x y)) / (b * sinh (b * L))

/-- Boundary (rank ≤ 2) correction. -/
noncomputable def Hb (b L x y : ℝ) : ℝ :=
  (sinh (b * (L - x)) * exp (-b * y) + sinh (b * x) * exp (-b * (L - y))) / sinh (b * L)

theorem kernel_split_le {b L x y : ℝ} (hb : 0 < b) (hL : 0 < L) (hxy : x ≤ y) :
    exp (-b * |x - y|) = 2 * b * greenD b L x y + Hb b L x y := by
  have hsh : sinh (b * L) ≠ 0 := (Real.sinh_pos_iff.mpr (by positivity)).ne'
  have habs : |x - y| = y - x := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
  unfold greenD Hb
  rw [habs, min_eq_left hxy, max_eq_right hxy]
  have hb0 : b ≠ 0 := hb.ne'
  field_simp
  simp only [Real.sinh_eq, mul_sub, Real.exp_sub, Real.exp_neg]
  field_simp
  ring

theorem kernel_split_ge {b L x y : ℝ} (hb : 0 < b) (hL : 0 < L) (hyx : y ≤ x) :
    exp (-b * |x - y|) = 2 * b * greenD b L x y + Hb b L x y := by
  have hsh : sinh (b * L) ≠ 0 := (Real.sinh_pos_iff.mpr (by positivity)).ne'
  have habs : |x - y| = x - y := abs_of_nonneg (by linarith)
  unfold greenD Hb
  rw [habs, min_eq_right hyx, max_eq_left hyx]
  have hb0 : b ≠ 0 := hb.ne'
  field_simp
  simp only [Real.sinh_eq, mul_sub, Real.exp_sub, Real.exp_neg]
  field_simp
  ring

/-- **Kernel identity (b).** For `b, L > 0`: `e^{−b|x−y|} = 2b·G_D(x,y) + H_b(x,y)`, with
`G_D` the Dirichlet Green kernel of `−∂²+b²` on `[0,L]` and `H_b` the explicit boundary term
(rank ≤ 2: two separated products). Pointwise scalar identity, all `x, y`. -/
theorem kernel_split {b L : ℝ} (hb : 0 < b) (hL : 0 < L) (x y : ℝ) :
    exp (-b * |x - y|) = 2 * b * greenD b L x y + Hb b L x y := by
  rcases le_total x y with h | h
  · exact kernel_split_le hb hL h
  · exact kernel_split_ge hb hL h

end GppUndampingKernel

#print axioms GppUndampingKernel.kernel_split
