import Mathlib.Tactic

/-!
# Odd/even parity reduction of a symmetric Loewner matrix

For an odd scalar phase `f`, a Loewner matrix sampled on symmetric nodes
`{±x_i}` splits into even and odd parity blocks.  The odd block is not an
unstructured new matrix: after the change of variable `t = x^2` it is,
up to a positive diagonal congruence, the Loewner matrix of the reduced
phase `f(x)/x`.

This is the finite algebra behind the current semilocal Weil odd-core
program.  It is completely independent of zeta zeros and makes no
positivity or RH claim.
-/

namespace GppOddLoewnerParity

/-- Off-diagonal divided difference. -/
noncomputable def dd (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (f x - f y) / (x - y)

/-- For an odd phase, the odd parity combination of the two symmetric-node
Loewner entries factors through the squared nodes. -/
theorem odd_offdiag_reduction
    (f : ℝ → ℝ) (x y : ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy2 : x ^ 2 ≠ y ^ 2)
    (hodd_y : f (-y) = -f y) :
    dd f x y - dd f x (-y) =
      2 * x * y *
        (((f x / x) - (f y / y)) / (x ^ 2 - y ^ 2)) := by
  have hsub : x - y ≠ 0 := by
    intro h
    apply hxy2
    have h' : x = y := sub_eq_zero.mp h
    rw [h']
  have hadd : x + y ≠ 0 := by
    intro h
    apply hxy2
    have h' : x = -y := by linarith
    rw [h']
    ring
  have hsq : x ^ 2 - y ^ 2 ≠ 0 := sub_ne_zero.mpr hxy2
  unfold dd
  rw [hodd_y]
  field_simp [hx, hy, hsub, hadd, hsq]
  ring

/-- For an odd phase, the even parity combination factors through
`x * f(x)` on the squared nodes. -/
theorem even_offdiag_reduction
    (f : ℝ → ℝ) (x y : ℝ)
    (hxy2 : x ^ 2 ≠ y ^ 2)
    (hodd_y : f (-y) = -f y) :
    dd f x y + dd f x (-y) =
      2 * (((x * f x) - (y * f y)) / (x ^ 2 - y ^ 2)) := by
  have hsub : x - y ≠ 0 := by
    intro h
    apply hxy2
    have h' : x = y := sub_eq_zero.mp h
    rw [h']
  have hadd : x + y ≠ 0 := by
    intro h
    apply hxy2
    have h' : x = -y := by linarith
    rw [h']
    ring
  have hsq : x ^ 2 - y ^ 2 ≠ 0 := sub_ne_zero.mpr hxy2
  unfold dd
  rw [hodd_y]
  field_simp [hsub, hadd, hsq]
  ring

/-- Diagonal odd-parity identity.  If `dfx` is read as `f'(x)`, the
right-hand factor is exactly the derivative of the reduced phase
`t ↦ f(√t)/√t` at `t=x²`. -/
theorem odd_diag_reduction (fx dfx x : ℝ) (hx : x ≠ 0) :
    dfx - fx / x =
      2 * x ^ 2 * ((x * dfx - fx) / (2 * x ^ 3)) := by
  field_simp [hx]

/-- Diagonal even-parity identity.  If `dfx=f'(x)`, the right-hand
factor is twice the derivative of `t ↦ √t f(√t)` at `t=x²`. -/
theorem even_diag_reduction (fx dfx x : ℝ) (hx : x ≠ 0) :
    dfx + fx / x =
      2 * ((fx + x * dfx) / (2 * x)) := by
  field_simp [hx]
  ring

/-- The off-diagonal odd block therefore has exactly the same sign as
the reduced divided difference after removing the positive factor
`2*x*y` for positive nodes. -/
theorem odd_offdiag_sign
    (f : ℝ → ℝ) (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hxy2 : x ^ 2 ≠ y ^ 2)
    (hodd_y : f (-y) = -f y)
    (hred : 0 ≤ ((f x / x) - (f y / y)) / (x ^ 2 - y ^ 2)) :
    0 ≤ dd f x y - dd f x (-y) := by
  rw [odd_offdiag_reduction f x y hx.ne' hy.ne' hxy2 hodd_y]
  positivity


/-! ### The odd pole channel is one Stieltjes atom -/

/-- The scalar function \`t ↦ -c/(t+a)\` has rank-one positive Loewner kernel
\`c / ((u+a)(v+a))\`.  This is the exact algebraic shape of the odd
\`s=0,1\` pole correction after passing to squared frequency. -/
theorem stieltjes_atom_dd (c a u v : ℝ)
    (hu : u + a ≠ 0) (hv : v + a ≠ 0) (huv : u ≠ v) :
    dd (fun t : ℝ => -c / (t + a)) u v =
      c / ((u + a) * (v + a)) := by
  unfold dd
  have huv' : u - v ≠ 0 := sub_ne_zero.mpr huv
  field_simp [hu, hv, huv']
  ring

/-- Adding the rank-one vector
\`s(x)=K*x/(x²+a)\` to an odd Loewner block is exactly the same as adding
the reduced Stieltjes atom \`-(K²/2)/(t+a)\` before the positive diagonal
congruence. -/
theorem odd_rankOne_is_stieltjes_atom
    (R K a x y : ℝ)
    (hxden : x ^ 2 + a ≠ 0) (hyden : y ^ 2 + a ≠ 0) :
    2 * x * y *
        (R + (K ^ 2 / 2) / ((x ^ 2 + a) * (y ^ 2 + a))) =
      2 * x * y * R +
        (K * x / (x ^ 2 + a)) * (K * y / (y ^ 2 + a)) := by
  field_simp [hxden, hyden]

end GppOddLoewnerParity

#print axioms GppOddLoewnerParity.odd_offdiag_reduction
#print axioms GppOddLoewnerParity.even_offdiag_reduction
#print axioms GppOddLoewnerParity.odd_diag_reduction
#print axioms GppOddLoewnerParity.odd_offdiag_sign
#print axioms GppOddLoewnerParity.stieltjes_atom_dd
#print axioms GppOddLoewnerParity.odd_rankOne_is_stieltjes_atom
