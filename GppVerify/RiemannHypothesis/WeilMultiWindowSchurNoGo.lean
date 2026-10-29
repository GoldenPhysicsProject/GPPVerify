import Mathlib

/-!
# Multi-window positivity: pairwise control is insufficient

An unconditional exact finite counterexample to the proposed inference
"each pair of support windows satisfies a strict Cauchy--Schwarz margin,
therefore their global quadratic form is positive".

The genuine completed Weil form is **not** instantiated here. These are
finite model obstruction and local prime-block algebra, not RH statements.

Three windows have diagonal entries 1 and every off-diagonal entry -3/5.
Every two-window principal restriction is PSD, with |cross|²=9/25 < 1,
but the all-ones direction has value -3/5.

Further, the sharp local N=1 geometric prime blocks (x=1/2,L=1 and
x=1/3,L=2) are squares with exact null directions. Any positive
cross-prime coupling on the temporal coordinates gives a negative
direction on the two nulls unless further diagonal compensation is added.
-/

namespace GppMultiWindow

def threeWindowForm (a b c : ℝ) : ℝ :=
  a ^ 2 + b ^ 2 + c ^ 2 - (6 / 5 : ℝ) * (a*b + a*c + b*c)

/-- Every two-window restriction is nonnegative, with a strict pairwise margin. -/
theorem twoWindow_nonneg (a b : ℝ) :
    0 ≤ a ^ 2 + b ^ 2 - (6 / 5 : ℝ) * a * b := by
  have h1 := sq_nonneg (a - (3 / 5 : ℝ) * b)
  have h2 := sq_nonneg ((4 / 5 : ℝ) * b)
  nlinarith

theorem pairwise_strict_margin :
    (3 / 5 : ℝ) ^ 2 = 1 - (16 / 25 : ℝ) := by
  norm_num

/-- All three windows together have a strictly negative direction. -/
theorem threeWindow_negative : threeWindowForm 1 1 1 = -(3 / 5 : ℝ) := by
  norm_num [threeWindowForm]

theorem pairwise_not_global :
    ¬ (∀ a b c : ℝ, 0 ≤ threeWindowForm a b c) := by
  intro h
  have hbad := h 1 1 1
  norm_num [threeWindowForm] at hbad

/-- A sharp positive local contact/threshold block at x=1/2, L=1. -/
def primeBlockOne (t a : ℝ) : ℝ := (a - 2*t) ^ 2 / 4

/-- A second sharp positive local block at x=1/3, L=2. -/
def primeBlockTwo (t a : ℝ) : ℝ := (2 / 9 : ℝ) * (a - 3*t) ^ 2

theorem primeBlockOne_nonneg (t a : ℝ) : 0 ≤ primeBlockOne t a := by
  unfold primeBlockOne
  positivity

theorem primeBlockTwo_nonneg (t a : ℝ) : 0 ≤ primeBlockTwo t a := by
  unfold primeBlockTwo
  positivity

/-- An unrestricted cross-window term need not preserve local PSD. -/
def coupledBlock (eps t₁ a₁ t₂ a₂ : ℝ) : ℝ :=
  primeBlockOne t₁ a₁ + primeBlockTwo t₂ a₂ + 2*eps*t₁*t₂

theorem coupledBlock_negative_on_nulls (eps : ℝ) :
    coupledBlock eps 1 2 (-1) (-3) = -2*eps := by
  norm_num [coupledBlock, primeBlockOne, primeBlockTwo]

theorem any_positive_cross_creates_negative_direction
    (eps : ℝ) (heps : 0 < eps) :
    ¬ (∀ t₁ a₁ t₂ a₂ : ℝ, 0 ≤ coupledBlock eps t₁ a₁ t₂ a₂) := by
  intro h
  have hbad := h 1 2 (-1) (-3)
  rw [coupledBlock_negative_on_nulls] at hbad
  linarith

end GppMultiWindow
