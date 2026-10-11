import Mathlib.Tactic

/-!
# No-go: one off-axis quartet makes **every** real three-node Pick determinant negative

**Statement (Codex, GPP-bridge PR #11, 2026-10-11; independently re-proved here).** For one symmetric
quartet of spectral zeros `±δ ± iγ` put `h = γ² − δ²`, `w = 4γ²δ²`, `D(x) = (x²+h)² + w`,
`f(x) = 4x(x²+h)/D(x)` and `K(x,y) = (f(x)+f(y))/(x+y)`. Then

* `K_eq`: `K(x,y) = 4 N(x,y) / (D(x) D(y))` with the explicit symmetric polynomial `N`;
* `detN_eq`: `det[N(xᵢ,xⱼ)]₃ = −w (a−b)²(a−c)²(b−c)² R(a,b,c)`;
* `det3K_neg`: if `h > 0`, `0 < w ≤ h²` and `a, b, c > 0` are distinct, the 3×3 Pick determinant
  is **strictly negative**.

So a *single* genuinely off-axis quartet (w > 0) fails the three-node test at every real triple, while
it passes every two-node test (`GppNoGo.TwoNodePick.twoNode_pos`). An on-axis pair (`w = 0`) gives
determinant `0` (rank ≤ 2).

**Scope.** This is about one quartet. The Pick kernel of `ξ` is the *sum* over all zero quartets; it
does not say anything about `ξ` itself.

**Hint.** Each off-axis quartet contributes exactly one negative square (consistent with the
Krein–Langer count: negative squares of a generalised Nevanlinna kernel = zeros in the open upper
half-plane). So RH ⇔ the total kernel has **zero** negative squares; the arithmetic must show that
the positive (on-line) contributions cannot be outweighed, which is again Weil positivity. No
loophole here; this pins down that the Pick route is exactly as hard as RH.
-/

namespace GppNoGo.QuartetThreeNode

/-- `D(x) = (x² + h)² + w`. -/
noncomputable def D (h w x : ℝ) : ℝ := (x ^ 2 + h) ^ 2 + w

/-- Folded-quartet response. -/
noncomputable def f (h w x : ℝ) : ℝ := 4 * x * (x ^ 2 + h) / D h w x

/-- Pick kernel. -/
noncomputable def K (h w x y : ℝ) : ℝ := (f h w x + f h w y) / (x + y)

/-- Codex's symmetric numerator polynomial. -/
def N (h w x y : ℝ) : ℝ :=
  x ^ 3 * y ^ 3 + h * (x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3) + (h ^ 2 + w) * (x ^ 2 + y ^ 2)
    + (h ^ 2 - w) * x * y + h ^ 3 + h * w

/-- `R(a,b,c)`. -/
def R (h w a b c : ℝ) : ℝ :=
  h * (a ^ 2 + h) * (b ^ 2 + h) * (c ^ 2 + h)
    + w * (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2 + h * (a ^ 2 + b ^ 2 + c ^ 2)) - w ^ 2

/-- Explicit 3×3 determinant of a function `M`. -/
def det3 (M : ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  M a a * (M b b * M c c - M b c * M c b) - M a b * (M b a * M c c - M b c * M c a)
    + M a c * (M b a * M c b - M b b * M c a)

theorem D_pos {h w x : ℝ} (hh : 0 < h) (hw : 0 ≤ w) : 0 < D h w x := by
  unfold D; positivity

theorem K_eq {h w x y : ℝ} (hh : 0 < h) (hw : 0 ≤ w) (hx : 0 < x) (hy : 0 < y) :
    K h w x y = 4 * N h w x y / (D h w x * D h w y) := by
  have hDx := (D_pos (x := x) hh hw).ne'
  have hDy := (D_pos (x := y) hh hw).ne'
  have hxy : x + y ≠ 0 := by positivity
  unfold K f N
  unfold D at hDx hDy ⊢
  field_simp
  ring

/-- The polynomial determinant identity (pure algebra). -/
theorem detN_eq (h w a b c : ℝ) :
    det3 (N h w) a b c = -w * (a - b) ^ 2 * (a - c) ^ 2 * (b - c) ^ 2 * R h w a b c := by
  unfold det3 N R
  ring

theorem det3K_eq {h w a b c : ℝ} (hh : 0 < h) (hw : 0 ≤ w) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    det3 (K h w) a b c
      = 64 * det3 (N h w) a b c / (D h w a ^ 2 * D h w b ^ 2 * D h w c ^ 2) := by
  have hDa := (D_pos (x := a) hh hw).ne'
  have hDb := (D_pos (x := b) hh hw).ne'
  have hDc := (D_pos (x := c) hh hw).ne'
  unfold det3
  rw [K_eq hh hw ha ha, K_eq hh hw ha hb, K_eq hh hw ha hc, K_eq hh hw hb ha, K_eq hh hw hb hb,
    K_eq hh hw hb hc, K_eq hh hw hc ha, K_eq hh hw hc hb, K_eq hh hw hc hc]
  field_simp
  ring

/-- **No-go.** One off-axis quartet (`w > 0`, `w ≤ h²`) gives a strictly negative 3×3 real-node Pick
determinant at every triple of distinct positive nodes. -/
theorem det3K_neg {h w a b c : ℝ} (hh : 0 < h) (hw : 0 < w) (hwh : w ≤ h ^ 2)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    det3 (K h w) a b c < 0 := by
  rw [det3K_eq hh hw.le ha hb hc, detN_eq]
  have hR : 0 < R h w a b c := by
    unfold R
    have h1 : h ^ 4 < h * (a ^ 2 + h) * (b ^ 2 + h) * (c ^ 2 + h) := by
      have ha2 : h < a ^ 2 + h := by nlinarith [sq_pos_of_pos ha]
      have hb2 : h < b ^ 2 + h := by nlinarith [sq_pos_of_pos hb]
      have hc2 : h < c ^ 2 + h := by nlinarith [sq_pos_of_pos hc]
      have := mul_lt_mul'' (mul_lt_mul'' ha2 hb2 hh.le hh.le) hc2 (by positivity) hh.le
      nlinarith
    have h2 : w ^ 2 ≤ h ^ 4 := by nlinarith
    have h3 : 0 < w * (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2 + h * (a ^ 2 + b ^ 2 + c ^ 2)) := by
      positivity
    linarith
  have hsq : 0 < (a - b) ^ 2 * (a - c) ^ 2 * (b - c) ^ 2 := by
    have := sub_ne_zero.mpr hab; have := sub_ne_zero.mpr hac; have := sub_ne_zero.mpr hbc
    positivity
  have hDa := D_pos (x := a) hh hw.le
  have hDb := D_pos (x := b) hh hw.le
  have hDc := D_pos (x := c) hh hw.le
  have hnum : 64 * (-w * (a - b) ^ 2 * (a - c) ^ 2 * (b - c) ^ 2 * R h w a b c) < 0 := by
    have : 0 < w * ((a - b) ^ 2 * (a - c) ^ 2 * (b - c) ^ 2) * R h w a b c := by positivity
    nlinarith
  exact div_neg_of_neg_of_pos hnum (by positivity)

end GppNoGo.QuartetThreeNode
