import Mathlib.Tactic

/-!
# Universal three-real-node Pick obstruction for a single displaced spectral quartet

For spectral poles ±gamma ± i*delta, put
  h = gamma^2 - delta^2,
  w = 4*gamma^2*delta^2.
Along the real Euler-coordinate x>0, the logarithmic-derivative response is
  f(x) = 4*x*(x^2+h)/((x^2+h)^2+w).
The real-node Pick entry is (f(x)+f(y))/(x+y).

This module proves an *all-triples* sign mechanism, not just one rational
example: when h>0, 0<w<=h^2, and a,b,c>0 are pairwise distinct, the
three-point determinant is NEGATIVE. Under exactly these hypotheses all
two-point principal determinants are POSITIVE (the companion theorem
in NoGo/TwoNodePickInsufficient and Codex's ArithmeticPickPole).

There is NO claim about the full completed xi function or RH. Other
quartets may alter the negative direction in their summed kernel.
-/

namespace GppQuartetThreeNodeUniversal

noncomputable section

def D (h w x : ℝ) : ℝ := (x ^ 2 + h) ^ 2 + w

def numerator (h w x y : ℝ) : ℝ :=
  x ^ 3 * y ^ 3
  + h * (x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3)
  + (h ^ 2 + w) * (x ^ 2 + y ^ 2)
  + (h ^ 2 - w) * x * y
  + h ^ 3 + h * w

def response (h w x : ℝ) : ℝ := 4 * x * (x ^ 2 + h) / D h w x
def pick (h w x y : ℝ) : ℝ := (response h w x + response h w y) / (x + y)

def det3 (h w a b c : ℝ) : ℝ :=
  pick h w a a * pick h w b b * pick h w c c
  + 2 * pick h w a b * pick h w a c * pick h w b c
  - pick h w a a * (pick h w b c) ^ 2
  - pick h w b b * (pick h w a c) ^ 2
  - pick h w c c * (pick h w a b) ^ 2

def polyDet (h w a b c : ℝ) : ℝ :=
  numerator h w a a * numerator h w b b * numerator h w c c
  + 2 * numerator h w a b * numerator h w a c * numerator h w b c
  - numerator h w a a * (numerator h w b c) ^ 2
  - numerator h w b b * (numerator h w a c) ^ 2
  - numerator h w c c * (numerator h w a b) ^ 2

def R (h w a b c : ℝ) : ℝ :=
  h * (a ^ 2 + h) * (b ^ 2 + h) * (c ^ 2 + h)
  + w * (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2
        + h * (a ^ 2 + b ^ 2 + c ^ 2))
  - w ^ 2

/-- Completely polynomial identity underlying the Pick-determinant sign. -/
theorem polyDet_factor (h w a b c : ℝ) :
    polyDet h w a b c =
      -w * (a-b)^2 * (a-c)^2 * (b-c)^2 * R h w a b c := by
  unfold polyDet numerator R
  ring

theorem D_pos {h w x : ℝ} (hh : 0 < h) (hw : 0 ≤ w) : 0 < D h w x := by
  unfold D
  positivity

/-- A Pick entry is an explicitly factored rational polynomial kernel. -/
theorem pick_eq_num {h w x y : ℝ}
    (hh : 0 < h) (hw : 0 ≤ w) (hx : 0 < x) (hy : 0 < y) :
    pick h w x y =
      4 * numerator h w x y / (D h w x * D h w y) := by
  have hDx : D h w x ≠ 0 := (D_pos hh hw).ne'
  have hDy : D h w y ≠ 0 := (D_pos hh hw).ne'
  have hxy : x + y ≠ 0 := ne_of_gt (add_pos hx hy)
  unfold pick response
  field_simp
  unfold numerator D
  ring

/-- The **complete** three-point determinant factorisation. -/
theorem det3_factor {h w a b c : ℝ}
    (hh : 0 < h) (hw : 0 ≤ w)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    det3 h w a b c =
      -64 * w * (a-b)^2 * (a-c)^2 * (b-c)^2 * R h w a b c /
        ((D h w a)^2 * (D h w b)^2 * (D h w c)^2) := by
  have hDa : D h w a ≠ 0 := (D_pos hh hw).ne'
  have hDb : D h w b ≠ 0 := (D_pos hh hw).ne'
  have hDc : D h w c ≠ 0 := (D_pos hh hw).ne'
  have hpoly := polyDet_factor h w a b c
  unfold det3
  rw [pick_eq_num hh hw ha ha, pick_eq_num hh hw hb hb,
      pick_eq_num hh hw hc hc, pick_eq_num hh hw ha hb,
      pick_eq_num hh hw ha hc, pick_eq_num hh hw hb hc]
  unfold polyDet at hpoly
  field_simp
  nlinarith [hpoly]

/-- Non-negativity of the residual from a polynomial positivity certificate. -/
theorem R_pos {h w a b c : ℝ}
    (hh : 0 < h) (hw : 0 < w) (hhw : w ≤ h ^ 2)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < R h w a b c := by
  have hdiff : 0 ≤ h ^ 4 - w ^ 2 := by
    have h1 : 0 ≤ h^2 - w := sub_nonneg.mpr hhw
    have h2 : 0 ≤ h^2 + w := by positivity
    nlinarith [mul_nonneg h1 h2]
  have hprod :
      0 ≤ h * (a ^ 2 + h) * (b ^ 2 + h) * (c ^ 2 + h) - h ^ 4 := by
    ring_nf
    positivity
  have hrest : 0 < w * (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2
        + h * (a ^ 2 + b ^ 2 + c ^ 2)) := by positivity
  unfold R
  linarith

/-- Universal failure of three-node positivity for a displaced quartet
    in the same high-height regime where every two-node minor passes. -/
theorem three_node_strictly_negative {h w a b c : ℝ}
    (hh : 0 < h) (hw : 0 < w) (hhw : w ≤ h ^ 2)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    det3 h w a b c < 0 := by
  rw [det3_factor hh (le_of_lt hw) ha hb hc]
  have hR : 0 < R h w a b c := R_pos hh hw hhw ha hb hc
  have hden : 0 < (D h w a)^2 * (D h w b)^2 * (D h w c)^2 := by
    have haD := D_pos hh (le_of_lt hw) (x := a)
    have hbD := D_pos hh (le_of_lt hw) (x := b)
    have hcD := D_pos hh (le_of_lt hw) (x := c)
    positivity
  have habs : 0 < (a-b)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hab)
  have hacs : 0 < (a-c)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hac)
  have hbcs : 0 < (b-c)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hbc)
  have hnum : 0 < 64 * w * (a-b)^2 * (a-c)^2 * (b-c)^2 * R h w a b c := by
    positivity
  exact div_neg_of_neg_of_pos (by nlinarith) hden

end

end GppQuartetThreeNodeUniversal
