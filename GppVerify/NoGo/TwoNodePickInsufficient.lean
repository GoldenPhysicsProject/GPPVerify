import Mathlib.Tactic

/-!
# No-go: two-node Pick positivity at every pair of real nodes does not imply three-node positivity

**Strategy refuted.** "Prove the real-node Pick criterion (Astra, `work/2026-10-10_astra_pick_continuation`)
by a two-point / local Schwarz–Pick argument: if every 2×2 real-node Pick matrix of `F` is PSD then all
are." Codex (GPP-bridge PR #11, 2026-10-10/11) found the witness and the two-point factorisation;
this module packages both into one theorem, independently of his PRs #280/#282.

**Witness.** The synthetic folded quartet with spectral zeros `±14 ± i/5` (Astra's `G(k)`), whose
real-axis response is `f(x) = 4x(x²+h)/((x²+h)²+w)` with `h = 4899/25`, `w = 784/25`
(equal to Codex's `100x(25x²+4899)/((25x²−10x+4901)(25x²+10x+4901))`; checked in exact arithmetic).
Pick entries are `(f(xᵢ)+f(xⱼ))/(xᵢ+xⱼ)`, `xᵢ = sᵢ − ½ > ½`.

* `twoNode_pos`: for **all** real `a ≠ b > 0` the 2×2 determinant is **strictly positive** (Codex's
  factorisation; it needs only `h > 0`, `h² > w`, i.e. `γ ≥ (1+√2)|δ|`).
* `threeNode_det_neg`: at `x = (1, 3, 14)` (`s = 3/2, 7/2, 29/2`) the 3×3 determinant is
  `−3995025526004205322265625/493483080809652320286918417738322424 < 0`.

**What the no-go leaves open (the hint).** The witness has the functional-equation symmetry and the
"all quartets far above the real axis" property of `ξ`, but **no Euler product**. Since every true `ξ`
quartet also satisfies `h² > w`, two-node tests cannot separate `ξ` from off-line models: a proof must
use matrices of size ≥ 3 *and* arithmetic (prime) input.
-/

namespace GppNoGo.TwoNodePick

/-- Folded-quartet real-axis response with parameters `h, w`. -/
noncomputable def f (h w x : ℝ) : ℝ := 4 * x * (x ^ 2 + h) / ((x ^ 2 + h) ^ 2 + w)

/-- 2×2 real-node Pick determinant. -/
noncomputable def det2 (h w a b : ℝ) : ℝ :=
  (f h w a + f h w a) / (a + a) * ((f h w b + f h w b) / (b + b)) - ((f h w a + f h w b) / (a + b)) ^ 2

/-- Codex's factorisation of the two-node determinant. -/
theorem det2_eq {h w a b : ℝ} (hh : 0 < h) (hw : 0 ≤ w) (ha : 0 < a) (hb : 0 < b) :
    det2 h w a b = 16 * (a - b) ^ 2 * ((a ^ 2 + h) * (b ^ 2 + h) - w)
      * (h * (a ^ 2 + h) * (b ^ 2 + h) + w * (h + a ^ 2 + b ^ 2))
      / (((a ^ 2 + h) ^ 2 + w) ^ 2 * ((b ^ 2 + h) ^ 2 + w) ^ 2) := by
  have hDa : (a ^ 2 + h) ^ 2 + w ≠ 0 := by positivity
  have hDb : (b ^ 2 + h) ^ 2 + w ≠ 0 := by positivity
  have hab : a + b ≠ 0 := by positivity
  unfold det2 f
  field_simp
  ring

/-- **Every** 2×2 real-node Pick determinant of the folded quartet is strictly positive when `h² > w`. -/
theorem twoNode_pos {h w a b : ℝ} (hh : 0 < h) (hw : 0 ≤ w) (hhw : w < h ^ 2)
    (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b) : 0 < det2 h w a b := by
  rw [det2_eq hh hw ha hb]
  have h1 : 0 < (a - b) ^ 2 := by positivity
  have h2 : 0 < (a ^ 2 + h) * (b ^ 2 + h) - w := by
    have : h ^ 2 ≤ (a ^ 2 + h) * (b ^ 2 + h) := by nlinarith [sq_nonneg a, sq_nonneg b]
    linarith
  have h3 : 0 < h * (a ^ 2 + h) * (b ^ 2 + h) + w * (h + a ^ 2 + b ^ 2) := by positivity
  positivity

/-- Astra's quartet: `h = γ² − δ² = 196 − 1/25`, `w = 4γ²δ² = 784/25` (`γ = 14`, `δ = 1/5`). -/
theorem astra_params : (0 : ℝ) < 4899 / 25 ∧ (0 : ℝ) ≤ 784 / 25 ∧ (784 / 25 : ℝ) < (4899 / 25) ^ 2 := by
  norm_num

/-- Exact rational response for Astra's quartet. -/
def fq (x : ℚ) : ℚ := 4 * x * (x ^ 2 + 4899 / 25) / ((x ^ 2 + 4899 / 25) ^ 2 + 784 / 25)

/-- Pick entry. -/
def P (x y : ℚ) : ℚ := (fq x + fq y) / (x + y)

/-- 3×3 determinant. -/
def det3 (a b c : ℚ) : ℚ :=
  P a a * (P b b * P c c - P b c * P c b) - P a b * (P b a * P c c - P b c * P c a)
    + P a c * (P b a * P c b - P b b * P c a)

/-- **The three-node determinant at `x = (1, 3, 14)` is negative** (exact). -/
theorem threeNode_det_neg :
    det3 1 3 14 = -3995025526004205322265625 / 493483080809652320286918417738322424 ∧
      det3 1 3 14 < 0 := by
  constructor <;> norm_num [det3, P, fq]

/-- **No-go (combined).** There is a response `F` (Astra's quartet) with every 2×2 real-node Pick
determinant strictly positive and a 3×3 real-node Pick determinant strictly negative. -/
theorem two_node_does_not_imply_three :
    (∀ a b : ℝ, 0 < a → 0 < b → a ≠ b → 0 < det2 (4899 / 25) (784 / 25) a b) ∧ det3 1 3 14 < 0 :=
  ⟨fun a b ha hb hne => twoNode_pos (by norm_num) (by norm_num) (by norm_num) ha hb hne,
   threeNode_det_neg.2⟩

end GppNoGo.TwoNodePick
