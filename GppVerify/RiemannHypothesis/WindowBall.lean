import GppVerify.RiemannHypothesis.WindowCRat
import GppVerify.RiemannHypothesis.WindowPolyBasis
import GppVerify.Upstream.ExpTaylorImaginary
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Rational ball arithmetic and certified enclosures of `log 2`, `log(5/4)`, `√2`, `cos`, `sin`, `log`

A *ball* `b = (c, ρ) : ℚ × ℚ` encloses a real `x` when `|x - c| ≤ ρ` (`InB x b`). Products, sums,
powers and the rounding `flr` of the centre to the `2^-80` grid (`bround`) preserve enclosure. With
these, the transcendental constants of the window symbol get kernel-checkable rational enclosures:

* `log 2 ∈ Lb`, `log(5/4) ∈ lamb` (from the alternating-free series `-log(1 - x) = Σ x^k/k` with its
  Mathlib remainder bound, `Real.abs_log_sub_add_sum_range_le`), `√2 ∈ sqb`, `A₂ = 2 log 2/√2 ∈ Ab`;
* `cos(c log 2) ∈ cosB c`, `sin(c log 2) ∈ sinB c` for every rational `c` (Taylor polynomial of
  `e^{iθ₀}` at `θ₀ = c · centre(Lb)`, plus `|c| radius(Lb)` for the shift of the argument);
* `logQlo c ≤ log((323/4)² + c²/4)` for every rational `c` with `|xQ c| < 1`.

Every enclosure is a theorem; the literals are checked by `decide +kernel`, never trusted.
Unconditional; no `sorry`, no axioms.
-/

namespace GppWindowBall

open Finset Complex GppWindowCRat GppWindowPolyBasis

/-! ### Rounding and balls -/

/-- Round down to the `2^-80` grid. -/
def flr (q : ℚ) : ℚ := (⌊q * 2 ^ 80⌋ : ℚ) / 2 ^ 80

theorem flr_le (q : ℚ) : flr q ≤ q := by
  unfold flr
  rw [div_le_iff₀ (by positivity)]
  exact Int.floor_le _

theorem sub_flr_lt (q : ℚ) : q - flr q < 1 / 2 ^ 80 := by
  have h1 := Int.lt_floor_add_one (q * 2 ^ 80)
  have h : (0 : ℚ) < 2 ^ 80 := by positivity
  have e : q - flr q = (q * 2 ^ 80 - (⌊q * 2 ^ 80⌋ : ℚ)) / 2 ^ 80 := by
    unfold flr; field_simp
  rw [e]
  exact (div_lt_div_iff_of_pos_right h).mpr (by linarith)

/-- A rational ball: centre and radius. -/
abbrev BQ := ℚ × ℚ

/-- `x` lies in the ball `b`. -/
def InB (x : ℝ) (b : BQ) : Prop := |x - (b.1 : ℝ)| ≤ (b.2 : ℝ)

def bex (q : ℚ) : BQ := (q, 0)
def badd (b d : BQ) : BQ := (b.1 + d.1, b.2 + d.2)
def bmul (b d : BQ) : BQ := (b.1 * d.1, |b.1| * d.2 + |d.1| * b.2 + b.2 * d.2)
def bround (b : BQ) : BQ := (flr b.1, b.2 + (b.1 - flr b.1))
def bpow (b : BQ) : ℕ → BQ
  | 0 => bex 1
  | n + 1 => bmul (bpow b n) b

theorem InB.rad_nonneg {x : ℝ} {b : BQ} (h : InB x b) : (0 : ℝ) ≤ b.2 := (abs_nonneg _).trans h

theorem InB_ex (q : ℚ) : InB (q : ℝ) (bex q) := by simp [InB, bex]

theorem InB_add {x y : ℝ} {b d : BQ} (hx : InB x b) (hy : InB y d) : InB (x + y) (badd b d) := by
  unfold InB badd at *
  push_cast
  calc |x + y - ((b.1 : ℝ) + d.1)| = |(x - b.1) + (y - d.1)| := by ring_nf
    _ ≤ |x - b.1| + |y - d.1| := abs_add_le _ _
    _ ≤ _ := add_le_add hx hy

theorem InB_mul {x y : ℝ} {b d : BQ} (hx : InB x b) (hy : InB y d) : InB (x * y) (bmul b d) := by
  have hb := hx.rad_nonneg
  unfold InB bmul at *
  push_cast
  have e : x * y - (b.1 : ℝ) * d.1 =
      (x - b.1) * (y - d.1) + (b.1 : ℝ) * (y - d.1) + (d.1 : ℝ) * (x - b.1) := by ring
  rw [e]
  refine (abs_add_three _ _ _).trans ?_
  rw [abs_mul, abs_mul, abs_mul]
  have h1 : |x - b.1| * |y - d.1| ≤ (b.2 : ℝ) * d.2 :=
    mul_le_mul hx hy (abs_nonneg _) hb
  have h2 : |(b.1 : ℝ)| * |y - d.1| ≤ |(b.1 : ℝ)| * d.2 :=
    mul_le_mul_of_nonneg_left hy (abs_nonneg _)
  have h3 : |(d.1 : ℝ)| * |x - b.1| ≤ |(d.1 : ℝ)| * b.2 :=
    mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  linarith

theorem InB_round {x : ℝ} {b : BQ} (hx : InB x b) : InB x (bround b) := by
  unfold InB bround at *
  have h0 : (0 : ℝ) ≤ ((b.1 - flr b.1 : ℚ) : ℝ) := by
    exact_mod_cast sub_nonneg.mpr (flr_le b.1)
  push_cast at h0 ⊢
  calc |x - (flr b.1 : ℝ)| = |(x - b.1) + ((b.1 : ℝ) - flr b.1)| := by ring_nf
    _ ≤ |x - b.1| + |(b.1 : ℝ) - flr b.1| := abs_add_le _ _
    _ ≤ _ := by rw [abs_of_nonneg h0]; linarith

theorem InB_pow {x : ℝ} {b : BQ} (hx : InB x b) (n : ℕ) : InB (x ^ n) (bpow b n) := by
  induction n with
  | zero => simpa [bpow] using InB_ex 1
  | succ n ih => rw [pow_succ]; exact InB_mul ih hx

theorem InB_mono {x : ℝ} {b d : BQ} (hx : InB x b) (h1 : b.1 = d.1) (h2 : b.2 ≤ d.2) : InB x d := by
  unfold InB at *
  rw [← h1]
  exact hx.trans (by exact_mod_cast h2)

theorem InB_le {x : ℝ} {b : BQ} (hx : InB x b) : x ≤ (b.1 : ℝ) + b.2 := by
  unfold InB at hx; linarith [le_abs_self (x - b.1)]

theorem InB_ge {x : ℝ} {b : BQ} (hx : InB x b) : (b.1 : ℝ) - b.2 ≤ x := by
  unfold InB at hx; linarith [neg_abs_le (x - b.1)]

/-! ### The logarithm series -/

/-- `Σ_{k<n} x^{k+1}/(k+1)`, computably. -/
def logSer (x : ℚ) (n : ℕ) : ℚ := ((List.range n).map fun (k : ℕ) => x ^ (k + 1) / ((k : ℚ) + 1)).sum

theorem logSer_cast (x : ℚ) (n : ℕ) :
    ((logSer x n : ℚ) : ℝ) = ∑ i ∈ range n, (x : ℝ) ^ (i + 1) / (i + 1) := by
  unfold logSer
  rw [← sum_range_eq_list]
  push_cast
  rfl

/-- `|log(1 - x) + Σ_{k<n} x^{k+1}/(k+1)| ≤ |x|^{n+1}/(1 - |x|)`, as a ball for `-log(1 - x)`. -/
theorem neg_log_one_sub_mem (x : ℚ) (hx : |x| < 1) (n : ℕ) :
    InB (-Real.log (1 - x)) (logSer x n, |x| ^ (n + 1) / (1 - |x|)) := by
  have hx' : |(x : ℝ)| < 1 := by exact_mod_cast hx
  have h := Real.abs_log_sub_add_sum_range_le hx' n
  unfold InB
  rw [logSer_cast]
  push_cast
  rw [← abs_neg]
  convert h using 2
  ring

/-! ### The constants -/

/-- `log 2` (`|log 2 - Lb.1| ≤ 2^-79`). -/
def Lb : BQ := (837963523372001241319907 / 2 ^ 80, 2 / 2 ^ 80)
/-- `log(5/4)`. -/
def lamb : BQ := (269764000664250092112816 / 2 ^ 80, 1 / 2 ^ 80)
/-- `√2`. -/
def sqb : BQ := (1709679290002018430137083 / 2 ^ 80, 1 / 2 ^ 80)
/-- `A₂ = 2 log 2/√2 = √2 log 2`. -/
def Ab : BQ := (1185059379526628168201959 / 2 ^ 80, 4 / 2 ^ 80)

theorem Lb_check : 0 ≤ logSer (1 / 2) 80 - Lb.1 ∧
    logSer (1 / 2) 80 - Lb.1 + |(1 / 2 : ℚ)| ^ (80 + 1) / (1 - |(1 / 2 : ℚ)|) ≤ Lb.2 := by
  decide +kernel

theorem lamb_check : 0 ≤ logSer (1 / 5) 40 - lamb.1 ∧
    logSer (1 / 5) 40 - lamb.1 + |(1 / 5 : ℚ)| ^ (40 + 1) / (1 - |(1 / 5 : ℚ)|) ≤ lamb.2 := by
  decide +kernel

/-- From a series ball for `-log(1 - x)` to a coarser ball with a rounded centre. -/
theorem InB_of_series {y : ℝ} {S R : ℚ} {b : BQ} (hy : InB y (S, R)) (h0 : 0 ≤ S - b.1)
    (h1 : S - b.1 + R ≤ b.2) : InB y b := by
  unfold InB at *
  have h0' : (0 : ℝ) ≤ S - b.1 := by exact_mod_cast h0
  have h1' : ((S : ℝ) - b.1) + R ≤ b.2 := by exact_mod_cast h1
  calc |y - b.1| = |(y - S) + ((S : ℝ) - b.1)| := by ring_nf
    _ ≤ |y - S| + |(S : ℝ) - b.1| := abs_add_le _ _
    _ ≤ _ := by rw [abs_of_nonneg h0']; simp only at hy; linarith

theorem log_two_mem : InB (Real.log 2) Lb := by
  have h := neg_log_one_sub_mem (1 / 2) (by norm_num) 80
  have e : -Real.log (1 - ((1 / 2 : ℚ) : ℝ)) = Real.log 2 := by
    rw [show (1 : ℝ) - ((1 / 2 : ℚ) : ℝ) = 2⁻¹ by norm_num, Real.log_inv, neg_neg]
  rw [e] at h
  exact InB_of_series h Lb_check.1 Lb_check.2

theorem log_five_fourths_mem : InB (Real.log (5 / 4)) lamb := by
  have h := neg_log_one_sub_mem (1 / 5) (by norm_num) 40
  have e : -Real.log (1 - ((1 / 5 : ℚ) : ℝ)) = Real.log (5 / 4) := by
    rw [show (1 : ℝ) - ((1 / 5 : ℚ) : ℝ) = (5 / 4)⁻¹ by norm_num, Real.log_inv, neg_neg]
  rw [e] at h
  exact InB_of_series h lamb_check.1 lamb_check.2

theorem sqb_check : 0 ≤ sqb.1 ∧ sqb.1 ^ 2 ≤ 2 ∧ 2 ≤ (sqb.1 + sqb.2) ^ 2 := by decide +kernel

theorem sqrt_two_mem : InB (Real.sqrt 2) sqb := by
  obtain ⟨h0, h1, h2⟩ := sqb_check
  have h0' : (0 : ℝ) ≤ sqb.1 := by exact_mod_cast h0
  have h1' : ((sqb.1 : ℝ)) ^ 2 ≤ 2 := by exact_mod_cast h1
  have h2' : (2 : ℝ) ≤ ((sqb.1 : ℝ) + sqb.2) ^ 2 := by exact_mod_cast h2
  have hr : (0 : ℝ) ≤ sqb.2 := by unfold sqb; norm_num
  have lo : (sqb.1 : ℝ) ≤ Real.sqrt 2 := by
    have := Real.abs_le_sqrt h1'; rwa [abs_of_nonneg h0'] at this
  have hi : Real.sqrt 2 ≤ (sqb.1 : ℝ) + sqb.2 := by
    have := Real.sqrt_le_sqrt h2'; rwa [Real.sqrt_sq (by linarith)] at this
  unfold InB
  rw [abs_le]; constructor <;> linarith

theorem Ab_check : (bround (bmul sqb Lb)).1 = Ab.1 ∧ (bround (bmul sqb Lb)).2 ≤ Ab.2 := by
  decide +kernel

theorem primeTwoA_eq : 2 * Real.log 2 / Real.sqrt 2 = Real.sqrt 2 * Real.log 2 := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  rw [Real.sq_sqrt (by norm_num)]

theorem primeTwoA_mem : InB (2 * Real.log 2 / Real.sqrt 2) Ab := by
  rw [primeTwoA_eq]
  exact InB_mono (InB_round (InB_mul sqrt_two_mem log_two_mem)) Ab_check.1 Ab_check.2

/-! ### Cosine and sine of `c log 2` -/

/-- Number of Taylor terms for `e^{iθ₀}`. -/
def NC : ℕ := 80

/-- `Σ_{m<N} Re(i^m) θ^m/m!`. -/
def cosTay (θ : ℚ) (N : ℕ) : ℚ :=
  ((List.range N).map fun m => (powQ (0, 1) m).1 * θ ^ m / m.factorial).sum

/-- `Σ_{m<N} Im(i^m) θ^m/m!`. -/
def sinTay (θ : ℚ) (N : ℕ) : ℚ :=
  ((List.range N).map fun m => (powQ (0, 1) m).2 * θ ^ m / m.factorial).sum

/-- The enclosure radius: `|c| rad(Lb) + |θ₀|^N/N!`. -/
def trigRad (c : ℚ) : ℚ := |c| * Lb.2 + |c * Lb.1| ^ NC / NC.factorial

def cosB (c : ℚ) : BQ := bround (cosTay (c * Lb.1) NC, trigRad c)
def sinB (c : ℚ) : BQ := bround (sinTay (c * Lb.1) NC, trigRad c)

theorem toC_im (z : CQ) : (toC z).im = (z.2 : ℝ) := by simp [toC]

theorem I_eq_toC : (I : ℂ) = toC (0, 1) := by simp [toC]

theorem taylor_term_eq (y : ℝ) (m : ℕ) :
    (I * y) ^ m / m.factorial = toC (powQ (0, 1) m) * ((y ^ m / m.factorial : ℝ) : ℂ) := by
  rw [toC_pow, ← I_eq_toC]; push_cast; ring

theorem re_taylor (y : ℝ) (N : ℕ) :
    (∑ m ∈ range N, (I * y) ^ m / m.factorial).re =
      ∑ m ∈ range N, ((powQ (0, 1) m).1 : ℝ) * (y ^ m / m.factorial) := by
  rw [Complex.re_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [taylor_term_eq, Complex.re_mul_ofReal, toC_re]

theorem im_taylor (y : ℝ) (N : ℕ) :
    (∑ m ∈ range N, (I * y) ^ m / m.factorial).im =
      ∑ m ∈ range N, ((powQ (0, 1) m).2 : ℝ) * (y ^ m / m.factorial) := by
  rw [Complex.im_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [taylor_term_eq, Complex.im_mul_ofReal, toC_im]

theorem cosTay_cast (θ : ℚ) (N : ℕ) :
    ((cosTay θ N : ℚ) : ℝ) = ∑ m ∈ range N, ((powQ (0, 1) m).1 : ℝ) * ((θ : ℝ) ^ m / m.factorial) := by
  unfold cosTay
  rw [← sum_range_eq_list]
  push_cast
  refine sum_congr rfl fun m _ => by ring

theorem sinTay_cast (θ : ℚ) (N : ℕ) :
    ((sinTay θ N : ℚ) : ℝ) = ∑ m ∈ range N, ((powQ (0, 1) m).2 : ℝ) * ((θ : ℝ) ^ m / m.factorial) := by
  unfold sinTay
  rw [← sum_range_eq_list]
  push_cast
  refine sum_congr rfl fun m _ => by ring

theorem exp_I_re (y : ℝ) : (Complex.exp (I * y)).re = Real.cos y := by
  rw [mul_comm]; exact Complex.exp_ofReal_mul_I_re y

theorem exp_I_im (y : ℝ) : (Complex.exp (I * y)).im = Real.sin y := by
  rw [mul_comm]; exact Complex.exp_ofReal_mul_I_im y

theorem trig_arg_bound (c : ℚ) :
    |(c : ℝ) * Real.log 2 - ((c * Lb.1 : ℚ) : ℝ)| ≤ |(c : ℝ)| * (Lb.2 : ℝ) := by
  have h := log_two_mem
  unfold InB at h
  push_cast
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

theorem trigRad_cast (c : ℚ) :
    ((trigRad c : ℚ) : ℝ) = |(c : ℝ)| * (Lb.2 : ℝ) +
      |((c * Lb.1 : ℚ) : ℝ)| ^ NC / (NC.factorial : ℝ) := by
  unfold trigRad; push_cast; ring

theorem cos_mem (c : ℚ) : InB (Real.cos (c * Real.log 2)) (cosB c) := by
  apply InB_round
  unfold InB
  simp only
  set θ0 : ℚ := c * Lb.1
  have h1 := Real.abs_cos_sub_cos_le ((c : ℝ) * Real.log 2) (θ0 : ℝ)
  have h2 := Complex.norm_exp_I_mul_sub_taylor_le NC (θ0 : ℝ)
  have h3 : |Real.cos θ0 - (cosTay θ0 NC : ℝ)| ≤ |(θ0 : ℝ)| ^ NC / NC.factorial := by
    refine le_trans ?_ h2
    rw [← exp_I_re, cosTay_cast, ← re_taylor, ← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  rw [trigRad_cast]
  calc |Real.cos (c * Real.log 2) - (cosTay θ0 NC : ℝ)|
      = |(Real.cos (c * Real.log 2) - Real.cos θ0) + (Real.cos θ0 - (cosTay θ0 NC : ℝ))| := by
        ring_nf
    _ ≤ |Real.cos (c * Real.log 2) - Real.cos θ0| + |Real.cos θ0 - (cosTay θ0 NC : ℝ)| :=
        abs_add_le _ _
    _ ≤ _ := add_le_add (h1.trans (trig_arg_bound c)) h3

theorem sin_mem (c : ℚ) : InB (Real.sin (c * Real.log 2)) (sinB c) := by
  apply InB_round
  unfold InB
  simp only
  set θ0 : ℚ := c * Lb.1
  have h1 := Real.abs_sin_sub_sin_le ((c : ℝ) * Real.log 2) (θ0 : ℝ)
  have h2 := Complex.norm_exp_I_mul_sub_taylor_le NC (θ0 : ℝ)
  have h3 : |Real.sin θ0 - (sinTay θ0 NC : ℝ)| ≤ |(θ0 : ℝ)| ^ NC / NC.factorial := by
    refine le_trans ?_ h2
    rw [← exp_I_im, sinTay_cast, ← im_taylor, ← Complex.sub_im]
    exact Complex.abs_im_le_norm _
  rw [trigRad_cast]
  calc |Real.sin (c * Real.log 2) - (sinTay θ0 NC : ℝ)|
      = |(Real.sin (c * Real.log 2) - Real.sin θ0) + (Real.sin θ0 - (sinTay θ0 NC : ℝ))| := by
        ring_nf
    _ ≤ |Real.sin (c * Real.log 2) - Real.sin θ0| + |Real.sin θ0 - (sinTay θ0 NC : ℝ)| :=
        abs_add_le _ _
    _ ≤ _ := add_le_add (h1.trans (trig_arg_bound c)) h3

/-! ### `log Q(c)`, `Q(c) = X² + c²/4`, `X = 323/4` -/

/-- `X = M + 3/4` for the shift `M = 80`. -/
def XQ : ℚ := 323 / 4

def Qc (c : ℚ) : ℚ := XQ ^ 2 + c ^ 2 / 4

/-- `Q(c) = 2^13 (1 - xQ c)`. -/
def xQ (c : ℚ) : ℚ := 1 - Qc c / 2 ^ 13

def NLOG : ℕ := 40

/-- A rational lower bound for `log Q(c)`. -/
def logQlo (c : ℚ) : ℚ :=
  flr (13 * (Lb.1 - Lb.2) - logSer (xQ c) NLOG - |xQ c| ^ (NLOG + 1) / (1 - |xQ c|))

theorem logQlo_le (c : ℚ) (hx : |xQ c| < 1) : (logQlo c : ℝ) ≤ Real.log (Qc c) := by
  have hser := InB_le (neg_log_one_sub_mem (xQ c) hx NLOG)
  have hL := InB_ge log_two_mem
  have hpos : (0 : ℝ) < 1 - (xQ c : ℝ) := by
    have : (xQ c : ℝ) < 1 := by
      have := (abs_lt.mp hx).2; exact_mod_cast this
    linarith
  have hQ : ((Qc c : ℚ) : ℝ) = 2 ^ 13 * (1 - (xQ c : ℝ)) := by
    unfold xQ; push_cast; ring
  have hlog : Real.log (Qc c) = 13 * Real.log 2 + Real.log (1 - (xQ c : ℝ)) := by
    rw [hQ, Real.log_mul (by positivity) hpos.ne', Real.log_pow]; push_cast; ring
  have hflr : ((logQlo c : ℚ) : ℝ) ≤
      ((13 * (Lb.1 - Lb.2) - logSer (xQ c) NLOG - |xQ c| ^ (NLOG + 1) / (1 - |xQ c|) : ℚ) : ℝ) := by
    exact_mod_cast flr_le _
  push_cast at hflr hser hL
  rw [hlog]
  linarith

end GppWindowBall

#print axioms GppWindowBall.cos_mem
#print axioms GppWindowBall.sin_mem
#print axioms GppWindowBall.logQlo_le
#print axioms GppWindowBall.primeTwoA_mem
#print axioms GppWindowBall.log_five_fourths_mem
