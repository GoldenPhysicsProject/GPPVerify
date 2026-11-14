import GppVerify.RiemannHypothesis.WindowBall
import GppVerify.RiemannHypothesis.WindowElementary
import GppVerify.RiemannHypothesis.WindowGM

/-!
# Input (b), the generic local bound: `G_80(c + u) ≥ Σ_n lbF c n · uⁿ - errF c` on `|u| ≤ 1/8`

For every rational centre `c` (with the side condition `|xQ c| < 1`, i.e. `Q(c) ∈ (0, 2^14)`) and
every real `|u| ≤ 1/8` (`GM_ge`):

  `Σ_{n<13} lbF c n · uⁿ - errF c ≤ G_80(c + u)`,

where `lbF c n`, `errF c` are rationals *computed* from `c` (so a kernel can evaluate them for each
piece centre), built from

* the rational terms `a/(a² + r²/4)`, `a = 1/4 + k`, `k ≤ 80`: finite geometric expansion at `c`
  (`GppWindowElementary.abs_re_inv_sub_taylor_le`), Taylor coefficients `tQ a c n` computed in
  `ℚ + ℚi` (`GppWindowCRat`) and rounded down to `2^-80` (error `rnd` each);
* `½ log Q(r) - 1/(4Q(r))`, `Q(r) = X² + r²/4`, `X = 323/4`: tangent bound for the log
  (`log_ge_tangent`), which leaves `-κ X/Q(r)` with `κ = Q(c)/(2X) + 1/(4X)`, expanded the same way,
  and `log Q(c) ≥ logQlo c`;
* `-A₂ cos(r log 2)`: Taylor at `c` (`abs_cos_sub_taylor_le`) with the coefficients
  `A₂ (log 2)^m/m! · Re(iᵐ e^{ic log 2})` enclosed in rational balls (`Kball`);
* the constant `-log π - β₂(25) = -2 log(5/4) - 3 log 2 + 1/25 + A₂ ≥ Klo` (`π` cancels).

`checkPiece i` then compares this with the stored minorant piece `pieceTable[i]`, re-centred at
`c_i = (2i+1)/8` (`shiftQ`, exact), and `piece_bound` turns `checkPiece i = true` into
`m ≤ G_80` and `|m| ≤ 8` on `[i/4, (i+1)/4]`.

Unconditional; no `sorry`, no axioms.
-/

namespace GppWindowBPiece

open Finset Complex GppWindowCRat GppWindowBall GppWindowElementary GppWindowGM
  GppRungOneReductionTwo GppWindowPolyBasis

/-- Taylor terms per expansion. -/
def NT : ℕ := 13

/-- `Re((-i/2)ⁿ / (a + i c/2)^{n+1})`, the `n`-th Taylor coefficient of `a/(a² + r²/4)` at `c`. -/
def tQ (a c : ℚ) (n : ℕ) : ℚ := (mulQ (powQ (0, -1 / 2) n) (powQ (invQ (a, c / 2)) (n + 1))).1

/-- The truncation error of that expansion on `|u| ≤ 1/8`. -/
def Eb (a : ℚ) : ℚ := (1 / 16) ^ NT / (a ^ NT * a)

/-- The rounding error of a rounded coefficient list on `|u| ≤ 1/8`. -/
def rnd : ℚ := 2 / 2 ^ 80

def aK (k : ℕ) : ℚ := 1 / 4 + k

def kappaX (c : ℚ) : ℚ := Qc c / (2 * XQ) + 1 / (4 * XQ)

/-- `Re(e^{iθ} iᵐ) = cos θ Re(iᵐ) - sin θ Im(iᵐ)`, `θ = c log 2`. -/
def sig (c : ℚ) (m : ℕ) : BQ :=
  badd (bmul (cosB c) (bex (powQ (0, 1) m).1)) (bmul (sinB c) (bex (-(powQ (0, 1) m).2)))

/-- `A₂ (log 2)^m/m! · Re(e^{iθ} iᵐ)`. -/
def Kball (c : ℚ) (m : ℕ) : BQ :=
  bround (bmul Ab (bmul (bmul (bex (1 / m.factorial)) (bpow Lb m)) (sig c m)))

/-- A lower bound for `-log π - β₂(25)`. -/
def Klo : ℚ := -2 * (lamb.1 + lamb.2) - 3 * (Lb.1 + Lb.2) + 1 / 25 + (Ab.1 - Ab.2)

/-- The coefficients of the lower bound. -/
def lbF (c : ℚ) (n : ℕ) : ℚ :=
  -((List.range 81).map fun k => flr (tQ (aK k) c n)).sum - flr (kappaX c * tQ XQ c n)
    - (Kball c n).1 + if n = 0 then logQlo c / 2 + 1 / 2 + Klo else 0

/-- The total error of the lower bound. -/
def errF (c : ℚ) : ℚ :=
  ((List.range 81).map fun k => Eb (aK k) + rnd).sum + (kappaX c * Eb XQ + rnd)
    + ((List.range NT).map fun m => (Kball c m).2 / 8 ^ m).sum
    + (Ab.1 + Ab.2) * ((Lb.1 + Lb.2) / 8) ^ NT / NT.factorial

/-! ### Casts -/

theorem listSum_cast (n : ℕ) (f : ℕ → ℚ) :
    ((((List.range n).map f).sum : ℚ) : ℝ) = ∑ i ∈ range n, (f i : ℝ) := by
  rw [← sum_range_eq_list]; push_cast; rfl

theorem tQ_cast (a c : ℚ) (n : ℕ) :
    ((tQ a c n : ℚ) : ℝ) =
      ((-(I / 2)) ^ n / (((a : ℝ) : ℂ) + (((c : ℝ) / 2 : ℝ) : ℂ) * I) ^ (n + 1)).re := by
  unfold tQ
  rw [← toC_re, toC_mul, toC_pow, toC_pow, toC_inv]
  have h1 : toC (0, -1 / 2) = -(I / 2) := by simp [toC]; ring
  have h2 : toC (a, c / 2) = (((a : ℝ) : ℂ) + (((c : ℝ) / 2 : ℝ) : ℂ) * I) := by
    simp [toC]
  rw [h1, h2, inv_pow, ← div_eq_mul_inv]

/-! ### The rational terms -/

theorem R_le_exact (a c : ℚ) (ha : 0 < a) {u : ℝ} (hu : |u| ≤ 1 / 8) :
    (a : ℝ) / ((a : ℝ) ^ 2 + (((c : ℝ) + u) / 2) ^ 2) ≤
      ∑ n ∈ range NT, (tQ a c n : ℝ) * u ^ n + (Eb a : ℝ) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  rw [re_inv_eq]
  have h := abs_re_inv_sub_taylor_le ha' (c : ℝ) u NT
  simp_rw [← tQ_cast] at h
  have hE : (|u| / 2) ^ NT / ((a : ℝ) ^ NT * a) ≤ (Eb a : ℝ) := by
    unfold Eb; push_cast
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by linarith) NT
  have := (abs_le.mp (h.trans hE)).2
  linarith

theorem round_poly (t : ℕ → ℚ) {u : ℝ} (hu : |u| ≤ 1 / 8) :
    ∑ n ∈ range NT, (t n : ℝ) * u ^ n ≤ ∑ n ∈ range NT, (flr (t n) : ℝ) * u ^ n + (rnd : ℝ) := by
  have hterm : ∀ n ∈ range NT, (t n : ℝ) * u ^ n ≤
      (flr (t n) : ℝ) * u ^ n + (1 / 2 ^ 80) * (1 / 2 : ℝ) ^ n := by
    intro n _
    have h0 : (0 : ℝ) ≤ t n - flr (t n) := by exact_mod_cast sub_nonneg.mpr (flr_le _)
    have h1 : ((t n : ℝ) - flr (t n)) ≤ 1 / 2 ^ 80 := by
      have h2 := (sub_flr_lt (t n)).le
      have h3 : ((t n - flr (t n) : ℚ) : ℝ) ≤ ((1 / 2 ^ 80 : ℚ) : ℝ) := by exact_mod_cast h2
      push_cast at h3; exact h3
    have hu' : |u ^ n| ≤ (1 / 2 : ℝ) ^ n := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) n
    have : ((t n : ℝ) - flr (t n)) * u ^ n ≤ (1 / 2 ^ 80) * (1 / 2 : ℝ) ^ n := by
      calc ((t n : ℝ) - flr (t n)) * u ^ n ≤ |((t n : ℝ) - flr (t n)) * u ^ n| := le_abs_self _
        _ = ((t n : ℝ) - flr (t n)) * |u ^ n| := by rw [abs_mul, abs_of_nonneg h0]
        _ ≤ (1 / 2 ^ 80) * (1 / 2 : ℝ) ^ n :=
            mul_le_mul h1 hu' (abs_nonneg _) (by positivity)
    linarith
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, ← mul_sum]
  have hg := sum_geometric_two_le NT
  have : (1 / 2 ^ 80 : ℝ) * ∑ i ∈ range NT, (1 / 2 : ℝ) ^ i ≤ rnd := by
    unfold rnd; push_cast
    nlinarith
  linarith

theorem R_le (a c : ℚ) (ha : 0 < a) {u : ℝ} (hu : |u| ≤ 1 / 8) :
    (a : ℝ) / ((a : ℝ) ^ 2 + (((c : ℝ) + u) / 2) ^ 2) ≤
      ∑ n ∈ range NT, (flr (tQ a c n) : ℝ) * u ^ n + ((Eb a + rnd : ℚ) : ℝ) := by
  have h1 := R_le_exact a c ha hu
  have h2 := round_poly (tQ a c) hu
  push_cast
  linarith

/-! ### Balls along a polynomial -/

theorem ball_poly_le {N : ℕ} (x : ℕ → ℝ) (b : ℕ → BQ) (hb : ∀ n, InB (x n) (b n)) {u : ℝ}
    (hu : |u| ≤ 1 / 8) :
    ∑ n ∈ range N, x n * u ^ n ≤
      ∑ n ∈ range N, ((b n).1 : ℝ) * u ^ n + ∑ n ∈ range N, ((b n).2 : ℝ) / 8 ^ n := by
  rw [← sum_add_distrib]
  refine sum_le_sum fun n _ => ?_
  have h := hb n
  unfold InB at h
  have hu' : |u ^ n| ≤ (1 / 8 : ℝ) ^ n := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hu n
  have : (x n - (b n).1) * u ^ n ≤ ((b n).2 : ℝ) / 8 ^ n := by
    calc (x n - (b n).1) * u ^ n ≤ |(x n - (b n).1) * u ^ n| := le_abs_self _
      _ = |x n - (b n).1| * |u ^ n| := abs_mul _ _
      _ ≤ (b n).2 * (1 / 8 : ℝ) ^ n := mul_le_mul h hu' (abs_nonneg _) ((abs_nonneg _).trans h)
      _ = ((b n).2 : ℝ) / 8 ^ n := by rw [one_div_pow, mul_one_div]
  linarith

/-! ### The cosine -/

/-- `(log 2)^m/m! · Re(e^{ic log 2} iᵐ)`. -/
noncomputable def kap (c : ℚ) (m : ℕ) : ℝ :=
  ((1 / (m.factorial : ℚ) : ℚ) : ℝ) * Real.log 2 ^ m *
    (Real.cos (c * Real.log 2) * ((powQ (0, 1) m).1 : ℝ) +
      Real.sin (c * Real.log 2) * ((-(powQ (0, 1) m).2 : ℚ) : ℝ))

theorem cos_poly_eq (c : ℚ) (u : ℝ) (N : ℕ) :
    (Complex.exp (I * ((c : ℝ) * Real.log 2 : ℝ)) *
        ∑ m ∈ range N, (I * (u * Real.log 2 : ℝ)) ^ m / m.factorial).re =
      ∑ m ∈ range N, kap c m * u ^ m := by
  rw [mul_sum, Complex.re_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [taylor_term_eq, ← mul_assoc, Complex.re_mul_ofReal, Complex.mul_re, exp_I_re, exp_I_im,
    toC_re, toC_im]
  unfold kap
  push_cast
  ring

theorem Kball_mem (c : ℚ) (m : ℕ) :
    InB ((2 * Real.log 2 / Real.sqrt 2) * kap c m) (Kball c m) := by
  unfold Kball kap
  refine InB_round (InB_mul primeTwoA_mem (InB_mul (InB_mul (InB_ex _) (InB_pow log_two_mem m))
    (InB_add (InB_mul (cos_mem c) (InB_ex _)) (InB_mul (sin_mem c) (InB_ex _)))))

theorem cos_part (c : ℚ) {u : ℝ} (hu : |u| ≤ 1 / 8) :
    primeTwoCos ((c : ℝ) + u) ≤
      ∑ m ∈ range NT, ((Kball c m).1 : ℝ) * u ^ m +
        ∑ m ∈ range NT, ((Kball c m).2 : ℝ) / 8 ^ m +
        ((Ab.1 + Ab.2) * ((Lb.1 + Lb.2) / 8) ^ NT / NT.factorial : ℚ) := by
  have hA0 : 0 ≤ primeTwoA := primeTwoA_nonneg
  have hL0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h := abs_cos_sub_taylor_le (c : ℝ) u (Real.log 2) NT
  rw [cos_poly_eq] at h
  have hcos : Real.cos (((c : ℝ) + u) * Real.log 2) ≤
      ∑ m ∈ range NT, kap c m * u ^ m + |u * Real.log 2| ^ NT / NT.factorial := by
    linarith [(abs_le.mp h).2]
  have hball := ball_poly_le (N := NT) (fun m => primeTwoA * kap c m) (Kball c) (fun m => by
    unfold primeTwoA; exact Kball_mem c m) hu
  have hAhi : primeTwoA ≤ (Ab.1 : ℝ) + Ab.2 := by unfold primeTwoA; exact InB_le primeTwoA_mem
  have hLhi : Real.log 2 ≤ (Lb.1 : ℝ) + Lb.2 := InB_le log_two_mem
  have htail : |u * Real.log 2| ≤ ((Lb.1 : ℝ) + Lb.2) / 8 := by
    rw [abs_mul, abs_of_nonneg hL0]
    calc |u| * Real.log 2 ≤ (1 / 8) * ((Lb.1 : ℝ) + Lb.2) :=
          mul_le_mul hu hLhi hL0 (by norm_num)
      _ = _ := by ring
  have htail2 : primeTwoA * (|u * Real.log 2| ^ NT / NT.factorial) ≤
      ((Ab.1 : ℝ) + Ab.2) * ((((Lb.1 : ℝ) + Lb.2) / 8) ^ NT / NT.factorial) := by
    apply mul_le_mul hAhi _ (by positivity) (hA0.trans hAhi)
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) htail NT) (by positivity)
  have hmul : primeTwoA * (∑ m ∈ range NT, kap c m * u ^ m) =
      ∑ m ∈ range NT, primeTwoA * kap c m * u ^ m := by
    rw [mul_sum]; exact sum_congr rfl fun m _ => by ring
  unfold primeTwoCos
  have := mul_le_mul_of_nonneg_left hcos hA0
  push_cast
  rw [mul_add, hmul] at this
  have e : ((Ab.1 : ℝ) + Ab.2) * ((((Lb.1 : ℝ) + Lb.2) / 8) ^ NT / NT.factorial) =
      ((Ab.1 : ℝ) + Ab.2) * (((Lb.1 : ℝ) + Lb.2) / 8) ^ NT / NT.factorial := by ring
  rw [e] at htail2
  linarith

/-! ### The logarithm and `1/Q` -/

theorem X_part (c : ℚ) (hx : |xQ c| < 1) {u : ℝ} (hu : |u| ≤ 1 / 8) :
    (logQlo c : ℝ) / 2 + 1 / 2 -
        (∑ n ∈ range NT, (flr (kappaX c * tQ XQ c n) : ℝ) * u ^ n + (rnd : ℝ) +
          (kappaX c : ℝ) * (Eb XQ : ℝ)) ≤
      Real.log ((XQ : ℝ) ^ 2 + (((c : ℝ) + u) / 2) ^ 2) / 2 -
        1 / ((XQ : ℝ) ^ 2 + (((c : ℝ) + u) / 2) ^ 2) / 4 := by
  set Q : ℝ := (XQ : ℝ) ^ 2 + (((c : ℝ) + u) / 2) ^ 2
  have hX : (0 : ℝ) < XQ := by unfold XQ; norm_num
  have hQ : 0 < Q := by positivity
  have hQc : ((Qc c : ℚ) : ℝ) = (XQ : ℝ) ^ 2 + (c : ℝ) ^ 2 / 4 := by unfold Qc; push_cast; ring
  have hQc0 : (0 : ℝ) < Qc c := by rw [hQc]; positivity
  have hlog := log_ge_tangent hQc0 hQ
  have hlo := logQlo_le c hx
  have hR := R_le_exact XQ c (by unfold XQ; norm_num) hu
  have hk0 : (0 : ℝ) ≤ kappaX c := by
    have : (0 : ℚ) ≤ kappaX c := by unfold kappaX Qc XQ; positivity
    exact_mod_cast this
  have hround := round_poly (fun n => kappaX c * tQ XQ c n) hu
  have hscale : (kappaX c : ℝ) * ∑ n ∈ range NT, (tQ XQ c n : ℝ) * u ^ n =
      ∑ n ∈ range NT, ((kappaX c * tQ XQ c n : ℚ) : ℝ) * u ^ n := by
    rw [mul_sum]; exact sum_congr rfl fun n _ => by push_cast; ring
  have hk : (Qc c : ℝ) / Q / 2 + 1 / Q / 4 = (kappaX c : ℝ) * ((XQ : ℝ) / Q) := by
    unfold kappaX; push_cast; field_simp
  have hmul := mul_le_mul_of_nonneg_left hR hk0
  rw [mul_add, hscale] at hmul
  have : Real.log Q / 2 - 1 / Q / 4 ≥ (Real.log (Qc c) + 1 - (Qc c : ℝ) / Q) / 2 - 1 / Q / 4 := by
    linarith
  have e2 : (Real.log (Qc c) + 1 - (Qc c : ℝ) / Q) / 2 - 1 / Q / 4 =
      Real.log (Qc c) / 2 + 1 / 2 - ((Qc c : ℝ) / Q / 2 + 1 / Q / 4) := by ring
  rw [e2, hk] at this
  linarith

/-! ### The constant -/

theorem const_part : (Klo : ℝ) ≤ -Real.log Real.pi - betaTwo 25 := by
  have hL := InB_le log_two_mem
  have hl := InB_le log_five_fourths_mem
  have hA := InB_ge primeTwoA_mem
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h25 : Real.log 25 = 2 * Real.log (5 / 4) + 4 * Real.log 2 := by
    rw [show (25 : ℝ) = (5 / 4) ^ 2 * 2 ^ 4 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]
    push_cast; ring
  have hb : betaTwo 25 = Real.log 25 - Real.log 2 - Real.log Real.pi - 1 / 25 -
      2 * Real.log 2 / Real.sqrt 2 := by
    unfold betaTwo primeTwoA
    rw [Real.log_div (by norm_num) (by positivity), Real.log_mul (by norm_num) hpi.ne']
    ring
  rw [hb, h25]
  unfold Klo
  push_cast
  linarith

/-! ### Assembly -/

theorem errF_cast (c : ℚ) :
    ((errF c : ℚ) : ℝ) = ∑ k ∈ range 81, ((Eb (aK k) + rnd : ℚ) : ℝ) +
      ((kappaX c : ℝ) * (Eb XQ : ℝ) + (rnd : ℝ)) +
      ∑ m ∈ range NT, ((Kball c m).2 : ℝ) / 8 ^ m +
      ((Ab.1 + Ab.2) * ((Lb.1 + Lb.2) / 8) ^ NT / NT.factorial : ℚ) := by
  unfold errF
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
    Rat.cast_natCast, listSum_cast]

theorem lbF_sum (c : ℚ) (u : ℝ) :
    ∑ n ∈ range NT, (lbF c n : ℝ) * u ^ n =
      -∑ k ∈ range 81, ∑ n ∈ range NT, (flr (tQ (aK k) c n) : ℝ) * u ^ n
        - ∑ n ∈ range NT, (flr (kappaX c * tQ XQ c n) : ℝ) * u ^ n
        - ∑ n ∈ range NT, ((Kball c n).1 : ℝ) * u ^ n
        + ((logQlo c : ℝ) / 2 + 1 / 2 + Klo) := by
  have hl : ∀ n, (lbF c n : ℝ) = -∑ k ∈ range 81, (flr (tQ (aK k) c n) : ℝ)
      - (flr (kappaX c * tQ XQ c n) : ℝ) - ((Kball c n).1 : ℝ)
      + (if n = 0 then ((logQlo c : ℝ) / 2 + 1 / 2 + Klo) else 0) := by
    intro n
    unfold lbF
    rw [Rat.cast_add, Rat.cast_sub, Rat.cast_sub, Rat.cast_neg, listSum_cast]
    split_ifs <;> push_cast <;> ring
  simp_rw [hl, add_mul, sub_mul, neg_mul, sum_add_distrib, sum_sub_distrib, sum_neg_distrib,
    sum_mul]
  rw [sum_comm (s := range NT) (t := range 81)]
  have hite : ∑ n ∈ range NT, (if n = 0 then ((logQlo c : ℝ) / 2 + 1 / 2 + Klo) else 0) * u ^ n =
      (logQlo c : ℝ) / 2 + 1 / 2 + Klo := by
    rw [sum_eq_single 0 (fun b _ hb => by simp [hb]) (fun h => absurd (by unfold NT; simp) h)]
    simp
  rw [hite]

/-- **The generic local lower bound for `G_80`.** -/
theorem GM_ge (c : ℚ) (hx : |xQ c| < 1) {u : ℝ} (hu : |u| ≤ 1 / 8) :
    ∑ n ∈ range NT, (lbF c n : ℝ) * u ^ n - errF c ≤ GM 80 ((c : ℝ) + u) := by
  have hR : ∀ k ∈ range 81,
      (aK k : ℝ) / ((aK k : ℝ) ^ 2 + (((c : ℝ) + u) / 2) ^ 2) ≤
        ∑ n ∈ range NT, (flr (tQ (aK k) c n) : ℝ) * u ^ n + ((Eb (aK k) + rnd : ℚ) : ℝ) :=
    fun k _ => R_le (aK k) c (by unfold aK; positivity) hu
  have hRs := sum_le_sum hR
  rw [sum_add_distrib] at hRs
  have hsum : (1 / 4 + ((80 : ℕ) : ℝ)) / ((1 / 4 + ((80 : ℕ) : ℝ)) ^ 2 + (((c : ℝ) + u) / 2) ^ 2) +
      ∑ k ∈ range 80, (1 / 4 + (k : ℝ)) / ((1 / 4 + (k : ℝ)) ^ 2 + (((c : ℝ) + u) / 2) ^ 2) =
      ∑ k ∈ range 81, (aK k : ℝ) / ((aK k : ℝ) ^ 2 + (((c : ℝ) + u) / 2) ^ 2) := by
    rw [show (81 : ℕ) = 80 + 1 from rfl, sum_range_succ (n := 80)]; unfold aK; push_cast; ring
  have hXp := X_part c hx hu
  have hXeq : (1 / 4 + ((80 : ℕ) : ℝ) + 1 / 2) = (XQ : ℝ) := by unfold XQ; push_cast; norm_num
  have hcos := cos_part c hu
  have hK := const_part
  rw [lbF_sum, errF_cast]
  unfold GM
  rw [hXeq]
  linarith

/-! ### Re-centring and the piece check -/

/-- The coefficients of `p(c + u)` in `u`. -/
def shiftQ (p : List ℚ) (c : ℚ) : List ℚ :=
  (List.range p.length).map fun n =>
    ((List.range p.length).map fun k => p.getD k 0 * (k.choose n : ℚ) * c ^ (k - n)).sum

theorem shiftQ_getD (p : List ℚ) (c : ℚ) {n : ℕ} (hn : n < p.length) :
    (shiftQ p c).getD n 0 =
      ((List.range p.length).map fun k => p.getD k 0 * (k.choose n : ℚ) * c ^ (k - n)).sum := by
  unfold shiftQ
  simp [List.getD_eq_getElem?_getD, hn]

theorem evalR_shift (p : List ℚ) (c : ℚ) (u : ℝ) :
    evalR p ((c : ℝ) + u) = ∑ n ∈ range p.length, ((shiftQ p c).getD n 0 : ℝ) * u ^ n := by
  unfold evalR
  have hk : ∀ k ∈ range p.length, (p.getD k 0 : ℝ) * ((c : ℝ) + u) ^ k =
      ∑ n ∈ range p.length, (p.getD k 0 : ℝ) * (k.choose n : ℝ) * (c : ℝ) ^ (k - n) * u ^ n := by
    intro k hk
    rw [add_comm, add_pow, mul_sum]
    have hsub : range (k + 1) ⊆ range p.length := by
      intro x hx; simp only [mem_range] at hx hk ⊢; omega
    rw [← sum_subset hsub]
    · exact sum_congr rfl fun n _ => by ring
    · intro n _ hn
      simp only [mem_range, not_lt] at hn
      rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rw [sum_congr rfl hk, sum_comm]
  refine sum_congr rfl fun n hn => ?_
  rw [shiftQ_getD p c (mem_range.mp hn), listSum_cast, sum_mul]
  exact sum_congr rfl fun k _ => by push_cast; ring

/-- The kernel-checked condition for piece `i` against a coefficient list `p` (ascending in `r`). -/
def checkPieceOf (p : List ℚ) (i : ℕ) : Bool :=
  let c : ℚ := (2 * i + 1) / 8
  let d := shiftQ p c
  (p.length == NT) && decide (|xQ c| < 1) &&
  decide (d.getD 0 0 + ((List.range 12).map fun j => |lbF c (j + 1) - d.getD (j + 1) 0| / 8 ^ (j + 1)).sum
      + errF c ≤ lbF c 0) &&
  decide (((List.range NT).map fun n => |d.getD n 0| / 8 ^ n).sum ≤ 8)

/-- **A checked piece.** On `[i/4, (i+1)/4]` the polynomial `p` lies below `G_80` and has `|p| ≤ 8`. -/
theorem piece_bound (p : List ℚ) (i : ℕ) (h : checkPieceOf p i = true) {r : ℝ}
    (hr : r ∈ Set.Icc ((i : ℝ) / 4) (((i : ℝ) + 1) / 4)) :
    evalR p r ≤ GM 80 r ∧ |evalR p r| ≤ 8 := by
  unfold checkPieceOf at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hlen, hx⟩, hchk⟩, h8⟩ := h
  set c : ℚ := (2 * i + 1) / 8 with hc
  set d := shiftQ p c
  set u : ℝ := r - c
  have hrc : r = (c : ℝ) + u := by simp [u]
  have hu : |u| ≤ 1 / 8 := by
    rw [abs_le]; simp only [u, hc]; push_cast
    constructor <;> linarith [hr.1, hr.2]
  have hev : evalR p r = ∑ n ∈ range NT, (d.getD n 0 : ℝ) * u ^ n := by
    rw [hrc, evalR_shift, hlen]
  have hd12 : ∀ f : ℕ → ℝ, ∑ n ∈ (range NT).erase 0, f n = ∑ j ∈ range 12, f (j + 1) := by
    intro f
    rw [sum_erase_eq_sub (by unfold NT; simp), show NT = 12 + 1 from rfl, sum_range_succ']
    ring
  constructor
  · -- `p ≤ G_80`
    have hpoly := poly_ge_of_abs_le (N := NT) (fun n => (lbF c n : ℝ) - d.getD n 0) hu
      (by unfold NT; norm_num)
    rw [hd12] at hpoly
    have hchk' : ((d.getD 0 0 + ((List.range 12).map fun j =>
        |lbF c (j + 1) - d.getD (j + 1) 0| / 8 ^ (j + 1)).sum + errF c : ℚ) : ℝ) ≤ lbF c 0 := by
      exact_mod_cast hchk
    rw [Rat.cast_add, Rat.cast_add, listSum_cast] at hchk'
    have hcmp : ∑ j ∈ range 12, |((lbF c (j + 1) : ℝ) - d.getD (j + 1) 0)| * (1 / 8 : ℝ) ^ (j + 1) =
        ∑ j ∈ range 12, ((|lbF c (j + 1) - d.getD (j + 1) 0| / 8 ^ (j + 1) : ℚ) : ℝ) :=
      sum_congr rfl fun j _ => by push_cast; rw [one_div_pow, mul_one_div]
    have hsplit : ∑ n ∈ range NT, ((lbF c n : ℝ) - d.getD n 0) * u ^ n =
        ∑ n ∈ range NT, (lbF c n : ℝ) * u ^ n - ∑ n ∈ range NT, (d.getD n 0 : ℝ) * u ^ n := by
      rw [← sum_sub_distrib]; exact sum_congr rfl fun n _ => by ring
    have hG := GM_ge c hx hu
    rw [hev, hrc]
    rw [hsplit, hcmp] at hpoly
    linarith
  · -- `|p| ≤ 8`
    rw [hev]
    have h8' : ((((List.range NT).map fun n => |d.getD n 0| / 8 ^ n).sum : ℚ) : ℝ) ≤ 8 := by
      exact_mod_cast h8
    rw [listSum_cast] at h8'
    refine (abs_sum_le_sum_abs _ _).trans (le_trans (sum_le_sum fun n _ => ?_) h8')
    rw [abs_mul, abs_pow]
    push_cast
    rw [div_eq_mul_one_div, ← one_div_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hu n) (abs_nonneg _)

end GppWindowBPiece

#print axioms GppWindowBPiece.GM_ge
#print axioms GppWindowBPiece.piece_bound
