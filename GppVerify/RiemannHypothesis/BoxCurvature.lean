import GppVerify.RiemannHypothesis.ReferenceMultiplierZero
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# The curvature of the box Weil form between prime powers

For the box `f_L = 1_{[−L/2, L/2]}` (autocorrelation `A_L(t) = (L − |t|)₊`) the Weil form is
`pole + archimedean + prime`:

* pole: `32 sinh²(L/4) = 16 (cosh(L/2) − 1)`;
* archimedean: `C∞ L + 2 ∫₀^∞ w(t) min(t, L) dt`, `w(t) = e^{−t/2}/(1 − e^{−2t})`;
* prime: `−2 Σ_{2 ≤ n ≤ e^L} Λ(n) n^{−1/2} (L − log n)`.

GPT's filing (numerically confirmed and audited by Turbo, bridge `fe9d9b5` → `f7f6242`) says that between
prime powers its second derivative is `2(e^{L/2} − κ(L))`, `κ(t) = e^{−5t/2}/(1 − e^{−2t})`. This file proves
the calculus behind that, in two steps (this is the first):

* `Gcl t = ½ log((1+u)/(1−u)) + arctan u`, `u = e^{−t/2}`, is the closed form of `∫_t^∞ w`, with
  `Gcl' = −w` (`hasDerivAt_Gcl`);
* the **smooth model** `smoothBox L = 16(cosh(L/2) − 1) + C∞ L + 2 ∫₁^L Gcl` has second derivative
  `4cosh(L/2) − 2w(L) = 2·curv(L)` (`smoothBox_second`), where `curv = e^{t/2} − κ` is the curvature of
  `PlasticConstant.lean`;
* the **prime part** is locally a polynomial of degree 1 on every gap `(log n₀, log(n₀+1))`
  (`primeBox_eq_on_gap`), so contributes nothing: `boxModel_second` — the second derivative of
  `smoothBox + primeBox` on a gap is `2·curv(L)`.

**Scope.** `smoothBox` uses the lower limit `1` in `∫₁^L Gcl`, so it differs from the true box form's
archimedean term by an additive **constant** (`∫_0^1` of the singular-at-`0` part and the by-parts boundary
terms) which the second derivative does not see; identifying the box form's `∫₀^∞ w·min(t, L)` with
`C∞ L + 2∫₀^L Gcl + const` (integration by parts at the singular endpoint `0`) is **not** done here, and
the box form is not identified with the in-tree `weilForm` (the box is not `C^∞`). So this proves the
curvature of the *model*, and says exactly how it matches the filing; nothing about positivity.

No `sorry`, no axiom.
-/

open Real Set MeasureTheory intervalIntegral
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GppBoxCurvature

open GppPlastic

/-- The archimedean kernel `w(t) = e^{−t/2}/(1 − e^{−2t})`. -/
def wk (t : ℝ) : ℝ := Real.exp (-t / 2) / (1 - Real.exp (-2 * t))

/-- Closed form of `∫_t^∞ w`: `½ log((1+u)/(1−u)) + arctan u`, `u = e^{−t/2}`. -/
def Gcl (t : ℝ) : ℝ :=
  (1 / 2) * Real.log ((1 + Real.exp (-t / 2)) / (1 - Real.exp (-t / 2))) +
    Real.arctan (Real.exp (-t / 2))

theorem exp_neg_half_lt_one {t : ℝ} (ht : 0 < t) : Real.exp (-t / 2) < 1 := by
  have := Real.exp_lt_exp.mpr (show -t / 2 < 0 by linarith)
  simpa using this

/-- `w(t) = u/(1 − u⁴)` with `u = e^{−t/2}`. -/
theorem wk_eq (t : ℝ) : wk t = Real.exp (-t / 2) / (1 - Real.exp (-t / 2) ^ 4) := by
  unfold wk
  congr 2
  rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

theorem hasDerivAt_Gcl {t : ℝ} (ht : 0 < t) : HasDerivAt Gcl (-wk t) t := by
  have hu1 : Real.exp (-t / 2) < 1 := exp_neg_half_lt_one ht
  have hu0 : 0 < Real.exp (-t / 2) := Real.exp_pos _
  obtain ⟨u, hu⟩ : ∃ u, u = Real.exp (-t / 2) := ⟨_, rfl⟩
  rw [← hu] at hu1 hu0
  have h0 : HasDerivAt (fun s : ℝ => -s / 2) (-1 / 2) t := by
    simpa using ((hasDerivAt_id t).neg.div_const 2)
  have hdu : HasDerivAt (fun s : ℝ => Real.exp (-s / 2)) (-(1 / 2) * u) t := by
    have := h0.exp
    convert this using 1
    rw [hu]; ring
  have h2 : (1 - Real.exp (-t / 2)) ≠ 0 := by rw [← hu]; linarith
  have hq : HasDerivAt (fun s : ℝ => (1 + Real.exp (-s / 2)) / (1 - Real.exp (-s / 2)))
      (((-(1 / 2) * u) * (1 - Real.exp (-t / 2)) - (1 + Real.exp (-t / 2)) * (-(-(1 / 2) * u))) /
        (1 - Real.exp (-t / 2)) ^ 2) t :=
    (hdu.const_add 1).div (hdu.const_sub 1) h2
  have hpos : 0 < (1 + Real.exp (-t / 2)) / (1 - Real.exp (-t / 2)) :=
    div_pos (by rw [← hu]; linarith) (by rw [← hu]; linarith)
  have hlog := hq.log hpos.ne'
  have harc := hdu.arctan
  have key : HasDerivAt Gcl _ t := (hlog.const_mul (1 / 2)).add harc
  refine key.congr_deriv ?_
  rw [wk_eq, ← hu]
  have h1 : (1 + u) ≠ 0 := by linarith
  have h2' : (1 - u) ≠ 0 := by linarith
  have h4 : (1 + u ^ 2) ≠ 0 := by positivity
  have h3 : 1 - u ^ 4 = (1 - u) * (1 + u) * (1 + u ^ 2) := by ring
  rw [h3]
  field_simp
  ring

theorem continuousOn_Gcl : ContinuousOn Gcl (Ioi 0) := by
  intro t ht
  exact (hasDerivAt_Gcl ht).continuousAt.continuousWithinAt

/-- The smooth model of the box form (pole + archimedean), up to an additive constant. -/
def smoothBox (L : ℝ) : ℝ :=
  16 * (Real.cosh (L / 2) - 1) + GppArchimedeanFloor.archimedeanFloor * L +
    2 * ∫ t in (1 : ℝ)..L, Gcl t

theorem hasDerivAt_smoothBox {L : ℝ} (hL : 0 < L) :
    HasDerivAt smoothBox
      (8 * Real.sinh (L / 2) + GppArchimedeanFloor.archimedeanFloor + 2 * Gcl L) L := by
  have hint : IntervalIntegrable Gcl volume 1 L := by
    apply ContinuousOn.intervalIntegrable
    refine continuousOn_Gcl.mono ?_
    intro x hx
    exact (lt_min one_pos hL).trans_le hx.1
  have hFTC : HasDerivAt (fun L => ∫ t in (1 : ℝ)..L, Gcl t) (Gcl L) L :=
    intervalIntegral.integral_hasDerivAt_right hint
      (continuousOn_Gcl.stronglyMeasurableAtFilter isOpen_Ioi L hL)
      (hasDerivAt_Gcl hL).continuousAt
  have hc : HasDerivAt (fun y : ℝ => Real.cosh (y / 2)) (Real.sinh (L / 2) * (1 / 2)) L := by
    have := ((hasDerivAt_id L).div_const 2).cosh
    simpa using this
  have := (((hc.sub_const 1).const_mul 16).add
    ((hasDerivAt_id L).const_mul GppArchimedeanFloor.archimedeanFloor)).add (hFTC.const_mul 2)
  refine this.congr_deriv ?_
  simp; ring

/-- `w(L) = e^{−L/2} + κ(L)`. -/
theorem wk_eq_add {L : ℝ} (hL : 0 < L) : wk L = Real.exp (-L / 2) + kappaGamma L := by
  have hx : 1 - Real.exp (-2 * L) ≠ 0 := (one_sub_exp_pos hL).ne'
  have e1 : Real.exp (-5 * L / 2) = Real.exp (-L / 2) * Real.exp (-2 * L) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [wk, kappaGamma, e1]
  generalize Real.exp (-L / 2) = a at *
  generalize Real.exp (-2 * L) = X at *
  field_simp
  ring

/-- The explicit second-derivative algebra: `4 cosh(L/2) − 2 w(L) = 2 (e^{L/2} − κ(L))`. -/
theorem second_algebra {L : ℝ} (hL : 0 < L) :
    4 * Real.cosh (L / 2) - 2 * wk L = 2 * curv L := by
  have e3 : Real.exp (-(L / 2)) = Real.exp (-L / 2) := by congr 1; ring
  rw [Real.cosh_eq, wk_eq_add hL, curv, e3]
  linarith

/-- Sum of the prime-power slopes: `−2 Σ_{n ≤ N} Λ(n)/√n`. -/
def primeSlope (N : ℕ) : ℝ := -2 * ∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ) / Real.sqrt n

/-- The prime part of the box form: `−2 Σ_{n ≤ e^L} Λ(n) n^{−1/2} (L − log n)`. -/
def primeBox (L : ℝ) : ℝ :=
  -2 * ∑ n ∈ Finset.Icc 1 ⌊Real.exp L⌋₊, (Λ n : ℝ) / Real.sqrt n * (L - Real.log n)

/-- The model of the box Weil form: smooth (pole + archimedean) part plus prime part. -/
def boxModel (L : ℝ) : ℝ := smoothBox L + primeBox L

/-- First derivative of the model on a prime-power gap with `⌊e^L⌋ = N`. -/
def boxSlope (N : ℕ) (y : ℝ) : ℝ :=
  8 * Real.sinh (y / 2) + GppArchimedeanFloor.archimedeanFloor + 2 * Gcl y + primeSlope N

theorem floor_eventually {L : ℝ} (hn : ∀ m : ℕ, Real.exp L ≠ m) :
    ∀ᶠ y in nhds L, ⌊Real.exp y⌋₊ = ⌊Real.exp L⌋₊ := by
  have h0 : 0 ≤ Real.exp L := (Real.exp_pos L).le
  have hle : ((⌊Real.exp L⌋₊ : ℕ) : ℝ) ≤ Real.exp L := Nat.floor_le h0
  have hlt : ((⌊Real.exp L⌋₊ : ℕ) : ℝ) < Real.exp L := lt_of_le_of_ne hle (fun h => hn _ h.symm)
  have hup : Real.exp L < ((⌊Real.exp L⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmem : Ioo (((⌊Real.exp L⌋₊ : ℕ) : ℝ)) (((⌊Real.exp L⌋₊ : ℕ) : ℝ) + 1) ∈ nhds (Real.exp L) :=
    Ioo_mem_nhds hlt hup
  filter_upwards [Real.continuous_exp.continuousAt.eventually_mem hmem] with y hy
  rw [Nat.floor_eq_iff (Real.exp_pos y).le]
  exact ⟨hy.1.le, hy.2⟩

theorem hasDerivAt_primeBox {L : ℝ} (hn : ∀ m : ℕ, Real.exp L ≠ m) :
    ∀ᶠ y in nhds L, HasDerivAt primeBox (primeSlope ⌊Real.exp L⌋₊) y := by
  filter_upwards [(floor_eventually hn).eventually_nhds] with y hy
  set N := ⌊Real.exp L⌋₊ with hN
  have hg : HasDerivAt (fun z : ℝ => -2 * ∑ n ∈ Finset.Icc 1 N,
      (Λ n : ℝ) / Real.sqrt n * (z - Real.log n)) (primeSlope N) y := by
    have hs : HasDerivAt (fun z : ℝ => ∑ n ∈ Finset.Icc 1 N,
        (Λ n : ℝ) / Real.sqrt n * (z - Real.log n))
        (∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ) / Real.sqrt n * 1) y :=
      HasDerivAt.fun_sum fun n _ => ((hasDerivAt_id y).sub_const (Real.log n)).const_mul _
    have := hs.const_mul (-2)
    refine this.congr_deriv ?_
    simp [primeSlope]
  refine hg.congr_of_eventuallyEq ?_
  filter_upwards [hy] with z hz
  simp only [primeBox, hz]

theorem hasDerivAt_boxSlope {L : ℝ} (hL : 0 < L) (N : ℕ) :
    HasDerivAt (boxSlope N) (2 * curv L) L := by
  have h1 : HasDerivAt (fun y : ℝ => Real.sinh (y / 2)) (Real.cosh (L / 2) * (1 / 2)) L :=
    ((hasDerivAt_id L).div_const 2).sinh
  have hG := hasDerivAt_Gcl hL
  have := (((h1.const_mul 8).add_const GppArchimedeanFloor.archimedeanFloor).add
    (hG.const_mul 2)).add_const (primeSlope N)
  unfold boxSlope
  refine this.congr_deriv ?_
  rw [← second_algebra hL]
  ring

/-- **Box-form curvature.** On every prime-power gap (`e^L` not an integer, `L > 0`) the model
`smoothBox + primeBox` is differentiable near `L` with derivative `boxSlope ⌊e^L⌋`, and that derivative
has derivative `2 (e^{L/2} − κ(L))` at `L`. -/
theorem boxModel_second {L : ℝ} (hL : 0 < L) (hn : ∀ m : ℕ, Real.exp L ≠ m) :
    (∀ᶠ y in nhds L, HasDerivAt boxModel (boxSlope ⌊Real.exp L⌋₊ y) y) ∧
      HasDerivAt (boxSlope ⌊Real.exp L⌋₊) (2 * curv L) L := by
  refine ⟨?_, hasDerivAt_boxSlope hL _⟩
  filter_upwards [hasDerivAt_primeBox hn, Ioi_mem_nhds hL] with y hy hy0
  have := (hasDerivAt_smoothBox hy0).add hy
  unfold boxModel boxSlope
  refine this.congr_deriv ?_
  ring

end GppBoxCurvature
