import GppVerify.RiemannHypothesis.BoxCurvature

/-!
# The event-parabola step

The logic of GPT's event-parabola certificate (bridge, Turbo's audit `033d913`), isolated as a pure
real-variable lemma.  On a prime-power gap `[a, b]` let `f` be the (model) potential, `g = f'`, and suppose
`g' ≥ k > 0` on the gap.  Then `f` lies above its tangent parabola at `a`:

`f t ≥ f a + g a (t − a) + (k/2) (t − a)²`  (`parabola_lower`),

and the parabola's global minimum is `f a − (g a)²/(2k)`, so

`2 k · f a > (g a)²  ⟹  f > 0 on [a, b]`  (`gap_positive`).

This is exactly the certificate's integer test `2·K·Y − max(−D, 0)² > 0` with `K` a lower bound for the curvature
on the gap, `Y = f(a)`, `D = g(a⁺)`.  The lemma is sufficient and not necessary (the parabola's minimiser may lie
past the next event).  The abstract step is about no particular function; the numbers (the values of `F`, `F'`,
`F''` at each event) are inputs.

**Specialisation** (`WnModel_pos_on_gap`).  The box model of `BoxCurvature.lean` with the floor frozen at `n`
(`WnModel c n`, shifted by a constant `c`) has `W'' = 2·curv` on the whole gap and `curv` is monotone on `(0, ∞)`
(`curv_monotoneOn`, since `κ` decreases), so the curvature on `[a, b]` is `≥ 2·curv a`; hence
`(W_n'(a))² < 2·(2 curv a)·(W_n a + c)` and `curv a > 0` give `W_n + c > 0` on `[a, b]`.  `boxModel_eq_WnModel`
identifies `boxModel` with `WnModel 0 n` on `[log n, log(n+1))`.

**Scope.** This is the logic of the certificate for the *defined model*, with `c` the (unspecified) additive
constant; it does **not** evaluate `W_n a` or `W_n'(a)` at any event — no numeric certificate is made here, and no
statement about the true box form (that needs `c = 2∫₀^1 Gcl` from `BoxArchimedean.lean` and the numerics).
Nothing is positivity of the Weil form; ARP, RH, OB-6, UB are OPEN.

No `sorry`, no axiom.
-/

open Set

noncomputable section

namespace GppEventParabola

/-- A function whose derivative has derivative `≥ k` on `(a, b)` lies above its tangent parabola at `a`. -/
theorem parabola_lower {f g h : ℝ → ℝ} {a b k : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x)
    (hgd : ∀ x ∈ Ioo a b, HasDerivAt g (h x) x) (hk : ∀ x ∈ Ioo a b, k ≤ h x)
    {t : ℝ} (ht : t ∈ Icc a b) :
    f a + g a * (t - a) + k / 2 * (t - a) ^ 2 ≤ f t := by
  -- ψ(x) = g x − g a − k (x − a) is monotone on [a, b], ψ a = 0
  have hψc : ContinuousOn (fun x => g x - g a - k * (x - a)) (Icc a b) := by fun_prop
  have hψd : ∀ x ∈ Ioo a b,
      HasDerivAt (fun x => g x - g a - k * (x - a)) (h x - k) x := by
    intro x hx
    have := ((hgd x hx).sub_const (g a)).sub (((hasDerivAt_id x).sub_const a).const_mul k)
    have e : (fun x => g x - g a - k * (x - a)) = (fun x => g x - g a) - fun y => k * (id y - a) := by
      funext y; simp
    rw [e]
    simpa using this
  have hψ : MonotoneOn (fun x => g x - g a - k * (x - a)) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hψc
    · intro x hx
      rw [interior_Icc] at hx
      exact (hψd x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hψd x hx).deriv]
      linarith [hk x hx]
  have hψnn : ∀ x ∈ Icc a b, 0 ≤ g x - g a - k * (x - a) := by
    intro x hx
    have := hψ (left_mem_Icc.mpr hab) hx hx.1
    simpa using this
  -- φ(x) = f x − (f a + g a (x − a) + k/2 (x − a)²) is monotone
  have hφc : ContinuousOn (fun x => f x - (f a + g a * (x - a) + k / 2 * (x - a) ^ 2)) (Icc a b) := by
    fun_prop
  have hφd : ∀ x ∈ Ioo a b, HasDerivAt
      (fun x => f x - (f a + g a * (x - a) + k / 2 * (x - a) ^ 2)) (g x - (g a + k * (x - a))) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => y - a) 1 x := (hasDerivAt_id x).sub_const a
    have h2 : HasDerivAt (fun y : ℝ => f a + g a * (y - a) + k / 2 * (y - a) ^ 2)
        (g a * 1 + k / 2 * (2 * (x - a) * 1)) x := by
      have := ((h1.const_mul (g a)).const_add (f a)).add ((h1.pow 2).const_mul (k / 2))
      refine this.congr_deriv ?_
      norm_num
    have := (hfd x hx).sub h2
    refine this.congr_deriv ?_
    ring
  have hφ : MonotoneOn (fun x => f x - (f a + g a * (x - a) + k / 2 * (x - a) ^ 2)) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hφc
    · intro x hx
      rw [interior_Icc] at hx
      exact (hφd x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hφd x hx).deriv]
      have := hψnn x ⟨hx.1.le, hx.2.le⟩
      linarith
  have := hφ (left_mem_Icc.mpr hab) ht ht.1
  simp at this
  linarith

/-- The minimum of a quadratic `f0 + g0 s + (k/2) s²` (`k > 0`) is `f0 − g0²/(2k)`. -/
theorem quadratic_ge {f0 g0 k : ℝ} (hk : 0 < k) (s : ℝ) :
    f0 - g0 ^ 2 / (2 * k) ≤ f0 + g0 * s + k / 2 * s ^ 2 := by
  have : 0 ≤ k / 2 * (s + g0 / k) ^ 2 := by positivity
  have e : k / 2 * (s + g0 / k) ^ 2 = k / 2 * s ^ 2 + g0 * s + g0 ^ 2 / (2 * k) := by
    field_simp; ring
  linarith

/-- **The event-parabola step.** If the curvature is `≥ k > 0` on the gap and `2 k f(a) > (g a)²`, then
`f > 0` on the whole gap `[a, b]`. -/
theorem gap_positive {f g h : ℝ → ℝ} {a b k : ℝ} (hab : a ≤ b) (hk0 : 0 < k)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x)
    (hgd : ∀ x ∈ Ioo a b, HasDerivAt g (h x) x) (hk : ∀ x ∈ Ioo a b, k ≤ h x)
    (hcert : g a ^ 2 < 2 * k * f a) {t : ℝ} (ht : t ∈ Icc a b) : 0 < f t := by
  have h1 := parabola_lower hab hf hg hfd hgd hk ht
  have h2 := quadratic_ge (f0 := f a) (g0 := g a) hk0 (t - a)
  have h3 : 0 < f a - g a ^ 2 / (2 * k) := by
    have : g a ^ 2 / (2 * k) < f a := by
      rw [div_lt_iff₀ (by positivity)]; linarith
    linarith
  linarith

/-! ### Specialisation to the box model on a prime-power gap -/

open GppBoxCurvature GppPlastic
open scoped ArithmeticFunction.vonMangoldt

/-- The curvature `curv(t) = e^{t/2} − κ(t)` is monotone on `(0, ∞)`: `κ` decreases, `e^{t/2}` increases. -/
theorem curv_monotoneOn : MonotoneOn curv (Ioi 0) := by
  intro s hs t ht hst
  simp only [mem_Ioi] at hs ht
  unfold curv kappaGamma
  have h1 : Real.exp (s / 2) ≤ Real.exp (t / 2) := Real.exp_le_exp.mpr (by linarith)
  have hs' := one_sub_exp_pos hs
  have ht' := one_sub_exp_pos ht
  have hnum : Real.exp (-5 * t / 2) ≤ Real.exp (-5 * s / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hden : 1 - Real.exp (-2 * s) ≤ 1 - Real.exp (-2 * t) := by
    have := Real.exp_le_exp.mpr (show -2 * t ≤ -2 * s by linarith)
    linarith
  have : Real.exp (-5 * t / 2) / (1 - Real.exp (-2 * t)) ≤
      Real.exp (-5 * s / 2) / (1 - Real.exp (-2 * s)) :=
    div_le_div₀ (Real.exp_pos _).le hnum hs' hden
  linarith

/-- The prime part with the floor frozen at `n`: `−2 Σ_{m ≤ n} Λ(m) m^{−1/2} (L − log m)`. -/
def primeAff (n : ℕ) (L : ℝ) : ℝ :=
  -2 * ∑ m ∈ Finset.Icc 1 n, (Λ m : ℝ) / Real.sqrt m * (L - Real.log m)

/-- The frozen-floor box model, shifted by a constant `c`. -/
def WnModel (c : ℝ) (n : ℕ) (L : ℝ) : ℝ := smoothBox L + primeAff n L + c

theorem hasDerivAt_primeAff (n : ℕ) (y : ℝ) : HasDerivAt (primeAff n) (primeSlope n) y := by
  have hs : HasDerivAt (fun z : ℝ => ∑ m ∈ Finset.Icc 1 n, (Λ m : ℝ) / Real.sqrt m * (z - Real.log m))
      (∑ m ∈ Finset.Icc 1 n, (Λ m : ℝ) / Real.sqrt m * 1) y :=
    HasDerivAt.fun_sum fun m _ => ((hasDerivAt_id y).sub_const (Real.log m)).const_mul _
  have := hs.const_mul (-2)
  refine this.congr_deriv ?_
  simp [primeSlope]

theorem hasDerivAt_WnModel {c : ℝ} (n : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (WnModel c n) (boxSlope n y) y := by
  have := ((hasDerivAt_smoothBox hy).add (hasDerivAt_primeAff n y)).add_const c
  unfold boxSlope
  refine this.congr_deriv ?_
  ring

theorem hasDerivAt_boxSlope' (n : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (boxSlope n) (2 * curv y) y := hasDerivAt_boxSlope hy n

theorem continuousOn_boxSlope (n : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (boxSlope n) (Icc a b) := fun _ hy =>
  (hasDerivAt_boxSlope' n (lt_of_lt_of_le ha hy.1)).continuousAt.continuousWithinAt

theorem continuousOn_WnModel (c : ℝ) (n : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (WnModel c n) (Icc a b) := fun _ hy =>
  (hasDerivAt_WnModel n (lt_of_lt_of_le ha hy.1)).continuousAt.continuousWithinAt

/-- **Event-parabola certificate for the box model on a gap.**  On `[a, b] ⊂ (0, ∞)`, the frozen-floor model
`W_n + c` has curvature `≥ 2·curv(a)`; if `(W_n'(a))² < 2·(2 curv a)·(W_n a + c)` then `W_n + c > 0` on
`[a, b]`. -/
theorem WnModel_pos_on_gap {c : ℝ} {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hcurv : 0 < curv a)
    (hcert : boxSlope n a ^ 2 < 2 * (2 * curv a) * WnModel c n a) {t : ℝ} (ht : t ∈ Icc a b) :
    0 < WnModel c n t := by
  refine gap_positive (f := WnModel c n) (g := boxSlope n) (h := fun y => 2 * curv y)
    (k := 2 * curv a) hab (by linarith) (continuousOn_WnModel c n ha)
    (continuousOn_boxSlope n ha) ?_ ?_ ?_ hcert ht
  · intro x hx; exact hasDerivAt_WnModel n (ha.trans hx.1)
  · intro x hx; exact hasDerivAt_boxSlope' n (ha.trans hx.1)
  · intro x hx
    have := curv_monotoneOn (mem_Ioi.mpr ha) (mem_Ioi.mpr (ha.trans hx.1)) hx.1.le
    linarith

/-- The frozen-floor model agrees with `boxModel` on `[log n, log (n+1))`, where `⌊e^L⌋ = n`. -/
theorem boxModel_eq_WnModel {n : ℕ} {L : ℝ} (hn : 1 ≤ n) (h1 : Real.log n ≤ L)
    (h2 : L < Real.log (n + 1)) : boxModel L = WnModel 0 n L := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hfl : ⌊Real.exp L⌋₊ = n := by
    rw [Nat.floor_eq_iff (Real.exp_pos L).le]
    constructor
    · calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hn0).symm
        _ ≤ Real.exp L := Real.exp_le_exp.mpr h1
    · calc Real.exp L < Real.exp (Real.log (n + 1)) := Real.exp_lt_exp.mpr h2
        _ = n + 1 := Real.exp_log (by positivity)
  simp [boxModel, WnModel, primeBox, primeAff, hfl]

end GppEventParabola

#print axioms GppEventParabola.gap_positive
#print axioms GppEventParabola.WnModel_pos_on_gap
#print axioms GppEventParabola.boxModel_eq_WnModel
