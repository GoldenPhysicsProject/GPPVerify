import GppVerify.RiemannHypothesis.VarianceSchur

/-!
# The plastic constant as the curvature crossover of the box potential

For the box form `W(f_L)`, `f_L = 1_{[−L/2, L/2]}`, GPT's filing (relayed by Daniel; numerically confirmed and
audited PASS by Turbo, bridge `fe9d9b5` → `f7f6242`) has, between prime-power events,

`W(f_L)'' = 2 (e^{L/2} − κ(L))`,   `κ(t) = e^{−5t/2} / (1 − e^{−2t})`.

This file proves the elementary analysis of the smooth curvature `c(t) = e^{t/2} − κ(t)` on `t > 0`:

* `curv_pos_iff`, `curv_neg_iff`, `curv_eq_zero_iff`: for `t > 0`, the sign of `c(t)` is the sign of
  `g(t) = e^{3t} − e^{t} − 1`.
* `g` is strictly increasing on `[0, ∞)` with `g(0) = −1 < 0`, hence has a **unique** positive root `t*`, and
  `r = e^{t*}` satisfies the plastic cubic `r³ = r + 1` with `1.3247 < r < 1.3248`.
* `c < 0` on `(0, t*)`, `c > 0` on `(t*, ∞)`.
* `t* < log 2`: the curvature is already positive at the first prime power, so **every** prime-power event
  `log n` (`n ≥ 2`) lies in the convex regime.

**Scope.** Only this real-variable analysis of the curvature function. The identity
`W(f_L)'' = 2(e^{L/2} − κ(L))` itself (closed form of the box form, differentiation of the archimedean integral)
is **not** here, nor is Suzuki's criterion, nor any positivity statement.

No `sorry`, no axiom.
-/

open Real

noncomputable section

namespace GppPlastic

/-- The lowest-gamma-mode term `κ(t) = e^{−5t/2}/(1 − e^{−2t})`. -/
def kappaGamma (t : ℝ) : ℝ := Real.exp (-5 * t / 2) / (1 - Real.exp (-2 * t))

/-- The smooth curvature `c(t) = e^{t/2} − κ(t)`. -/
def curv (t : ℝ) : ℝ := Real.exp (t / 2) - kappaGamma t

/-- The cubic form `g(t) = e^{3t} − e^{t} − 1`. -/
def gcub (t : ℝ) : ℝ := Real.exp (3 * t) - Real.exp t - 1

theorem one_sub_exp_pos {t : ℝ} (ht : 0 < t) : 0 < 1 - Real.exp (-2 * t) := by
  have : Real.exp (-2 * t) < 1 := by
    have := Real.exp_lt_exp.mpr (show -2 * t < 0 by linarith)
    simpa using this
  linarith

/-- For `t > 0`: `c(t) = e^{−5t/2} · g(t) / (1 − e^{−2t})`. -/
theorem curv_eq {t : ℝ} (ht : 0 < t) :
    curv t = Real.exp (-5 * t / 2) * gcub t / (1 - Real.exp (-2 * t)) := by
  have hd := one_sub_exp_pos ht
  unfold curv kappaGamma gcub
  rw [eq_div_iff hd.ne', sub_mul, div_mul_cancel₀ _ hd.ne']
  have e1 : Real.exp (t / 2) * Real.exp (-5 * t / 2) = Real.exp (-2 * t) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-5 * t / 2) * Real.exp (3 * t) = Real.exp (t / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have e3 : Real.exp (-5 * t / 2) * Real.exp t = Real.exp (-3 * t / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  -- expand and compare
  have e4 : Real.exp (-2 * t) = Real.exp (-5 * t / 2) * Real.exp (t / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have e5 : Real.exp (-3 * t / 2) = Real.exp (-5 * t / 2) * Real.exp t := e3.symm
  have e6 : Real.exp (t / 2) = Real.exp (-5 * t / 2) * Real.exp (3 * t) := e2.symm
  have e7 : Real.exp (t / 2) * Real.exp (-2 * t) = Real.exp (-5 * t / 2) * Real.exp t := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  nlinarith [e4, e5, e6, e7, e1]

theorem curv_pos_iff {t : ℝ} (ht : 0 < t) : 0 < curv t ↔ 0 < gcub t := by
  rw [curv_eq ht]
  have hd := one_sub_exp_pos ht
  have he := Real.exp_pos (-5 * t / 2)
  constructor
  · intro h
    by_contra hg
    push Not at hg
    have : Real.exp (-5 * t / 2) * gcub t / (1 - Real.exp (-2 * t)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos he.le hg) hd.le
    linarith
  · intro h
    exact div_pos (mul_pos he h) hd

theorem curv_neg_iff {t : ℝ} (ht : 0 < t) : curv t < 0 ↔ gcub t < 0 := by
  rw [curv_eq ht]
  have hd := one_sub_exp_pos ht
  have he := Real.exp_pos (-5 * t / 2)
  constructor
  · intro h
    by_contra hg
    push Not at hg
    have : 0 ≤ Real.exp (-5 * t / 2) * gcub t / (1 - Real.exp (-2 * t)) :=
      div_nonneg (mul_nonneg he.le hg) hd.le
    linarith
  · intro h
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg he h) hd

theorem curv_eq_zero_iff {t : ℝ} (ht : 0 < t) : curv t = 0 ↔ gcub t = 0 := by
  rw [curv_eq ht]
  have hd := one_sub_exp_pos ht
  have he := Real.exp_pos (-5 * t / 2)
  rw [div_eq_zero_iff, mul_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · exact absurd h he.ne'
    · exact h
    · exact absurd h hd.ne'
  · intro h; exact Or.inl (Or.inr h)

/-- `g` is strictly increasing on `[0, ∞)`. -/
theorem gcub_strictMonoOn : StrictMonoOn gcub (Set.Ici 0) := by
  intro s hs t ht hst
  have hs0 : (0 : ℝ) ≤ s := hs
  have ht0 : (0 : ℝ) ≤ t := ht
  unfold gcub
  have h1 : Real.exp s < Real.exp t := Real.exp_lt_exp.mpr hst
  have e3 : Real.exp (3 * t) - Real.exp (3 * s) =
      (Real.exp t - Real.exp s) * (Real.exp t ^ 2 + Real.exp t * Real.exp s + Real.exp s ^ 2) := by
    rw [show Real.exp (3 * t) = Real.exp t ^ 3 by rw [← Real.exp_nat_mul]; norm_num,
        show Real.exp (3 * s) = Real.exp s ^ 3 by rw [← Real.exp_nat_mul]; norm_num]
    ring
  have hs1 : 1 ≤ Real.exp s := Real.one_le_exp hs0
  have h3 : 3 ≤ Real.exp t ^ 2 + Real.exp t * Real.exp s + Real.exp s ^ 2 := by
    have : 1 ≤ Real.exp t := hs1.trans h1.le
    nlinarith
  nlinarith [mul_pos (sub_pos.mpr h1) (by linarith : (0 : ℝ) < 3)]

theorem gcub_zero : gcub 0 = -1 := by simp [gcub]

theorem gcub_continuous : Continuous gcub := by unfold gcub; fun_prop

/-- **The unique positive root `t*` of `e^{3t} − e^t − 1`.** -/
theorem exists_unique_root : ∃! t : ℝ, 0 < t ∧ gcub t = 0 := by
  have hpos : 0 < gcub 1 := by
    unfold gcub
    have : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9; linarith
    have h3 : Real.exp (3 * 1) = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h3]
    have he : 2 < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    nlinarith [mul_pos (sub_pos.mpr he) (by positivity : (0 : ℝ) < Real.exp 1 ^ 2 + 2 * Real.exp 1 + 3)]
  obtain ⟨t, ht, hz⟩ := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1)
    gcub_continuous.continuousOn (by rw [gcub_zero]; exact ⟨by norm_num, hpos⟩ : (0 : ℝ) ∈
      Set.Ioo (gcub 0) (gcub 1))
  refine ⟨t, ⟨ht.1, hz⟩, ?_⟩
  rintro u ⟨hu, hgu⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := gcub_strictMonoOn (Set.mem_Ici.mpr hu.le) (Set.mem_Ici.mpr ht.1.le) h
    rw [hgu, hz] at this; exact lt_irrefl _ this
  · have := gcub_strictMonoOn (Set.mem_Ici.mpr ht.1.le) (Set.mem_Ici.mpr hu.le) h
    rw [hgu, hz] at this; exact lt_irrefl _ this

/-- The crossover point `t*`. -/
def tStar : ℝ := Classical.choose exists_unique_root.exists

theorem tStar_pos : 0 < tStar := (Classical.choose_spec exists_unique_root.exists).1
theorem gcub_tStar : gcub tStar = 0 := (Classical.choose_spec exists_unique_root.exists).2

/-- **Sign pattern of the smooth curvature.** -/
theorem curv_neg_of_lt {t : ℝ} (ht : 0 < t) (h : t < tStar) : curv t < 0 := by
  rw [curv_neg_iff ht]
  have := gcub_strictMonoOn (Set.mem_Ici.mpr ht.le) (Set.mem_Ici.mpr tStar_pos.le) h
  rwa [gcub_tStar] at this

theorem curv_pos_of_gt {t : ℝ} (h : tStar < t) : 0 < curv t := by
  have ht : 0 < t := tStar_pos.trans h
  rw [curv_pos_iff ht]
  have := gcub_strictMonoOn (Set.mem_Ici.mpr tStar_pos.le) (Set.mem_Ici.mpr ht.le) h
  rwa [gcub_tStar] at this

theorem curv_tStar : curv tStar = 0 := (curv_eq_zero_iff tStar_pos).mpr gcub_tStar

/-- **`t* < log 2`**: the curvature is positive at every prime power. -/
theorem tStar_lt_log_two : tStar < Real.log 2 := by
  by_contra h
  push Not at h
  have h2 : Real.log 2 > 0 := Real.log_pos (by norm_num)
  have hm : gcub (Real.log 2) ≤ gcub tStar :=
    gcub_strictMonoOn.monotoneOn (Set.mem_Ici.mpr h2.le) (Set.mem_Ici.mpr tStar_pos.le) h
  have : gcub (Real.log 2) = 5 := by
    unfold gcub
    rw [show 3 * Real.log 2 = Real.log 8 by rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num,
      Real.exp_log (by norm_num), Real.exp_log (by norm_num)]
    norm_num
  rw [gcub_tStar] at hm
  linarith

/-- Every prime-power event `log n`, `n ≥ 2`, lies in the convex regime. -/
theorem curv_pos_at_event {n : ℕ} (hn : 2 ≤ n) : 0 < curv (Real.log n) := by
  have : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  exact curv_pos_of_gt (tStar_lt_log_two.trans_le this)

/-- **The plastic constant:** `r = e^{t*}` satisfies `r³ = r + 1`. -/
theorem plastic_cubic : Real.exp tStar ^ 3 = Real.exp tStar + 1 := by
  have h := gcub_tStar
  unfold gcub at h
  have : Real.exp (3 * tStar) = Real.exp tStar ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  linarith

/-- `1.3247 < r < 1.3248`. -/
theorem plastic_bounds : (1.3247 : ℝ) < Real.exp tStar ∧ Real.exp tStar < 1.3248 := by
  have hr1 : 1 < Real.exp tStar := by
    have := Real.exp_lt_exp.mpr tStar_pos
    simpa using this
  have hc := plastic_cubic
  set r := Real.exp tStar with hr
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (r - 1.3247), sq_nonneg r, mul_pos (by linarith : (0:ℝ) < r) (by linarith : (0:ℝ) < r)]
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (r - 1.3248), sq_nonneg r, mul_pos (by linarith : (0:ℝ) < r) (by linarith : (0:ℝ) < r)]

end GppPlastic

#print axioms GppPlastic.curv_pos_of_gt
#print axioms GppPlastic.tStar_lt_log_two
#print axioms GppPlastic.plastic_bounds
