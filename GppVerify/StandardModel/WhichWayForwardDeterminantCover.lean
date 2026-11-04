import Mathlib.Tactic

/-!
# *Which Way Is Forward?*: the determinant cover — the meridian loop and its deck sign

Source: Daniel Toupin, *Which Way Is Forward?* (v26), the determinant-cover
discussion of §"three covers", and its check script `verify_wwif.py`,
function `verify_determinant_cover`. The algebraic half of that check
(`det (L A Rᵀ) = det A`) is on main in `WhichWayForwardV26Gaps`; this module
adds the topological content the script verifies numerically:

* the meridian loop `γ(t) = ρ · e^{2πit}` (`ρ > 0`) is a loop: `γ(0) = γ(1)`;
* it has the explicit square-root lift `ℓ(t) = √ρ · e^{πit}`, with
  `ℓ(t)² = γ(t)` for all `t` and `ℓ(1) = -ℓ(0)`;
* **every** continuous square root `f` of `γ` on `[0, 1]` satisfies
  `f(1) = -f(0)`. In particular no continuous square root of the meridian
  loop is periodic: the loop represents the nontrivial class of the double
  cover, and analytic continuation of its square root around it picks up
  the deck sign `-1`.

Scope: this is the deck-sign statement the paper uses. It is proved by an
intermediate-value argument on `f / ℓ`, with no winding-number machinery;
the analytic winding number of `γ` in Mathlib's sense is not separately
asserted.
-/

namespace GppWhichWayForwardDetCover

open Complex
open scoped Real

/-- The meridian loop, of radius `ρ`, traversed once counterclockwise. -/
noncomputable def meridian (ρ : ℝ) (t : ℝ) : ℂ := (ρ : ℂ) * exp (2 * π * I * (t : ℂ))

/-- The explicit square-root lift of the meridian loop. -/
noncomputable def sqrtLift (ρ : ℝ) (t : ℝ) : ℂ := (Real.sqrt ρ : ℂ) * exp (π * I * (t : ℂ))

theorem meridian_zero (ρ : ℝ) : meridian ρ 0 = (ρ : ℂ) := by
  simp [meridian]

theorem meridian_one (ρ : ℝ) : meridian ρ 1 = (ρ : ℂ) := by
  simp [meridian, Complex.exp_two_pi_mul_I]

/-- The meridian is a loop. -/
theorem meridian_loop (ρ : ℝ) : meridian ρ 0 = meridian ρ 1 := by
  rw [meridian_zero, meridian_one]

theorem meridian_ne_zero (hρ : ρ ≠ 0) (t : ℝ) : meridian ρ t ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr hρ) (Complex.exp_ne_zero _)

theorem sqrtLift_ne_zero (hρ : 0 < ρ) (t : ℝ) : sqrtLift ρ t ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hρ).ne')
    (Complex.exp_ne_zero _)

/-- The lift squares to the loop, pointwise. -/
theorem sqrtLift_sq (hρ : 0 ≤ ρ) (t : ℝ) : (sqrtLift ρ t) ^ 2 = meridian ρ t := by
  rw [sqrtLift, meridian, mul_pow]
  congr 1
  · rw [← Complex.ofReal_pow, Real.sq_sqrt hρ]
  · rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring

/-- The lift flips sign after one traversal: the deck sign is `-1`. -/
theorem sqrtLift_one (ρ : ℝ) : sqrtLift ρ 1 = - sqrtLift ρ 0 := by
  simp [sqrtLift, Complex.exp_pi_mul_I]

theorem sqrtLift_continuous (ρ : ℝ) : Continuous (fun t : ℝ => sqrtLift ρ t) := by
  unfold sqrtLift
  exact continuous_const.mul
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))

/-- **Deck sign for every continuous square root.** Any continuous
square root of the meridian loop on `[0, 1]` ends at minus its start. -/
theorem sqrt_loop_endpoint_flip (hρ : 0 < ρ) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Set.Icc 0 1))
    (hfsq : ∀ t ∈ Set.Icc (0 : ℝ) 1, (f t) ^ 2 = meridian ρ t) :
    f 1 = - f 0 := by
  have hℓ : ∀ t, sqrtLift ρ t ≠ 0 := fun t => sqrtLift_ne_zero hρ t
  set g : ℝ → ℂ := fun t => f t / sqrtLift ρ t with hg
  have hgcont : ContinuousOn g (Set.Icc 0 1) :=
    hf.div (sqrtLift_continuous ρ).continuousOn (fun t _ => hℓ t)
  have hgsq : ∀ t ∈ Set.Icc (0 : ℝ) 1, (g t) ^ 2 = 1 := by
    intro t ht
    show (f t / sqrtLift ρ t) ^ 2 = 1
    rw [div_pow, hfsq t ht, sqrtLift_sq hρ.le t]
    exact div_self (meridian_ne_zero hρ.ne' t)
  have hgval : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t = 1 ∨ g t = -1 :=
    fun t ht => sq_eq_one_iff.mp (hgsq t ht)
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hgre : ∀ s ∈ Set.Icc (0 : ℝ) 1, (g s).re = 1 ∨ (g s).re = -1 := by
    intro s hs
    rcases hgval s hs with h | h <;> rw [h] <;> simp
  have hconst : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t = g 0 := by
    intro t ht
    by_contra hne
    have hφ : ContinuousOn (fun s => (g s).re) (Set.Icc 0 1) := Complex.continuous_re.comp_continuousOn hgcont
    have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 1 := Set.Icc_subset_Icc le_rfl ht.2
    rcases hgval 0 h0mem with h00 | h00 <;> rcases hgval t ht with htt | htt
    · exact hne (htt.trans h00.symm)
    · -- g 0 = 1, g t = -1: intermediate value on the real part
      obtain ⟨s, hs, hφs⟩ := intermediate_value_Icc' ht.1 (hφ.mono hsub)
        (show (0 : ℝ) ∈ Set.Icc (g t).re (g 0).re by rw [h00, htt]; simp)
      have hφs' : (g s).re = 0 := hφs
      rcases hgre s (hsub hs) with h | h <;> rw [hφs'] at h <;> norm_num at h
    · -- g 0 = -1, g t = 1: symmetric
      obtain ⟨s, hs, hφs⟩ := intermediate_value_Icc ht.1 (hφ.mono hsub)
        (show (0 : ℝ) ∈ Set.Icc (g 0).re (g t).re by rw [h00, htt]; simp)
      have hφs' : (g s).re = 0 := hφs
      rcases hgre s (hsub hs) with h | h <;> rw [hφs'] at h <;> norm_num at h
    · exact hne (htt.trans h00.symm)
  have hf0 : f 0 = g 0 * sqrtLift ρ 0 := by
    show f 0 = (f 0 / sqrtLift ρ 0) * sqrtLift ρ 0
    exact (div_mul_cancel₀ (f 0) (hℓ 0)).symm
  have hf1 : f 1 = g 1 * sqrtLift ρ 1 := by
    show f 1 = (f 1 / sqrtLift ρ 1) * sqrtLift ρ 1
    exact (div_mul_cancel₀ (f 1) (hℓ 1)).symm
  rw [hf1, hconst 1 h1mem, sqrtLift_one, mul_neg, ← hf0]

/-- **No continuous square root of the meridian loop is periodic.** -/
theorem no_periodic_sqrt (hρ : 0 < ρ) :
    ¬ ∃ f : ℝ → ℂ, ContinuousOn f (Set.Icc 0 1) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, (f t) ^ 2 = meridian ρ t) ∧ f 0 = f 1 := by
  rintro ⟨f, hf, hfsq, hper⟩
  have hflip := sqrt_loop_endpoint_flip hρ f hf hfsq
  rw [hper] at hflip
  have hf0 : (f 0) ^ 2 = meridian ρ 0 := hfsq 0 ⟨le_rfl, zero_le_one⟩
  rw [meridian_zero] at hf0
  have hf1z : f 1 = 0 := by
    have hcon := congrArg (fun z : ℂ => z + f 1) hflip
    simp only [neg_add_cancel] at hcon
    have h2 : (2 : ℂ) * f 1 = 0 := by rw [two_mul]; exact hcon
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  have hf0z : f 0 = 0 := by rw [hper]; exact hf1z
  have hρ0 : (ρ : ℂ) = 0 := by rw [← hf0, hf0z]; simp
  exact hρ.ne' (Complex.ofReal_eq_zero.mp hρ0)

end GppWhichWayForwardDetCover
