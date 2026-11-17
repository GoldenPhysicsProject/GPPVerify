import GppVerify.RiemannHypothesis.TwoSpaceForm

/-!
# OB-6 is the cofinal family of integer widths — the all-width quantifier, made explicit

`arp_iff_ob6 : ARP ↔ OB6` with `OB6 := ∀ L, OB6At L` (`ShiftPresentation.lean`), and
`ob6At_iff_single_cutoff` removes only the *cutoff* quantifier `∀ N` at a **fixed** width `L`
(`TwoSpaceForm.lean`).  So a contractivity certificate at one cutoff and one width proves `OB6At L₀` at that width
and nothing more.  The width quantifier is a separate obligation, and this file names the repaired chain:

* `arp_of_cofinal_widths : (∀ m : ℕ, OB6At m) → ARP` — every compactly supported test fits in some integer-width
  interval, and `weilForm_regrouped` returns Weil positivity of that test from the domination at one admissible
  cutoff;
* `ob6_iff_cofinal_widths : OB6 ↔ ∀ m : ℕ, OB6At m` and `arp_iff_cofinal_widths : ARP ↔ ∀ m : ℕ, OB6At m`;
* `arp_iff_cofinal_single_cutoffs`: `ARP ↔` for every `m : ℕ`, the contraction `‖C_N g‖² ≤ B_N g` at the single admissible
  cutoff `N_m = ⌈e^m⌉₊` for all tests supported in width `m` — **one cutoff per integer width**, infinitely many
  widths.

**Scope.** Exact logical statements about the in-tree definitions, in answer to Turbo's audit of GPT's
single-cutoff / all-width correction (bridge, Project Week 25): a single-width certificate proves `OB6At(L₀)`, not
`ARP`.  Nothing here proves any `OB6At`; ARP, RH, OB-6, UB are OPEN.

No `sorry`, no axiom.
-/

open Real GppArithmeticReflection
open scoped ContDiff

noncomputable section

namespace GppShiftPresentation

/-- A cutoff admissible at width `m`: `N_m = ⌈e^m⌉₊` (so `m < log(N_m + 1)`). -/
theorem admissible_cutoff (m : ℝ) : m < Real.log (⌈Real.exp m⌉₊ + 1) := by
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  have := Nat.le_ceil (Real.exp m)
  linarith

/-- **The cofinal integer widths give ARP.** -/
theorem arp_of_cofinal_widths (h : ∀ m : ℕ, OB6At (m : ℝ)) : ArithmeticReflectionPositivity := by
  intro g hg hc
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨m, hm⟩ := exists_nat_ge (2 * |R|)
  have hsupp : ∀ y : ℝ, (m : ℝ) / 2 < |y| → g y = 0 := by
    intro y hy
    by_contra hne
    have hy' : y ∈ Metric.closedBall (0 : ℝ) R := hR (subset_tsupport _ hne)
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hy'
    linarith [le_abs_self R]
  have hN := admissible_cutoff (m : ℝ)
  have h1 := h m g hg hc hsupp ⌈Real.exp m⌉₊ hN
  have h2 := weilForm_regrouped hg.continuous hc hsupp hN
  linarith

theorem ob6_iff_cofinal_widths : OB6 ↔ ∀ m : ℕ, OB6At (m : ℝ) :=
  ⟨fun h m => h m, fun h => arp_iff_ob6.mp (arp_of_cofinal_widths h)⟩

theorem arp_iff_cofinal_widths : ArithmeticReflectionPositivity ↔ ∀ m : ℕ, OB6At (m : ℝ) :=
  arp_iff_ob6.trans ob6_iff_cofinal_widths

/-- **One admissible cutoff per integer width, infinitely many widths.** -/
theorem arp_iff_cofinal_single_cutoffs :
    ArithmeticReflectionPositivity ↔ ∀ m : ℕ, ∀ g : ℝ → ℝ, ∀ hg : ContDiff ℝ ∞ g,
      ∀ hc : HasCompactSupport g, (∀ y : ℝ, (m : ℝ) / 2 < |y| → g y = 0) →
        ‖CN ⌈Real.exp m⌉₊ hg.continuous hc‖ ^ 2 ≤ BNform ⌈Real.exp m⌉₊ g := by
  rw [arp_iff_cofinal_widths]
  refine forall_congr' fun m => ?_
  exact ob6At_iff_single_cutoff (m : ℝ) ⌈Real.exp m⌉₊ (admissible_cutoff m)

end GppShiftPresentation

#print axioms GppShiftPresentation.arp_iff_cofinal_single_cutoffs
