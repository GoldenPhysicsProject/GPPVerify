import GppVerify.RiemannHypothesis.WeilPositivityCriterion

/-!
# The two-point criterion: the zero side of Weil positivity carries no analytic content

Thread D2. `rh_iff_weil_pairedForm_nonneg` (Thread D, PR #65) proved RH equivalent to
positive semidefiniteness of the paired form on EVERY finite subset of the nontrivial
zero set. This file records what that proof actually consumes: positivity on the minimal
two-point configurations `{rho, 1 - conj rho}` alone.

* `involution_fixed_of_two_point_nonneg` — the finite criterion in minimal form: an
  involution fixes `rho_0` as soon as the paired form is nonnegative on the single pair
  `{rho_0, iota rho_0}` (the same `-2` test vector as PR #65; the all-finite-subsets
  hypothesis and the closure hypothesis are both deleted — they were never used);
* **`rh_iff_two_point_pairedForm_nonneg`** — RH iff pair positivity: every nontrivial
  zero lies on the critical line iff the paired form is PSD on each reflection pair
  `{rho, zetaInvolution rho}` with `rho` a nontrivial zero;
* `rh_of_two_point_pairedForm_nonneg` — the conditional-RH reading, spelled out.

**The moral, recorded formally.** The full-strength hypothesis (all finite subsets) and
the minimal hypothesis (single reflection pairs) are BOTH equivalent to RH. Hence no
strengthening, weakening, or refinement of the zero-side quadratic-form criterion can
ever add analytic content: the zero side is combinatorial bookkeeping. Analytic content
must be *imported* through an identity connecting the paired form to an independently
positive object — an L2 norm (GNS, `HaarPositivityWeil`), a trace of `T* T`, the prime
side of the explicit formula (`WeilSupportLadder`), or a reflection-positivity /
entanglement datum (the shadow-positivity memo; `QuartetPerturbation`). In OS language
the pair form at `{rho, iota rho}` is the reflection inner product at the minimal
bipartition, with the reflection `rho -> 1 - conj rho` playing the role of Theta.

**Honest boundary**: nothing here discharges the positivity hypothesis. This is a
sharpening of the reduction, proved to *prevent* effort being spent where content
cannot live.
-/

namespace GppWeilCriterion

open Finset

/-- **The two-point criterion, minimal form**: if `iota` is involutive at `rho_0` and
    the paired form is nonnegative on the single pair `{rho_0, iota rho_0}` for every
    weight, then `rho_0` is a fixed point. Identical `-2` test-vector proof as
    `involution_fixed_of_pairedForm_nonneg`, with the all-finite-subsets hypothesis and
    the closure hypothesis deleted. -/
theorem involution_fixed_of_two_point_nonneg {ι : ℂ → ℂ} {ρ₀ : ℂ}
    (hinv : ι (ι ρ₀) = ρ₀)
    (hpos : ∀ c : ℂ → ℂ, 0 ≤ (pairedForm ι ({ρ₀, ι ρ₀} : Finset ℂ) c).re) :
    ι ρ₀ = ρ₀ := by
  by_contra hne
  have hρσ : ρ₀ ≠ ι ρ₀ := fun h => hne h.symm
  set c : ℂ → ℂ := fun s => if s = ρ₀ then 1 else if s = ι ρ₀ then -1 else 0 with hc
  have hc1 : c ρ₀ = 1 := by simp [hc]
  have hc2 : c (ι ρ₀) = -1 := by simp [hc, Ne.symm hρσ]
  have hval : pairedForm ι ({ρ₀, ι ρ₀} : Finset ℂ) c = -2 := by
    simp only [pairedForm]
    rw [Finset.sum_pair hρσ, hinv]
    exact GppYakaboylu.swap_test_vector_value hc1 hc2
  have h0 := hpos c
  rw [hval] at h0
  have hcast : (-2 : ℂ) = ((-2 : ℝ) : ℂ) := by norm_cast
  rw [hcast, Complex.ofReal_re] at h0
  linarith

/-- **RH iff two-point positivity**: every nontrivial zero of zeta lies on the critical
    line **iff** the Weil/Yakaboylu paired form is positive semidefinite on each single
    reflection pair `{rho, zetaInvolution rho}` with `rho` a nontrivial zero. Together
    with `rh_iff_weil_pairedForm_nonneg` this pins the zero-side criterion between two
    RH-equivalent endpoints: the all-subsets form and the pair form. Everything in
    between is bookkeeping. -/
theorem rh_iff_two_point_pairedForm_nonneg :
    (∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2) ↔
      (∀ ρ ∈ nontrivialZeros, ∀ c : ℂ → ℂ,
        0 ≤ (pairedForm zetaInvolution ({ρ, zetaInvolution ρ} : Finset ℂ) c).re) := by
  constructor
  · intro hrh ρ hρ c
    refine rh_iff_weil_pairedForm_nonneg.mp hrh ({ρ, zetaInvolution ρ} : Finset ℂ) ?_ c
    intro z hz
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hρ
    · exact nontrivialZeros_mem_involution hρ
  · intro h2 ρ hρ
    exact (zetaInvolution_fixed_iff ρ).mp
      (involution_fixed_of_two_point_nonneg (zetaInvolution_involutive ρ) (h2 ρ hρ))

/-- The conditional-RH reading of the two-point criterion, spelled out: pair positivity
    on the reflection pairs of nontrivial zeros forces every nontrivial zero onto the
    critical line. -/
theorem rh_of_two_point_pairedForm_nonneg
    (hpos : ∀ ρ ∈ nontrivialZeros, ∀ c : ℂ → ℂ,
      0 ≤ (pairedForm zetaInvolution ({ρ, zetaInvolution ρ} : Finset ℂ) c).re)
    {ρ : ℂ} (hzero : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ρ.re = 1 / 2 :=
  rh_iff_two_point_pairedForm_nonneg.mpr hpos ρ ⟨hzero, h0, h1⟩

end GppWeilCriterion

-- Summary checks
#check @GppWeilCriterion.involution_fixed_of_two_point_nonneg
#check @GppWeilCriterion.rh_iff_two_point_pairedForm_nonneg
#check @GppWeilCriterion.rh_of_two_point_pairedForm_nonneg
