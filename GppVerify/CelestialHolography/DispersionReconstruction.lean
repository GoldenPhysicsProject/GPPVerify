import GppVerify.CelestialHolography.TreeLoopSewing
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Dispersion reconstruction: the exact mechanism behind `ShadowPairSewing.sewing_identity`

`TreeLoopSewing.lean` isolates the celestial sewing identity

```
𝓜⁻¹_{5,6}[dDisc_sh^(56) T̃₆] = closePair T a b     (= i/(ℓ²+i0) · T₆(ℓ,p₁,…,p₄,-ℓ))
```

as a local hypothesis (`ShadowPairSewing.sewing_identity`) rather than an axiom or a
`True`-stub, precisely because the paper (`GPPVERIFY_TREE_LOOP_HANDOFF.md`, "Remaining
analytic theorem") states that its normalization/sign/prescription must be *derived*, not
inserted. This file proves the one piece of that derivation that **is** a genuine,
self-contained, unconditional mathematical fact, independent of any celestial convention:
the classical mechanism by which a discontinuity across a real pole determines the analytic
function with that pole, i.e. the algebraic core of the Sokhotski–Plemelj identity.

## What is proved here (unconditional, unrelated to any physics convention)

* `lorentzian_jump`: for `z₀ ε x : ℝ` with `ε ≠ 0`, the exact non-distributional identity
  `1/((x-z₀)+iε) - 1/((x-z₀)-iε) = -2iε/((x-z₀)²+ε²)`. This is the finite-`ε` content of
  "the jump of a regulated simple pole is a Lorentzian kernel" — the precise statement that
  a discontinuity of `1/(u+i0)`-type object concentrates at the pole.
* `lorentzian_kernel_pos`, `lorentzian_kernel_symm`: the Lorentzian/Cauchy kernel
  `ε/((x-z₀)²+ε²)` is positive for `ε > 0` and symmetric under `x - z₀ ↦ -(x - z₀)`.
* `lorentzian_kernel_tendsto_zero_off_pole`: pointwise, away from the pole, the kernel
  vanishes as `ε → 0⁺` — the rigorous, non-distributional half of "the regulated jump
  concentrates at the pole." The complementary mass statement `∫ x, ε/((x-z₀)²+ε²) dx = π`
  for every `ε > 0` (the kernel's total mass is `ε`-independent, which together with the
  pointwise vanishing above is the classical non-distributional content of "the regulated
  jump becomes a delta function of mass `2πi` as `ε → 0⁺`") is a standard Cauchy/Poisson
  kernel fact — reducible to Mathlib's `integral_univ_inv_one_add_sq` by the affine
  substitution `x = z₀ + ε·u` — numerically certified in `verify_dispersion.py` (Check 1
  margin) but **not additionally formalized in this file**: the substitution needs a
  translation-invariance-of-Lebesgue-measure lemma this session did not chase down; a
  genuine gap named honestly rather than forced.

## What this does and does NOT establish about `ShadowPairSewing.sewing_identity`

This file makes precise **which three analytic facts about the actual six-point celestial
tree** would let `sewing_identity` be *derived* rather than assumed, via the classical
Cauchy dispersion relation `F(z) = (1/2πi) ∫_ℝ [Disc F(x)]/(x-z) dx` (valid for `F`
meromorphic off the real axis with a single real simple pole and suitable decay at
infinity — see `verify_dispersion.py` for the numerical certification of this classical
mechanism, and Titchmarsh, *Theory of Functions*, Ch. 5, or any standard QFT dispersion-
relation reference, for the citation):

  * **(H1) Meromorphy.** After the `ℓ`-space completeness/inverse-Mellin integral of
    `dDisc_sh^(56) T̃₆`, the resulting function of `ℓ²` is meromorphic with its *only*
    singularity a simple pole at `ℓ² = 0`.
  * **(H2) Decay.** That function vanishes at infinity fast enough for the dispersion
    contour to close (a Jordan's-lemma-type condition).
  * **(H3) Residue match.** The discontinuity computed via the shadow-pair OPE/unitarity
    argument (the existing `haar_qg_paper_v215.tex` Theorem `thm:shadow-disc`, Steps 1–5)
    has, at `ℓ² = 0`, exactly the residue `-2πi · T₆(ℓ,p₁,…,p₄,-ℓ)` required to reconstruct
    `closePair`.

None of (H1)–(H3) is established here for the actual celestial six-point amplitude with its
`(z,z̄)`-dependence — that is exactly the open boundary every paper in this program already
names (`GPPVERIFY_TREE_LOOP_HANDOFF.md`: "the exact normalization/sign/prescription must be
derived from the actual celestial conventions"). What is new here is that the *mechanism*
converting a discontinuity into a propagator (Sokhotski–Plemelj) is now a proved fact in this
tree rather than an implicit citation, and the remaining gap is stated as three named,
checkable analytic properties of `G₆^tree` instead of one opaque hypothesis. This file does
**not** discharge `ShadowPairSewing.sewing_identity`, does not touch `GppShadowDisc`'s stubs,
and proves nothing about the `(z,z̄)`-dependent celestial completeness relation.
-/

namespace GppDispersion

open Complex

/-- **The exact finite-`ε` Lorentzian jump identity** (the algebraic core of
    Sokhotski–Plemelj): for real `z₀, ε, x` with `ε ≠ 0`, the jump of the regulated simple
    pole `1/((x-z₀)±iε)` across the real line is the Lorentzian kernel, exactly, with no
    limiting procedure. -/
theorem lorentzian_jump (z₀ ε x : ℝ) (hε : ε ≠ 0) :
    (1 : ℂ) / ((x : ℂ) - (z₀ : ℂ) + (ε : ℂ) * I) -
        (1 : ℂ) / ((x : ℂ) - (z₀ : ℂ) - (ε : ℂ) * I)
      = -2 * I * (ε : ℂ) / (((x - z₀) ^ 2 + ε ^ 2 : ℝ) : ℂ) := by
  have himeq1 : ((x : ℂ) - (z₀ : ℂ) + (ε : ℂ) * I).im = ε := by simp
  have himeq2 : ((x : ℂ) - (z₀ : ℂ) - (ε : ℂ) * I).im = -ε := by simp
  have hne1 : (x : ℂ) - (z₀ : ℂ) + (ε : ℂ) * I ≠ 0 := by
    intro h; rw [h] at himeq1; simp at himeq1; exact hε himeq1.symm
  have hne2 : (x : ℂ) - (z₀ : ℂ) - (ε : ℂ) * I ≠ 0 := by
    intro h; rw [h] at himeq2; simp at himeq2
    exact hε himeq2
  have hden : ((x : ℂ) - (z₀ : ℂ) + (ε : ℂ) * I) * ((x : ℂ) - (z₀ : ℂ) - (ε : ℂ) * I)
      = (((x - z₀) ^ 2 + ε ^ 2 : ℝ) : ℂ) := by
    push_cast
    linear_combination (-(ε : ℂ) ^ 2) * Complex.I_sq
  rw [div_sub_div _ _ hne1 hne2, hden]
  congr 1
  ring

/-- The Lorentzian/Cauchy kernel `ε/((x-z₀)²+ε²)`. -/
noncomputable def lorentzianKernel (z₀ ε x : ℝ) : ℝ := ε / ((x - z₀) ^ 2 + ε ^ 2)

/-- The kernel is strictly positive for `ε > 0`. -/
theorem lorentzian_kernel_pos {z₀ ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    0 < lorentzianKernel z₀ ε x := by
  unfold lorentzianKernel
  apply div_pos hε
  positivity

/-- The kernel is symmetric about the pole `x = z₀`. -/
theorem lorentzian_kernel_symm (z₀ ε : ℝ) (x : ℝ) :
    lorentzianKernel z₀ ε (z₀ + (x - z₀)) = lorentzianKernel z₀ ε (z₀ - (x - z₀)) := by
  unfold lorentzianKernel
  have hsq : (z₀ + (x - z₀) - z₀) ^ 2 = (z₀ - (x - z₀) - z₀) ^ 2 := by ring
  rw [hsq]

/-- **Pointwise vanishing off the pole as `ε → 0⁺`**: away from `x = z₀`, the Lorentzian
    kernel tends to zero. This is the rigorous, non-distributional half of "the regulated
    jump concentrates at the pole." -/
theorem lorentzian_kernel_tendsto_zero_off_pole {z₀ x : ℝ} (hx : x ≠ z₀) :
    Filter.Tendsto (fun ε : ℝ => lorentzianKernel z₀ ε x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hne : x - z₀ ≠ 0 := sub_ne_zero.mpr hx
  have hcont : Continuous (fun ε : ℝ => lorentzianKernel z₀ ε x) := by
    unfold lorentzianKernel
    apply Continuous.div continuous_id (by fun_prop)
    intro ε
    have : (0:ℝ) < (x - z₀) ^ 2 + ε ^ 2 := by positivity
    exact this.ne'
  have h0 : lorentzianKernel z₀ 0 x = 0 := by unfold lorentzianKernel; simp
  have htendsto := hcont.tendsto (0:ℝ)
  rw [h0] at htendsto
  exact htendsto.mono_left nhdsWithin_le_nhds

end GppDispersion
