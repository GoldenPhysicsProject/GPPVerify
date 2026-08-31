import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.InnerProductSpace.l2Space
import GppVerify.RiemannHypothesis.HaarPositivityWeil

/-!
# Local shadow kernels and the finite-prime Weil kernel: the exact identities

From a 2026-08-22 research-front update to "Local-field shadow kernels, celestial unitarity,
and the adelic principal series": the proposed route
`celestial Cutkosky positivity → local shadow kernels → finite-prime Weil kernel → Casimir
compression → global Weil positivity → RH`. The final logical step (finite Weil paired-form
positivity on all nontrivial zeros ⟺ RH) is **already** proved unconditionally in
`GppVerify/RiemannHypothesis/WeilPositivityCriterion.lean` (`rh_iff_weil_pairedForm_nonneg`)
— that criterion is an *abstract* pairing over finite subsets of the actual (unknown) zero
set, not the classical Weil explicit-formula prime-sum quadratic form built here. Connecting
the two is itself a substantial, separate undertaking (the classical explicit formula linking
zeta zeros to prime sums via an integral transform) and is **not attempted in this file**.

This file formalizes only the exact, unconditional local identities: the finite-place shadow
kernel `K_p`, its vacuum-subtracted form `W_p`, and the Casimir-weighted Archimedean kernel
`H`'s positivity. **No claim toward RH, no claim of global Weil positivity, no axiom.**

## Self-correction (same research thread, second pass)

The first pass of this file's research question — "does a positivity-preserving projection
from `K_p` to `K_p - 1` exist?" — was investigated by building a **Toeplitz matrix of Fourier
coefficients** `T[j,k] = c_{j-k}` (indices `j,k` ranging over frequencies) and finding it
indefinite. That is a real computation, but it tests the wrong object: it asks whether the
*coefficient sequence itself* is positive-definite as a new kernel on the integers — not
whether the vacuum-subtracted kernel `K_p - 1` is positive-definite as a function on the
circle (i.e. whether `M_{jk} = (K_p-1)(θ_j-θ_k)`, built from **point evaluations at arbitrary
finite configurations of angles**, is PSD). These are different statements. Under the
correct notion, the vacuum subtraction is manifestly compatible with positivity — trivially,
since convolution by `K_p - 1` is diagonalized by the Fourier basis with eigenvalues `0` at
`n=0` and `r^{|n|}>0` at `n≠0`: dropping one nonnegative eigenvalue (the DC mode) to zero
cannot make the rest negative. `KrN0_gram_nonneg` below proves this rigorously at every
finite truncation, via the finite Fourier/Gram-square identity, not merely asserts it. See
`discovery/cutkosky_weil/notes.md` for the corrected numerical verification and the full
account of the earlier error.

## Proof-engineering note (third pass)

A second attempt formalized the full two-sided `HasSum` over all of `ℤ` (the untruncated
`K_p`) as one monolithic theorem, then built `PositiveType (K_p - 1)` on top of it in another
monolithic theorem. Both repeatedly hit `(deterministic) timeout at whnf` even at 4,000,000
heartbeats (20× default) — a proof-engineering failure, not a mathematical one, traced by
bisection (isolating sub-`have`s in standalone scratch files with default heartbeats) to two
causes: (1) `HasSum.of_nat_of_neg_add_one` elaborates near-instantly in a minimal context but
catastrophically slowly inlined into a large local context carrying `r, hr0, hr1, θ` — fixed
by extracting it as its own minimal-context lemma; (2) the full Gram-square argument, run once
as a single nested proof over an infinite series, accumulates enough `ring_nf`/`nlinarith`
work on giant terms to blow up regardless. Restructured (this pass) into the small independent
layers below — `gram_square_freq` (single frequency), `gram_square_freqSum` (finite weighted
sum), `gram_square_freqSum_nonneg` (corollary), `KrN0`/`KrN0_gram_nonneg` (the truncated
kernel) — each tested standalone in under 4 seconds before composition.

## Fourth pass: the removable singularity and the `N → ∞` passage, completed

Two items left open by the third pass are now done, again as small independently-tested
layers (never more than a few seconds each): `tendsto_cutKernel_zero`/`Hext` replace the
`t=0` junk value `0/0=0` with the genuine limit `C(0)=1/(8π)`, `H(0)=1/(32π)` (from `sinh`'s
derivative at `0`, not asserted); and `tendsto_Icc_atTop` through `KrClosed_minus_one_positiveType`
complete the two-sided `HasSum` over all of `ℤ` and the `N → ∞` passage from `KrN0` to the
genuine, untruncated `K_r - 1`, landing `GppHaarPositivityWeil.PositiveType (K_r - 1)`
unconditionally — the analytic statement the third pass's monolithic attempt had failed to
reach. The route that worked (per review): build `Summable` via absolute-value comparison to
the geometric tail bound `Summable.of_nat_of_neg` + `Summable.of_nonneg_of_le` (existence
only — much cheaper than tracking `HasSum` values through `Int.rec`), identify the `tsum`'s
value via the two one-sided geometric series (`Summable.tsum_of_nat_of_neg`), then pass
positivity to the limit via `ge_of_tendsto` composed with cofinality of `Finset.Icc(-N,N)` in
`Finset.atTop`. Still deferred, not attempted in this file: the spectral vacuum-projection
operator identity `C_{K_p-1} = P_0 C_{K_p} P_0` on a precisely-defined Hilbert space, and the
Mellin/Fourier/adelic bridge to the finite-prime Weil kernel — the honest next boundary, not
silently dropped.
-/

namespace GppCutkoskyWeil

open Real
open scoped InnerProductSpace ENNReal

/-- The finite-place shadow kernel `K_p(t) = (1-p⁻¹)/|1-p^{-1/2-it}|²`, in its real
    closed form `(1-p⁻¹)/(1 - 2p^{-1/2}\cos(t\log p) + p^{-1})` (the modulus-squared
    denominator of the complex form, since `p^{-1/2+it} = \overline{p^{-1/2-it}}` for real
    `p,t`). -/
noncomputable def Kp (p t : ℝ) : ℝ :=
  (1 - p⁻¹) / (1 - 2 * p ^ (-(1:ℝ) / 2) * Real.cos (t * Real.log p) + p⁻¹)

/-- The vacuum-subtracted, log-weighted finite-place kernel: the local prime-frequency
    kernel appearing in the normalized Weil explicit formula. -/
noncomputable def Wp (p t : ℝ) : ℝ := Real.log p * (Kp p t - 1)

/-- `K_p(t) > 0` for `p > 1`: it is a Poisson kernel value, manifestly positive. -/
theorem Kp_pos {p : ℝ} (hp : 1 < p) (t : ℝ) : 0 < Kp p t := by
  have hp0 : (0:ℝ) < p := lt_trans one_pos hp
  have hr : p ^ (-(1:ℝ)/2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp (by norm_num)
  have hrpos : 0 < p ^ (-(1:ℝ)/2) := Real.rpow_pos_of_pos hp0 _
  have hnum : 0 < 1 - p⁻¹ := by
    rw [sub_pos]; exact inv_lt_one_of_one_lt₀ hp
  have hden : 0 < 1 - 2 * p ^ (-(1:ℝ)/2) * Real.cos (t * Real.log p) + p⁻¹ := by
    have hcos : Real.cos (t * Real.log p) ≤ 1 := Real.cos_le_one _
    have hval_sq : p ^ (-(1:ℝ)/2) * p ^ (-(1:ℝ)/2) = p⁻¹ := by
      rw [← Real.rpow_add hp0, show (-(1:ℝ)/2 + -(1:ℝ)/2) = (-1:ℝ) by ring,
        Real.rpow_neg_one]
    have hstrict : 0 < (1 - p ^ (-(1:ℝ)/2)) * (1 - p ^ (-(1:ℝ)/2)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [hstrict, mul_nonneg hrpos.le (sub_nonneg.mpr hcos), hval_sq]
  unfold Kp
  exact div_pos hnum hden

/-! ## The Casimir-weighted Archimedean kernel -/

/-- The celestial cut kernel, already derived (`discovery/shadow_ope/`,
    `GppVerify/QuantumGravity/LocalShadowKernel.lean`): `C(t) = t/(4\sinh(2\pi t))`. -/
noncomputable def cutKernel (t : ℝ) : ℝ := t / (4 * Real.sinh (2 * π * t))

/-- The Casimir-weighted Archimedean kernel `H(t) = (t²+1/4)·C(t)`, the rank-one
    principal-series Casimir eigenvalue `t²+1/4` times the celestial cut. -/
noncomputable def H (t : ℝ) : ℝ := (t ^ 2 + 1 / 4) * cutKernel t

/-- **`H(t) ≥ 0` for every real `t`**: `t` and `\sinh(2\pi t)` always share the same sign
    (both positive for `t>0`, both negative for `t<0`), so their ratio is nonnegative; at
    `t=0` the formula gives the junk value `0/0=0` (not the continuous extension
    `1/(32\pi)`, verified only numerically — see `discovery/cutkosky_weil/`), which is
    still `≥ 0`. -/
theorem H_nonneg (t : ℝ) : 0 ≤ H t := by
  unfold H cutKernel
  have hcasimir : (0:ℝ) ≤ t ^ 2 + 1 / 4 := by positivity
  apply mul_nonneg hcasimir
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have hsinh : Real.sinh (2 * π * t) < 0 :=
      Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg (by positivity) ht)
    exact le_of_lt (div_pos_of_neg_of_neg ht (by linarith))
  · simp [ht]
  · have hsinh : 0 < Real.sinh (2 * π * t) := Real.sinh_pos_iff.mpr (by positivity)
    exact le_of_lt (div_pos ht (by linarith))

/-! ## The finite Fourier/Gram-square theorem: `K_r - 1` is positive-type

This is the corrected, rigorous answer to the research question above. It is stated for a
general Poisson-kernel parameter `0 ≤ r < 1` (recovering `K_p` at `r = p^{-1/2}`), since the
positivity mechanism has nothing to do with `p` being prime. -/

open Finset

/-- The closed form of the two-sided Poisson kernel, `(1-r²)/(1-2r\cos θ+r²)` — the same
    closed form as `Kp`, but with the Poisson-kernel parameter `r` exposed directly instead
    of folded into `p^{-1/2}`. -/
noncomputable def KrClosed (r θ : ℝ) : ℝ := (1 - r ^ 2) / (1 - 2 * r * Real.cos θ + r ^ 2)

/-- `Kp p t` is `KrClosed` at `r = p^{-1/2}`, `θ = t \log p`: the two closed forms agree, since
    `p^{-1} = (p^{-1/2})^2` and both share the same numerator/denominator shape. -/
theorem Kp_eq_KrClosed {p : ℝ} (hp : 1 < p) (t : ℝ) :
    Kp p t = KrClosed (p ^ (-(1:ℝ) / 2)) (t * Real.log p) := by
  have hp0 : (0:ℝ) < p := lt_trans one_pos hp
  have hsq : (p ^ (-(1:ℝ) / 2)) ^ 2 = p⁻¹ := by
    rw [← Real.rpow_natCast (p ^ (-(1:ℝ)/2)) 2, ← Real.rpow_mul hp0.le]
    norm_num
    rw [Real.rpow_neg_one]
  unfold Kp KrClosed
  rw [hsq]


/-! ## Layered finite Gram-square development

Per review: the earlier monolithic `HasSum`-based development repeatedly hit elaboration
timeouts (even at 4M heartbeats) from fighting one large nested proof. Restructured into
small, independently-fast layers, each tested standalone before composition — no layer here
takes more than ~4s to elaborate in isolation. The two-sided Fourier series (`HasSum` over
all of `ℤ`) and the passage to the infinite-radius limit are deferred; what lands here is
the finite-truncation milestone, proved cleanly. -/

/-- Layer 1: pure finite Gram-square algebra at a FIXED frequency `n`. No analysis, no
    `HasSum`, no geometric series. Generalizes `GppHaarPositivityWeil.gram_square_nonneg`
    (`ConvolutionSquarePositive.lean`) to complex amplitudes `e^{inθⱼ}`. -/
theorem gram_square_freq {N : ℕ} (c : Fin N → ℂ) (θ : Fin N → ℝ) (n : ℤ) :
    (∑ j : Fin N, ∑ k : Fin N, (starRingEnd ℂ) (c j) * c k *
      Complex.exp (Complex.I * n * (θ j - θ k)) : ℂ) =
    (Complex.normSq (∑ j : Fin N, c j * Complex.exp (-(Complex.I * n * θ j))) : ℂ) := by
  have hfactor : ∀ j k : Fin N, (starRingEnd ℂ) (c j) * c k *
      Complex.exp (Complex.I * n * (θ j - θ k)) =
      ((starRingEnd ℂ) (c j) * Complex.exp (Complex.I * n * θ j)) *
        (c k * Complex.exp (-(Complex.I * n * θ k))) := by
    intro j k
    have hexp : Complex.exp (Complex.I * n * (θ j - θ k)) =
        Complex.exp (Complex.I * n * θ j) * Complex.exp (-(Complex.I * n * θ k)) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [hexp]; ring
  simp_rw [hfactor]
  rw [← Fintype.sum_mul_sum]
  set T : ℂ := ∑ j : Fin N, c j * Complex.exp (-(Complex.I * n * θ j)) with hTdef
  have hconj : (∑ j : Fin N, (starRingEnd ℂ) (c j) * Complex.exp (Complex.I * n * θ j)) =
      (starRingEnd ℂ) T := by
    rw [hTdef, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, ← Complex.exp_conj]
    congr 1
    simp [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [hconj, mul_comm ((starRingEnd ℂ) T) T, Complex.mul_conj]

/-- Layer 2: finite weighted sum over frequencies `n ∈ F`, derived from Layer 1 by pure
    finite-sum reordering. Still no analysis. -/
theorem gram_square_freqSum {N : ℕ} (c : Fin N → ℂ) (θ : Fin N → ℝ) (F : Finset ℤ) (a : ℤ → ℝ) :
    (∑ j : Fin N, ∑ k : Fin N, (starRingEnd ℂ) (c j) * c k *
      (∑ n ∈ F, (a n : ℂ) * Complex.exp (Complex.I * n * (θ j - θ k)))) =
    ((∑ n ∈ F, a n * Complex.normSq (∑ j : Fin N, c j * Complex.exp (-(Complex.I * n * θ j)))
        : ℝ) : ℂ) := by
  have hstep : ∀ j k : Fin N, (starRingEnd ℂ) (c j) * c k *
      (∑ n ∈ F, (a n : ℂ) * Complex.exp (Complex.I * n * (θ j - θ k))) =
      ∑ n ∈ F, (a n : ℂ) *
        ((starRingEnd ℂ) (c j) * c k * Complex.exp (Complex.I * n * (θ j - θ k))) := by
    intro j k
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  simp_rw [hstep]
  have hswap_kn : ∀ j : Fin N, (∑ k : Fin N, ∑ n ∈ F, (a n : ℂ) *
      ((starRingEnd ℂ) (c j) * c k * Complex.exp (Complex.I * n * (θ j - θ k)))) =
      ∑ n ∈ F, ∑ k : Fin N, (a n : ℂ) *
        ((starRingEnd ℂ) (c j) * c k * Complex.exp (Complex.I * n * (θ j - θ k))) :=
    fun j => Finset.sum_comm
  simp_rw [hswap_kn]
  rw [Finset.sum_comm]
  push_cast
  apply Finset.sum_congr rfl
  intro n _
  rw [← gram_square_freq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]

/-- Layer 3: nonnegativity corollary — trivial given Layer 2, via `Finset.sum_nonneg`. -/
theorem gram_square_freqSum_nonneg {N : ℕ} (c : Fin N → ℂ) (θ : Fin N → ℝ) (F : Finset ℤ)
    (a : ℤ → ℝ) (ha : ∀ n ∈ F, 0 ≤ a n) :
    0 ≤ (∑ j : Fin N, ∑ k : Fin N, (starRingEnd ℂ) (c j) * c k *
      (∑ n ∈ F, (a n : ℂ) * Complex.exp (Complex.I * n * (θ j - θ k)))).re := by
  rw [gram_square_freqSum, Complex.ofReal_re]
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (ha n hn) (Complex.normSq_nonneg _)

/-- Layer 4: the truncated finite-place shadow kernel `K^0_{r,N}(θ) = Σ_{0<|n|≤N} r^{|n|}e^{inθ}`
    — purely algebraic (a genuine finite sum, no `HasSum`, no convergence). Recovers `K_p - 1`
    in the limit `N → ∞` (not formalized this round — see module doc). -/
noncomputable def KrN0 (r : ℝ) (N : ℕ) (θ : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Icc (-(N : ℤ)) N).filter (· ≠ 0),
    (r : ℂ) ^ n.natAbs * Complex.exp (Complex.I * n * θ)

/-- **The immediate milestone**: `Σⱼₖ c̄ⱼcₖ K⁰_{r,N}(θⱼ-θₖ) ≥ 0` for every truncation `N`, every
    finite point configuration, and every `0 ≤ r`. This is the corrected, rigorous, and now
    *fast* answer to the file's central research question at finite truncation: the vacuum
    subtraction (`K_p` with the `n=0` term already excluded from the sum) is a positive
    kernel, for every `N` — no projection is needed beyond simply not including that term. -/
theorem KrN0_gram_nonneg {r : ℝ} (hr0 : 0 ≤ r) (N : ℕ) {M : ℕ} (c : Fin M → ℂ) (θ : Fin M → ℝ) :
    0 ≤ (∑ j : Fin M, ∑ k : Fin M, (starRingEnd ℂ) (c j) * c k *
      KrN0 r N (θ j - θ k)).re := by
  have heq : ∀ j k : Fin M, KrN0 r N (θ j - θ k) =
      ∑ n ∈ (Finset.Icc (-(N : ℤ)) N).filter (· ≠ 0), ((r ^ n.natAbs : ℝ) : ℂ) *
        Complex.exp (Complex.I * n * (θ j - θ k)) := by
    intro j k
    unfold KrN0
    push_cast
    ring_nf
  simp_rw [heq]
  exact gram_square_freqSum_nonneg c θ _ (fun n => r ^ n.natAbs) (fun n _ => pow_nonneg hr0 _)

/-! ## The Archimedean removable singularity: `C(0) = 1/(8π)`, `H(0) = 1/(32π)`

Per review: Lean's total division gives `cutKernel 0 = 0/0 = 0`, a junk value that must not be
retained in the analytic kernel. The genuine limit is `1/(8π)` for `cutKernel`, `1/(32π)` for
`H`, both proved here from first principles (via `Real.sinh`'s derivative at `0`), not merely
asserted. -/

/-- `cutKernel t → 1/(8π)` as `t → 0` (`t ≠ 0`): the genuine removable-singularity limit,
    computed from `sinh`'s derivative at `0` (`cosh 0 = 1`), not asserted. -/
theorem tendsto_cutKernel_zero :
    Filter.Tendsto cutKernel (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (1 / (8 * π))) := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * π * t) (2 * π) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 * π)
  have h2 : HasDerivAt (fun t : ℝ => Real.sinh (2 * π * t)) (Real.cosh (2 * π * 0) * (2 * π)) 0 :=
    (Real.hasDerivAt_sinh (2 * π * 0)).comp 0 h1
  simp only [mul_zero, Real.cosh_zero, one_mul] at h2
  rw [hasDerivAt_iff_tendsto_slope] at h2
  have h3 : Filter.Tendsto (fun t : ℝ => Real.sinh (2 * π * t) / t)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (2 * π)) := by
    apply h2.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
    rw [slope_def_field]
    simp [ht]
  have h4 : Filter.Tendsto (fun t : ℝ => 4 * (Real.sinh (2 * π * t) / t))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (4 * (2 * π))) := h3.const_mul 4
  have hne : (4 * (2 * π) : ℝ) ≠ 0 := by positivity
  have h5 := h4.inv₀ hne
  have heq : (4 * (2 * π) : ℝ)⁻¹ = 1 / (8 * π) := by
    rw [show (4 * (2 * π) : ℝ) = 8 * π from by ring, one_div]
  rw [heq] at h5
  apply h5.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
  unfold cutKernel
  field_simp

/-- The continuous extension of `cutKernel` to `t=0`, replacing Lean's junk `0/0=0` with the
    genuine limiting value `1/(8π)`. -/
noncomputable def cutKernelExt : ℝ → ℝ := Function.update cutKernel 0 (1 / (8 * π))

theorem cutKernelExt_eq_cutKernel {t : ℝ} (ht : t ≠ 0) : cutKernelExt t = cutKernel t :=
  Function.update_of_ne ht _ _

theorem cutKernelExt_zero : cutKernelExt 0 = 1 / (8 * π) := Function.update_self ..

theorem continuousAt_cutKernelExt_zero : ContinuousAt cutKernelExt 0 :=
  continuousAt_update_same.mpr tendsto_cutKernel_zero

/-- The Casimir-weighted Archimedean kernel, with the `t=0` junk value replaced by its genuine
    limit `1/(32π)`. -/
noncomputable def Hext (t : ℝ) : ℝ := (t ^ 2 + 1 / 4) * cutKernelExt t

theorem Hext_eq_H {t : ℝ} (ht : t ≠ 0) : Hext t = H t := by
  unfold Hext H; rw [cutKernelExt_eq_cutKernel ht]

theorem Hext_zero : Hext 0 = 1 / (32 * π) := by
  unfold Hext; rw [cutKernelExt_zero]; ring

theorem continuousAt_Hext_zero : ContinuousAt Hext 0 :=
  ((continuous_pow 2).add continuous_const).continuousAt.mul continuousAt_cutKernelExt_zero

theorem Hext_nonneg (t : ℝ) : 0 ≤ Hext t := by
  rcases eq_or_ne t 0 with ht | ht
  · rw [ht, Hext_zero]; positivity
  · rw [Hext_eq_H ht]; exact H_nonneg t

/-! ## The `N → ∞` passage: from `KrN0_gram_nonneg` to genuine positive-type positivity

Per review: separate the analysis (convergence, via the geometric tail bound) from the algebra
(the Gram-square identity, already proved above for every finite truncation). Layers A–F below
are each independently fast (seconds) to elaborate standalone; only the final composition
combines them. -/

/-- Layer A: the symmetric intervals `Icc(-N,N)` exhaust `ℤ` (cofinal in `Finset.atTop`). -/
theorem tendsto_Icc_atTop :
    Filter.Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) N) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.mpr
  intro s
  refine Filter.eventually_atTop.mpr ⟨s.sup (·.natAbs), fun N hN => ?_⟩
  intro x hx
  simp only [Finset.mem_Icc]
  have hb : x.natAbs ≤ N := le_trans (Finset.le_sup hx) hN
  omega

/-- Layer B: real summability of `r^|n|` (zeroed at `n=0`), by comparison to the geometric
    series, using `Summable.of_nat_of_neg` (existence only, no value tracking). -/
theorem summable_rpow_natAbs {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℤ => if n = 0 then (0 : ℝ) else r ^ n.natAbs) := by
  apply Summable.of_nat_of_neg
  · refine Summable.of_nonneg_of_le (f := fun n : ℕ => r ^ n)
      (fun n => by split_ifs <;> positivity) (fun n => ?_)
      (summable_geometric_of_lt_one hr0 hr1)
    split_ifs with h
    · positivity
    · exact le_of_eq (by norm_cast)
  · refine Summable.of_nonneg_of_le (f := fun n : ℕ => r ^ n)
      (fun n => by split_ifs <;> positivity) (fun n => ?_)
      (summable_geometric_of_lt_one hr0 hr1)
    split_ifs with h
    · positivity
    · exact le_of_eq (by simp [Int.natAbs_neg])

/-- Layer C: the complex summand is summable, by norm comparison to Layer B. -/
theorem summable_KrClosed_summand {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    Summable (fun n : ℤ => if n = 0 then (0 : ℂ) else (r : ℂ) ^ n.natAbs *
      Complex.exp (Complex.I * n * θ)) := by
  apply Summable.of_norm_bounded (summable_rpow_natAbs hr0 hr1)
  intro n
  split_ifs with h
  · simp
  · have hexp : ‖Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      have : (Complex.I * (n : ℂ) * (θ : ℂ)).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [this, Real.exp_zero]
    rw [norm_mul, Complex.norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0, hexp, mul_one]

/-- Layer D: removing a single (n=0) term from a tsum. -/
theorem tsum_ite_zero_eq_tsum_sub {h : ℕ → ℂ} (hh : Summable h) :
    tsum (fun n : ℕ => if n = 0 then (0 : ℂ) else h n) = tsum h - h 0 := by
  have h0 : HasSum (fun n : ℕ => if n = 0 then h 0 else 0) (h 0) := hasSum_ite_eq 0 (h 0)
  have hdiff := hh.hasSum.sub h0
  have heq : (fun n : ℕ => h n - (if n = 0 then h 0 else 0)) =
      (fun n : ℕ => if n = 0 then (0 : ℂ) else h n) := by
    funext n; by_cases hn : n = 0 <;> simp [hn]
  rw [heq] at hdiff
  exact hdiff.tsum_eq

/-- Layer E: the value of the tsum, computed via the two geometric series and Layer D — the
    two-sided Fourier series `K_r(θ) - 1 = Σ_{n≠0} r^{|n|}e^{inθ}`, as a genuine `tsum`
    identity (not merely numerically checked). -/
theorem tsum_KrClosed_summand_eq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    tsum (fun n : ℤ => if n = 0 then (0 : ℂ) else (r : ℂ) ^ n.natAbs *
      Complex.exp (Complex.I * n * θ)) = ((KrClosed r θ : ℝ) : ℂ) - 1 := by
  set ξ : ℂ := (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) with hξdef
  set η : ℂ := (r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I) with hηdef
  have hξnorm : ‖ξ‖ < 1 := by
    rw [hξdef, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hr0]
    exact hr1
  have hη_eq : η = (starRingEnd ℂ) ξ := by
    rw [hξdef, hηdef, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hηnorm : ‖η‖ < 1 := by rw [hη_eq, Complex.norm_conj]; exact hξnorm
  have hsumξ : Summable (fun n : ℕ => ξ ^ n) := summable_geometric_of_norm_lt_one hξnorm
  have hsumη : Summable (fun n : ℕ => η ^ n) := summable_geometric_of_norm_lt_one hηnorm
  set g : ℤ → ℂ := fun n => if n = 0 then (0 : ℂ) else (r : ℂ) ^ n.natAbs *
    Complex.exp (Complex.I * n * θ) with hgdef
  have hg0 : g 0 = 0 := by simp [hgdef]
  have hgpos : ∀ n : ℕ, g (n : ℤ) = if n = 0 then (0 : ℂ) else ξ ^ n := by
    intro n
    rcases eq_or_ne n 0 with hn | hn
    · subst hn; simp [hgdef]
    · have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
      simp only [hgdef, if_neg hn', if_neg hn]
      rw [hξdef, mul_pow, ← Complex.exp_nat_mul, Int.natAbs_natCast]
      congr 2
      push_cast; ring
  have hgneg : ∀ n : ℕ, g (-(n : ℤ)) = if n = 0 then (0 : ℂ) else η ^ n := by
    intro n
    rcases eq_or_ne n 0 with hn | hn
    · subst hn; simp [hgdef]
    · have hn' : (-(n : ℤ)) ≠ 0 := by omega
      have hnatAbs : (-(n : ℤ)).natAbs = n := by simp
      simp only [hgdef, if_neg hn', if_neg hn]
      rw [hηdef, mul_pow, ← Complex.exp_nat_mul, hnatAbs]
      congr 2
      push_cast; ring
  have hSummableG : Summable g := summable_KrClosed_summand hr0 hr1 θ
  have hSumPos : Summable (fun n : ℕ => g (n : ℤ)) :=
    hSummableG.comp_injective Nat.cast_injective
  have hSumNeg : Summable (fun n : ℕ => g (-(n : ℤ))) :=
    hSummableG.comp_injective (neg_injective.comp Nat.cast_injective)
  have hval := Summable.tsum_of_nat_of_neg (f := g) hSumPos hSumNeg
  rw [hg0, sub_zero] at hval
  have heqpos : tsum (fun n : ℕ => g (n : ℤ)) = (1 - ξ)⁻¹ - 1 := by
    rw [show (fun n : ℕ => g (n : ℤ)) = (fun n : ℕ => if n = 0 then (0 : ℂ) else ξ ^ n) from
      funext hgpos, tsum_ite_zero_eq_tsum_sub hsumξ, tsum_geometric_of_norm_lt_one hξnorm, pow_zero]
  have heqneg : tsum (fun n : ℕ => g (-(n : ℤ))) = (1 - η)⁻¹ - 1 := by
    rw [show (fun n : ℕ => g (-(n : ℤ))) = (fun n : ℕ => if n = 0 then (0 : ℂ) else η ^ n) from
      funext hgneg, tsum_ite_zero_eq_tsum_sub hsumη, tsum_geometric_of_norm_lt_one hηnorm, pow_zero]
  rw [heqpos, heqneg] at hval
  rw [show tsum g = tsum (fun n : ℤ => if n = 0 then (0 : ℂ) else (r : ℂ) ^ n.natAbs *
    Complex.exp (Complex.I * n * θ)) from rfl] at hval
  rw [hval]
  have h1ξ : (1 : ℂ) - ξ ≠ 0 := by
    intro h
    have hξ1 : ξ = 1 := by linear_combination -h
    rw [hξ1] at hξnorm; simp at hξnorm
  have h1η_eq : (1 : ℂ) - η = (starRingEnd ℂ) (1 - ξ) := by rw [hη_eq, map_sub, map_one]
  have h1η : (1 : ℂ) - η ≠ 0 := by rw [h1η_eq]; exact (map_ne_zero _).mpr h1ξ
  have hden : (1 - ξ) * (1 - η) = ((1 - 2 * r * Real.cos θ + r ^ 2 : ℝ) : ℂ) := by
    rw [h1η_eq, Complex.mul_conj]
    congr 1
    have hre : (1 - ξ).re = 1 - r * Real.cos θ := by
      rw [hξdef]
      simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
      ring
    have him : (1 - ξ).im = -(r * Real.sin θ) := by
      rw [hξdef]
      simp only [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
      ring
    rw [Complex.normSq_apply, hre, him]
    have hpyth : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    nlinarith [hpyth]
  have hξre : ξ.re = r * Real.cos θ := by
    rw [hξdef]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  have hsum_ξη : ξ + η = ((2 * r * Real.cos θ : ℝ) : ℂ) := by
    rw [hη_eq, Complex.add_conj, hξre]; push_cast; ring
  have hnum2 : (1 - η) + (1 - ξ) = ((2 - 2 * r * Real.cos θ : ℝ) : ℂ) := by
    rw [show (1 : ℂ) - η + (1 - ξ) = 2 - (ξ + η) from by ring, hsum_ξη]; push_cast; ring
  have hden_ne : (1 - 2 * r * Real.cos θ + r ^ 2 : ℝ) ≠ 0 := by
    intro hz
    exact mul_ne_zero h1ξ h1η (by rw [hden, hz]; simp)
  have hrealeq : (2 - 2 * r * Real.cos θ) / (1 - 2 * r * Real.cos θ + r ^ 2) = KrClosed r θ + 1 := by
    unfold KrClosed
    field_simp
    ring
  have hAB : (1 - ξ)⁻¹ + (1 - η)⁻¹ = ((KrClosed r θ : ℝ) : ℂ) + 1 := by
    rw [show (1 - ξ)⁻¹ + (1 - η)⁻¹ = 1 / (1 - ξ) + 1 / (1 - η) from by rw [one_div, one_div],
      div_add_div _ _ h1ξ h1η]
    simp only [one_mul, mul_one]
    rw [hnum2, hden, ← Complex.ofReal_div, hrealeq, Complex.ofReal_add, Complex.ofReal_one]
  have hnum : (1 - ξ)⁻¹ - 1 + ((1 - η)⁻¹ - 1) = ((KrClosed r θ : ℝ) : ℂ) - 1 := by
    have : (1 - ξ)⁻¹ - 1 + ((1 - η)⁻¹ - 1) = ((1 - ξ)⁻¹ + (1 - η)⁻¹) - 2 := by ring
    rw [this, hAB]; ring
  rw [hnum]

/-- Layer F: `KrN0 r N θ → K_r(θ) - 1` as `N → ∞`, by composing the `HasSum` (unfolded as
    a tendsto along `Finset.atTop`) with cofinality of the symmetric intervals (Layer A). -/
theorem tendsto_KrN0 {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    Filter.Tendsto (fun N : ℕ => KrN0 r N θ) Filter.atTop
      (nhds (((KrClosed r θ : ℝ) : ℂ) - 1)) := by
  have hg : Summable (fun n : ℤ => if n = 0 then (0 : ℂ) else (r : ℂ) ^ n.natAbs *
      Complex.exp (Complex.I * n * θ)) := summable_KrClosed_summand hr0 hr1 θ
  have hHasSum : HasSum (fun n : ℤ => if n = 0 then (0 : ℂ) else (r : ℂ) ^ n.natAbs *
      Complex.exp (Complex.I * n * θ)) (((KrClosed r θ : ℝ) : ℂ) - 1) := by
    rw [← tsum_KrClosed_summand_eq hr0 hr1 θ]; exact hg.hasSum
  have hcomp := hHasSum.comp tendsto_Icc_atTop
  have hKrN0_eq : ∀ N : ℕ, KrN0 r N θ = ∑ i ∈ Finset.Icc (-(N : ℤ)) N,
      (if i = 0 then (0 : ℂ) else (r : ℂ) ^ i.natAbs * Complex.exp (Complex.I * i * θ)) := by
    intro N
    unfold KrN0
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i = 0 <;> simp [hi]
  simpa only [Pi.div_def, Function.comp, hKrN0_eq] using hcomp

/-- **The full analytic result**: `Σⱼₖ c̄ⱼcₖ(K_r-1)(xⱼ-xₖ) ≥ 0` for the genuine, untruncated
    kernel, obtained from the finite-truncation milestone `KrN0_gram_nonneg` by passing to the
    limit `N → ∞`. -/
theorem KrClosed_minus_one_tendsto_positive {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {M : ℕ} (x : Fin M → ℝ) (c : Fin M → ℂ) :
    0 ≤ (∑ j : Fin M, ∑ k : Fin M, (starRingEnd ℂ) (c j) * c k *
      (((KrClosed r (x j - x k) : ℝ) : ℂ) - 1)).re := by
  have hTendstoSum : Filter.Tendsto (fun N : ℕ => ∑ j : Fin M, ∑ k : Fin M,
      (starRingEnd ℂ) (c j) * c k * KrN0 r N (x j - x k)) Filter.atTop
      (nhds (∑ j : Fin M, ∑ k : Fin M, (starRingEnd ℂ) (c j) * c k *
        (((KrClosed r (x j - x k) : ℝ) : ℂ) - 1))) := by
    apply tendsto_finsetSum
    intro j _
    apply tendsto_finsetSum
    intro k _
    exact tendsto_const_nhds.mul (tendsto_KrN0 hr0 hr1 (x j - x k))
  have hNonneg : ∀ᶠ N in Filter.atTop, 0 ≤ (∑ j : Fin M, ∑ k : Fin M,
      (starRingEnd ℂ) (c j) * c k * KrN0 r N (x j - x k)).re :=
    Filter.Eventually.of_forall (fun N => KrN0_gram_nonneg hr0 N c x)
  exact ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hTendstoSum) hNonneg

/-- **`K_r - 1` is positive-type**, in the sense of `GppHaarPositivityWeil.PositiveType`, for
    the genuine untruncated kernel — the closing step of the analytic passage requested in
    review, completing the finite-truncation milestone `KrN0_gram_nonneg`. -/
theorem KrClosed_minus_one_positiveType {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    GppHaarPositivityWeil.PositiveType (fun θ => KrClosed r θ - 1) := by
  intro M x c
  have := KrClosed_minus_one_tendsto_positive hr0 hr1 x c
  convert this using 3
  push_cast
  ring

/-! ## Fifth pass: the operator-level vacuum-compression identity

Per a further review directive, item 1 of the near-term program: formalize the actual
*operator* statement `C_{K_r-1} = P_0 C_{K_r} P_0` — not merely the finite Fourier identity
already proved above — on a precisely-defined Hilbert space, with positivity of the
compressed operator as a corollary of its Fourier eigenvalues.

**The space**: `Ell2Z := ℓ²(ℤ,ℂ)` (Mathlib's `lp (fun _:ℤ=>ℂ) 2`), the natural Fourier model —
under the circle/ℤ Fourier duality, convolution on `L²(𝕋)` by a kernel is unitarily
equivalent to multiplication on `ℓ²(ℤ)` by that kernel's Fourier coefficients (Parseval), so
working directly on `ℓ²(ℤ)` with diagonal multiplication operators is the same operator
content as convolution on the circle, without needing to build the circle convolution
operator itself (Bochner kernel integrals) in Lean.

**The operators**: `mulOpCLM w hw : Ell2Z →L[ℂ] Ell2Z` is the bounded (operator norm `≤ 1`)
diagonal multiplication operator for a weight `w : ℤ → ℂ` with `‖w n‖ ≤ 1`. `C_{K_r} :=
mulOpCLM (KrWeight r)` (symbol `r^{|n|}`), `P_0 := mulOpCLM P0Weight` (symbol `0` at `n=0`,
`1` elsewhere — the orthogonal projection deleting the constant/vacuum Fourier mode), and
`C_{K_r-1} := mulOpCLM (KrMinusOneWeight r)` (symbol `0` at `n=0`, `r^{|n|}` elsewhere,
matching the two-sided Fourier series of `K_r-1` established in `tsum_KrClosed_summand_eq`
above).

**The identity**: `vacuum_compression_operator_identity` proves
`C_{K_r-1} = P_0 * C_{K_r} * P_0` as genuine `ContinuousLinearMap` composition (not a finite
Gram matrix identity), via `mulOpLin_comp` (composition of diagonal operators multiplies
symbols) reducing to the pointwise algebraic fact `P_0(n) K_r(n) P_0(n) = (K_r-1)(n)` for
every `n ∈ ℤ` (`P0Weight_mul_KrWeight_mul_P0Weight_eq`) — `0=1-1` at `n=0`,
`1·r^{|n|}·1=r^{|n|}` at `n≠0`.

**Positivity as a corollary**: `mulOpCLM_inner_re_nonneg` is the general fact that any
bounded diagonal operator with `Re(w(n)) ≥ 0` for every `n` is positive semidefinite
(`⟪x,Tx⟫.re ≥ 0`), proved directly from the eigenvalue signs via `⟪x,Tx⟫ = Σ_n w(n)|x(n)|²`
(imaginary part of `w` plays no role, since the cross term vanishes against the manifestly
real `|x(n)|²`). `vacuum_compressed_operator_positive` specializes this to `C_{K_r-1}`,
whose eigenvalues (`0` and `r^{|n|} ≥ 0`) are already known — no new analytic content beyond
the general lemma, exactly the "as a corollary" the review asked for.

**Honest boundary, still deferred**: this closes item 1 (the operator identity) but not
items 2–4 of the wider program. See the module doc above (`GppVerify.lean`'s import comment,
and `docs/FORMALIZATION_PLAN.md`) for the precise finding on why "the finite-prime Weil
kernel in the normalization used by `rh_iff_weil_pairedForm_nonneg`" does not exist as
stated — that theorem's `pairedForm` is a zero-indexed reflection pairing with no prime or
Mellin content, a fact already flagged in this file's own module doc above (`Connecting the
two is itself a substantial, separate undertaking`) — and for the precise elementary
identity `W_p(t) = 2·Re(-ζ_p'/ζ_p(1/2+it))` (checked by hand, not yet formalized) that
correctly identifies `W_p` with the local Euler-factor logarithmic derivative on the
critical line, the honest next Lean target for items 2–3. -/

/-- The Hilbert space `ℓ²(ℤ,ℂ)`: the natural Fourier-coefficient model dual to the circle,
    on which `K_r`-convolution becomes diagonal multiplication by `r^{|n|}`. -/
noncomputable abbrev Ell2Z := lp (fun _ : ℤ => ℂ) 2

theorem memℓp_mul_bounded {w : ℤ → ℂ} (hw : ∀ n, ‖w n‖ ≤ 1) {x : ℤ → ℂ}
    (hx : Memℓp x 2) : Memℓp (fun n => w n * x n) 2 := by
  rw [memℓp_gen_iff (show (0:ℝ) < (2:ℝ≥0∞).toReal by norm_num)] at hx ⊢
  have hx' : Summable (fun n : ℤ => ‖x n‖ ^ (2:ℕ)) := by
    have := hx
    simp only [show (2:ℝ≥0∞).toReal = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast] at this
    exact this
  have hcomp : Summable (fun n : ℤ => ‖w n‖ ^ (2:ℕ) * ‖x n‖ ^ (2:ℕ)) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hx'
    have : ‖w n‖ ^ (2:ℕ) ≤ 1 := by
      have h1 : 0 ≤ ‖w n‖ := norm_nonneg _
      calc ‖w n‖ ^ (2:ℕ) ≤ 1 ^ (2:ℕ) := by
            apply pow_le_pow_left₀ h1 (hw n)
        _ = 1 := one_pow 2
    nlinarith [sq_nonneg (‖x n‖), norm_nonneg (x n)]
  have heq : (fun n : ℤ => ‖w n * x n‖ ^ ((2:ℝ≥0∞).toReal)) =
      (fun n : ℤ => ‖w n‖ ^ (2:ℕ) * ‖x n‖ ^ (2:ℕ)) := by
    funext n
    rw [show (2:ℝ≥0∞).toReal = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, norm_mul, mul_pow]
  rw [heq]
  exact hcomp

/-- The bounded pointwise-multiplication ("diagonal") linear map on `Ell2Z`, for a weight
    bounded in norm by `1`. -/
noncomputable def mulOpLin (w : ℤ → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1) : Ell2Z →ₗ[ℂ] Ell2Z where
  toFun x := ⟨fun n => w n * (x : ℤ → ℂ) n, memℓp_mul_bounded hw x.2⟩
  map_add' x y := by
    ext n
    show w n * ((x : ℤ → ℂ) n + (y : ℤ → ℂ) n) = w n * (x : ℤ → ℂ) n + w n * (y : ℤ → ℂ) n
    ring
  map_smul' c x := by
    ext n
    show w n * (c * (x : ℤ → ℂ) n) = c * (w n * (x : ℤ → ℂ) n)
    ring

theorem mulOpLin_apply (w : ℤ → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1) (x : Ell2Z) (n : ℤ) :
    (mulOpLin w hw x : ℤ → ℂ) n = w n * (x : ℤ → ℂ) n := rfl

/-- Composition of two bounded diagonal multiplication operators is the diagonal operator
    for the pointwise-multiplied weight. -/
theorem mulOpLin_comp (w₁ w₂ : ℤ → ℂ) (hw₁ : ∀ n, ‖w₁ n‖ ≤ 1) (hw₂ : ∀ n, ‖w₂ n‖ ≤ 1)
    (hw₁₂ : ∀ n, ‖w₁ n * w₂ n‖ ≤ 1) :
    (mulOpLin w₁ hw₁).comp (mulOpLin w₂ hw₂) = mulOpLin (fun n => w₁ n * w₂ n) hw₁₂ := by
  apply LinearMap.ext
  intro x
  ext n
  show w₁ n * (w₂ n * (x : ℤ → ℂ) n) = w₁ n * w₂ n * (x : ℤ → ℂ) n
  ring

/-- The bounded diagonal multiplication operator is norm-nonincreasing:
    `‖mulOpLin w hw x‖ ≤ ‖x‖`. -/
theorem mulOpLin_norm_le (w : ℤ → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1) (x : Ell2Z) :
    ‖mulOpLin w hw x‖ ≤ ‖x‖ := by
  have hp2 : (0:ℝ) < (2:ℝ≥0∞).toReal := by norm_num
  have hsq := lp.norm_rpow_eq_tsum hp2 (mulOpLin w hw x)
  have hsq' := lp.norm_rpow_eq_tsum hp2 x
  have hle : (‖mulOpLin w hw x‖ : ℝ) ^ ((2:ℝ≥0∞).toReal) ≤ ‖x‖ ^ ((2:ℝ≥0∞).toReal) := by
    rw [hsq, hsq']
    apply (lp.hasSum_norm hp2 (mulOpLin w hw x)).summable.tsum_le_tsum _
      (lp.hasSum_norm hp2 x).summable
    intro n
    have hbound : ‖w n‖ ≤ 1 := hw n
    have heval : (mulOpLin w hw x : ℤ → ℂ) n = w n * (x : ℤ → ℂ) n := rfl
    rw [heval, norm_mul]
    have h2 : (2:ℝ≥0∞).toReal = ((2:ℕ):ℝ) := by norm_num
    rw [h2, Real.rpow_natCast, Real.rpow_natCast, mul_pow]
    have hxn : 0 ≤ ‖(x : ℤ → ℂ) n‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖(x : ℤ → ℂ) n‖), pow_le_pow_left₀ (norm_nonneg (w n)) hbound 2]
  have hnn1 : (0:ℝ) ≤ ‖mulOpLin w hw x‖ := norm_nonneg _
  have hnn2 : (0:ℝ) ≤ ‖x‖ := norm_nonneg _
  exact (Real.rpow_le_rpow_iff hnn1 hnn2 hp2).mp hle

/-- The genuine bounded operator (`ContinuousLinearMap`) version of `mulOpLin`, with operator
    norm `≤ 1`. -/
noncomputable def mulOpCLM (w : ℤ → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1) : Ell2Z →L[ℂ] Ell2Z :=
  (mulOpLin w hw).mkContinuous 1 (fun x => by
    rw [one_mul]; exact mulOpLin_norm_le w hw x)

theorem mulOpCLM_apply (w : ℤ → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1) (x : Ell2Z) :
    mulOpCLM w hw x = mulOpLin w hw x := rfl

/-- The Fourier symbol of the Poisson-kernel convolution operator: `r^{|n|}`. -/
def KrWeight (r : ℝ) (n : ℤ) : ℂ := (r : ℂ) ^ n.natAbs

/-- The Fourier symbol of the vacuum-deleting projection: `0` at `n=0`, `1` elsewhere. -/
def P0Weight (n : ℤ) : ℂ := if n = 0 then 0 else 1

/-- The Fourier symbol of the vacuum-subtracted kernel: `0` at `n=0`, `r^{|n|}` elsewhere. -/
def KrMinusOneWeight (r : ℝ) (n : ℤ) : ℂ := if n = 0 then 0 else (r : ℂ) ^ n.natAbs

theorem KrWeight_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℤ) : ‖KrWeight r n‖ ≤ 1 := by
  unfold KrWeight
  rw [Complex.norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0]
  exact pow_le_one₀ hr0 hr1.le

theorem P0Weight_bound (n : ℤ) : ‖P0Weight n‖ ≤ 1 := by
  unfold P0Weight; split_ifs <;> norm_num

theorem KrMinusOneWeight_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℤ) :
    ‖KrMinusOneWeight r n‖ ≤ 1 := by
  unfold KrMinusOneWeight; split_ifs
  · norm_num
  · exact KrWeight_bound hr0 hr1 n

theorem P0_mul_bound (n : ℤ) : ‖P0Weight n * P0Weight n‖ ≤ 1 := by
  rw [norm_mul]; nlinarith [P0Weight_bound n, norm_nonneg (P0Weight n)]

theorem P0_Kr_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℤ) :
    ‖P0Weight n * KrWeight r n‖ ≤ 1 := by
  rw [norm_mul]; nlinarith [P0Weight_bound n, KrWeight_bound hr0 hr1 n, norm_nonneg (P0Weight n),
    norm_nonneg (KrWeight r n)]

theorem P0_Kr_P0_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℤ) :
    ‖P0Weight n * KrWeight r n * P0Weight n‖ ≤ 1 := by
  rw [norm_mul]
  nlinarith [P0_Kr_bound hr0 hr1 n, P0Weight_bound n, norm_nonneg (P0Weight n * KrWeight r n),
    norm_nonneg (P0Weight n)]

/-- **Positivity of the compressed operator, as a corollary of the Fourier eigenvalues.**
    If a bounded diagonal weight `w` has nonnegative real part everywhere, the associated
    operator is positive semidefinite: `⟪x, mulOpCLM w hw x⟫.re ≥ 0` for every `x`
    (the imaginary part of `w` plays no role, since the cross term vanishes against the
    manifestly-real `‖x n‖²`). -/
theorem mulOpCLM_inner_re_nonneg (w : ℤ → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1)
    (hnn : ∀ n, 0 ≤ (w n).re) (x : Ell2Z) :
    0 ≤ (⟪x, mulOpCLM w hw x⟫_ℂ).re := by
  have hsum := lp.hasSum_inner (𝕜 := ℂ) x (mulOpCLM w hw x)
  have hsumRe := Complex.reCLM.hasSum hsum
  have hnonneg : ∀ n : ℤ, 0 ≤ Complex.reCLM ⟪(x : ℤ → ℂ) n, (mulOpCLM w hw x : ℤ → ℂ) n⟫_ℂ := by
    intro n
    rw [Complex.reCLM_apply]
    have heval : (mulOpCLM w hw x : ℤ → ℂ) n = w n * (x : ℤ → ℂ) n := rfl
    rw [heval, RCLike.inner_apply' (𝕜 := ℂ)]
    have hrw : (starRingEnd ℂ) ((x : ℤ → ℂ) n) * (w n * (x : ℤ → ℂ) n)
        = w n * (Complex.normSq ((x : ℤ → ℂ) n) : ℂ) := by
      rw [← mul_assoc, mul_comm (starRingEnd ℂ ((x : ℤ → ℂ) n)) (w n), mul_assoc,
        ← Complex.normSq_eq_conj_mul_self]
    rw [hrw, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonneg (hnn n) (Complex.normSq_nonneg _)
  rw [← Complex.reCLM_apply]
  apply ge_of_tendsto hsumRe
  filter_upwards with s
  exact Finset.sum_nonneg (fun n _ => hnonneg n)

/-- **The pointwise Fourier-symbol identity**: `P_0(n) K_r(n) P_0(n) = (K_r-1)(n)` for every
    `n`, the algebraic core of the operator compression. -/
theorem P0Weight_mul_KrWeight_mul_P0Weight_eq (r : ℝ) (n : ℤ) :
    P0Weight n * KrWeight r n * P0Weight n = KrMinusOneWeight r n := by
  unfold P0Weight KrWeight KrMinusOneWeight
  by_cases h : n = 0 <;> simp [h]

/-- **The operator-level vacuum-compression identity**: on the Fourier model `Ell2Z = ℓ²(ℤ,ℂ)`,
    convolution by `K_r - 1` equals the vacuum-deleting projection `P_0` sandwiching
    convolution by `K_r`, as genuine bounded operators (`ContinuousLinearMap`s) on `Ell2Z` —
    not merely the finite Fourier identity. -/
theorem vacuum_compression_operator_identity {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (mulOpCLM P0Weight P0Weight_bound).comp
      ((mulOpCLM (KrWeight r) (KrWeight_bound hr0 hr1)).comp
        (mulOpCLM P0Weight P0Weight_bound))
      = mulOpCLM (KrMinusOneWeight r) (KrMinusOneWeight_bound hr0 hr1) := by
  apply ContinuousLinearMap.coe_injective
  show (mulOpLin P0Weight P0Weight_bound).comp
      ((mulOpLin (KrWeight r) (KrWeight_bound hr0 hr1)).comp
        (mulOpLin P0Weight P0Weight_bound))
    = mulOpLin (KrMinusOneWeight r) (KrMinusOneWeight_bound hr0 hr1)
  have hinner : (mulOpLin (KrWeight r) (KrWeight_bound hr0 hr1)).comp
      (mulOpLin P0Weight P0Weight_bound)
      = mulOpLin (fun n => KrWeight r n * P0Weight n)
          (fun n => by dsimp only; rw [mul_comm]; exact P0_Kr_bound hr0 hr1 n) :=
    mulOpLin_comp (KrWeight r) P0Weight (KrWeight_bound hr0 hr1) P0Weight_bound _
  rw [hinner]
  rw [mulOpLin_comp P0Weight (fun n => KrWeight r n * P0Weight n) P0Weight_bound _
        (fun n => by dsimp only; rw [← mul_assoc]; exact P0_Kr_P0_bound hr0 hr1 n)]
  congr 1
  funext n
  rw [← mul_assoc]
  exact P0Weight_mul_KrWeight_mul_P0Weight_eq r n

/-- `KrMinusOneWeight r n` has nonnegative real part for every `n` and `0 ≤ r < 1`: `0` at
    `n=0`, `r^{|n|} ≥ 0` elsewhere. -/
theorem KrMinusOneWeight_re_nonneg {r : ℝ} (hr0 : 0 ≤ r) (n : ℤ) :
    0 ≤ (KrMinusOneWeight r n).re := by
  unfold KrMinusOneWeight
  split_ifs with h
  · simp
  · rw [← Complex.ofReal_pow, Complex.ofReal_re]
    positivity

/-- **Positivity of the compressed operator `C_{K_r-1} = P_0 C_{K_r} P_0`, as a direct
    corollary of its Fourier eigenvalues** (`0` at `n=0`, `r^{|n|} ≥ 0` at `n≠0`) via
    `mulOpCLM_inner_re_nonneg` — the operator-level analogue of the finite-truncation
    positivity `KrN0_gram_nonneg` proved for the circle-kernel picture. -/
theorem vacuum_compressed_operator_positive {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : Ell2Z) :
    0 ≤ (⟪x, mulOpCLM (KrMinusOneWeight r) (KrMinusOneWeight_bound hr0 hr1) x⟫_ℂ).re :=
  mulOpCLM_inner_re_nonneg (KrMinusOneWeight r) (KrMinusOneWeight_bound hr0 hr1)
    (KrMinusOneWeight_re_nonneg hr0) x

end GppCutkoskyWeil
