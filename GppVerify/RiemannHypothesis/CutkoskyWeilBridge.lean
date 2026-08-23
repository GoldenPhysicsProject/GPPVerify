import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
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
kernel) — each tested standalone in under 4 seconds before composition. The two-sided
`HasSum` over all of `ℤ`, the passage `N → ∞` from `KrN0` to `K_p - 1` by continuity, and the
spectral vacuum-projection identity `C_{K_p-1} = P_0 C_{K_p} P_0` are deferred, not attempted
in this file — the honest next boundary, not silently dropped.
-/

namespace GppCutkoskyWeil

open Real

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

end GppCutkoskyWeil
