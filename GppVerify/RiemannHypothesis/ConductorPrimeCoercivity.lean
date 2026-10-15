import Mathlib.Tactic

/-!
# Conductor domination of a finite signed Euler-current quadratic

Daniel Toupin / Golden Physics Project, 2026-10-15.
Proof note: GPP-bridge/work/codex/2026-10-15_high_conductor_uniform_window_GRH_coercivity.md.

This is an unconditional **finite-sum abstract Hilbert quadratic bound**.
In the actual completed Dirichlet Weil operator the weights are
log(p) / sqrt(p^k), N = ||g||², the signed coefficients are
Re(chi(p)^k) * autocorr_g(k log p), the conductor L=log f,
and E is the nonnegative gamma kinetic. Those identifications, the
explicit formula and the elementary B(h) <= 8 h exp(h) estimate are
NOT asserted by this module and require independent formalization.

No statement of RH or GRH is assumed or proved.
-/

namespace GppConductorPrimeCoercivity

variable {ι : Type*}

/-- Nonnegative coefficients bound every finite signed prime current
whose correlations are at most the squared test norm N. -/
theorem weighted_pairing_upper (s : Finset ι) (w b : ι → ℝ) (N : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hb : ∀ i ∈ s, b i ≤ N) :
    (∑ i ∈ s, w i * b i) ≤ (∑ i ∈ s, w i) * N := by
  have hsum : (∑ i ∈ s, w i * b i) ≤ ∑ i ∈ s, w i * N := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hb i hi) (hw i hi)
  simpa only [Finset.sum_mul] using hsum

/-- The signed Euler operator can never subtract more than twice the
total positive prime weight times N. -/
theorem signed_euler_lower (s : Finset ι) (w b : ι → ℝ) (N : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hb : ∀ i ∈ s, b i ≤ N) :
    -(2 * (∑ i ∈ s, w i * b i)) ≥
      -(2 * (∑ i ∈ s, w i) * N) := by
  have h := weighted_pairing_upper s w b N hw hb
  linarith

/-- Exact abstract conductor coercivity inequality.
No positivity of the completed Weil form is assumed. -/
theorem conductor_coercivity (s : Finset ι) (w b : ι → ℝ)
    (E L c N : ℝ) (hE : 0 ≤ E)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hb : ∀ i ∈ s, b i ≤ N) :
    (L - c - 2 * ∑ i ∈ s, w i) * N ≤
      E + (L - c) * N - 2 * ∑ i ∈ s, w i * b i := by
  have h := weighted_pairing_upper s w b N hw hb
  nlinarith

/-- A conductor exceeding the finite prime mass plus gamma scalar
forces a nonnegative completed model quadratic. -/
theorem conductor_dominates (s : Finset ι) (w b : ι → ℝ)
    (E L c N : ℝ) (hE : 0 ≤ E) (hN : 0 ≤ N)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hb : ∀ i ∈ s, b i ≤ N)
    (hcond : c + 2 * ∑ i ∈ s, w i ≤ L) :
    0 ≤ E + (L - c) * N - 2 * ∑ i ∈ s, w i * b i := by
  have h := conductor_coercivity s w b E L c N hE hw hb
  have hgap : 0 ≤ (L - c - 2 * ∑ i ∈ s, w i) * N :=
    mul_nonneg (by linarith) hN
  linarith

/-- Any genuinely negative finite signed Euler-current direction must
come from a sector whose conductor fails the simple dominance threshold. -/
theorem negative_requires_small_conductor (s : Finset ι) (w b : ι → ℝ)
    (E L c N : ℝ) (hE : 0 ≤ E) (hN : 0 ≤ N)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hb : ∀ i ∈ s, b i ≤ N)
    (hneg : E + (L - c) * N - 2 * ∑ i ∈ s, w i * b i < 0) :
    L < c + 2 * ∑ i ∈ s, w i := by
  by_contra h
  have hcond : c + 2 * ∑ i ∈ s, w i ≤ L := le_of_not_gt h
  have hnonneg := conductor_dominates s w b E L c N hE hN hw hb hcond
  linarith

end GppConductorPrimeCoercivity
