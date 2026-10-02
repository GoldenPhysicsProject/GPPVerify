import Mathlib.NumberTheory.LSeries.RiemannZeta
import GppVerify.RiemannHypothesis.CasimirCriticalLine

/-!
# Mathlib's `RiemannHypothesis`, stated in the conformal-Casimir variable

Source: Codex, GPPDiscovery2 `codex/discovery-workbench`:
* `DiscoveryLean/PrincipalSeriesZeroCriterion.lean` (`15b48f1`) and
  `research/2026-09-28_shadow_euler_casimir_fredholm_completion.md` (`d522f08`);
* the parallel-sum identity from `DiscoveryLean/ShadowEulerSchur.lean` (`ddb7bcb`).

Codex's checker states RH for zeros in the open critical strip as "every strip zero has a real,
non-positive centered square `(s − ½)²`". This file connects that criterion, and the Casimir
form `c = s(1−s) = ¼ − (s − ½)²` already in GPPVerify, to **Mathlib's own definition**
`RiemannHypothesis`. That definition covers every nontrivial zero, not only the strip.

* `casimir_eq_quarter_sub_centeredSq`: `s(1−s) = ¼ − (s − ½)²`.
* `centeredSq_nonpos_real_iff`: `(s − ½)²` is real and `≤ 0` **iff** `Re s = ½`.
* `riemannHypothesis_iff_casimir`: `RiemannHypothesis` **iff** every nontrivial zero has real
  Casimir `≥ ¼`, the principal-series range.
* `riemannHypothesis_iff_centeredSq`: `RiemannHypothesis` **iff** every nontrivial zero has a
  real, non-positive centered square.

Codex's note audits the May 2026 paper "The Shadow Euler Identity". It observes that the product
over positive ordinates `∏_{γ>0} (1 + z²/γ²)` presupposes RH, and that the unconditional
object is the genus-zero product in `u = (s − ½)²`. That audit is correct, and is why the
Casimir/centered-square variable is the right coordinate. The genus-zero (Hadamard) product
itself is not formalized here.

The **parallel-sum identity** (`parallel_sum_energy_identity`, `parallel_sum_lower_bound`,
`parallel_sum_attained`) is ported from Codex's checker with attribution. It is the scalar
Schur-complement core of her Shadow Euler bridge: `min{k x² + N y² : x + y = z} = (kN/(k+N)) z²`.

## Scope

These are restatements. None proves or assumes RH. `riemannHypothesis_iff_casimir` is an
equivalence of *statements*. It says what a proof would have to deliver: the zeros as the
Casimir spectrum `≥ ¼` of something self-adjoint.
-/

namespace GppCasimirRH

open GppCasimirCriticalLine

/-- The centered square `(s − ½)²`. -/
noncomputable def centeredSq (s : ℂ) : ℂ := (s - 1 / 2) ^ 2

/-- `s(1−s) = ¼ − (s − ½)²`. -/
theorem casimir_eq_quarter_sub_centeredSq (s : ℂ) : casimir s = 1 / 4 - centeredSq s := by
  simp only [casimir, centeredSq]; ring

/-- `(s − ½)²` is real and `≤ 0` iff `Re s = ½`. -/
theorem centeredSq_nonpos_real_iff (s : ℂ) :
    ((centeredSq s).im = 0 ∧ (centeredSq s).re ≤ 0) ↔ s.re = 1 / 2 := by
  rw [← casimir_ge_quarter_iff s, casimir_eq_quarter_sub_centeredSq]
  simp only [Complex.sub_im, Complex.sub_re]
  norm_num

/-- **Mathlib's `RiemannHypothesis` in the Casimir variable.** RH holds iff every nontrivial zero
`s` (not a trivial zero `−2(n+1)`, not `s = 1`) has real Casimir `s(1−s) ≥ ¼`. -/
theorem riemannHypothesis_iff_casimir :
    RiemannHypothesis ↔
      ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 →
        (casimir s).im = 0 ∧ 1 / 4 ≤ (casimir s).re := by
  constructor
  · intro h s hz ht h1
    exact (casimir_ge_quarter_iff s).mpr (h s hz ht h1)
  · intro h s hz ht h1
    exact (casimir_ge_quarter_iff s).mp (h s hz ht h1)

/-- **Mathlib's `RiemannHypothesis` in the centered-square variable** (Codex's criterion, on all
nontrivial zeros). -/
theorem riemannHypothesis_iff_centeredSq :
    RiemannHypothesis ↔
      ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 →
        (centeredSq s).im = 0 ∧ (centeredSq s).re ≤ 0 := by
  constructor
  · intro h s hz ht h1
    exact (centeredSq_nonpos_real_iff s).mpr (h s hz ht h1)
  · intro h s hz ht h1
    exact (centeredSq_nonpos_real_iff s).mp (h s hz ht h1)

/-- Parallel sum as an exact energy split (Codex). For `x + y = z` and `k + N ≠ 0`,
`k x² + N y² = (kN/(k+N)) z² + ((k+N) x − N z)² / (k+N)`. -/
theorem parallel_sum_energy_identity (k N x y z : ℝ) (hkN : k + N ≠ 0) (hxy : x + y = z) :
    k * x ^ 2 + N * y ^ 2 = k * N / (k + N) * z ^ 2 + ((k + N) * x - N * z) ^ 2 / (k + N) := by
  have hy : y = z - x := by linarith
  rw [hy]; field_simp; ring

/-- The parallel sum is a lower bound for positive stiffnesses. -/
theorem parallel_sum_lower_bound (k N x y z : ℝ) (hk : 0 < k) (hN : 0 < N) (hxy : x + y = z) :
    k * N / (k + N) * z ^ 2 ≤ k * x ^ 2 + N * y ^ 2 := by
  have hkN : 0 < k + N := add_pos hk hN
  rw [parallel_sum_energy_identity k N x y z hkN.ne' hxy]
  have : 0 ≤ ((k + N) * x - N * z) ^ 2 / (k + N) := by positivity
  linarith

/-- The minimum is attained at `x = N z/(k+N)`, `y = k z/(k+N)`. -/
theorem parallel_sum_attained (k N z : ℝ) (hkN : k + N ≠ 0) :
    N * z / (k + N) + k * z / (k + N) = z ∧
      k * (N * z / (k + N)) ^ 2 + N * (k * z / (k + N)) ^ 2 = k * N / (k + N) * z ^ 2 := by
  constructor
  · field_simp; ring
  · field_simp; ring

end GppCasimirRH
