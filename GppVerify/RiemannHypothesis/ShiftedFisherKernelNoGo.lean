import GppVerify.RiemannHypothesis.FisherKernelPositive

/-!
# No-go: a positive-definite Fisher kernel does not force zeros onto the line

Source: Claude Code falsifier check for Codex's cross-face operator request (GPP-bridge PR #11
comment 6162660622), using the `F_θ` control.

The shifted control `F_θ(s) = ξ(s − θ) ξ(s + θ)` has a functional equation and, for `0 < θ < ½`,
off-line zeros `ρ ± θ`. Its Dirichlet part is `ζ(s − θ) ζ(s + θ)`, whose log-derivative coefficients
are `Λ(n)(n^θ + n^{−θ}) ≥ 0`. So its Fisher kernel is the sum of two shifted zeta Fisher kernels, and
`FisherKernelPositive.fisher_kernel_posDef` makes it positive definite:
* `shifted_kernel_posDef`: for `σ − θ > 1`, every Hermitian form in
  `τ ↦ (ζ'/ζ)'(σ − θ + iτ) + (ζ'/ζ)'(σ + θ + iτ)` is real and `≥ 0`.

Consequence: any proposed positivity transfer (a Hardy, Bost–Connes or Tate boundary operator,
or the cross-face pole compensation) that uses only (A) the functional equation and (B) the
`Λ ≥ 0` / Fisher-PD structure is falsified by `F_θ`. It must also use (C) tempered local factors
with the single pole pair `{0, 1}`, which `F_θ` violates (poles `±θ, 1 ± θ`). The Davenport–Heilbronn
function falsifies A + C without B (`(log DH)''(2) < 0`, Arb). **No RH claim.**
-/

namespace GppShiftedFisherKernelNoGo

open Complex GppFisherKernelPositive

/-- **The shifted control's Fisher kernel is positive definite.** -/
theorem shifted_kernel_posDef {σ θ : ℝ} (h : 1 < σ - θ) (hθ : 0 ≤ θ) {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (t : ι → ℝ) :
    ∃ r : ℝ, 0 ≤ r ∧
      ∑ i ∈ S, ∑ j ∈ S, c i * (starRingEnd ℂ) (c j) *
          (deriv (fun z => deriv riemannZeta z / riemannZeta z) ((σ - θ : ℝ) + (t i - t j) * I) +
            deriv (fun z => deriv riemannZeta z / riemannZeta z) ((σ + θ : ℝ) + (t i - t j) * I)) =
        r := by
  obtain ⟨e1, p1⟩ := fisher_kernel_posDef h S c t
  obtain ⟨e2, p2⟩ := fisher_kernel_posDef (show 1 < σ + θ by linarith) S c t
  refine ⟨_, add_nonneg p1 p2, ?_⟩
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [e1, e2, ofReal_add]

end GppShiftedFisherKernelNoGo
