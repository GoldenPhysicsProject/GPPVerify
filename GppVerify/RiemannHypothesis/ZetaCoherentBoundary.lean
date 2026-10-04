import GppVerify.RiemannHypothesis.ZetaGibbsEscape

/-!
# Normalized zeta coherent states at the boundary: overlap and orthogonality

Source: Codex, GPPDiscovery2 `research/2026-09-27_zeta_pole_forces_su11_half_hardy_kernel.md`, §§4–5.

The normalized overlap of arithmetic coherent states at equal radial coordinate `r` is
`ζ(1 + 2r + i(t − u)) / ζ(1 + 2r)`. Put `ε = 2r`.

* `overlap_scaling_limit` (§4): with `t − u = ε y`, the overlap is `ζ(1 + ε(1 + iy))/ζ(1 + ε) → 1/(1 + iy)`
  as `ε ↓ 0`, the characteristic function of `Exp(1)` — this is `GppZetaGibbs.tendsto_laplace` at `s = iy`;
* `fixed_frequency_orthogonal` (§5): for fixed `Δ ≠ 0`, `ζ(1 + ε + iΔ)/ζ(1 + ε) → 0` as `ε ↓ 0`, because the
  numerator stays finite while `ζ(1 + ε)` diverges (the coherent states become mutually orthogonal).

## Checks and scope

Both claims check; the second is new. **Not formalized:** the Hardy-space / `SU(1,1)` `k = 1/2` reading
(§§1–3, partly in `CayleyHardyKernel`), the identification of the boundary with the principal-series
continuum, and the interpretation of the "surviving ghost" (§§6–7). The weak escape is a statement
about this limit, not about any Hilbert-space completion. No RH claim.
-/

open Complex Filter Topology

namespace GppZetaCoherentBoundary

/-- **Scaling limit of the overlap**: `→ 1/(1 + iy)`. -/
theorem overlap_scaling_limit (y : ℝ) :
    Tendsto (fun ε : ℝ => riemannZeta (1 + (ε : ℂ) * (1 + (y : ℂ) * Complex.I)) /
        riemannZeta (1 + (ε : ℂ))) (𝓝[>] 0) (𝓝 (1 / (1 + (y : ℂ) * Complex.I))) := by
  have h : 1 + (y : ℂ) * Complex.I ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
  have := GppZetaGibbs.tendsto_laplace ((y : ℂ) * Complex.I) (by
    intro h0
    have := congrArg Complex.re h0
    simp at this)
  simpa using this

/-- **Fixed-frequency orthogonality.** -/
theorem fixed_frequency_orthogonal (Δ : ℝ) (hΔ : Δ ≠ 0) :
    Tendsto (fun ε : ℝ => riemannZeta (1 + (ε : ℂ) + (Δ : ℂ) * Complex.I) /
        riemannZeta (1 + (ε : ℂ))) (𝓝[>] 0) (𝓝 0) := by
  have h1 : (1 : ℂ) + (Δ : ℂ) * Complex.I ≠ 1 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    exact hΔ this
  -- numerator is continuous at the nonpolar point 1 + iΔ
  have hdiff : DifferentiableAt ℂ riemannZeta (1 + (Δ : ℂ) * Complex.I) :=
    differentiableAt_riemannZeta h1
  have hnum : Tendsto (fun ε : ℝ => riemannZeta (1 + (ε : ℂ) + (Δ : ℂ) * Complex.I)) (𝓝[>] 0)
      (𝓝 (riemannZeta (1 + (Δ : ℂ) * Complex.I))) := by
    have hc : Continuous fun ε : ℝ => 1 + (ε : ℂ) + (Δ : ℂ) * Complex.I := by fun_prop
    have h0 : Tendsto (fun ε : ℝ => 1 + (ε : ℂ) + (Δ : ℂ) * Complex.I) (𝓝[>] 0)
        (𝓝 (1 + (Δ : ℂ) * Complex.I)) := by
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using this
    exact (hdiff.continuousAt.tendsto).comp h0
  have hden := GppZetaGibbs.tendsto_residue_path 1 one_ne_zero
  have hε : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using this
  have hn := hε.mul hnum
  have hlim := hn.div hden one_ne_zero
  simp only [zero_mul, zero_div] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε0
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast (Set.mem_Ioi.mp hε0).ne'
  simp only [mul_one]
  exact mul_div_mul_left _ _ hε'

end GppZetaCoherentBoundary
