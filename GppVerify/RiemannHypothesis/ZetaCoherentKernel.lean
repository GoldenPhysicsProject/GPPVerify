import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Zeta is the reproducing kernel of the Dirichlet Hardy space; coherent overlaps orthogonalize at `σ = ½`

Source: Codex, GPPDiscovery2 `research/2026-09-27_zeta_coherent_state_ads2_geometry.md` §§1–2
(branch `codex/discovery-workbench`).

In the Dirichlet Hardy space `{Σ a_n n^{−s} : Σ|a_n|² < ∞}` the evaluation vector at `w` is
`K_w = Σ n^{−w̄} e_n`. This file proves:
* `kernel_eq_zeta`: `⟨K_w, K_s⟩ = Σ_{n≥1} n^{−s} · conj(n^{−w}) = ζ(s + w̄)` whenever
  `Re s + Re w > 1`. So `ζ` is the reproducing kernel.
* `equal_sigma_kernel`: at equal radial coordinate, `s + w̄ = 2σ + i(t − u)`, so the normalized
  coherent overlap is `ζ(2σ + i(t − u)) / ζ(2σ)`.
* `overlap_tendsto_zero`: for `τ ≠ 0`, `ζ(x + iτ)/ζ(x) → 0` as real `x → 1⁺` (i.e. `σ → ½⁺`).
  The diagonal stays `1` while every off-diagonal overlap vanishes, because `ζ` has a pole at `1`
  and is finite at `1 + iτ`. The critical line appears as the orthogonalized continuum limit.

**Not formalized:** the Fisher metric `g = (log ζ)''(2σ) = Var(log N)` and its asymptotics
`1/(4r²)` (§§3–5). That needs termwise second derivatives and the Laurent expansion. **No RH claim.**
-/

namespace GppZetaCoherentKernel

open Complex Filter Topology

theorem conj_natCast_cpow (n : ℕ) (z : ℂ) :
    (starRingEnd ℂ) (((n : ℂ) + 1) ^ z) = ((n : ℂ) + 1) ^ (starRingEnd ℂ z) := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.cpow_conj _ _ (by rw [Complex.arg_ofReal_of_nonneg hpos.le]; exact Real.pi_pos.ne),
    Complex.conj_ofReal]

/-- **Reproducing kernel**: `Σ n^{−s} conj(n^{−w}) = ζ(s + w̄)` for `Re s + Re w > 1`. -/
theorem kernel_eq_zeta {s w : ℂ} (h : 1 < s.re + w.re) :
    ∑' n : ℕ, (1 / ((n : ℂ) + 1) ^ s) * (starRingEnd ℂ) (1 / ((n : ℂ) + 1) ^ w) =
      riemannZeta (s + (starRingEnd ℂ) w) := by
  have hre : 1 < (s + (starRingEnd ℂ) w).re := by simpa using h
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre]
  congr 1; funext n
  have hb : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [map_div₀, map_one, conj_natCast_cpow, cpow_add _ _ hb]
  field_simp

/-- At equal radial coordinate the kernel argument is `2σ + i(t − u)`. -/
theorem equal_sigma_kernel (σ t u : ℝ) :
    ((σ : ℂ) + t * I) + (starRingEnd ℂ) ((σ : ℂ) + u * I) = 2 * σ + (t - u : ℝ) * I := by
  simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring

/-- **Off-diagonal coherent overlaps vanish at the critical line**: for `τ ≠ 0`,
`ζ(x + iτ)/ζ(x) → 0` as real `x → 1⁺`. -/
theorem overlap_tendsto_zero {τ : ℝ} (hτ : τ ≠ 0) :
    Tendsto (fun x : ℝ => riemannZeta (x + τ * I) / riemannZeta x) (𝓝[>] 1) (𝓝 0) := by
  -- numerator → ζ(1 + iτ) (continuity away from the pole)
  have hne : (1 : ℂ) + τ * I ≠ 1 := by
    intro h; apply hτ; have := congrArg Complex.im h; simpa using this
  have hnum : Tendsto (fun x : ℝ => riemannZeta (x + τ * I)) (𝓝[>] 1)
      (𝓝 (riemannZeta (1 + τ * I))) := by
    have hc : ContinuousAt riemannZeta (1 + τ * I) := (differentiableAt_riemannZeta hne).continuousAt
    have hpath : Tendsto (fun x : ℝ => (x : ℂ) + τ * I) (𝓝[>] 1) (𝓝 (1 + τ * I)) := by
      have : Tendsto (fun x : ℝ => (x : ℂ) + τ * I) (𝓝 1) (𝓝 ((1 : ℝ) + τ * I)) :=
        (Complex.continuous_ofReal.tendsto 1).add tendsto_const_nhds
      simpa using this.mono_left nhdsWithin_le_nhds
    exact hc.tendsto.comp hpath
  -- (x − 1) ζ(x) → 1 along real x → 1⁺
  have hres : Tendsto (fun x : ℝ => ((x : ℂ) - 1) * riemannZeta x) (𝓝[>] 1) (𝓝 1) := by
    have hmap : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have := (Complex.continuous_ofReal.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with x hx
        have hx' : (1 : ℝ) < x := hx
        exact fun h => (ne_of_gt hx') (by exact_mod_cast Set.mem_singleton_iff.mp h)
    exact riemannZeta_residue_one.comp hmap
  -- x − 1 → 0
  have hsub : Tendsto (fun x : ℝ => ((x : ℂ) - 1)) (𝓝[>] 1) (𝓝 0) := by
    have : Tendsto (fun x : ℝ => ((x : ℂ) - 1)) (𝓝 1) (𝓝 (((1 : ℝ) : ℂ) - 1)) :=
      (Complex.continuous_ofReal.tendsto 1).sub tendsto_const_nhds
    simpa using this.mono_left nhdsWithin_le_nhds
  have hlim := (hnum.mul hsub).div hres one_ne_zero
  rw [mul_zero, zero_div] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx1 : ((x : ℂ) - 1) ≠ 0 := by
    rw [sub_ne_zero, Ne, Complex.ofReal_eq_one]; exact ne_of_gt hx
  simp only [Pi.div_apply]
  rw [mul_comm ((x : ℂ) - 1) (riemannZeta x), mul_div_mul_right _ _ hx1]

end GppZetaCoherentKernel
