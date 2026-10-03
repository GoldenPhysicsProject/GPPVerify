import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Tomita modular flow on ratio states is the principal-series exponent

Source: Codex, bridge `research/codex/2026-10-03_tomita_ratio_principal_series_bridge.md`, §§1–3
(commit `7f220e1`; the exact finite-cutoff identities).

On the product basis `|m,n⟩` the modular operator is diagonal, `Δ_N |m,n⟩ = (n/m)|m,n⟩`, so on a
basis vector with ratio `ρ = n/m`:

* `modular_flow_inv`: `ρ^{it} = (ρ⁻¹)^{−it}`, i.e. `(n/m)^{it} = (m/n)^{−it}`;
* `principal_exponent`: for `s = ½ + it` and `r > 0`, `r^{½ − s} = r^{−it}`; with `r = m/n` this is
  exactly the modular flow `Δ_N^{it}` restricted to `|m,n⟩`, the note's
  `r^{½−Δ_cel} = Δ_N^{it}|_{(m,n)}`;
* `tomita_reverses_ratio`: the swap `J : |m,n⟩ ↦ |n,m⟩` sends ratio `n/m` to `m/n = (n/m)⁻¹`, so
  `Δ J = J Δ⁻¹` on basis vectors: Tomita conjugation is ratio reversal;
* `unit_modulus`: for `r > 0` the principal-series factor `r^{−it}` has modulus `1`, so the flow is
  unitary.

## Scope

Pointwise complex-power identities on basis vectors. **Not formalized:** the Hilbert space, the
critical Gibbs state and the thermodynamic limit (the note's §4 shows the modular ratios are
cutoff independent although the state itself diverges), and the intertwiner into the primitive
modular lattice (the finite-place part is `GppPrimeTFDLax`). No RH claim.
-/

open Complex

namespace GppTomitaRatio

/-- `(n/m)^{it} = (m/n)^{−it}` for positive `m, n`. -/
theorem modular_flow_inv (m n t : ℝ) (hm : 0 < m) (hn : 0 < n) :
    ((n / m : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) =
      ((m / n : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I)) := by
  have hpos : 0 < m / n := div_pos hm hn
  have harg : (((m / n : ℝ)) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hpos.le]; exact Real.pi_ne_zero.symm
  have e : ((n / m : ℝ) : ℂ) = (((m / n : ℝ)) : ℂ)⁻¹ := by
    push_cast; rw [inv_div]
  rw [e, Complex.inv_cpow _ _ harg, Complex.cpow_neg]

/-- For `s = ½ + it`: `r^{½ − s} = r^{−it}`. -/
theorem principal_exponent (r : ℝ) (t : ℝ) :
    ((r : ℂ)) ^ ((1 / 2 : ℂ) - ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) =
      (r : ℂ) ^ (-((t : ℂ) * Complex.I)) := by
  congr 1; ring

/-- Tomita conjugation reverses the ratio: `(n/m)⁻¹ = m/n`. -/
theorem tomita_reverses_ratio (m n : ℝ) : (n / m)⁻¹ = m / n := by
  rw [inv_div]

/-- The principal-series factor has unit modulus. -/
theorem unit_modulus (r : ℝ) (hr : 0 < r) (t : ℝ) :
    ‖(r : ℂ) ^ (-((t : ℂ) * Complex.I))‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp

end GppTomitaRatio
