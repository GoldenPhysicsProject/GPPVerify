import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Suzuki shifted-operator kernel reduction (`formalization_queue` item `2e8ff61e`)

On `L²₀(-a,a)` (mean-zero functions on `(-a,a)`), Suzuki 2026 §8 has `K_a = (-Δ_N)⁻¹` with
integral kernel `N_a(x,y) = (x²+y²)/(4a) - |x-y|/2 + a/6` and `G_a = P_a C_g P_a`. The
item's claim: for mean-zero `u`, `K_a u = P_a C_{-|·|/2} u` — the `x²` and `a/6` terms in
`N_a` vanish against `∫u = 0`, and the `y²` term is a constant (independent of `x`) that
drops out under the mean-zero projection `P_a`. Combined with a companion identity for
`G_a`, this gives the item's "exact shifted Suzuki transfer identity"
`S_{a,λ} = G_a - λK_a = P_a C_{g+λ|·|/2} P_a`.

**Proved here — the tractable kernel-integral half.** `suzukiKernel_integral_eq_shift_add_const`:
for `u` integrable on `(-a,a)` with `∫u = 0`, and the two side-integrability conditions the
kernel's own two non-constant-multiple terms need (`y²·u(y)` and `|x-y|·u(y)` integrable —
automatic whenever `u` is, say, continuous or bounded, as every intended application is;
stated as hypotheses here rather than re-derived, since deriving them needs no theory
beyond `u`'s own regularity in each use case),

```
∫ y in (-a)..a, N_a(x,y) · u(y) dy = ∫ y in (-a)..a, (-|x-y|/2) · u(y) dy
                                        + ∫ y in (-a)..a, (y²/(4a)) · u(y) dy
```

exactly — i.e. `(K_a u)(x)` and `(C_{-|·|/2} u)(x)` differ by the single additive constant
`∫ y²/(4a)·u(y) dy` (manifestly independent of `x`), which is precisely the item's own
claimed reduction stated as a pointwise integral identity rather than at operator level.
This is pure `intervalIntegral` linearity plus `ring` on the kernel's algebraic
decomposition — no functional-analytic machinery, and in particular no distribution
theory, is needed for this half.

**Honest boundary, not attempted here.**
* The operator-level statement `K_a u = P_a C_{-|·|/2} u` (with `K_a` built as the genuine
  inverse Neumann-Laplacian `(-Δ_N)⁻¹` on `L²₀(-a,a)`, and `P_a` a literal orthogonal
  projection) is not constructed — only the underlying kernel-integral algebra above,
  which is the identity's actual mathematical content. Building `(-Δ_N)⁻¹` itself as an
  unbounded self-adjoint operator is a separate, larger undertaking not attempted here.
* The second half of the item — passing to Fourier frequency via `(|x|)'' = 2δ₀` to get
  `hat{|x|}(z) = -2/z²` and hence `hat{k_λ}(z) = z⁻²[ξ'/ξ(1/2-iz) - λ]` — needs
  tempered-distribution theory with derivative and Fourier-transform operations. Mathlib
  has only the Schwartz test-function space itself
  (`Mathlib.Analysis.Distribution.SchwartzSpace`) and the Fourier transform ON Schwartz
  functions, not the dual distribution space or distributional derivatives — confirmed
  absent by inspection of `Mathlib.Analysis.Distribution.*`. This is the same
  tempered-distribution gap already documented as a standing Mathlib infrastructure gap
  (alongside Schatten-class operators) blocking the distributional half of this item.
  Not attempted.
* `S_{a,λ} = G_a - λK_a = P_a C_{g+λ|·|/2} P_a` (the full transfer identity) is not
  assembled, since it needs both the operator-level `K_a`/`G_a` construction above and the
  distributional Fourier half.
-/

namespace GppWeilParity

open intervalIntegral MeasureTheory

/-- Suzuki's shifted kernel `N_a(x,y) = (x²+y²)/(4a) - |x-y|/2 + a/6` on `(-a,a)×(-a,a)`. -/
noncomputable def suzukiKernel (a x y : ℝ) : ℝ := (x ^ 2 + y ^ 2) / (4 * a) - |x - y| / 2 + a / 6

/-- **The kernel-integral reduction, item `2e8ff61e`'s own claim as a pointwise integral
    identity.** For `u` mean-zero on `(-a,a)`, integrating `N_a(x,·)` against `u` equals
    integrating the shift kernel `-|x-·|/2` against `u`, plus the single `x`-independent
    constant `∫ y²/(4a)·u(y) dy` — the `x²` and `a/6` terms of `N_a` vanish outright against
    `∫u = 0`, exactly as the item states. -/
theorem suzukiKernel_integral_eq_shift_add_const
    (a x : ℝ) (u : ℝ → ℝ)
    (hu : IntervalIntegrable u volume (-a) a)
    (hu2 : IntervalIntegrable (fun y => y ^ 2 / (4 * a) * u y) volume (-a) a)
    (hua : IntervalIntegrable (fun y => -(|x - y| / 2) * u y) volume (-a) a)
    (hmean : ∫ y in (-a)..a, u y = 0) :
    (∫ y in (-a)..a, suzukiKernel a x y * u y) =
      (∫ y in (-a)..a, -(|x - y| / 2) * u y) + ∫ y in (-a)..a, y ^ 2 / (4 * a) * u y := by
  have hsplit : ∀ y, suzukiKernel a x y * u y =
      x ^ 2 / (4 * a) * u y + y ^ 2 / (4 * a) * u y + -(|x - y| / 2) * u y + a / 6 * u y := by
    intro y; unfold suzukiKernel; ring
  simp_rw [hsplit]
  have h1 : IntervalIntegrable (fun y => x ^ 2 / (4 * a) * u y) volume (-a) a := hu.const_mul _
  have h4 : IntervalIntegrable (fun y => a / 6 * u y) volume (-a) a := hu.const_mul _
  rw [intervalIntegral.integral_add ((h1.add hu2).add hua) h4,
      intervalIntegral.integral_add (h1.add hu2) hua,
      intervalIntegral.integral_add h1 hu2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hmean,
      mul_zero, mul_zero, zero_add, add_zero]
  exact add_comm _ _

end GppWeilParity
