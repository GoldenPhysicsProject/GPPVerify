import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Doubled BPY KMS autocorrelation: detailed balance and Grassmann wedge fibers

Source: Codex, GPP-bridge `research/codex/2026-09-30_bpy_doubled_kms_wedge.md` §§1, 3, 4.

Boundary densities are `p₊(x) = 2e^{x/2}Φ(x)` and `p₋(x) = 2e^{−x/2}Φ(x)`, for any real `Φ`.
In the note `Φ` is the Riemann kernel, but nothing here uses that. The relative density is
`w(a) = ∫ p₊(u+a) p₋(u) du`, and the excited fiber is
`𝔉_g(a) = ∫ p₊(u+a) p₋(u) |g(u+a) − g(u)|² du`.
* `kernel_factor`: `p₊(u+a) p₋(u) = 4 e^{a/2} Φ(u+a) Φ(u)`.
* `autocorr_even`: `∫ Φ(u+a)Φ(u) du` is even in `a` (translation invariance). So the KMS-symmetrized
  `h₀(a) = e^{−a/2} w(a) = 4⟨T_aΦ, Φ⟩` is even.
* `detailed_balance`: `w(a) = e^a w(−a)`.
* `fiber_detailed_balance`: `𝔉_g(a) = e^a 𝔉_g(−a)`.
* `wedge_det`: with `ψ₀ = √Φ` and `ψ_g = √Φ·g` (`Φ ≥ 0`), the `2 × 2` determinant
  `ψ_g(u+a)ψ₀(u) − ψ₀(u+a)ψ_g(u)` equals `√(Φ(u+a)Φ(u))·(g(u+a) − g(u))`. Each jump fiber is a
  Grassmann norm.

Not formalized: the Fourier identity `ĥ₀ = 4Ξ²` (§2). Codex notes that positivity of the
autocorrelation does not imply RH (Fisher-zero no-go), and that the wedge identity does not supply a
Hodge-index theorem over `ℚ`. **No RH claim.**
-/

namespace GppBpyDoubledKmsWedge

open Real MeasureTheory

/-- Plus boundary density. -/
noncomputable def pPlus (Φ : ℝ → ℝ) (x : ℝ) : ℝ := 2 * exp (x / 2) * Φ x
/-- Minus boundary density. -/
noncomputable def pMinus (Φ : ℝ → ℝ) (x : ℝ) : ℝ := 2 * exp (-x / 2) * Φ x

theorem kernel_factor (Φ : ℝ → ℝ) (u a : ℝ) :
    pPlus Φ (u + a) * pMinus Φ u = 4 * exp (a / 2) * (Φ (u + a) * Φ u) := by
  unfold pPlus pMinus
  have : exp ((u + a) / 2) * exp (-u / 2) = exp (a / 2) := by rw [← exp_add]; ring_nf
  calc 2 * exp ((u + a) / 2) * Φ (u + a) * (2 * exp (-u / 2) * Φ u)
      = 4 * (exp ((u + a) / 2) * exp (-u / 2)) * (Φ (u + a) * Φ u) := by ring
    _ = 4 * exp (a / 2) * (Φ (u + a) * Φ u) := by rw [this]

/-- Relative density `w(a)`. -/
noncomputable def w (Φ : ℝ → ℝ) (a : ℝ) : ℝ := ∫ u, pPlus Φ (u + a) * pMinus Φ u

/-- Excited fiber `𝔉_g(a)`. -/
noncomputable def fiber (Φ g : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ u, pPlus Φ (u + a) * pMinus Φ u * (g (u + a) - g u) ^ 2

/-- Even weight under the shift `u ↦ u − a`. -/
theorem shift_even (F : ℝ → ℝ → ℝ) (hF : ∀ x y, F x y = F y x) (a : ℝ) :
    ∫ u, F (u + a) u = ∫ u, F (u + -a) u := by
  rw [← integral_add_right_eq_self (fun u => F (u + -a) u) a]
  congr 1; funext u
  rw [show u + a + -a = u by ring, hF]

theorem autocorr_even (Φ : ℝ → ℝ) (a : ℝ) :
    ∫ u, Φ (u + a) * Φ u = ∫ u, Φ (u + -a) * Φ u :=
  shift_even (fun x y => Φ x * Φ y) (fun _ _ => mul_comm _ _) a

/-- **Detailed balance**: `w(a) = e^a w(−a)`. -/
theorem detailed_balance (Φ : ℝ → ℝ) (a : ℝ) : w Φ a = exp a * w Φ (-a) := by
  unfold w
  simp_rw [kernel_factor]
  rw [integral_const_mul, integral_const_mul, autocorr_even Φ a,
    show exp (a / 2) = exp a * exp (-a / 2) by rw [← exp_add]; ring_nf]
  ring

/-- **Fiber detailed balance**: `𝔉_g(a) = e^a 𝔉_g(−a)`. -/
theorem fiber_detailed_balance (Φ g : ℝ → ℝ) (a : ℝ) :
    fiber Φ g a = exp a * fiber Φ g (-a) := by
  unfold fiber
  simp_rw [kernel_factor, mul_assoc (4 * exp _)]
  rw [integral_const_mul, integral_const_mul]
  rw [shift_even (fun x y => Φ x * Φ y * (g x - g y) ^ 2) (fun _ _ => by ring) a,
    show exp (a / 2) = exp a * exp (-a / 2) by rw [← exp_add]; ring_nf]
  ring

/-- **Grassmann wedge**: the `2 × 2` determinant of `(ψ_g, ψ₀)` at `u + a` and `u`. -/
theorem wedge_det {Φ : ℝ → ℝ} (hΦ : ∀ x, 0 ≤ Φ x) (g : ℝ → ℝ) (u a : ℝ) :
    sqrt (Φ (u + a)) * g (u + a) * sqrt (Φ u) - sqrt (Φ (u + a)) * (sqrt (Φ u) * g u) =
      sqrt (Φ (u + a) * Φ u) * (g (u + a) - g u) := by
  rw [sqrt_mul (hΦ _)]; ring

end GppBpyDoubledKmsWedge
