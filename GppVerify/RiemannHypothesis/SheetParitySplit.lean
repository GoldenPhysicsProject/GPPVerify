import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import GppVerify.RiemannHypothesis.OddCollisionTrace

/-!
# The sheet-exchange involution on `L²(ℝ)`: even/odd splitting and the odd sector

The log-scale line `ℝ` carries the parity `P f (u) = f(−u)` (`LogScaleParity`: on the Laplace side
`z ↦ −z`, equivalently the critical-line reflection `D`). Viewing `L²(ℝ)` as the doubled space
(left sheet ⊕ right sheet exchanged by `P`), this file proves the exact Hilbert-space facts:

* `integral_sq_swap`: `P` is an isometry, `∫ (f∘neg)² = ∫ f²`;
* `even_odd_orthogonal`: the even and odd parts are orthogonal, `∫ f_e f_o = 0`;
* `pythagoras`: for `f ∈ L²`, `∫ f² = ∫ f_e² + ∫ f_o²` — the doubled space splits orthogonally into the
  `+1` (symmetric) and `−1` (antisymmetric) sectors of the sheet exchange;
* `pole_pairing_odd_only`: the pole functional `v(x) = sinh(x/2)` is odd, so `⟨v, f⟩ = ⟨v, f_o⟩`: the
  negative rank-one pole term of the completed odd collision form (`OddCollisionTrace`) is invisible to
  the even sector. This is why the odd sector is the right place for the pole.

## Scope

Real-valued functions; a statement about the reflection `u ↦ −u` only. It is **not** a charge
conjugation, it does not exhibit a commuting charge operator (the "identical charge" half of the
two-disc picture needs extra structure), and it does not touch zero locations. No RH claim.
-/

open MeasureTheory GppOddCollision

namespace GppSheetParity

/-- Sheet exchange. -/
def swap (f : ℝ → ℝ) : ℝ → ℝ := fun x => f (-x)

/-- Symmetric (`+1`) part. -/
noncomputable def evenPart (f : ℝ → ℝ) : ℝ → ℝ := fun x => (f x + f (-x)) / 2

/-- Antisymmetric (`−1`) part. -/
noncomputable def oddPart (f : ℝ → ℝ) : ℝ → ℝ := fun x => (f x - f (-x)) / 2

theorem even_add_odd (f : ℝ → ℝ) (x : ℝ) : evenPart f x + oddPart f x = f x := by
  unfold evenPart oddPart; ring

theorem evenPart_neg (f : ℝ → ℝ) (x : ℝ) : evenPart f (-x) = evenPart f x := by
  simp [evenPart, add_comm]

theorem oddPart_neg (f : ℝ → ℝ) (x : ℝ) : oddPart f (-x) = -oddPart f x := by
  simp [oddPart]; ring

/-- The integral of an odd function vanishes (no integrability needed). -/
theorem integral_odd {g : ℝ → ℝ} (h : ∀ x, g (-x) = -g x) : ∫ x, g x = 0 := by
  have := integral_neg_eq_self g (volume : Measure ℝ)
  have h2 : ∫ x, g (-x) = -∫ x, g x := by simp [h, integral_neg]
  linarith

/-- `P` is an isometry of `L²`. -/
theorem integral_sq_swap (f : ℝ → ℝ) : ∫ x, (swap f x) ^ 2 = ∫ x, f x ^ 2 :=
  integral_neg_eq_self (fun x => f x ^ 2) volume

/-- The even and odd parts are orthogonal. -/
theorem even_odd_orthogonal (f : ℝ → ℝ) : ∫ x, evenPart f x * oddPart f x = 0 := by
  apply integral_odd
  intro x
  rw [evenPart_neg, oddPart_neg]; ring

theorem memLp_swap {f : ℝ → ℝ} (hf : MemLp f 2 volume) : MemLp (swap f) 2 volume :=
  hf.comp_measurePreserving (Measure.measurePreserving_neg volume)

/-- **Orthogonal splitting of the doubled space.** -/
theorem pythagoras {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    ∫ x, f x ^ 2 = (∫ x, evenPart f x ^ 2) + ∫ x, oddPart f x ^ 2 := by
  have hs : MemLp (swap f) 2 volume := memLp_swap hf
  have he : MemLp (evenPart f) 2 volume := by
    have := (hf.add hs).const_smul (1 / 2 : ℝ)
    convert this using 1
    funext x; simp [evenPart, swap]; ring
  have ho : MemLp (oddPart f) 2 volume := by
    have := (hf.sub hs).const_smul (1 / 2 : ℝ)
    convert this using 1
    funext x; simp [oddPart, swap]; ring
  have ie : Integrable (fun x => evenPart f x ^ 2) := by simpa using MemLp.integrable_sq he
  have io : Integrable (fun x => oddPart f x ^ 2) := by simpa using MemLp.integrable_sq ho
  have i1 : Integrable (fun x => f x ^ 2) := by simpa using MemLp.integrable_sq hf
  have i2 : Integrable (fun x => swap f x ^ 2) := by simpa using MemLp.integrable_sq hs
  rw [← integral_add ie io]
  have : (fun x => evenPart f x ^ 2 + oddPart f x ^ 2) =
      fun x => (1 / 2 : ℝ) * (f x ^ 2 + swap f x ^ 2) := by
    funext x; simp [evenPart, oddPart, swap]; ring
  rw [this, integral_const_mul, integral_add i1 i2, integral_sq_swap]
  ring

/-- **The pole functional sees only the odd sector:** `⟨v, f⟩ = ⟨v, f_o⟩` for `v = sinh(·/2)`,
whenever `v f` is integrable. -/
theorem pole_pairing_odd_only (f : ℝ → ℝ) (hf : Integrable (fun x => poleV x * f x)) :
    ∫ x, poleV x * f x = ∫ x, poleV x * oddPart f x := by
  have hv : ∀ x, poleV (-x) = -poleV x := by
    intro x; simp only [poleV]; rw [neg_div, Real.sinh_neg]
  have hsw : Integrable (fun x => poleV x * f (-x)) := by
    have := hf.comp_neg.neg
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [hv]
  have ev : ∫ x, poleV x * evenPart f x = 0 := by
    apply integral_odd
    intro x; rw [hv, evenPart_neg]; ring
  have e1 : (fun x => poleV x * f x) =
      fun x => poleV x * evenPart f x + poleV x * oddPart f x := by
    funext x; rw [← mul_add, even_add_odd]
  have hei : Integrable (fun x => poleV x * evenPart f x) := by
    have := (hf.add hsw).const_mul (1 / 2 : ℝ)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [evenPart]; ring
  have hoi : Integrable (fun x => poleV x * oddPart f x) := by
    have := (hf.sub hsw).const_mul (1 / 2 : ℝ)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [oddPart]; ring
  rw [e1, integral_add hei hoi, ev, zero_add]

end GppSheetParity
