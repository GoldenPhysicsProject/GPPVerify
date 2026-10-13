import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The shifted-product control is a no-go witness

**Purpose.** This file is a sharper witness for the No-Go ledger row
"functional equation + Euler product alone cannot locate zeros". The classical
witness is Davenport–Heilbronn (functional equation without Euler product).
Here the witness is stronger: for `0 < θ < 1/2` the shifted product

    F_θ(s) = Λ(s − θ) · Λ(s + θ)

**satisfies the functional equation** (`F_one_sub`, proved below from Mathlib's
`completedRiemannZeta_one_sub`) and **has a degree-2 Euler product** (each prime
contributes the two local factors of `Λ` at `s − θ` and `s + θ`; this is the
mathematical context, not a Lean claim), yet **every on-line zero of `Λ`
produces off-line zeros of `F_θ`** (`F_zero_add`, `F_zero_sub`).

**On `Λ` vs `ξ`.** The directive specifies `F_θ` with `ξ`; we formalize with
Mathlib's `completedRiemannZeta` (the completed zeta `Λ`), which satisfies the
same functional equation `Λ(1 − s) = Λ(s)`. The no-go moral — the functional
equation plus an Euler product does not locate zeros — is unaffected by this
substitution.

**Zero-existence hypothesis.** Mathlib cannot yet prove that `Λ` (or `ξ`) *has*
a zero, so the existence of an on-line zero `ρ` is an **explicit hypothesis**
(`hzero`), not a proved fact. The theorems are therefore conditional: *if* such
a zero exists, *then* `F_θ` has the off-line zeros `ρ ± θ`. This file makes no
claim about the existence or location of zeros of `ζ`.

**Scope.** This is a no-go, not a go: it shows that any proof locating zeros
must use something that `F_θ` lacks — the specific arithmetic content of `ζ`'s
Euler factors (a bare Euler product is not enough), i.e. the one-channel
structure detected by the `F_θ` falsifier. **No RH claim.**
-/

namespace GppNoGo.ShiftedProductControl

/-- The shifted product `F_θ(s) = Λ(s − θ) · Λ(s + θ)`, with `θ` real.
`Λ` is Mathlib's `completedRiemannZeta`. -/
noncomputable def F (θ : ℝ) (s : ℂ) : ℂ :=
  completedRiemannZeta (s - θ) * completedRiemannZeta (s + θ)

/-- **Functional equation of the shifted product:** `F_θ(1 − s) = F_θ(s)`.
From `(1 − s) − θ = 1 − (s + θ)` and `(1 − s) + θ = 1 − (s − θ)`, each factor
is fixed by Mathlib's `completedRiemannZeta_one_sub`. -/
theorem F_one_sub (θ : ℝ) (s : ℂ) : F θ (1 - s) = F θ s := by
  have h1 : (1 - s : ℂ) - (θ : ℂ) = 1 - (s + (θ : ℂ)) := by ring
  have h2 : (1 - s : ℂ) + (θ : ℂ) = 1 - (s - (θ : ℂ)) := by ring
  unfold F
  rw [h1, h2, completedRiemannZeta_one_sub, completedRiemannZeta_one_sub, mul_comm]

/-- **Zeros shift up off the line:** if `Λ(ρ) = 0` with `Re ρ = 1/2`, then
`F_θ(ρ + θ) = 0` while `Re(ρ + θ) = 1/2 + θ ≠ 1/2`.
The zero-existence `hzero` is an explicit hypothesis: Mathlib cannot prove
that `Λ` has a zero. -/
theorem F_zero_add {θ : ℝ} (hθ : 0 < θ ∧ θ < 1 / 2) {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    (hzero : completedRiemannZeta ρ = 0) :
    F θ (ρ + θ) = 0 ∧ (ρ + (θ : ℂ)).re ≠ 1 / 2 := by
  have hco : (ρ + (θ : ℂ)) - (θ : ℂ) = ρ := by ring
  refine ⟨?_, ?_⟩
  · unfold F
    rw [hco, hzero, zero_mul]
  · have hre : (ρ + (θ : ℂ)).re = 1 / 2 + θ := by
      rw [Complex.add_re, Complex.ofReal_re, hρ]
    rw [hre]
    intro hcon
    linarith [hθ.1]

/-- **Zeros shift down off the line:** if `Λ(ρ) = 0` with `Re ρ = 1/2`, then
`F_θ(ρ − θ) = 0` while `Re(ρ − θ) = 1/2 − θ ≠ 1/2`.
The zero-existence `hzero` is an explicit hypothesis: Mathlib cannot prove
that `Λ` has a zero. -/
theorem F_zero_sub {θ : ℝ} (hθ : 0 < θ ∧ θ < 1 / 2) {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    (hzero : completedRiemannZeta ρ = 0) :
    F θ (ρ - θ) = 0 ∧ (ρ - (θ : ℂ)).re ≠ 1 / 2 := by
  have hco : (ρ - (θ : ℂ)) + (θ : ℂ) = ρ := by ring
  refine ⟨?_, ?_⟩
  · unfold F
    rw [hco, hzero, mul_zero]
  · have hre : (ρ - (θ : ℂ)).re = 1 / 2 - θ := by
      rw [Complex.sub_re, Complex.ofReal_re, hρ]
    rw [hre]
    intro hcon
    linarith [hθ.1]

/-- The shifted zeros stay inside the open critical strip: this is where the
hypothesis `θ < 1/2` is load-bearing (`1/2 ± θ ∈ (0, 1)`). -/
theorem F_shifted_in_strip {θ : ℝ} (hθ : 0 < θ ∧ θ < 1 / 2) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    0 < (ρ + (θ : ℂ)).re ∧ (ρ + (θ : ℂ)).re < 1 ∧
      0 < (ρ - (θ : ℂ)).re ∧ (ρ - (θ : ℂ)).re < 1 := by
  have h1 : (ρ + (θ : ℂ)).re = 1 / 2 + θ := by
    rw [Complex.add_re, Complex.ofReal_re, hρ]
  have h2 : (ρ - (θ : ℂ)).re = 1 / 2 - θ := by
    rw [Complex.sub_re, Complex.ofReal_re, hρ]
  rw [h1, h2]
  exact ⟨by linarith [hθ.1], by linarith [hθ.2], by linarith [hθ.2], by linarith [hθ.2]⟩

end GppNoGo.ShiftedProductControl

