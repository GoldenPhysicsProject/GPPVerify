import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The zero quartet as a four-lift orbit, and the two spectral half-flips

Source: Codex, bridge `research/codex/2026-10-03_qt_zero_quartet_half_flip_bridge.md`, §§1–5
(commit `d70ef85`; the exact algebraic part).

Work in the centered coordinate `z = s − ½ = δ + iγ`. There are two involutions of the plane:

* the functional-equation (shadow) flip `R_sh : z ↦ −z` (this is `s ↦ 1 − s`);
* complex conjugation `R_c : z ↦ z̄`.

They commute and compose to `D_spec = R_sh R_c : z ↦ −z̄`.

* `quartet_orbit`: the orbit of `z = δ + iγ` under `⟨R_sh, R_c⟩` is `{±δ ± iγ}` (the zero quartet).
* `D_spec_apply`, `D_fixed_iff`: `D_spec z = −z̄`, and `D_spec z = z ⟺ Re z = 0`, i.e. `Re s = ½`;
* `halfflip_agree_iff`: `R_sh z = R_c z ⟺ Re z = 0` (the same condition: "`1 − s = s̄ ⟺ Re s = ½`");
* the splitting `z = P_+ z + P_- z` with `P_+ z = i Im z` (even part) and `P_- z = Re z` (odd part, the
  off-line displacement `δ`): `split_apply`, `P_minus_eq_zero_iff`;
* `riemannHypothesis_iff_P_minus`: Mathlib's `RiemannHypothesis` holds iff `P_- z_ρ = 0` for
  every nontrivial zero `ρ` (`z_ρ = ρ − ½`).

## Checks and scope

All verified by hand against the note; no corrections. The note itself records the limitation
(§7) that even observables alone cannot see the ghost coordinate; this file formalizes only the
finite algebra and the restatement of RH, not the physical-quotient target `R_sh = R_c` on
`H_phys`. No RH claim.
-/

namespace GppZeroQuartet

/-- The functional-equation flip `z ↦ −z`. -/
def Rsh (z : ℂ) : ℂ := -z

/-- Complex conjugation. -/
def Rc (z : ℂ) : ℂ := (starRingEnd ℂ) z

/-- `D_spec = R_sh ∘ R_c`. -/
def Dspec (z : ℂ) : ℂ := Rsh (Rc z)

/-- The even part `P_+ z = i Im z`. -/
def Pplus (z : ℂ) : ℂ := (z.im : ℂ) * Complex.I

/-- The odd part `P_- z = Re z`. -/
def Pminus (z : ℂ) : ℂ := (z.re : ℂ)

theorem Rsh_Rc_comm (z : ℂ) : Rsh (Rc z) = Rc (Rsh z) := by
  simp [Rsh, Rc]

theorem Rsh_invol (z : ℂ) : Rsh (Rsh z) = z := by simp [Rsh]

theorem Rc_invol (z : ℂ) : Rc (Rc z) = z := by simp [Rc]

theorem D_spec_apply (z : ℂ) : Dspec z = -((starRingEnd ℂ) z) := rfl

/-- **The zero quartet.** The orbit of `z` under `{id, R_sh, R_c, R_sh R_c}` is `{z, −z, z̄, −z̄}`;
for `z = δ + iγ` these are `δ + iγ, −δ − iγ, δ − iγ, −δ + iγ`. -/
theorem quartet_orbit (δ γ : ℝ) :
    let z : ℂ := δ + γ * Complex.I
    (Rsh z = ((-δ : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * Complex.I) ∧
      (Rc z = (δ : ℂ) + ((-γ : ℝ) : ℂ) * Complex.I) ∧
      (Dspec z = ((-δ : ℝ) : ℂ) + (γ : ℂ) * Complex.I) := by
  intro z
  refine ⟨?_, ?_, ?_⟩
  · simp [Rsh, z]; ring
  · apply Complex.ext <;> simp [Rc, z]
  · apply Complex.ext <;> simp [Dspec, Rsh, Rc, z]

/-- **Fixed points of `D_spec`.** `D_spec z = z ⟺ Re z = 0`. -/
theorem D_fixed_iff (z : ℂ) : Dspec z = z ↔ z.re = 0 := by
  constructor
  · intro h
    have := congrArg Complex.re h
    simp [Dspec, Rsh, Rc] at this
    linarith
  · intro h
    apply Complex.ext <;> simp [Dspec, Rsh, Rc, h]

/-- **The two half-flips agree exactly on the critical line.** `R_sh z = R_c z ⟺ Re z = 0`,
i.e. (with `z = s − ½`) `1 − s = s̄ ⟺ Re s = ½`. -/
theorem halfflip_agree_iff (z : ℂ) : Rsh z = Rc z ↔ z.re = 0 := by
  constructor
  · intro h
    have := congrArg Complex.re h
    simp [Rsh, Rc] at this
    linarith
  · intro h
    apply Complex.ext <;> simp [Rsh, Rc, h]

/-- In the original coordinate: `1 − s = s̄ ⟺ Re s = ½`. -/
theorem one_sub_eq_conj_iff (s : ℂ) : 1 - s = (starRingEnd ℂ) s ↔ s.re = 1 / 2 := by
  have h := halfflip_agree_iff (s - 1 / 2)
  simp only [Rsh, Rc, map_sub, map_div₀, map_one, map_ofNat, Complex.sub_re] at h
  constructor
  · intro hs
    have : -(s - 1 / 2) = (starRingEnd ℂ) s - 1 / 2 := by linear_combination hs
    have := h.mp this
    simp at this
    linarith
  · intro hs
    have : (s - 1 / 2).re = 0 := by simp; linarith
    have := h.mpr this
    linear_combination this

/-- **Splitting.** `z = P_+ z + P_- z`. -/
theorem split_apply (z : ℂ) : z = Pplus z + Pminus z := by
  apply Complex.ext <;> simp [Pplus, Pminus]

/-- **The odd part is the off-line displacement.** `P_- z = 0 ⟺ Re z = 0`. -/
theorem P_minus_eq_zero_iff (z : ℂ) : Pminus z = 0 ↔ z.re = 0 := by
  simp [Pminus]

/-- **RH as vanishing of the odd part.** Mathlib's `RiemannHypothesis` holds iff `P_-(ρ − ½) = 0`
for every nontrivial zero `ρ`. -/
theorem riemannHypothesis_iff_P_minus :
    RiemannHypothesis ↔
      ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 →
        Pminus (s - 1 / 2) = 0 := by
  constructor
  · intro h s hz ht h1
    rw [P_minus_eq_zero_iff]
    have := h s hz ht h1
    simp [this]
  · intro h s hz ht h1
    have := (P_minus_eq_zero_iff _).mp (h s hz ht h1)
    simp at this
    linarith

end GppZeroQuartet
