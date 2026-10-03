import GppVerify.RiemannHypothesis.CasimirCriticalLine

/-!
# The centered principal-series Casimir for any self-dual L-function, and the off-axis quartet

Source: Codex, GPP-bridge `research/codex/` (commits `9de8fa5`, `9dcd4d5`, `bd1c7cc`):
* `2026-10-02_celestial_casimir_bulk_bridge.md`, §§1–2;
* `2026-10-03_universal_centered_principal_series.md`;
* `2026-10-03_wall_krylov_shell_test.md`, §5.

**Universal normalization.** For a completed L-function with symmetry center `c`
(`s ↦ 2c − s`), put `Δ = 1 + (s − c)`. Then:

* `reflect_iff`: `s ↦ 2c − s` is `Δ ↦ 2 − Δ`;
* `re_delta_eq_one_iff`: `Re s = c` iff `Re Δ = 1`;
* `psCasimir_eq`: `C_ps = Δ(2 − Δ) = 1 − (s − c)²`;
* `psCasimir_line`: on the line `s = c + iγ`, `C_ps = 1 + γ²`;
* `psCasimir_ge_one_iff`: `C_ps` is real and `≥ 1` iff `Re s = c`.

Zeta has `c = ½` (`Δ = s + ½`); elliptic-curve L-functions in the standard normalization have
`c = 1` (`Δ = s`). For zeta this is the `SL(2,ℝ)` Casimir of `CasimirCriticalLine` shifted by a
constant: `C_ps = s(1 − s) + ¾` (`psCasimir_half`). The floor is `1` here and `¼` there; both
are normalizations of one statement. The floor `1` is the scalar `SL(2,ℂ)` (celestial,
`d = 2`) principal-series convention `Δ(2 − Δ)`.

**The off-axis quartet** (`wall_krylov_shell_test.md` §5). In the centered variable `z = s − ½`,
`Q(z) = ((z − δ)² + γ²)((z + δ)² + γ²)` is even, real on real `z`, has `Q(0) = (δ² + γ²)² > 0`,
and vanishes at `z = ±δ ± iγ`. So `Ξ · Q/Q(0)` keeps evenness, reality, and `Ξ(0)`, but has
off-axis zeros.

**Correction to the note's reading of this deformation.** The note says the deformation
"preserves the entire finite-prime Euler data" and concludes that "the Archimedean/Tate
completion must enter" every positivity-preserving recursion. The deformation is equally a
change of the Archimedean factor: `Ξ · Q/Q(0)` is `ζ` times the modified gamma factor
`Γ_ℝ(s) · s(s−1)/2 · Q/Q(0)`. So an argument that allows *some* Archimedean completion is
defeated by the same quartet. What excludes `Ξ · Q/Q(0)` is the *exact* `Γ_ℝ` factor together
with the Dirichlet series. That is Hamburger's rigidity: under his growth hypotheses, a Dirichlet series with ζ's functional
equation and Γ-factor is a multiple of ζ. So the design constraint is that a recursion must use
the exact `Γ_ℝ` (equivalently, the Dirichlet-series growth that `Q` destroys), not merely that
some Archimedean term enters.

## Scope

Affine algebra and one explicit polynomial. Nothing here locates a zero; GRH for a given
L-function is equivalent to its zeros satisfying `psCasimir_ge_one_iff`, and that is open.
-/

namespace GppCenteredPS

/-- The centered principal-series label `Δ = 1 + (s − c)`. -/
def delta (c s : ℂ) : ℂ := 1 + (s - c)

/-- The normalized principal-series Casimir `Δ(2 − Δ)`. -/
def psCasimir (c s : ℂ) : ℂ := delta c s * (2 - delta c s)

/-- `s ↦ 2c − s` is `Δ ↦ 2 − Δ`. -/
theorem reflect_iff (c s : ℂ) : delta c (2 * c - s) = 2 - delta c s := by
  simp only [delta]; ring

/-- `Re s = c` iff `Re Δ = 1` (for real center `c`). -/
theorem re_delta_eq_one_iff (c : ℝ) (s : ℂ) : (delta c s).re = 1 ↔ s.re = c := by
  simp only [delta, Complex.add_re, Complex.one_re, Complex.sub_re, Complex.ofReal_re]
  constructor <;> intro h <;> linarith

/-- `Δ(2 − Δ) = 1 − (s − c)²`. -/
theorem psCasimir_eq (c s : ℂ) : psCasimir c s = 1 - (s - c) ^ 2 := by
  simp only [psCasimir, delta]; ring

/-- On the line `s = c + iγ`: `C_ps = 1 + γ²`. -/
theorem psCasimir_line (c γ : ℝ) : psCasimir c (c + γ * Complex.I) = 1 + γ ^ 2 := by
  rw [psCasimir_eq]
  have : ((c : ℂ) + γ * Complex.I - c) ^ 2 = -(γ : ℂ) ^ 2 := by
    rw [add_sub_cancel_left, mul_pow, Complex.I_sq]; ring
  rw [this]; ring

/-- **The principal-series criterion.** `C_ps` is real and `≥ 1` iff `Re s = c`. -/
theorem psCasimir_ge_one_iff (c : ℝ) (s : ℂ) :
    ((psCasimir c s).im = 0 ∧ 1 ≤ (psCasimir c s).re) ↔ s.re = c := by
  rw [psCasimir_eq]
  set x := s.re - c
  set y := s.im
  have hre : (1 - (s - c) ^ 2).re = 1 - (x ^ 2 - y ^ 2) := by
    simp [x, y, sq, Complex.mul_re]
  have him : (1 - (s - c) ^ 2).im = -(2 * x * y) := by
    simp [x, y, sq, Complex.mul_im]; ring
  rw [hre, him]
  constructor
  · rintro ⟨h1, h2⟩
    have hxy : x * y = 0 := by linarith
    rcases mul_eq_zero.mp hxy with hx | hy
    · simp only [x] at hx; linarith
    · rw [hy] at h2
      have : x ^ 2 = 0 := by nlinarith [sq_nonneg x]
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      simp only [x] at this; linarith
  · intro h
    have hx : x = 0 := by simp only [x]; linarith
    rw [hx]
    constructor
    · ring
    · nlinarith [sq_nonneg y]

/-- **Zeta normalization.** At `c = ½`: `C_ps = s(1 − s) + ¾`. -/
theorem psCasimir_half (s : ℂ) :
    psCasimir (1 / 2) s = GppCasimirCriticalLine.casimir s + 3 / 4 := by
  rw [psCasimir_eq]; simp only [GppCasimirCriticalLine.casimir]; ring

/-- The off-axis quartet polynomial `Q(z) = ((z − δ)² + γ²)((z + δ)² + γ²)`. -/
def quartet (δ γ : ℝ) (z : ℂ) : ℂ := ((z - δ) ^ 2 + (γ : ℂ) ^ 2) * ((z + δ) ^ 2 + (γ : ℂ) ^ 2)

/-- `Q` is even. -/
theorem quartet_even (δ γ : ℝ) (z : ℂ) : quartet δ γ (-z) = quartet δ γ z := by
  simp only [quartet]; ring

/-- `Q` commutes with conjugation, so it is real on the real axis. -/
theorem quartet_conj (δ γ : ℝ) (z : ℂ) :
    quartet δ γ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (quartet δ γ z) := by
  simp only [quartet, map_mul, map_add, map_pow, map_sub, Complex.conj_ofReal]

/-- `Q(0) = (δ² + γ²)²`, positive unless `δ = γ = 0`. -/
theorem quartet_zero (δ γ : ℝ) : quartet δ γ 0 = (((δ : ℂ) ^ 2 + (γ : ℂ) ^ 2)) ^ 2 := by
  simp only [quartet]; ring

theorem quartet_zero_pos (δ γ : ℝ) (h : γ ≠ 0) : 0 < (δ ^ 2 + γ ^ 2) ^ 2 := by
  have : 0 < γ ^ 2 := by positivity
  positivity

/-- `Q` vanishes at the four off-axis points `z = ±δ ± iγ`. -/
theorem quartet_vanishes (δ γ : ℝ) (σ τ : ℝ) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    quartet δ γ (σ * δ + τ * γ * Complex.I) = 0 := by
  simp only [quartet]
  rcases hσ with rfl | rfl
  · apply mul_eq_zero_of_left
    rcases hτ with rfl | rfl <;> · push_cast; linear_combination (γ : ℂ) ^ 2 * Complex.I_sq
  · apply mul_eq_zero_of_right
    rcases hτ with rfl | rfl <;> · push_cast; linear_combination (γ : ℂ) ^ 2 * Complex.I_sq

end GppCenteredPS
