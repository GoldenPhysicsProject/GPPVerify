import Mathlib.Tactic

/-!
# The `C₂` class-character projection of the Epstein lattice counts for `D = −20`

Source: Codex, GPP-bridge PR #11 comment 6390593150 (Discovery2 PR #22), building on Grok's S99
Epstein audit. Daniel Toupin / Golden Physics Project, with AI assistance from Codex (statement)
and Claude Code (formalization).

The two reduced positive forms of discriminant `−20` are `Q₀ = x² + 5y²` and
`Q₁ = 2x² + 2xy + 3y²`. Put `f_j(n) = r_j(n)/2`, where `r_j(n)` is the number of `(x, y) ∈ ℤ²`
with `Q_j(x, y) = n`.

* `idem_plus`, `idem_minus`, `idem_orth`, `idem_sum`, `g_mul_plus`, `g_mul_minus`: in any
  commutative ring where `2` is invertible, if `g² = 1` then `e± = (1 ± g)/2` are complementary
  orthogonal idempotents and `g e± = ± e±`. This is the finite Peter–Weyl decomposition of `C₂`.
* `inv_fourier`: `f₀ = (A₊ + A₋)/2` and `f₁ = (A₊ − A₋)/2`, where `A± = f₀ ± f₁`.
* `sol_bound_Q0`, `sol_bound_Q1`: every solution of `Q_j(x, y) = n` has `|x|, |y| ≤ n`. So the
  box counts `rBox` are the full representation numbers.
* `f0_not_mult`: `f₀(2) = f₀(3) = 0` but `f₀(6) = 2`, so `f₀` is not multiplicative even though
  `2` and `3` are coprime.
* `Aplus_mult_2_3`, `Aminus_mult_2_3`: `A₊(2, 3, 6) = (1, 2, 2)` and `A₋(2, 3, 6) = (−1, −2, 2)`.
  Both channels are multiplicative at this pair.

**Scope.** Only the pair `(2, 3)` is checked here. The 480 coprime pairs with `ab ≤ 128` live in
Discovery2 #22. It is not formalized that `Q₀` and `Q₁` represent the two ideal classes of
`ℚ(√−5)`, nor that `A±` are the Dirichlet coefficients of `ζ_K` and of the nontrivial
class-character `L`-function, nor that either has an Euler product (classical Hecke theory).
Nothing here bears on GRH, and no claim is made about RH or BSD.
-/

namespace GppC2ClassCharacter

section Idempotents

variable {R : Type*} [CommRing R] [Invertible (2 : R)] (g : R)

/-- `e₊ = (1 + g)/2`. -/
def ePlus : R := ⅟2 * (1 + g)

/-- `e₋ = (1 − g)/2`. -/
def eMinus : R := ⅟2 * (1 - g)

lemma two_inv_sq : (⅟2 : R) * ⅟2 * 2 = ⅟2 := by
  rw [mul_assoc, invOf_mul_self, mul_one]

theorem idem_plus (hg : g * g = 1) : ePlus g * ePlus g = ePlus g := by
  have h : ePlus g * ePlus g = ⅟2 * ⅟2 * (1 + 2 * g + g * g) := by unfold ePlus; ring
  rw [h, hg, show (1 : R) + 2 * g + 1 = 2 * (1 + g) by ring, ← mul_assoc, two_inv_sq, ePlus]

theorem idem_minus (hg : g * g = 1) : eMinus g * eMinus g = eMinus g := by
  have h : eMinus g * eMinus g = ⅟2 * ⅟2 * (1 - 2 * g + g * g) := by unfold eMinus; ring
  rw [h, hg, show (1 : R) - 2 * g + 1 = 2 * (1 - g) by ring, ← mul_assoc, two_inv_sq, eMinus]

theorem idem_orth (hg : g * g = 1) : ePlus g * eMinus g = 0 := by
  have h : ePlus g * eMinus g = ⅟2 * ⅟2 * (1 - g * g) := by unfold ePlus eMinus; ring
  rw [h, hg, sub_self, mul_zero]

theorem idem_sum : ePlus g + eMinus g = 1 := by
  have h : ePlus g + eMinus g = ⅟2 * 2 := by unfold ePlus eMinus; ring
  rw [h, invOf_mul_self]

theorem g_mul_plus (hg : g * g = 1) : g * ePlus g = ePlus g := by
  have h : g * ePlus g = ⅟2 * (g + g * g) := by unfold ePlus; ring
  rw [h, hg, add_comm, ePlus]

theorem g_mul_minus (hg : g * g = 1) : g * eMinus g = -eMinus g := by
  have h : g * eMinus g = ⅟2 * (g - g * g) := by unfold eMinus; ring
  rw [h, hg, eMinus]; ring

end Idempotents

/-- Inverse `C₂` Fourier transform: `f₀ = (A₊ + A₋)/2` and `f₁ = (A₊ − A₋)/2`. -/
theorem inv_fourier (f₀ f₁ : ℚ) :
    f₀ = ((f₀ + f₁) + (f₀ - f₁)) / 2 ∧ f₁ = ((f₀ + f₁) - (f₀ - f₁)) / 2 := by
  constructor <;> ring

/-- The principal form `x² + 5y²`. -/
def Q0 (x y : ℤ) : ℤ := x ^ 2 + 5 * y ^ 2

/-- The nonprincipal form `2x² + 2xy + 3y²`. -/
def Q1 (x y : ℤ) : ℤ := 2 * x ^ 2 + 2 * x * y + 3 * y ^ 2

theorem sol_bound_Q0 {x y n : ℤ} (h : Q0 x y = n) : |x| ≤ n ∧ |y| ≤ n := by
  unfold Q0 at h
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1),
    sq_nonneg (y - 1), sq_nonneg (y + 1), sq_nonneg x, sq_nonneg y]

theorem sol_bound_Q1 {x y n : ℤ} (h : Q1 x y = n) : |x| ≤ n ∧ |y| ≤ n := by
  unfold Q1 at h
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1),
    sq_nonneg (y - 1), sq_nonneg (y + 1), sq_nonneg (x + y), sq_nonneg x, sq_nonneg y]

/-- Number of `(x, y)` in the box `[−n, n]²` with `Q(x, y) = n`, enumerated as
`x = i − n`, `y = j − n` with `i, j < 2n + 1`. By `sol_bound_Q0` and `sol_bound_Q1` this is the
full representation number for `Q0` and `Q1`. -/
def rBox (Q : ℤ → ℤ → ℤ) (n : ℕ) : ℕ :=
  ((Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1)).filter
    (fun p => Q ((p.1 : ℤ) - n) ((p.2 : ℤ) - n) = n)).card

/-- `f_j = r_j / 2` (two units `±1` in `ℚ(√−5)`). -/
def f0 (n : ℕ) : ℤ := (rBox Q0 n : ℤ) / 2

def f1 (n : ℕ) : ℤ := (rBox Q1 n : ℤ) / 2

def Aplus (n : ℕ) : ℤ := f0 n + f1 n

def Aminus (n : ℕ) : ℤ := f0 n - f1 n

lemma rBox_Q0_2 : rBox Q0 2 = 0 := by decide
lemma rBox_Q0_3 : rBox Q0 3 = 0 := by decide
lemma rBox_Q0_6 : rBox Q0 6 = 4 := by decide
lemma rBox_Q1_2 : rBox Q1 2 = 2 := by decide
lemma rBox_Q1_3 : rBox Q1 3 = 4 := by decide
lemma rBox_Q1_6 : rBox Q1 6 = 0 := by decide

/-- `f₀` is not multiplicative: `f₀(2) f₀(3) = 0 ≠ 2 = f₀(6)`. -/
theorem f0_not_mult : f0 2 = 0 ∧ f0 3 = 0 ∧ f0 6 = 2 ∧ f0 2 * f0 3 ≠ f0 6 := by
  simp [f0, rBox_Q0_2, rBox_Q0_3, rBox_Q0_6]

theorem Aplus_mult_2_3 : Aplus 2 = 1 ∧ Aplus 3 = 2 ∧ Aplus 6 = 2 ∧ Aplus 2 * Aplus 3 = Aplus 6 := by
  simp [Aplus, f0, f1, rBox_Q0_2, rBox_Q0_3, rBox_Q0_6, rBox_Q1_2, rBox_Q1_3, rBox_Q1_6]

theorem Aminus_mult_2_3 :
    Aminus 2 = -1 ∧ Aminus 3 = -2 ∧ Aminus 6 = 2 ∧ Aminus 2 * Aminus 3 = Aminus 6 := by
  simp [Aminus, f0, f1, rBox_Q0_2, rBox_Q0_3, rBox_Q0_6, rBox_Q1_2, rBox_Q1_3, rBox_Q1_6]

end GppC2ClassCharacter
