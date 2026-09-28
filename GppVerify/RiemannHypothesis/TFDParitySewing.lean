import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# TFD boundary Cayley transform and parity determinants

Source: Codex, GPPDiscovery2 branch `codex/discovery-workbench`,
`research/2026-09-27_tfd_boundary_cayley_parity_sewing.md` §§1–3 (commit `47b7599`); formalized
here 2026-09-28.

For the interval equation `-f'' + q² f = 0` of length `ℓ`, the normalized Dirichlet-to-Neumann
matrix is `Q = [[coth a, -csch a], [-csch a, coth a]]` with `a = qℓ`, and the TFD covariance is
`Γ = Q⁻¹/(2q)`. Everything is rational in the attenuation `x = e^{-a} ∈ (0,1)`:
`coth a = (1+x²)/(1-x²)`, `csch a = 2x/(1-x²)` (`coth_eq`, `csch_eq`). With `S` the sheet exchange
`[[0,1],[1,0]]`:

* `Q_mul` / `cayley_Q`: `Q (I + xS) = I - xS`, i.e. `Q = (I - xS)(I + xS)⁻¹`, and
  `(I - Q) = xS (I + Q)`, i.e. the Cayley transform of the precision is the attenuated exchange
  `xS` (note eq. in §1);
* `Q_inv`: `Q⁻¹ = [[coth a, csch a], [csch a, coth a]]`;
* `Γ` on the parity vectors `(1, ±1)`: eigenvalues `(1/2q)(1+x)/(1-x)` and `(1/2q)(1-x)/(1+x)`,
  i.e. `coth(a/2)/(2q)` and `tanh(a/2)/(2q)`;
* §3 currents: `qΓ₊ - 1/2 = x/(1-x)`, `qΓ₋ - 1/2 = -x/(1+x)`, `q Tr Γ - 1 = 2x²/(1-x²)` (twice the
  normal covariance), `(q/2)(Γ₊ - Γ₋) = x/(1-x²)` (the anomalous covariance);
* §4 Schur complement: `Γ₀₀ - Γ₀₁ Γ₁₁⁻¹ Γ₁₀ = (1/2q)(1-x²)/(1+x²) = tanh(a)/(2q)`;
* §2 determinants: `det(I - xS) = 1 - x²` with parity factors `1 - x` and `1 + x`, and for a
  finite family of attenuations `x_p` the block-diagonal exchange has
  `det(I - ⊕ x_p S) = ∏ (1 - x_p²)`; `Tr (xS)^m = 0` for odd `m` and `2 x^m` for even `m`.

With `ℓ_p = (log p)/2` and `q = 2s` one has `x_p = p^{-s}`, so these are the local factors the
note assembles into `ζ(s)`, `ζ(2s)/ζ(s)` and `ζ(2s)`.

## Not formalized here

The Mittag-Leffler (Stieltjes) expansion of `tanh(ℓ√v)/(2√v)` in §4, the global Euler-product
identities for `Re s > 1`, and §5's `arctanh` split of `log ζ` are not formalized. All of the
above is exact local algebra and is not a step that proves RH.
-/

open Matrix

namespace GppTFDParitySewing

/-- The sheet exchange `S = [[0,1],[1,0]]`. -/
def S : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- `coth a` in the attenuation variable. -/
noncomputable def cothX (x : ℝ) : ℝ := (1 + x ^ 2) / (1 - x ^ 2)

/-- `csch a` in the attenuation variable. -/
noncomputable def cschX (x : ℝ) : ℝ := 2 * x / (1 - x ^ 2)

/-- The normalized DtN matrix `Q = [[coth, -csch], [-csch, coth]]`. -/
noncomputable def Q (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cothX x, -cschX x; -cschX x, cothX x]

/-- The TFD covariance `Γ = Q⁻¹/(2q)`, written out. -/
noncomputable def Γ (q x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / (2 * q)) • !![cothX x, cschX x; cschX x, cothX x]

section Hyperbolic

lemma coth_eq (a : ℝ) (ha : 0 < a) :
    Real.cosh a / Real.sinh a = cothX (Real.exp (-a)) := by
  have hs : Real.sinh a ≠ 0 := (Real.sinh_pos_iff.mpr ha).ne'
  have hx : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
  have hd : 1 - Real.exp (-a) ^ 2 ≠ 0 := by
    have : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have : 0 < Real.exp (-a) := Real.exp_pos _
    nlinarith
  unfold cothX
  rw [div_eq_div_iff hs hd, Real.cosh_eq, Real.sinh_eq]
  have ea : Real.exp a = 1 / Real.exp (-a) := by rw [Real.exp_neg, one_div, inv_inv]
  rw [ea]
  field_simp

lemma csch_eq (a : ℝ) (ha : 0 < a) :
    1 / Real.sinh a = cschX (Real.exp (-a)) := by
  have hs : Real.sinh a ≠ 0 := (Real.sinh_pos_iff.mpr ha).ne'
  have hd : 1 - Real.exp (-a) ^ 2 ≠ 0 := by
    have : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have : 0 < Real.exp (-a) := Real.exp_pos _
    nlinarith
  unfold cschX
  rw [div_eq_div_iff hs hd, Real.sinh_eq]
  have ea : Real.exp a = 1 / Real.exp (-a) := by rw [Real.exp_neg, one_div, inv_inv]
  rw [ea]
  field_simp

lemma tanh_eq (a : ℝ) :
    Real.tanh a = (1 - Real.exp (-a) ^ 2) / (1 + Real.exp (-a) ^ 2) := by
  have hc : Real.cosh a ≠ 0 := (Real.cosh_pos a).ne'
  have hd : 1 + Real.exp (-a) ^ 2 ≠ 0 := by positivity
  rw [Real.tanh_eq_sinh_div_cosh, div_eq_div_iff hc hd, Real.cosh_eq, Real.sinh_eq]
  have ea : Real.exp a = 1 / Real.exp (-a) := by rw [Real.exp_neg, one_div, inv_inv]
  rw [ea]
  have : Real.exp (-a) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

end Hyperbolic

variable {x : ℝ}

lemma one_sub_sq_ne (hx0 : 0 ≤ x) (hx1 : x < 1) : 1 - x ^ 2 ≠ 0 := by nlinarith

/-- `Q (I + xS) = I - xS`, i.e. `Q = (I - xS)(I + xS)⁻¹`. -/
theorem Q_mul (hx0 : 0 ≤ x) (hx1 : x < 1) : Q x * (1 + x • S) = 1 - x • S := by
  have hd := one_sub_sq_ne hx0 hx1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Q, S, cothX, cschX, Matrix.mul_apply, Fin.sum_univ_two] <;>
    (try field_simp) <;> (try ring)

/-- **Cayley transform of the precision.** `I - Q = xS (I + Q)`, i.e. `(I - Q)(I + Q)⁻¹ = xS`. -/
theorem cayley_Q (hx0 : 0 ≤ x) (hx1 : x < 1) : 1 - Q x = (x • S) * (1 + Q x) := by
  have hd := one_sub_sq_ne hx0 hx1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Q, S, cothX, cschX, Matrix.mul_apply, Fin.sum_univ_two] <;>
    (try field_simp) <;> (try ring)

/-- `Q⁻¹ = [[coth, csch], [csch, coth]]` (via `coth² - csch² = 1`). -/
theorem Q_inv (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Q x * !![cothX x, cschX x; cschX x, cothX x] = 1 := by
  have hd := one_sub_sq_ne hx0 hx1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Q, cothX, cschX, Matrix.mul_apply, Fin.sum_univ_two] <;>
    (try field_simp) <;> (try ring)

/-- `Γ` on the symmetric vector `(1,1)`: eigenvalue `(1/2q)(1+x)/(1-x)` (`= coth(a/2)/(2q)`). -/
theorem Γ_symm (q : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Γ q x *ᵥ ![1, 1] = ((1 / (2 * q)) * ((1 + x) / (1 - x))) • ![1, 1] := by
  have hd := one_sub_sq_ne hx0 hx1
  have h1 : 1 - x ≠ 0 := by linarith
  ext i
  fin_cases i <;> simp [Γ, cothX, cschX, mulVec, dotProduct, Fin.sum_univ_two] <;>
    (try field_simp) <;> (try ring)

/-- `Γ` on the antisymmetric vector `(1,-1)`: eigenvalue `(1/2q)(1-x)/(1+x)` (`= tanh(a/2)/(2q)`). -/
theorem Γ_anti (q : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Γ q x *ᵥ ![1, -1] = ((1 / (2 * q)) * ((1 - x) / (1 + x))) • ![1, -1] := by
  have hd := one_sub_sq_ne hx0 hx1
  have h1 : 1 + x ≠ 0 := by linarith
  ext i
  fin_cases i <;> simp [Γ, cothX, cschX, mulVec, dotProduct, Fin.sum_univ_two] <;>
    (try field_simp) <;> (try ring)

/-- §3 currents, from the parity eigenvalues `Γ₊ = (1/2q)(1+x)/(1-x)`, `Γ₋ = (1/2q)(1-x)/(1+x)`. -/
theorem parity_currents (q : ℝ) (hq : q ≠ 0) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    let Γp := (1 / (2 * q)) * ((1 + x) / (1 - x))
    let Γm := (1 / (2 * q)) * ((1 - x) / (1 + x))
    q * Γp - 1 / 2 = x / (1 - x) ∧ q * Γm - 1 / 2 = -(x / (1 + x)) ∧
      q * (Γ q x).trace - 1 = 2 * (x ^ 2 / (1 - x ^ 2)) ∧
      q / 2 * (Γp - Γm) = x / (1 - x ^ 2) := by
  have hd := one_sub_sq_ne hx0 hx1
  have h1 : 1 - x ≠ 0 := by linarith
  have h2 : 1 + x ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp; ring
  · field_simp; ring
  · simp [Γ, Matrix.trace, Fin.sum_univ_two, cothX]
    field_simp; ring
  · field_simp; ring

/-- §4 Schur complement: `Γ₀₀ - Γ₀₁ Γ₁₁⁻¹ Γ₁₀ = (1/2q)(1-x²)/(1+x²)` (`= tanh(a)/(2q)`). -/
theorem schur_complement (q : ℝ) (hq : q ≠ 0) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Γ q x 0 0 - Γ q x 0 1 * (Γ q x 1 1)⁻¹ * Γ q x 1 0 =
      (1 / (2 * q)) * ((1 - x ^ 2) / (1 + x ^ 2)) := by
  have hd := one_sub_sq_ne hx0 hx1
  have hp : 1 + x ^ 2 ≠ 0 := by positivity
  simp [Γ, cothX, cschX]
  field_simp
  ring

/-- §2, one prime: `det(I - xS) = 1 - x²`, with parity factors `(1 - x)(1 + x)`. -/
theorem det_one_sub_exchange (x : ℝ) : (1 - x • S).det = (1 - x) * (1 + x) := by
  simp [S, Matrix.det_fin_two]
  ring

/-- §2, finite prime set: `det(I - ⊕_p x_p S) = ∏_p (1 - x_p²)`. -/
theorem det_block_exchange {ι : Type*} [Fintype ι] [DecidableEq ι] (xs : ι → ℝ) :
    (1 - blockDiagonal (fun p => xs p • S)).det = ∏ p, (1 - xs p ^ 2) := by
  have : (1 : Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ) - blockDiagonal (fun p => xs p • S) =
      blockDiagonal (fun p => 1 - xs p • S) := by
    rw [← blockDiagonal_one, ← blockDiagonal_sub]
    rfl
  rw [this, det_blockDiagonal]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  rw [det_one_sub_exchange]
  ring

/-- `Tr (xS)^m = 0` for odd `m` and `2 x^m` for even `m`. -/
theorem trace_exchange_pow (x : ℝ) (m : ℕ) :
    ((x • S) ^ m).trace = if Even m then 2 * x ^ m else 0 := by
  have hS2 : S * S = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [S, Matrix.mul_apply, Fin.sum_univ_two]
  rw [smul_pow, trace_smul]
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hSe : S ^ (k + k) = 1 := by rw [← two_mul, pow_mul, sq, hS2, one_pow]
    rw [if_pos ⟨k, rfl⟩, hSe]
    simp [Matrix.trace]
    ring
  · have hSo : S ^ (2 * k + 1) = S := by rw [pow_succ, pow_mul, sq, hS2, one_pow, one_mul]
    rw [if_neg (Nat.not_even_iff_odd.mpr ⟨k, rfl⟩), hSo]
    simp [S, Matrix.trace, Fin.sum_univ_two]

end GppTFDParitySewing
