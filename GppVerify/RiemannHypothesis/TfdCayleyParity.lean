import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The TFD boundary Cayley transform, parity determinants, and the Schur complement

Source: Codex, GPPDiscovery2 `research/2026-09-27_tfd_boundary_cayley_parity_sewing.md`, §§1–5.

For the interval equation `−f'' + q² f = 0` of length `ℓ` put `u = qℓ`, `x = e^{−u}`, and
`Q = Λ/q = [[coth u, −csch u], [−csch u, coth u]]` (`Qmat`), `S = [[0,1],[1,0]]`.

* `cayley_Q`, `det_one_add_Q_ne`: `I − Q = (x S)(I + Q)` and `I + Q` is invertible, i.e.
  `(I − Q)(I + Q)^{-1} = x S`: the Cayley transform of the normalized TFD precision is the attenuated
  sheet-exchange transfer;
* `parity_eigen_plus`, `parity_eigen_minus`: `Q` has eigenvalue `(1−x)/(1+x)` on `(1,1)` and
  `(1+x)/(1−x)` on `(1,−1)`;
* `det_full`, `prod_parity`: `det(I − xS) = (1 − x)(1 + x) = 1 − x²`, where `1 ∓ x` are the two parity
  factors (the eigenvalues of `xS` are `±x`), and over a finite prime set
  `Π(1 − x_p) · Π(1 + x_p) = Π(1 − x_p²)` (the full double sees `ζ(2s)`, not `ζ(s)`);
* `trace_pow`: `Tr (x S)^m = 0` for odd `m` and `2 x^m` for even `m`;
* `cov_plus_exp`, `cov_minus_exp`, `normal_sector`, `anomalous_sector`: with `Γ_± = (coth u ± csch u)/(2q)`,
  `q Γ_+ − ½ = x/(1−x)`, `q Γ_- − ½ = −x/(1+x)`, `q(Γ_+ + Γ_-) − 1 = 2x²/(1−x²)` and
  `(q/2)(Γ_+ − Γ_-) = x/(1−x²)`;
* `schur_complement`: `Γ₀₀ − Γ₀₁ Γ₁₁^{-1} Γ₁₀ = tanh(u)/(2q)`;
* `neglog_decomp`: for `|x| < 1`, `−log(1 − x) = −½ log(1 − x²) + artanh x`, the even/odd split of
  the Euler factor.

## Checks and scope

All claims check. **Not formalized:** the Dirichlet-to-Neumann matrix itself from the interval ODE
(`PrimeEdgeDtn` has the edge composition), the positive spectral expansion
`tanh(ℓ√v)/(2√v) = (1/ℓ) Σ 1/(v + ((n+½)π/ℓ)²)`, the Euler-product statements
`det(I − T_+)^{-1} = ζ(s)` etc. (they need the zeta Euler product at the level of determinants),
and the convergence of `H_odd` for `Re s > 1/3`. No RH claim.
-/

open Matrix Real

namespace GppTfdCayley

/-- `Q = Λ/q`. -/
noncomputable def Qmat (u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh u / Real.sinh u, -(1 / Real.sinh u); -(1 / Real.sinh u), Real.cosh u / Real.sinh u]

/-- The sheet exchange `S`. -/
def Smat : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

private theorem sinh_pos' (u : ℝ) (hu : 0 < u) : 0 < Real.sinh u := by
  rw [Real.sinh_eq]
  have := Real.exp_lt_exp.mpr (by linarith : -u < u)
  linarith

private theorem cosh_add_sinh (u : ℝ) : Real.cosh u + Real.sinh u = Real.exp u := by
  rw [Real.cosh_eq, Real.sinh_eq]; ring

private theorem cosh_sub_sinh (u : ℝ) : Real.cosh u - Real.sinh u = Real.exp (-u) := by
  rw [Real.cosh_eq, Real.sinh_eq]; ring

/-- Two key scalar identities: `coth u − 1 = x · csch u · …` in the form used below. -/
private theorem scalar_ids (u : ℝ) (hu : 0 < u) :
    1 - Real.cosh u / Real.sinh u = -(Real.exp (-u) * (1 / Real.sinh u)) ∧
      1 / Real.sinh u = Real.exp (-u) * (1 + Real.cosh u / Real.sinh u) := by
  have hs := (sinh_pos' u hu).ne'
  have h1 := cosh_sub_sinh u
  have h2 := cosh_add_sinh u
  have h3 : Real.exp (-u) * (Real.cosh u + Real.sinh u) = 1 := by
    rw [h2, ← Real.exp_add]; simp
  constructor
  · field_simp
    linarith
  · field_simp
    nlinarith [h3]

/-- **Cayley transform of the TFD precision is the attenuated exchange.** -/
theorem cayley_Q (u : ℝ) (hu : 0 < u) :
    1 - Qmat u = (Real.exp (-u) • Smat) * (1 + Qmat u) := by
  obtain ⟨h1, h2⟩ := scalar_ids u hu
  simp only [one_div] at h1 h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Qmat, Smat, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linarith

theorem det_one_add_Q_ne (u : ℝ) (hu : 0 < u) : (1 + Qmat u).det ≠ 0 := by
  have hs := sinh_pos' u hu
  rw [show (1 + Qmat u) = !![1 + Real.cosh u / Real.sinh u, -(1 / Real.sinh u);
    -(1 / Real.sinh u), 1 + Real.cosh u / Real.sinh u] by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Qmat], Matrix.det_fin_two_of]
  have h : (1 + Real.cosh u / Real.sinh u) * (1 + Real.cosh u / Real.sinh u) -
      -(1 / Real.sinh u) * -(1 / Real.sinh u) = 2 * Real.exp u / Real.sinh u := by
    rw [← cosh_add_sinh u]
    field_simp
    nlinarith [Real.cosh_sq u]
  rw [h]
  positivity

/-- Eigenvalue on the symmetric endpoint vector. -/
theorem parity_eigen_plus (u : ℝ) (hu : 0 < u) :
    Real.cosh u / Real.sinh u - 1 / Real.sinh u = (1 - Real.exp (-u)) / (1 + Real.exp (-u)) := by
  have hs := (sinh_pos' u hu).ne'
  have hc := Real.cosh_eq u
  have hsn := Real.sinh_eq u
  have hE : (0 : ℝ) < Real.exp (-u) := Real.exp_pos _
  have hE' : Real.exp u = (Real.exp (-u))⁻¹ := by rw [Real.exp_neg, inv_inv]
  rw [← sub_div, div_eq_div_iff hs (by positivity)]
  rw [hc, hsn, hE', Real.exp_neg]
  field_simp
  ring

/-- Eigenvalue on the antisymmetric endpoint vector. -/
theorem parity_eigen_minus (u : ℝ) (hu : 0 < u) :
    Real.cosh u / Real.sinh u + 1 / Real.sinh u = (1 + Real.exp (-u)) / (1 - Real.exp (-u)) := by
  have hs := (sinh_pos' u hu).ne'
  have hc := Real.cosh_eq u
  have hsn := Real.sinh_eq u
  have hlt : Real.exp (-u) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  rw [← add_div, div_eq_div_iff hs (by linarith)]
  rw [hc, hsn, Real.exp_neg]
  have hE : (Real.exp u)⁻¹ < 1 := by rw [← Real.exp_neg]; exact hlt
  have hne : 1 - (Real.exp u)⁻¹ ≠ 0 := by linarith
  field_simp
  ring

/-! ### Parity determinants -/

/-- The full double: `det(I − xS) = 1 − x²`, which is the product of the two parity factors. -/
theorem det_full (x : ℝ) : (1 - x • Smat).det = (1 - x) * (1 + x) := by
  rw [Smat, show (1 - x • !![(0 : ℝ), 1; 1, 0]) = !![1, -x; -x, 1] by
    ext i j; fin_cases i <;> fin_cases j <;> simp, Matrix.det_fin_two_of]
  ring

/-- Over a finite prime set the parity products multiply to the full double product. -/
theorem prod_parity {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    (∏ i ∈ s, (1 - x i)) * (∏ i ∈ s, (1 + x i)) = ∏ i ∈ s, (1 - x i ^ 2) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => by ring

/-- Traces of powers of the attenuated exchange. -/
theorem trace_pow (x : ℝ) (m : ℕ) :
    ((x • Smat) ^ m).trace = if Even m then 2 * x ^ m else 0 := by
  have hS : Smat * Smat = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Smat, Matrix.mul_apply, Fin.sum_univ_two]
  rw [smul_pow]
  rcases Nat.even_or_odd m with he | ho
  · obtain ⟨k, rfl⟩ := he
    have : Smat ^ (k + k) = 1 := by
      rw [← two_mul, pow_mul, pow_two, hS, one_pow]
    rw [Matrix.trace_smul, this, if_pos ⟨k, rfl⟩]
    simp [Matrix.trace_one]
    ring
  · obtain ⟨k, rfl⟩ := ho
    have : Smat ^ (2 * k + 1) = Smat := by
      rw [pow_succ, pow_mul, pow_two, hS, one_pow, one_mul]
    rw [Matrix.trace_smul, this, if_neg (Nat.not_even_iff_odd.mpr ⟨k, rfl⟩)]
    simp [Smat, Matrix.trace_fin_two]

/-! ### Parity covariances and the current -/

theorem cov_plus (q u x : ℝ) (hq : 0 < q) (hx : x ≠ 1) (hcsum : Real.cosh u / Real.sinh u + 1 / Real.sinh u = (1 + x) / (1 - x)) :
    q * ((Real.cosh u / Real.sinh u + 1 / Real.sinh u) / (2 * q)) - 1 / 2 = x / (1 - x) := by
  rw [hcsum]
  have : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  field_simp
  ring

theorem cov_minus (q u x : ℝ) (hq : 0 < q) (hx : x ≠ -1) (hcdiff : Real.cosh u / Real.sinh u - 1 / Real.sinh u = (1 - x) / (1 + x)) :
    q * ((Real.cosh u / Real.sinh u - 1 / Real.sinh u) / (2 * q)) - 1 / 2 = -(x / (1 + x)) := by
  rw [hcdiff]
  have : 1 + x ≠ 0 := fun h => hx (by linarith)
  field_simp
  ring

/-- The symmetric-parity covariance gives `x/(1−x)` with `x = e^{−u}`. -/
theorem cov_plus_exp (q u : ℝ) (hq : 0 < q) (hu : 0 < u) :
    q * ((Real.cosh u / Real.sinh u + 1 / Real.sinh u) / (2 * q)) - 1 / 2 =
      Real.exp (-u) / (1 - Real.exp (-u)) :=
  cov_plus q u (Real.exp (-u)) hq (by
    have : Real.exp (-u) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    exact this.ne) (parity_eigen_minus u hu)

/-- The antisymmetric-parity covariance gives `−x/(1+x)` with `x = e^{−u}`. -/
theorem cov_minus_exp (q u : ℝ) (hq : 0 < q) (hu : 0 < u) :
    q * ((Real.cosh u / Real.sinh u - 1 / Real.sinh u) / (2 * q)) - 1 / 2 =
      -(Real.exp (-u) / (1 + Real.exp (-u))) :=
  cov_minus q u (Real.exp (-u)) hq (by
    have := Real.exp_pos (-u)
    linarith [this]) (parity_eigen_plus u hu)

theorem normal_sector (x : ℝ) (hx : |x| < 1) :
    ((1 + x) / (1 - x) + (1 - x) / (1 + x)) / 2 - 1 = 2 * x ^ 2 / (1 - x ^ 2) := by
  have h1 : 1 - x ≠ 0 := by linarith [abs_lt.mp hx]
  have h2 : 1 + x ≠ 0 := by linarith [abs_lt.mp hx]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [abs_lt.mp hx, sq_abs x]
  field_simp
  ring

theorem anomalous_sector (x : ℝ) (hx : |x| < 1) :
    ((1 + x) / (1 - x) - (1 - x) / (1 + x)) / 4 = x / (1 - x ^ 2) := by
  have h1 : 1 - x ≠ 0 := by linarith [abs_lt.mp hx]
  have h2 : 1 + x ≠ 0 := by linarith [abs_lt.mp hx]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [abs_lt.mp hx, sq_abs x]
  field_simp
  ring

/-! ### The Schur complement -/

/-- `Γ₀₀ − Γ₀₁ Γ₁₁^{-1} Γ₁₀ = tanh(u)/(2q)`, with `Γ = (1/(2q)) [[coth, csch],[csch, coth]]`. -/
theorem schur_complement (q u : ℝ) (hq : 0 < q) (hu : 0 < u) :
    Real.cosh u / Real.sinh u / (2 * q) -
        (1 / Real.sinh u / (2 * q)) * (Real.cosh u / Real.sinh u / (2 * q))⁻¹ *
          (1 / Real.sinh u / (2 * q)) = Real.tanh u / (2 * q) := by
  have hs := (sinh_pos' u hu).ne'
  have hc : Real.cosh u ≠ 0 := (Real.cosh_pos u).ne'
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  nlinarith [Real.cosh_sq u]

/-! ### The even/odd split of the Euler factor -/

/-- `−log(1 − x) = −½ log(1 − x²) + artanh x`. -/
theorem neglog_decomp (x : ℝ) (hx : |x| < 1) :
    -Real.log (1 - x) = -(1 / 2) * Real.log (1 - x ^ 2) + Real.artanh x := by
  have hm : x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨(abs_lt.mp hx).1, (abs_lt.mp hx).2⟩
  have h1 : 0 < 1 - x := by linarith [abs_lt.mp hx]
  have h2 : 0 < 1 + x := by linarith [abs_lt.mp hx]
  rw [Real.artanh_eq_half_log ⟨hm.1.le, hm.2.le⟩, show 1 - x ^ 2 = (1 - x) * (1 + x) by ring,
    Real.log_mul h1.ne' h2.ne', Real.log_div h2.ne' h1.ne']
  ring

end GppTfdCayley
