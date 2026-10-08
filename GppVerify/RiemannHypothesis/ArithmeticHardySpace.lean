import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The arithmetic Hardy space: coherent vectors in `ℓ²(ℕ₊)`, their Gram kernel `ζ(1 + z + w̄)`, and the
prime annihilation operators

For `Re z > 0` let `e_z ∈ ℓ²(ℕ)` be the vector `e_z(n) = n^{-1/2-z}` (`e_z(0) = 0`). It is
square-summable exactly because `Σ n^{-1-2 Re z} < ∞`.

* `coherent_inner`: `⟨e_w, e_z⟩ = ζ(1 + z + w̄)` — the Dirichlet–Hardy kernel is the Gram kernel of the
  vectors `e_z`, so it is positive semidefinite (`gram_nonneg`), i.e. the Hilbert space exists and is
  `ℓ²`, with no appeal to a completion;
* `kernel_dilation_invariant`: `ζ(1 + (z+it) + conj(w+it)) = ζ(1 + z + w̄)`, and `dilate_coherent`:
  the diagonal unitary `D_t f(n) = n^{-it} f(n)` sends `e_z` to `e_{z+it}`;
* `norm_sq_coherent`: `‖e_z‖² = ζ(1 + 2 Re z)`;
* `annihilate_coherent`: for the Hecke-type operator `(A_p f)(n) = f(p n)`, `A_p e_z = p^{-1/2-z} e_z` —
  the `e_z` are coherent states for *every* prime annihilation operator at once, with eigenvalue the
  Euler-factor variable `p^{-s}`, `s = 1/2 + z`;
* `annihilate_create`, `annihilate_comm`, `dilate_annihilate`: the relations `A_p S_p = 1` (with
  `(S_p f)(n) = f(n/p)` on multiples of `p`), `A_p A_q = A_q A_p`, and
  `A_p D_t = p^{-it} D_t A_p` (dilation covariance with charge `log p`).

## Checks and scope

All claims check. This constructs the *right-sheet* state space only: coherent vectors exist for
`Re z > 0` (`Re s > 1/2`); `e_z ∉ ℓ²` for `Re z ≤ 0`. The other half of the critical strip is reached
through the functional equation, not through vectors of this space, and nothing here says where the
zeros of `ζ` sit. The kernel is the `SU(1,1)` Szegő kernel only at leading order at the boundary pole
(`CayleyHardyKernel`, `SU11KernelCovariance`); the regular part is the arithmetic deformation. Not
formalized: the full Bost–Connes `C*`-algebra, the KMS states as states on it, and the Fock-space
factorization `ℓ²(ℕ₊) ≅ ⊗_p ℓ²(ℕ₀)`. No RH claim.
-/

open Complex ComplexConjugate

namespace GppArithmeticHardy

/-- `log n` as a complex number. -/
noncomputable def logC (n : ℕ) : ℂ := ((Real.log (n : ℝ) : ℝ) : ℂ)

/-- The coherent sequence `e_z(n) = n^{-1/2-z}` (and `0` at `n = 0`). -/
noncomputable def coh (z : ℂ) (n : ℕ) : ℂ :=
  (((Real.sqrt n)⁻¹ : ℝ) : ℂ) * Complex.exp (-z * logC n)

theorem coh_zero (z : ℂ) : coh z 0 = 0 := by simp [coh]

theorem norm_sq_coh (z : ℂ) (n : ℕ) (hn : 1 ≤ n) :
    ‖coh z n‖ ^ 2 = ((n : ℝ) ^ (-(1 + 2 * z.re))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold coh logC
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.norm_exp]
  have hre : (-z * ((Real.log (n : ℝ) : ℝ) : ℂ)).re = -z.re * Real.log n := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have e1 : (n : ℝ)⁻¹ = Real.exp (-Real.log n) := by rw [Real.exp_neg, Real.exp_log hn0]
  rw [hre, inv_pow, Real.sq_sqrt hn0.le, Real.rpow_def_of_pos hn0, e1, sq (Real.exp _),
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The general-`n` form of the norm identity (the `n = 0` term is `0`). -/
theorem norm_sq_coh' (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    ‖coh z n‖ ^ 2 = ((n : ℝ) ^ (-(1 + 2 * z.re))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h : (-(1 + 2 * z.re)) ≠ 0 := by linarith
    rw [coh_zero, norm_zero, Nat.cast_zero, Real.zero_rpow h]
    norm_num
  · exact norm_sq_coh z n hn

theorem summable_norm_sq (z : ℂ) (hz : 0 < z.re) : Summable fun n : ℕ => ‖coh z n‖ ^ 2 := by
  have h : Summable fun n : ℕ => ((n : ℝ) ^ (-(1 + 2 * z.re))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact h.congr fun n => (norm_sq_coh' z hz n).symm

/-- The coherent vector `e_z ∈ ℓ²(ℕ)`, `Re z > 0`. -/
noncomputable def cohLp (z : ℂ) (hz : 0 < z.re) : lp (fun _ : ℕ => ℂ) 2 :=
  ⟨coh z, memℓp_gen (by
    simpa [ENNReal.toReal_ofNat, Real.rpow_two] using summable_norm_sq z hz)⟩

/-- Term-wise form of the Gram kernel: `e_z(n) · conj e_w(n) = n^{-(1+z+w̄)}` for `n ≥ 1`. -/
theorem coh_mul_conj (z w : ℂ) (n : ℕ) (hn : 1 ≤ n) :
    coh z n * conj (coh w n) = 1 / (n : ℂ) ^ (1 + z + conj w) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  unfold coh logC
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_ofReal]
  rw [Complex.cpow_def_of_ne_zero hnC]
  have hlog : Complex.log (n : ℂ) = ((Real.log (n : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
  rw [hlog, one_div, ← Complex.exp_neg]
  have hs : (((Real.sqrt (n : ℝ))⁻¹ : ℝ) : ℂ) * (((Real.sqrt (n : ℝ))⁻¹ : ℝ) : ℂ) =
      Complex.exp (-((Real.log (n : ℝ) : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg,
      Real.exp_log hn0]
    congr 1
    rw [← mul_inv, Real.mul_self_sqrt hn0.le]
  calc (((Real.sqrt (n : ℝ))⁻¹ : ℝ) : ℂ) * Complex.exp (-z * ((Real.log (n : ℝ) : ℝ) : ℂ)) *
        ((((Real.sqrt (n : ℝ))⁻¹ : ℝ) : ℂ) * Complex.exp (-(starRingEnd ℂ) w * ((Real.log (n : ℝ) : ℝ) : ℂ)))
      = ((((Real.sqrt (n : ℝ))⁻¹ : ℝ) : ℂ) * (((Real.sqrt (n : ℝ))⁻¹ : ℝ) : ℂ)) *
          (Complex.exp (-z * ((Real.log (n : ℝ) : ℝ) : ℂ)) *
            Complex.exp (-(starRingEnd ℂ) w * ((Real.log (n : ℝ) : ℝ) : ℂ))) := by ring
    _ = Complex.exp (-(((Real.log (n : ℝ) : ℝ) : ℂ) * (1 + z + (starRingEnd ℂ) w))) := by
        rw [hs, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring

/-- The term identity valid for every `n` (the `n = 0` term is `0` on both sides). -/
theorem coh_mul_conj_all (z w : ℂ) (hs : 0 < (1 + z + conj w).re) (n : ℕ) :
    coh z n * conj (coh w n) = 1 / (n : ℂ) ^ (1 + z + conj w) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : (1 + z + conj w) ≠ 0 := by
      intro h; rw [h] at hs; simp at hs
    simp [coh_zero, Complex.zero_cpow h0]
  · exact coh_mul_conj z w n hn

/-- **The Gram kernel is the Dirichlet–Hardy kernel.** -/
theorem coherent_inner (z w : ℂ) (hz : 0 < z.re) (hw : 0 < w.re) :
    inner ℂ (cohLp w hw) (cohLp z hz) = riemannZeta (1 + z + conj w) := by
  have hre : 1 < (1 + z + conj w).re := by simp; linarith
  rw [zeta_eq_tsum_one_div_nat_cpow hre, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  have h := coh_mul_conj_all z w (by linarith) n
  simpa [cohLp, RCLike.inner_apply] using h

/-- Hermitian symmetry of the kernel. -/
theorem kernel_hermitian (z w : ℂ) (hz : 0 < z.re) (hw : 0 < w.re) :
    riemannZeta (1 + w + conj z) = conj (riemannZeta (1 + z + conj w)) := by
  rw [← coherent_inner z w hz hw, ← coherent_inner w z hw hz, inner_conj_symm]

/-- **Positive semidefiniteness**: the Gram form of any finite family of coherent vectors is `≥ 0`. -/
theorem gram_nonneg {ι : Type*} (S : Finset ι) (z : ι → ℂ) (hz : ∀ i, 0 < (z i).re) (c : ι → ℂ) :
    0 ≤ (∑ i ∈ S, ∑ j ∈ S, conj (c i) * c j * riemannZeta (1 + z j + conj (z i))).re := by
  have key : ∑ i ∈ S, ∑ j ∈ S, conj (c i) * c j * riemannZeta (1 + z j + conj (z i)) =
      inner ℂ (∑ i ∈ S, c i • cohLp (z i) (hz i)) (∑ j ∈ S, c j • cohLp (z j) (hz j)) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, inner_smul_right, coherent_inner (z j) (z i) (hz j) (hz i)]
    ring
  rw [key]
  exact inner_self_nonneg (𝕜 := ℂ)

/-- **The norm of a coherent vector.** -/
theorem norm_sq_cohLp (z : ℂ) (hz : 0 < z.re) :
    ‖cohLp z hz‖ ^ 2 = (riemannZeta (1 + 2 * z.re)).re := by
  have h := coherent_inner z z hz hz
  rw [inner_self_eq_norm_sq_to_K] at h
  have e : (1 + z + conj z : ℂ) = ((1 + 2 * z.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp; ring
    · simp
  rw [e] at h
  have := congrArg Complex.re h
  simpa [← Complex.ofReal_pow] using this

/-- **Dilation invariance** of the kernel: translating both labels by `it` does not change it. -/
theorem kernel_dilation_invariant (z w : ℂ) (t : ℝ) :
    riemannZeta (1 + (z + (t : ℂ) * Complex.I) + conj (w + (t : ℂ) * Complex.I)) =
      riemannZeta (1 + z + conj w) := by
  congr 1
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-! ### Prime operators on sequences -/

/-- The prime annihilation (Hecke) operator `(A_p f)(n) = f(p n)`. -/
def annihilate (p : ℕ) (f : ℕ → ℂ) : ℕ → ℂ := fun n => f (p * n)

/-- The prime creation operator `(S_p f)(n) = f(n/p)` on multiples of `p`, `0` otherwise. -/
noncomputable def create (p : ℕ) (f : ℕ → ℂ) : ℕ → ℂ := fun n => if p ∣ n then f (n / p) else 0

/-- The dilation `(D_t f)(n) = n^{-it} f(n)` (diagonal, unimodular on `n ≥ 1`). -/
noncomputable def dilate (t : ℝ) (f : ℕ → ℂ) : ℕ → ℂ :=
  fun n => Complex.exp (-((t : ℂ) * Complex.I) * logC n) * f n

/-- `A_p S_p = 1`: `S_p` is a right inverse of `A_p`, i.e. `S_p` is an isometric shift. -/
theorem annihilate_create (p : ℕ) (hp : 0 < p) (f : ℕ → ℂ) : annihilate p (create p f) = f := by
  funext n
  simp [annihilate, create, Nat.mul_div_cancel_left n hp]

/-- The annihilation operators for distinct (indeed all) primes commute. -/
theorem annihilate_comm (p q : ℕ) (f : ℕ → ℂ) :
    annihilate p (annihilate q f) = annihilate q (annihilate p f) := by
  funext n
  simp only [annihilate]
  rw [mul_left_comm]

/-- The eigenvalue of `A_p` on `e_z`: `p^{-1/2} e^{-z log p}`, the Euler-factor variable `p^{-s}`
(`s = 1/2 + z`). -/
noncomputable def eigenvalue (p : ℕ) (z : ℂ) : ℂ :=
  (((Real.sqrt p)⁻¹ : ℝ) : ℂ) * Complex.exp (-z * logC p)

/-- **Coherent states for every prime annihilation operator.** `A_p e_z = p^{-1/2-z} e_z`. -/
theorem annihilate_coherent (p : ℕ) (hp : 0 < p) (z : ℂ) :
    annihilate p (coh z) = fun n => eigenvalue p z * coh z n := by
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [annihilate, coh_zero]
  · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    unfold annihilate eigenvalue coh logC
    rw [Nat.cast_mul, Real.log_mul hp0.ne' hn0.ne', Real.sqrt_mul hp0.le, mul_inv,
      Complex.ofReal_mul, Complex.ofReal_add, mul_add, Complex.exp_add]
    ring

/-- The dilation sends `e_z` to `e_{z + it}`. -/
theorem dilate_coherent (t : ℝ) (z : ℂ) : dilate t (coh z) = coh (z + (t : ℂ) * Complex.I) := by
  funext n
  unfold dilate coh
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

/-- **Dilation covariance of the annihilation operators.** On sequences vanishing at `0`,
`A_p D_t = p^{-it} D_t A_p`: the prime `p` carries dilation charge `log p`. -/
theorem dilate_annihilate (p : ℕ) (hp : 0 < p) (t : ℝ) (f : ℕ → ℂ) (hf : f 0 = 0) :
    annihilate p (dilate t f) =
      fun n => Complex.exp (-((t : ℂ) * Complex.I) * logC p) * dilate t (annihilate p f) n := by
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [annihilate, dilate, hf]
  · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    unfold annihilate dilate logC
    rw [Nat.cast_mul, Real.log_mul hp0.ne' hn0.ne', Complex.ofReal_add, mul_add, Complex.exp_add]
    ring

end GppArithmeticHardy
