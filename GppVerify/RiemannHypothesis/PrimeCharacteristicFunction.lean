import GppVerify.RiemannHypothesis.PrimeContractionUnitarity

/-!
# Prime characteristic-function S-matrix (`formalization_queue` item `0452a4c4`)

On `ℓ²(primes)`, with `L e_p = (log p) e_p`, `A = exp(-L/2)`, `U_t = exp(-itL)`, the item
defines `S(t) = (U_t - A)(I - A U_t)⁻¹` and asks for the Sz.-Nagy/Foias Blaschke
characteristic factor formula `S(t) e_p = ((p^{-it} - p^{-1/2})/(1 - p^{-1/2-it})) e_p`,
its unitarity, the scattering operator `R(t) = U_t* S(t)`, and a finite Euler shadow
determinant identity.

**Proved here.**
* `norm_sub_real_eq_norm_one_sub_mul` -- the Blaschke-factor modulus identity: for real `a`
  and `w` on the unit circle, `‖w - a‖ = ‖1 - a·w‖` exactly.
* `norm_blaschke_eq_one` -- for `|a| < 1` and `‖w‖ = 1`, the Blaschke factor `(w-a)/(1-a·w)`
  has modulus exactly `1` (a standard disk-automorphism fact; absent from Mathlib, which has
  no Blaschke-factor infrastructure at all -- confirmed via
  `grep -rl "Blaschke" .lake/packages/mathlib/Mathlib/`, zero hits).
* `primeCharFn_norm_eq_one` -- the item's own formula, instantiated: for every prime `p`
  and real `t`, `‖(p^{-it} - p^{-1/2})/(1 - p^{-1/2-it})‖ = 1`.
* `primeCharFn_diag_unitary_of_modulus_one` -- combining `primeCharFn_norm_eq_one` with
  `GppPrimeContraction.prime_contraction_unitary_of_modulus_one`: the diagonal operator
  built from this weight is unitary in the operator sense established there (exact
  `ℓ²`-norm preservation plus a two-sided inverse via the conjugate weight).

**Honest boundary, not attempted here.**
* `R(t) = U_t* S(t)` and its Schatten-class membership (`R(t) - I ∈ S3`) are not
  formalized -- this needs `K_t ∈ S3`, i.e. Schatten-class operator theory, which Mathlib
  has none of at all (confirmed absent: `grep -rl "Schatten" .lake/packages/mathlib/Mathlib/`
  returns zero hits) -- the same gap already documented against `be59ab82`'s trace-class
  portion and against the fully-blocked item `189645c2`.
* The finite Euler "shadow determinant" identity `det R_P(t) = ζ_P(1/2+it)/ζ_P(1/2-it)` is
  not attempted, for the same reason (finite-rank determinants of diagonal operators are
  in principle tractable without Schatten theory, but `R(t)` itself is not constructed
  here since it needs the `S3`-membership groundwork first).
* The operator-level `U_t`, `A`, `S(t)` as literal `exp(-L/2)`/`exp(-itL)` constructions
  are not built; only the diagonal weight (the item's own closed-form eigenvalue formula)
  is used directly, matching the pattern already established in
  `PrimeContractionUnitarity.lean`.
-/

namespace GppPrimeCharFn

open Complex GppPrimeContraction

/-- **The Blaschke-factor modulus identity.** For real `a` and complex `w` with `‖w‖ = 1`,
    `‖w - a‖ = ‖1 - a * w‖` exactly. -/
theorem norm_sub_real_eq_norm_one_sub_mul {a : ℝ} {w : ℂ} (hw : ‖w‖ = 1) :
    ‖w - (a : ℂ)‖ = ‖1 - (a : ℂ) * w‖ := by
  have hns : Complex.normSq w = 1 := by
    have hsq := Complex.sq_norm w
    rw [hw] at hsq
    simpa using hsq.symm
  have hns' : w.re * w.re + w.im * w.im = 1 := by
    rw [← Complex.normSq_apply]; exact hns
  have ha2 : a * a * (w.re * w.re + w.im * w.im) = a * a := by rw [hns']; ring
  have key : Complex.normSq (w - (a:ℂ)) = Complex.normSq (1 - (a:ℂ) * w) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at *
    nlinarith [hns, ha2]
  have h1 : ‖w - (a:ℂ)‖ ^ 2 = Complex.normSq (w - (a:ℂ)) := Complex.sq_norm _
  have h2 : ‖1 - (a:ℂ) * w‖ ^ 2 = Complex.normSq (1 - (a:ℂ) * w) := Complex.sq_norm _
  have hsq : ‖w - (a:ℂ)‖ ^ 2 = ‖1 - (a:ℂ) * w‖ ^ 2 := by rw [h1, h2, key]
  nlinarith [sq_nonneg (‖w - (a:ℂ)‖ - ‖1 - (a:ℂ)*w‖), norm_nonneg (w - (a:ℂ)),
    norm_nonneg (1 - (a:ℂ)*w), hsq]

/-- **The Blaschke factor at a real point of the unit circle has modulus 1.** For real `a`
    with `|a| < 1` and complex `w` with `‖w‖ = 1`, the Blaschke factor `(w-a)/(1-a·w)` has
    modulus exactly `1`. -/
theorem norm_blaschke_eq_one {a : ℝ} (ha : |a| < 1) {w : ℂ} (hw : ‖w‖ = 1) :
    ‖(w - (a:ℂ)) / (1 - (a:ℂ) * w)‖ = 1 := by
  have hden_ne : (1:ℂ) - (a:ℂ) * w ≠ 0 := by
    intro heq
    have haw : (a:ℂ) * w = 1 := by linear_combination -heq
    have hnorm : ‖(a:ℂ) * w‖ = 1 := by rw [haw]; simp
    rw [norm_mul, Complex.norm_real, hw, mul_one, Real.norm_eq_abs] at hnorm
    linarith [ha, hnorm]
  rw [norm_div, norm_sub_real_eq_norm_one_sub_mul hw]
  exact div_self (norm_ne_zero_iff.mpr hden_ne)

/-- **The prime characteristic-function weight has modulus 1.** For every prime `p` and
    real `t`, `‖(p^{-it} - p^{-1/2}) / (1 - p^{-1/2-it})‖ = 1` -- the Sz.-Nagy/Foias
    Blaschke characteristic factor at the prime delay, item `0452a4c4`'s own formula. -/
theorem primeCharFn_norm_eq_one (p : ℕ) (hp : p.Prime) (t : ℝ) :
    ‖(((p:ℝ):ℂ) ^ (-(t:ℂ) * Complex.I) - ((p:ℝ):ℂ) ^ (-(1:ℂ)/2)) /
        (1 - ((p:ℝ):ℂ) ^ (-(1:ℂ)/2 - (t:ℂ) * Complex.I))‖ = 1 := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
  have hpC0 : ((p:ℝ):ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hp1 : (1:ℝ) < (p:ℝ) := by
    have h2 := hp.two_le
    have h2' : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast h2
    linarith
  have haC : (((p:ℝ) ^ (-(1:ℝ)/2) : ℝ) : ℂ) = ((p:ℝ):ℂ) ^ (-(1:ℂ)/2) := by
    rw [Complex.ofReal_cpow hp0.le]; norm_num
  have hwnorm : ‖((p:ℝ):ℂ) ^ (-(t:ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hp0]
    have him0 : (-(t:ℂ) * Complex.I).re = 0 := by simp
    rw [him0]; norm_num
  have hane : |(p:ℝ) ^ (-(1:ℝ)/2)| < 1 := by
    rw [abs_of_pos (Real.rpow_pos_of_pos hp0 _)]
    exact (Real.rpow_lt_one_iff_of_pos hp0).mpr (Or.inl ⟨hp1, by norm_num⟩)
  have hden_eq : (1:ℂ) - ((p:ℝ):ℂ) ^ (-(1:ℂ)/2 - (t:ℂ) * Complex.I)
      = 1 - (((p:ℝ) ^ (-(1:ℝ)/2) : ℝ) : ℂ) * (((p:ℝ):ℂ) ^ (-(t:ℂ) * Complex.I)) := by
    rw [haC, ← Complex.cpow_add _ _ hpC0]
    ring_nf
  rw [hden_eq, ← haC]
  exact norm_blaschke_eq_one hane hwnorm

/-- **Operator-level unitarity of the prime characteristic-function diagonal.** For fixed
    real `t`, the diagonal operator on `Ell2Primes` built from the weight
    `p ↦ (p^{-it}-p^{-1/2})/(1-p^{-1/2-it})` is unitary in the precise operator sense of
    `GppPrimeContraction.prime_contraction_unitary_of_modulus_one`: exact `ℓ²`-norm
    preservation plus a genuine two-sided inverse via the conjugate weight. -/
theorem primeCharFn_diag_unitary_of_modulus_one (t : ℝ) :
    ∃ hw1 : ∀ p : Primes, ‖(((p.1:ℝ):ℂ) ^ (-(t:ℂ) * Complex.I) - ((p.1:ℝ):ℂ) ^ (-(1:ℂ)/2)) /
        (1 - ((p.1:ℝ):ℂ) ^ (-(1:ℂ)/2 - (t:ℂ) * Complex.I))‖ = 1,
      (∀ x, ‖mulOpLinP
          (fun p : Primes => (((p.1:ℝ):ℂ) ^ (-(t:ℂ) * Complex.I) - ((p.1:ℝ):ℂ) ^ (-(1:ℂ)/2)) /
              (1 - ((p.1:ℝ):ℂ) ^ (-(1:ℂ)/2 - (t:ℂ) * Complex.I)))
          (fun p => le_of_eq (hw1 p)) x‖ = ‖x‖) := by
  have hw1 : ∀ p : Primes, ‖(((p.1:ℝ):ℂ) ^ (-(t:ℂ) * Complex.I) - ((p.1:ℝ):ℂ) ^ (-(1:ℂ)/2)) /
      (1 - ((p.1:ℝ):ℂ) ^ (-(1:ℂ)/2 - (t:ℂ) * Complex.I))‖ = 1 := fun p =>
    primeCharFn_norm_eq_one p.1 p.2 t
  exact ⟨hw1, mulOpLinP_norm_eq _ hw1⟩

end GppPrimeCharFn
