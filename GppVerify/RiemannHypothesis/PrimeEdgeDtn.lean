import GppVerify.RiemannHypothesis.PrimeCayleyChannel
import GppVerify.RiemannHypothesis.SU11CharacterDefect
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Prime powers as Schur-composed massive edges

Source: Codex, GPPDiscovery2 `research/`:
* `2026-09-27_prime_power_schur_edge_semigroup.md` (all sections);
* `2026-09-26_prime_tfd_massive_edge_dtn_geometry.md` (the finite algebra).

For an interval of length `ℓ > 0`, the Dirichlet-to-Neumann matrix is
`Λ(ℓ) = [[coth ℓ, −csch ℓ], [−csch ℓ, coth ℓ]]`, and the hyperbolic transfer matrix is
`M(ℓ) = [[cosh ℓ, sinh ℓ], [sinh ℓ, cosh ℓ]]`.

* `dtn_inverse`: `Λ(ℓ)⁻¹ = [[coth, csch], [csch, coth]]`, so `Γ(ℓ) = ½ Λ(ℓ)⁻¹` has entries
  `½ coth ℓ` and `½ csch ℓ`.
* `schur_dtn`: gluing two intervals and eliminating the common boundary value by a Schur
  complement adds the lengths: `Λ(ℓ₁) ⋆ Λ(ℓ₂) = Λ(ℓ₁ + ℓ₂)`.
* `M_add`, `M_pow`: `M(ℓ₁) M(ℓ₂) = M(ℓ₁ + ℓ₂)` and `M(ℓ)^m = M(mℓ)`;
* `M_primeFactorsList`: for `n ≥ 1` and `ℓ_n = ½ log n`,
  `M(ℓ_n) = ∏_{p ∣ n, with multiplicity} M(ℓ_p)`. This is the note's "the multiplicative semigroup
  of positive integers has an exact one-parameter hyperbolic transfer representation".

**At a prime** (`ℓ_p = ½ log p`):
* `coth_prime`: `coth ℓ_p = (p+1)/(p−1)`, so `½ coth ℓ_p = C_p + ½` with `C_p = 1/(p−1)`, and
  `½ csch ℓ_p = A_p = √p/(p−1)` (`SU11CharacterDefect.prime_anomalous`);
* `dtn_eigen_tanh`, `dtn_eigen_prime`: the smaller eigenvalue `λ_-` of `Γ(ℓ)` satisfies
  `2 λ_- = tanh(ℓ/2)`, and `tanh(ℓ_p/2) = (√p−1)/(√p+1) = q_p`, the Cayley coordinate;
* `edge_amplitude`: `(log p) p^{−m/2} = 2ℓ_p e^{−mℓ_p}`, the factor of two between the one-way
  edge `ℓ_p` and the closed orbit length `2ℓ_p = log p`.

**The Archimedean weight.** `w_infty_eq`: `e^{−x/2} + e^{x/2} − e^{x/2} A(x) =
e^{x/2} − e^{−5x/2}/(1 − e^{−2x})` with `A(x) = 1/(2 sinh x)`.

## Checks

All identities were verified by hand against the notes; no corrections. The note marks the
two-sheet round-trip reading of the factor of two as a structural hypothesis, not a theorem, and
nothing here asserts it.

## Scope

Finite `2 × 2` algebra and hyperbolic identities. No RH claim.
-/

open Matrix

namespace GppPrimeEdgeDtn

/-- `coth ℓ = cosh ℓ / sinh ℓ`. -/
noncomputable def coth (ℓ : ℝ) : ℝ := Real.cosh ℓ / Real.sinh ℓ

/-- `csch ℓ = 1 / sinh ℓ`. -/
noncomputable def csch (ℓ : ℝ) : ℝ := 1 / Real.sinh ℓ

/-- The Dirichlet-to-Neumann matrix of an interval of length `ℓ`. -/
noncomputable def dtn (ℓ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![coth ℓ, -csch ℓ; -csch ℓ, coth ℓ]

/-- The hyperbolic transfer matrix. -/
noncomputable def hyp (ℓ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh ℓ, Real.sinh ℓ; Real.sinh ℓ, Real.cosh ℓ]

/-- Schur composition: glue the second node of `A` to the first node of `B` and eliminate it. -/
noncomputable def schurStar (A B : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![A 0 0 - A 0 1 * A 1 0 / (A 1 1 + B 0 0), -(A 0 1 * B 0 1) / (A 1 1 + B 0 0);
     -(B 1 0 * A 1 0) / (A 1 1 + B 0 0), B 1 1 - B 1 0 * B 0 1 / (A 1 1 + B 0 0)]

lemma coth_sq_sub_csch_sq (ℓ : ℝ) (hℓ : 0 < ℓ) : coth ℓ ^ 2 - csch ℓ ^ 2 = 1 := by
  have hs : Real.sinh ℓ ≠ 0 := (Real.sinh_pos_iff.mpr hℓ).ne'
  unfold coth csch
  rw [div_pow, div_pow, one_pow, ← sub_div, Real.cosh_sq]
  field_simp
  ring

/-- **The DtN matrix is inverted by `[[coth, csch], [csch, coth]]`.** -/
theorem dtn_inverse (ℓ : ℝ) (hℓ : 0 < ℓ) :
    dtn ℓ * !![coth ℓ, csch ℓ; csch ℓ, coth ℓ] = 1 := by
  have h := coth_sq_sub_csch_sq ℓ hℓ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dtn, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [h]

lemma coth_add_coth (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    coth a + coth b = Real.sinh (a + b) / (Real.sinh a * Real.sinh b) := by
  have h1 : Real.sinh a ≠ 0 := (Real.sinh_pos_iff.mpr ha).ne'
  have h2 : Real.sinh b ≠ 0 := (Real.sinh_pos_iff.mpr hb).ne'
  unfold coth
  rw [Real.sinh_add]
  field_simp
  ring

/-- **Schur elimination adds lengths.** `Λ(ℓ₁) ⋆ Λ(ℓ₂) = Λ(ℓ₁ + ℓ₂)`. -/
theorem schur_dtn (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    schurStar (dtn a) (dtn b) = dtn (a + b) := by
  have hab : 0 < a + b := add_pos ha hb
  have h1 : Real.sinh a ≠ 0 := (Real.sinh_pos_iff.mpr ha).ne'
  have h2 : Real.sinh b ≠ 0 := (Real.sinh_pos_iff.mpr hb).ne'
  have h3 : Real.sinh (a + b) ≠ 0 := (Real.sinh_pos_iff.mpr hab).ne'
  have hD : Real.sinh a * Real.cosh b + Real.cosh a * Real.sinh b ≠ 0 := by
    rw [← Real.sinh_add]; exact h3
  have hca := Real.cosh_sq a
  have hcb := Real.cosh_sq b
  have hsum : coth a + coth b = Real.sinh (a + b) / (Real.sinh a * Real.sinh b) :=
    coth_add_coth a b ha hb
  have hd : coth a + coth b ≠ 0 := by rw [hsum]; exact div_ne_zero h3 (mul_ne_zero h1 h2)
  have e00 : coth a - csch a * csch a / (coth a + coth b) = coth (a + b) := by
    rw [hsum]; unfold coth csch; rw [Real.sinh_add, Real.cosh_add]
    have : Real.sinh a * Real.cosh b + Real.cosh a * Real.sinh b ≠ 0 := hD
    field_simp
    linear_combination Real.sinh b * hca
  have e11 : coth b - csch b * csch b / (coth a + coth b) = coth (a + b) := by
    rw [hsum]; unfold coth csch; rw [Real.sinh_add, Real.cosh_add]
    have : Real.sinh a * Real.cosh b + Real.cosh a * Real.sinh b ≠ 0 := hD
    field_simp
    linear_combination Real.sinh a * hcb
  have e01 : -(csch a * csch b) / (coth a + coth b) = -csch (a + b) := by
    rw [hsum]; unfold csch; field_simp
  have e10 : -(csch b * csch a) / (coth a + coth b) = -csch (a + b) := by
    rw [hsum]; unfold csch; field_simp
  ext i j
  fin_cases i <;> fin_cases j <;> simp [schurStar, dtn] <;> assumption

/-! ### The hyperbolic semigroup -/

/-- `M(ℓ₁) M(ℓ₂) = M(ℓ₁ + ℓ₂)`. -/
theorem M_add (a b : ℝ) : hyp a * hyp b = hyp (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hyp, Matrix.mul_apply, Fin.sum_univ_two, Real.cosh_add,
    Real.sinh_add] <;> ring

theorem M_zero : hyp 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hyp]

/-- `M(ℓ)^m = M(mℓ)`. -/
theorem M_pow (ℓ : ℝ) (m : ℕ) : hyp ℓ ^ m = hyp (m * ℓ) := by
  induction m with
  | zero => simp [M_zero]
  | succ m ih => rw [pow_succ, ih, M_add]; congr 1; push_cast; ring

/-- `M(½ log (∏ L)) = ∏ M(½ log p)` over a list of positive naturals. -/
theorem M_list_prod (L : List ℕ) (hL : ∀ p ∈ L, 0 < p) :
    hyp (1 / 2 * Real.log (L.prod : ℕ)) = (L.map (fun p : ℕ => hyp (1 / 2 * Real.log (p : ℝ)))).prod := by
  induction L with
  | nil => simp [M_zero]
  | cons p L ih =>
    have hp : 0 < p := hL p (List.mem_cons_self)
    have hL' : ∀ q ∈ L, 0 < q := fun q hq => hL q (List.mem_cons_of_mem _ hq)
    have hpr : 0 < L.prod := List.prod_pos hL'
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih hL', M_add]
    congr 1
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hp.ne') (by exact_mod_cast hpr.ne')]
    ring

/-- **The integers form a one-parameter hyperbolic semigroup.** For `n ≥ 1`,
`M(½ log n) = ∏_{p ∣ n with multiplicity} M(½ log p)`. -/
theorem M_primeFactorsList (n : ℕ) (hn : 0 < n) :
    hyp (1 / 2 * Real.log n) = (n.primeFactorsList.map (fun p : ℕ => hyp (1 / 2 * Real.log (p : ℝ)))).prod := by
  have h := M_list_prod n.primeFactorsList (fun p hp => (Nat.prime_of_mem_primeFactorsList hp).pos)
  rwa [Nat.prod_primeFactorsList hn.ne'] at h

/-! ### At a prime -/

/-- `coth(½ log p) = (p+1)/(p−1)` for `p > 1`. -/
theorem coth_prime (p : ℝ) (hp : 1 < p) : coth (1 / 2 * Real.log p) = (p + 1) / (p - 1) := by
  have hp0 : 0 < p := by linarith
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hexp : Real.exp (1 / 2 * Real.log p) = Real.sqrt p := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp0]; congr 1; ring
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  obtain ⟨u, hu0, hpu⟩ : ∃ u : ℝ, 0 < u ∧ u ^ 2 = p := ⟨Real.sqrt p, hs, hsq⟩
  have hu1 : 1 < u ^ 2 := by rw [hpu]; exact hp
  have hroot : Real.sqrt p = u := by rw [← hpu, Real.sqrt_sq hu0.le]
  unfold coth
  rw [Real.cosh_eq, Real.sinh_eq, Real.exp_neg, hexp, hroot, ← hpu]
  have hne : u ^ 2 - 1 ≠ 0 := by linarith
  have hune : u ≠ 0 := hu0.ne'
  have hden : u - u⁻¹ ≠ 0 := by
    intro h0
    apply hne
    field_simp at h0
    linarith
  field_simp

/-- **The smaller DtN eigenvalue.** `coth ℓ − csch ℓ = tanh(ℓ/2)` for `ℓ > 0`. -/
theorem dtn_eigen_tanh (ℓ : ℝ) (hℓ : 0 < ℓ) : coth ℓ - csch ℓ = Real.tanh (ℓ / 2) := by
  have hx : 0 < ℓ / 2 := by linarith
  have hs : 0 < Real.sinh (ℓ / 2) := Real.sinh_pos_iff.mpr hx
  have hc : 0 < Real.cosh (ℓ / 2) := Real.cosh_pos _
  have hsq := Real.cosh_sq (ℓ / 2)
  have e2 : ℓ = 2 * (ℓ / 2) := by ring
  unfold coth csch
  rw [Real.tanh_eq_sinh_div_cosh]
  conv_lhs => rw [e2, Real.cosh_two_mul, Real.sinh_two_mul]
  field_simp
  nlinarith [hsq]

/-- **The DtN eigenvalue at a prime is the Cayley coordinate.**
`coth ℓ_p − csch ℓ_p = (√p − 1)/(√p + 1)` for `ℓ_p = ½ log p`. -/
theorem dtn_eigen_prime (p : ℝ) (hp : 1 < p) :
    coth (1 / 2 * Real.log p) - csch (1 / 2 * Real.log p) = (Real.sqrt p - 1) / (Real.sqrt p + 1) := by
  have hp0 : 0 < p := by linarith
  have hlog : 0 < Real.log p := Real.log_pos hp
  rw [dtn_eigen_tanh _ (by positivity), GppPrimeCayley.cayley_eq_tanh p hp0]
  congr 1; ring

/-- **The covariances are the entries of `Γ(ℓ_p) = ½ Λ(ℓ_p)⁻¹`.**
`½ coth ℓ_p = C_p + ½` with `C_p = 1/(p−1)`, and `½ csch ℓ_p = A_p = √p/(p−1)`. -/
theorem gamma_prime (p : ℝ) (hp : 1 < p) :
    (1 / 2 : ℝ) * coth (1 / 2 * Real.log p) = 1 / (p - 1) + 1 / 2 ∧
      (1 / 2 : ℝ) * csch (1 / 2 * Real.log p) = Real.sqrt p / (p - 1) := by
  have hne : p - 1 ≠ 0 := by linarith
  refine ⟨?_, ?_⟩
  · rw [coth_prime p hp]; field_simp; ring
  · rw [← GppSU11CharacterDefect.prime_anomalous p hp]
    unfold csch
    field_simp

/-- **Edge amplitude.** `(log p) p^{−m/2} = 2 ℓ_p e^{−m ℓ_p}` with `ℓ_p = ½ log p`:
the one-way edge has length `ℓ_p`, the closed orbit `2 ℓ_p = log p`. -/
theorem edge_amplitude (p : ℝ) (hp : 0 < p) (m : ℝ) :
    Real.log p * p ^ (-(m / 2)) =
      2 * (1 / 2 * Real.log p) * Real.exp (-(m * (1 / 2 * Real.log p))) := by
  rw [Real.rpow_def_of_pos hp]
  have : Real.log p * -(m / 2) = -(m * (1 / 2 * Real.log p)) := by ring
  rw [this]; ring

/-- **The Archimedean weight.** For `x > 0` and `A(x) = 1/(2 sinh x)`:
`e^{−x/2} + e^{x/2} − e^{x/2} A(x) = e^{x/2} − e^{−5x/2}/(1 − e^{−2x})`. -/
theorem w_infty_eq (x : ℝ) (hx : 0 < x) :
    Real.exp (-x / 2) + Real.exp (x / 2) - Real.exp (x / 2) * (1 / (2 * Real.sinh x)) =
      Real.exp (x / 2) - Real.exp (-(5 * x / 2)) / (1 - Real.exp (-2 * x)) := by
  have hu : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx
  have hu0 : Real.exp x ≠ 0 := (Real.exp_pos _).ne'
  have hh : Real.exp (x / 2) ^ 2 = Real.exp x := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hh0 : Real.exp (x / 2) ≠ 0 := (Real.exp_pos _).ne'
  have hm : Real.exp (-x / 2) = (Real.exp (x / 2))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
  have hm5 : Real.exp (-(5 * x / 2)) = ((Real.exp (x / 2)) ^ 5)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; push_cast; ring
  have hm2 : Real.exp (-2 * x) = ((Real.exp (x / 2)) ^ 4)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; push_cast; ring
  have hsin : Real.sinh x = (Real.exp (x / 2) ^ 2 - (Real.exp (x / 2) ^ 2)⁻¹) / 2 := by
    rw [Real.sinh_eq, Real.exp_neg, hh]
  set u := Real.exp (x / 2) with hu'
  have hu4 : u ^ 4 - 1 ≠ 0 := by
    have : 1 < u ^ 2 := by rw [hh]; exact hu
    nlinarith
  have hu2 : u ^ 2 - (u ^ 2)⁻¹ ≠ 0 := by
    have : 1 < u ^ 2 := by rw [hh]; exact hu
    have hp : 0 < u ^ 2 := by positivity
    intro h0; field_simp at h0; nlinarith
  rw [hm, hm5, hm2, hsin]
  field_simp
  ring

end GppPrimeEdgeDtn
