import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Rank-one pole thresholds, the Sobolev-trace DtN identity, midpoint uniqueness, theta-control whitening

Source: Codex's `codex.formalization_queue` rows (read 2026-10-03; the queue's statuses are stale,
the row texts are the specification) and the notes behind them:
* "Rank-one pole-threshold inertia closure" (priority 99);
* "Sobolev trace TFD Dirichlet-to-Neumann identity" (priority 96);
* "Pure TFD midpoint uniqueness versus shifted two-radius control" (priority 94);
* "Shifted-product theta control local whitening and complementary-channel identity" (priority 85).

All four are finite algebra and none claims anything about zeta zeros.

## 1. Rank-one pole thresholds

For a real symmetric invertible `A` and a vector `c`, let `u = A⁻¹ c`.

* `pole_threshold_neg`: if `cᵀ A⁻¹ c = −2` and `A` is positive definite on the hyperplane `c^⊥`
  (`yᵀc = 0, y ≠ 0 ⟹ yᵀAy > 0`), then `A + ½ c cᵀ` is positive semidefinite, `u` lies in its kernel,
  and its kernel is exactly the line `ℝ u`.
* `pole_threshold_pos`: if `A` is positive definite and `sᵀ A⁻¹ s = 2`, then `A − ½ s sᵀ` is
  positive semidefinite and singular, with `A⁻¹ s` in its kernel.

**Reading of the hypothesis.** The queue row states the first with "`A` has exactly one negative
eigenvalue". For invertible `A` and `cᵀA⁻¹c < 0`, Haynsworth inertia additivity shows that this
is equivalent to `A` being positive definite on `c^⊥`, which is the form used here. That
equivalence (Sylvester's law of inertia) is not proved in this file; the hypothesis is stated in the
form the proof uses, and the docstring says so rather than hiding it. The proof is the
decomposition `x = α u + y` with `yᵀc = 0`, which gives `xᵀ(A + ½ccᵀ)x = yᵀAy`.

## 2. The Sobolev-trace DtN identity

`dtn_tfd_identity`: for `κ, ℓ > 0` and `r = e^{−κℓ}`, `C = r²/(1−r²)`, `A = r/(1−r²)`:
`κ coth(κℓ) = 2κ(C + ½)` and `κ csch(κℓ) = 2κ A`. Hence the interval DtN matrix
`κ [[coth, −csch], [−csch, coth]]` equals `2κ [[C + ½, −A], [−A, C + ½]]`. At `κ = ½`, `ℓ = log p`
this is `r = p^{-1/2}`, `C = 1/(p−1)`, `A = √p/(p−1)` (`dtn_tfd_prime`).

## 3. Midpoint uniqueness

On two-mode Fock coefficients `ψ : ℕ × ℕ → ℝ` put `a_L ψ (m,n) = √(m+1) ψ(m+1,n)` and
`a_R† ψ (m,n) = √n ψ(m, n−1)` (zero at `n = 0`), and `Ω_r(m,n) = √(1−r²) r^n · [m = n]`.

* `midpoint_annihilation`: `(a_L − r a_R†) Ω_r = 0`;
* `aR_dag_injective`: `a_R†` is injective;
* `unique_radius`: if `(a_L − r a_R†) ψ = 0 = (a_L − r' a_R†) ψ` with `r ≠ r'`, then `ψ = 0`.

So the pure TFD vector is distinguished among vectors by its radius, which is the
discriminator against the shifted two-radius control. It is a discriminator only.

## 4. Theta-control whitening

`theta_whitening`: for `a = p^θ`, in any commutative ring with a real-algebra structure,
`(1 − r a u)(1 − r a⁻¹ u) = 1 − 2 r cosh(θ log p) u + r² u²`; and `weights_cosh`:
`p^{kθ} + p^{−kθ} = 2 cosh(kθ log p)`. This is the exact algebra behind the note's calibration
lemma: generic first-order whitening differs from the doubled complementary control.

## Scope

Finite linear algebra, one hyperbolic identity, and coefficient bookkeeping on Fock sequences. No
RH claim.
-/

open Matrix

namespace GppRankOneControls

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The quadratic form of a rank-one matrix: `xᵀ (c cᵀ) x = (c · x)²`. -/
lemma quad_vecMulVec (c x : n → ℝ) :
    x ⬝ᵥ (Matrix.vecMulVec c c *ᵥ x) = (c ⬝ᵥ x) ^ 2 := by
  rw [Matrix.vecMulVec_mulVec]
  simp [dotProduct_smul, sq, dotProduct_comm]

omit [DecidableEq n] in
lemma sym_dot (A : Matrix n n ℝ) (hsymm : A.IsSymm) (y z : n → ℝ) :
    y ⬝ᵥ (A *ᵥ z) = z ⬝ᵥ (A *ᵥ y) := by
  have h1 : y ⬝ᵥ (A *ᵥ z) = (y ᵥ* A) ⬝ᵥ z := Matrix.dotProduct_mulVec _ _ _
  have h2 : y ᵥ* A = A *ᵥ y := by
    have := Matrix.vecMul_transpose A y
    rwa [hsymm] at this
  rw [h1, h2, dotProduct_comm]

omit [DecidableEq n] in
/-- Expansion of the quadratic form of a sum: `(y + z)ᵀ A (y + z) = yᵀAy + 2 yᵀAz + zᵀAz`. -/
lemma quad_add (A : Matrix n n ℝ) (hsymm : A.IsSymm) (y z : n → ℝ) :
    (y + z) ⬝ᵥ (A *ᵥ (y + z)) = y ⬝ᵥ (A *ᵥ y) + 2 * (y ⬝ᵥ (A *ᵥ z)) + z ⬝ᵥ (A *ᵥ z) := by
  rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct,
    sym_dot A hsymm z y]
  ring

omit [DecidableEq n] in
lemma mulVec_rankOne (c x : n → ℝ) :
    Matrix.vecMulVec c c *ᵥ x = (c ⬝ᵥ x) • c := by
  ext i
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- **Pole threshold, negative case.** -/
theorem pole_threshold_neg (A : Matrix n n ℝ) (hsymm : A.IsSymm) (hdet : IsUnit A.det)
    (c : n → ℝ) (hc : c ⬝ᵥ (A⁻¹ *ᵥ c) = -2)
    (hpd : ∀ y : n → ℝ, y ⬝ᵥ c = 0 → y ≠ 0 → 0 < y ⬝ᵥ (A *ᵥ y)) :
    (∀ x : n → ℝ, 0 ≤ x ⬝ᵥ ((A + (1 / 2 : ℝ) • Matrix.vecMulVec c c) *ᵥ x)) ∧
      (A + (1 / 2 : ℝ) • Matrix.vecMulVec c c) *ᵥ (A⁻¹ *ᵥ c) = 0 ∧
      (∀ x : n → ℝ, (A + (1 / 2 : ℝ) • Matrix.vecMulVec c c) *ᵥ x = 0 →
        ∃ α : ℝ, x = α • (A⁻¹ *ᵥ c)) := by
  set u : n → ℝ := A⁻¹ *ᵥ c with hu
  have hAu : A *ᵥ u = c := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hcu : c ⬝ᵥ u = -2 := hc
  have huAu : u ⬝ᵥ (A *ᵥ u) = -2 := by rw [hAu, dotProduct_comm]; exact hcu
  -- The decomposition `x = α u + y` with `y ⬝ c = 0`.
  have decomp : ∀ x : n → ℝ,
      x ⬝ᵥ ((A + (1 / 2 : ℝ) • Matrix.vecMulVec c c) *ᵥ x) =
        (x - (-(c ⬝ᵥ x) / 2) • u) ⬝ᵥ (A *ᵥ (x - (-(c ⬝ᵥ x) / 2) • u)) ∧
      (x - (-(c ⬝ᵥ x) / 2) • u) ⬝ᵥ c = 0 := by
    intro x
    set α : ℝ := -(c ⬝ᵥ x) / 2 with hα
    set y : n → ℝ := x - α • u with hy
    have hyc : y ⬝ᵥ c = 0 := by
      rw [hy, sub_dotProduct, smul_dotProduct, dotProduct_comm u c, hcu, hα]
      simp [dotProduct_comm]
    refine ⟨?_, hyc⟩
    have hx : x = y + α • u := by rw [hy]; abel
    have hyAu : y ⬝ᵥ (A *ᵥ u) = 0 := by rw [hAu]; exact hyc
    have hexp : x ⬝ᵥ (A *ᵥ x) = y ⬝ᵥ (A *ᵥ y) - 2 * α ^ 2 := by
      conv_lhs => rw [hx]
      rw [quad_add A hsymm]
      simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
      rw [hyAu, huAu]
      ring
    have hrank : x ⬝ᵥ (((1 / 2 : ℝ) • Matrix.vecMulVec c c) *ᵥ x) = 2 * α ^ 2 := by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, mulVec_rankOne, dotProduct_smul,
        smul_eq_mul, dotProduct_comm x c, hα]
      ring
    rw [Matrix.add_mulVec, dotProduct_add, hrank, hexp]
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro x
    obtain ⟨h1, h2⟩ := decomp x
    rw [h1]
    by_cases hy : x - (-(c ⬝ᵥ x) / 2) • u = 0
    · rw [hy]; simp
    · exact (hpd _ h2 hy).le
  · rw [Matrix.add_mulVec, Matrix.smul_mulVec, mulVec_rankOne, hAu, hcu]
    ext i
    simp
  · intro x hx
    obtain ⟨h1, h2⟩ := decomp x
    have h0 : x ⬝ᵥ ((A + (1 / 2 : ℝ) • Matrix.vecMulVec c c) *ᵥ x) = 0 := by rw [hx]; simp
    rw [h1] at h0
    by_contra hne
    have hy : x - (-(c ⬝ᵥ x) / 2) • u ≠ 0 := by
      intro h; apply hne
      exact ⟨-(c ⬝ᵥ x) / 2, sub_eq_zero.mp h⟩
    have := hpd _ h2 hy
    linarith

/-- **Pole threshold, positive case.** If `A` is positive definite and `sᵀ A⁻¹ s = 2`, then
`A − ½ s sᵀ` is positive semidefinite and singular, with `A⁻¹ s` in its kernel. -/
theorem pole_threshold_pos (A : Matrix n n ℝ) (hsymm : A.IsSymm) (hdet : IsUnit A.det)
    (s : n → ℝ) (hs : s ⬝ᵥ (A⁻¹ *ᵥ s) = 2)
    (hpd : ∀ y : n → ℝ, y ≠ 0 → 0 < y ⬝ᵥ (A *ᵥ y)) :
    (∀ x : n → ℝ, 0 ≤ x ⬝ᵥ ((A - (1 / 2 : ℝ) • Matrix.vecMulVec s s) *ᵥ x)) ∧
      (A - (1 / 2 : ℝ) • Matrix.vecMulVec s s) *ᵥ (A⁻¹ *ᵥ s) = 0 := by
  set u : n → ℝ := A⁻¹ *ᵥ s with hu
  have hAu : A *ᵥ u = s := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hsu : s ⬝ᵥ u = 2 := hs
  have huAu : u ⬝ᵥ (A *ᵥ u) = 2 := by rw [hAu, dotProduct_comm]; exact hsu
  have hnn : ∀ z : n → ℝ, 0 ≤ z ⬝ᵥ (A *ᵥ z) := by
    intro z
    by_cases hz : z = 0
    · rw [hz]; simp
    · exact (hpd z hz).le
  refine ⟨?_, ?_⟩
  · intro x
    -- Complete the square: `(x − t u)ᵀ A (x − t u) ≥ 0` with `t = (s · x)/2`.
    set t : ℝ := (s ⬝ᵥ x) / 2 with ht
    have hq := hnn (x - t • u)
    have hxAu : x ⬝ᵥ (A *ᵥ u) = s ⬝ᵥ x := by rw [hAu, dotProduct_comm]
    have hexp : (x - t • u) ⬝ᵥ (A *ᵥ (x - t • u)) =
        x ⬝ᵥ (A *ᵥ x) - 2 * t * (s ⬝ᵥ x) + t ^ 2 * 2 := by
      have h := quad_add A hsymm x (-(t • u))
      rw [sub_eq_add_neg, h]
      simp only [Matrix.mulVec_neg, Matrix.mulVec_smul, dotProduct_neg, dotProduct_smul,
        neg_dotProduct, smul_dotProduct, smul_eq_mul, hxAu, huAu]
      ring
    rw [hexp] at hq
    have hrank : x ⬝ᵥ (((1 / 2 : ℝ) • Matrix.vecMulVec s s) *ᵥ x) = (1 / 2) * (s ⬝ᵥ x) ^ 2 := by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, mulVec_rankOne, dotProduct_smul,
        smul_eq_mul, dotProduct_comm x s]
      ring
    rw [Matrix.sub_mulVec, dotProduct_sub, hrank]
    rw [ht] at hq
    nlinarith [hq]
  · rw [Matrix.sub_mulVec, Matrix.smul_mulVec, mulVec_rankOne, hAu, hsu]
    ext i
    simp

/-! ### The Sobolev-trace DtN identity -/

/-- **DtN identity.** For `κ, ℓ > 0`, `r = e^{−κℓ}`, `C = r²/(1−r²)`, `A = r/(1−r²)`:
`κ coth(κℓ) = 2κ (C + ½)` and `κ csch(κℓ) = 2κ A`. -/
theorem dtn_tfd_identity (κ ℓ : ℝ) (hκ : 0 < κ) (hℓ : 0 < ℓ) :
    κ * (Real.cosh (κ * ℓ) / Real.sinh (κ * ℓ)) =
        2 * κ * (Real.exp (-(κ * ℓ)) ^ 2 / (1 - Real.exp (-(κ * ℓ)) ^ 2) + 1 / 2) ∧
      κ * (1 / Real.sinh (κ * ℓ)) =
        2 * κ * (Real.exp (-(κ * ℓ)) / (1 - Real.exp (-(κ * ℓ)) ^ 2)) := by
  have hx : 0 < κ * ℓ := mul_pos hκ hℓ
  set x := κ * ℓ with hxdef
  have hu : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx
  have hu0 : Real.exp x ≠ 0 := (Real.exp_pos _).ne'
  have hs : Real.sinh x = (Real.exp x - (Real.exp x)⁻¹) / 2 := by rw [Real.sinh_eq, Real.exp_neg]
  have hc : Real.cosh x = (Real.exp x + (Real.exp x)⁻¹) / 2 := by rw [Real.cosh_eq, Real.exp_neg]
  have h2 : Real.exp x ^ 2 - 1 ≠ 0 := by nlinarith
  have hd : Real.exp x - (Real.exp x)⁻¹ ≠ 0 := by
    intro h0; apply h2; field_simp at h0; nlinarith
  rw [Real.exp_neg, hs, hc]
  constructor
  · field_simp
    ring
  · field_simp

/-- **At a prime** (`κ = ½`, `ℓ = log p`): `r = p^{-1/2}`, so the entries are
`C + ½ = ½ coth(½ log p)` and `A`, with `κ`-free forms `r²/(1−r²) = 1/(p−1)` and
`r/(1−r²) = √p/(p−1)`. -/
theorem dtn_tfd_prime (p : ℝ) (hp : 1 < p) :
    (p ^ (-(1 / 2 : ℝ))) ^ 2 / (1 - (p ^ (-(1 / 2 : ℝ))) ^ 2) = 1 / (p - 1) ∧
      p ^ (-(1 / 2 : ℝ)) / (1 - (p ^ (-(1 / 2 : ℝ))) ^ 2) = Real.sqrt p / (p - 1) := by
  have hp0 : 0 < p := by linarith
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
  have hr : p ^ (-(1 / 2 : ℝ)) = (Real.sqrt p)⁻¹ := by
    rw [Real.rpow_neg hp0.le, Real.sqrt_eq_rpow]
  have hne : p - 1 ≠ 0 := by linarith
  rw [hr]
  have hsne : Real.sqrt p ≠ 0 := hs.ne'
  have hps : p ≠ 0 := hp0.ne'
  constructor
  · rw [inv_pow, sq, hsq]
    field_simp
  · rw [inv_pow, sq, hsq]
    have : 1 - p⁻¹ ≠ 0 := by
      have : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
      linarith
    field_simp
    nlinarith [hsq]

/-! ### Midpoint uniqueness on two-mode Fock coefficients -/

/-- The left annihilation operator on coefficients: `(a_L ψ)(m,n) = √(m+1) ψ(m+1,n)`. -/
noncomputable def aL (ψ : ℕ × ℕ → ℝ) : ℕ × ℕ → ℝ :=
  fun mn => Real.sqrt ((mn.1 : ℝ) + 1) * ψ (mn.1 + 1, mn.2)

/-- The right creation operator on coefficients: `(a_R† ψ)(m,n) = √n ψ(m,n−1)` (zero at `n = 0`). -/
noncomputable def aRdag (ψ : ℕ × ℕ → ℝ) : ℕ × ℕ → ℝ :=
  fun mn => if mn.2 = 0 then 0 else Real.sqrt (mn.2 : ℝ) * ψ (mn.1, mn.2 - 1)

/-- The TFD vector `Ω_r = √(1−r²) Σ r^n |n,n⟩` on coefficients. -/
noncomputable def omega (r : ℝ) : ℕ × ℕ → ℝ :=
  fun mn => if mn.1 = mn.2 then Real.sqrt (1 - r ^ 2) * r ^ mn.2 else 0

/-- **The midpoint relation.** `(a_L − r a_R†) Ω_r = 0`. -/
theorem midpoint_annihilation (r : ℝ) : aL (omega r) - r • aRdag (omega r) = 0 := by
  funext ⟨m, k⟩
  simp only [aL, aRdag, omega, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  by_cases hk : k = 0
  · subst hk
    simp
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    by_cases hmj : m = j
    · subst hmj
      simp
      ring
    · have h2 : ¬ (m = j) := hmj
      simp [h2]

/-- `a_R†` is injective on coefficient arrays. -/
theorem aRdag_injective : Function.Injective aRdag := by
  intro ψ φ h
  funext ⟨m, k⟩
  have h1 := congrFun h (m, k + 1)
  simp only [aRdag, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at h1
  have hk : Real.sqrt ((k + 1 : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    exact (Real.sqrt_pos.mpr this).ne'
  exact mul_left_cancel₀ hk h1 |> fun h' => by
    simpa using h'

/-- **A nonzero vector has at most one radius.** If `(a_L − r a_R†) ψ = 0 = (a_L − r' a_R†) ψ`
with `r ≠ r'`, then `ψ = 0`. -/
theorem unique_radius (ψ : ℕ × ℕ → ℝ) (r r' : ℝ) (hrr : r ≠ r')
    (h1 : aL ψ - r • aRdag ψ = 0) (h2 : aL ψ - r' • aRdag ψ = 0) : ψ = 0 := by
  have h3 : (r' - r) • aRdag ψ = 0 := by
    have := sub_eq_zero.mpr (h1.trans h2.symm)
    calc (r' - r) • aRdag ψ = (aL ψ - r • aRdag ψ) - (aL ψ - r' • aRdag ψ) := by
          rw [sub_smul]; abel
      _ = 0 := by rw [h1, h2]; simp
  have h4 : aRdag ψ = 0 := by
    rcases smul_eq_zero.mp h3 with h | h
    · exact absurd (sub_eq_zero.mp h).symm hrr
    · exact h
  have h5 : aRdag ψ = aRdag 0 := by rw [h4]; funext ⟨m, k⟩; simp [aRdag]
  exact aRdag_injective h5

/-! ### Theta-control whitening -/

/-- **Whitening of the shifted-radius control.** For `a = p^θ` and `r = p^{-1/2}`, in a commutative
real algebra, `(1 − r a u)(1 − r a⁻¹ u) = 1 − 2 r cosh(θ log p) u + r² u²`. -/
theorem theta_whitening {R : Type*} [CommRing R] [Algebra ℝ R] (p θ : ℝ) (hp : 0 < p) (u : R) :
    (1 - (p ^ (-(1 / 2 : ℝ)) * p ^ θ) • u) * (1 - (p ^ (-(1 / 2 : ℝ)) * (p ^ θ)⁻¹) • u) =
      1 - (2 * p ^ (-(1 / 2 : ℝ)) * Real.cosh (θ * Real.log p)) • u +
        (p ^ (-(1 / 2 : ℝ))) ^ 2 • (u * u) := by
  have hc : p ^ θ + (p ^ θ)⁻¹ = 2 * Real.cosh (θ * Real.log p) := by
    rw [Real.cosh_eq, Real.rpow_def_of_pos hp, ← Real.exp_neg]
    rw [show Real.log p * θ = θ * Real.log p by ring]
    have : Real.exp (θ * Real.log p) ≠ 0 := (Real.exp_pos _).ne'
    ring
  set r := p ^ (-(1 / 2 : ℝ)) with hr
  have e : (r * p ^ θ + r * (p ^ θ)⁻¹) = 2 * r * Real.cosh (θ * Real.log p) := by
    rw [← mul_add, hc]; ring
  have e2 : (r * p ^ θ) * (r * (p ^ θ)⁻¹) = r ^ 2 := by
    have : p ^ θ ≠ 0 := (Real.rpow_pos_of_pos hp θ).ne'
    field_simp
  calc (1 - (r * p ^ θ) • u) * (1 - (r * (p ^ θ)⁻¹) • u)
      = 1 - ((r * p ^ θ) + (r * (p ^ θ)⁻¹)) • u + ((r * p ^ θ) * (r * (p ^ θ)⁻¹)) • (u * u) := by
        simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, add_smul, one_mul,
          mul_one]
        module
    _ = _ := by rw [e, e2]

/-- **Prime-power weights.** `p^{kθ} + p^{−kθ} = 2 cosh(kθ log p)`. -/
theorem weights_cosh (p θ k : ℝ) (hp : 0 < p) :
    p ^ (k * θ) + p ^ (-(k * θ)) = 2 * Real.cosh (k * θ * Real.log p) := by
  rw [Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hp, Real.cosh_eq]
  rw [show Real.log p * (k * θ) = k * θ * Real.log p by ring,
    show Real.log p * -(k * θ) = -(k * θ * Real.log p) by ring]
  ring

end GppRankOneControls
