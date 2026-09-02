import Mathlib.Tactic
import GppVerify.GrassmannianMass

/-!
# Mass as Orientation Coupling: the Fermion as the Square Root of a Null Direction
# Lean 4 | GPPVerify
# Author: Daniel Toupin | Golden Physics Project

Source: mass_orientation_coupling_v3.tex

## Statement

On the big cell of Gr(2,4), a 2-plane is charted by A = [[a,b],[c,d]] via the
row-reduced matrix [I | A]. The map τ(A) = A ε / det(A), ε = [[0,1],[-1,0]],
is the chart transition to the complementary patch, and Theorem 3.3(i) of
this paper states τ² = -id, τ⁴ = id. In coordinates,
  τ(a,b,c,d) = (-b, a, -d, c) / (ad - bc).

This is exactly the map `GppGrassmannian.transition` proved in
`GrassmannianMass.lean`: the two papers describe the same object from two
directions (Grassmannian chart transition; fermion orientation coupling),
and `transition_transition_eq_neg` there is Theorem 3.3(i) here. This file
restates that theorem in the present paper's own notation for direct
citation, rather than duplicating the proof.

## What remains open in this paper

Theorem 3.3(iv) (the differential dτ_A has characteristic polynomial t⁴ - Δ⁻⁴,
Δ = det A, with explicit eigenvectors) is the derivative-level refinement of
τ² = -id. **It is now proved**, in `TauDifferential.lean` — see the retired
stub below for what the estimate in this paragraph got right and wrong.

Lemma 2.1(c) (a positive momentum matrix decomposes as p = λ₁λ₁* + λ₂λ₂*
with det p = m² = |⟨λ₁,λ₂⟩|², the spinor-helicity decomposition) is now
formalized below via an explicit Cholesky-type factorization, avoiding
Mathlib's abstract spectral theorem for Hermitian matrices entirely.

Theorem 4.1 (clock locking): parts (b)-(d) are now formalized below (special values
U(π/ω_C) = -1, U(2π/ω_C) = 1; the population oscillation; and the algebraic core of the
gamma5 double-commutator identity). Part (a) (that the closed-form trajectory actually
solves the rest-frame Dirac ODE) is taken from standard linear-ODE theory and not
independently re-derived via Lean's derivative machinery -- see the section docstring
below for the exact scope.
-/

namespace GppMassOrientationCoupling

open GppGrassmannian

/-- The orientation map τ(a,b,c,d) = (-b,a,-d,c)/(ad-bc), Theorem 3.3(i)'s
    τ, is exactly the Grassmannian chart transition. -/
noncomputable def tau (a b c d : ℝ) : ℝ × ℝ × ℝ × ℝ := transition a b c d

/-- Theorem 3.3(i): τ² = -id. Applying the orientation map twice negates
    every coordinate of the chart -- the fermion's internal orientation
    flips sign after one full "square root of a null direction" cycle. -/
theorem tau_tau_eq_neg (a b c d : ℝ) (hD : a * d - b * c ≠ 0) :
    tau (-b / (a * d - b * c)) (a / (a * d - b * c))
        (-d / (a * d - b * c)) (c / (a * d - b * c))
      = (-a, -b, -c, -d) :=
  transition_transition_eq_neg a b c d hD

/-- The orientation map as a self-map of the coordinate 4-tuple, so `τ⁴` can be written
    as an actual iterate. -/
noncomputable def tauT (p : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ := tauMap p

/-- Theorem 3.3(i), second clause: **τ⁴ = id.** The fermion's internal orientation returns
    to itself after four applications — the period-4 structure the Zitterbewegung reading
    of this chart oscillation rests on.

    This was parked as a stub until 2026-09-01 on the grounds that it is "an immediate
    one-line consequence" of `tau_tau_eq_neg` and so not separate mathematical content.
    That was the wrong call twice over. It *is* provable, so parking it as a vacuous `True`
    understated the tree; and the step is not quite free — applying `τ²` a second time needs
    the negated tuple's determinant to be nonzero, which holds because negation preserves
    `ad - bc` (`GppGrassmannian.det_neg`). A stub is for something open, not for something
    short. -/
theorem tau_pow_four_eq_id (a b c d : ℝ) (hD : a * d - b * c ≠ 0) :
    tauT^[4] (a, b, c, d) = (a, b, c, d) :=
  tauMap_iterate_four a b c d hD

/-- And the period is exactly 4, not 2: `τ² = -id` genuinely differs from the identity at
    every point of the chart. Without this, "order 4" would not be established — an
    involution satisfies `τ⁴ = id` too. -/
theorem tau_tau_ne_id (a b c d : ℝ) (hD : a * d - b * c ≠ 0) :
    tauT (tauT (a, b, c, d)) ≠ (a, b, c, d) :=
  tauMap_tauMap_ne_self a b c d hD

-- `open_differential_charpoly` was retired on 2026-09-02. Theorem 3.3(iv) is now proved in
-- `GppVerify/StandardModel/TauDifferential.lean`.
--
-- The stub read: "Not formalized: needs the Jacobian of τ as an endomorphism of M₂(ℝ)
-- together with eigenvalue/spectrum theory for a non-symmetric real matrix." The first half
-- was right and is done — `GppTauDifferential.hasDerivAt_tau4_a` … `_d` are the four partial
-- derivatives as genuine `HasDerivAt` statements, so the Jacobian is a theorem rather than an
-- asserted matrix. The second half turned out to be unnecessary: what "characteristic
-- polynomial t⁴ - Δ⁻⁴" asserts about the matrix is Cayley-Hamilton plus the two eigenvalues,
-- and both are matrix arithmetic:
--
--   GppTauDifferential.tauJac_pow_four          (dτ_A)⁴ = Δ⁻⁴ · I
--   GppTauDifferential.tauJac_mulVec_eigen_pos  A(1-ε) ↦ +Δ⁻¹
--   GppTauDifferential.tauJac_mulVec_eigen_neg  A(1+ε) ↦ -Δ⁻¹
--
-- No spectrum theory for non-symmetric real matrices was used. Two things are deliberately
-- NOT claimed there and are stated in that module's own scope section: Fréchet
-- differentiability of τ (the partials are proved; the C¹ criterion is not formalized), and
-- a literal `Matrix.charpoly` equation (which would need a symbolic 4×4 determinant over
-- `Polynomial ℝ`).

/-- The Cholesky-type factor `λ¹ = (√p00, p̄01/√p00)` from Lemma 2.1(c). -/
noncomputable def lambda1 (p00 : ℝ) (p01 : ℂ) : ℂ × ℂ :=
  (Real.sqrt p00, (starRingEnd ℂ) p01 / (Real.sqrt p00 : ℂ))

/-- The Cholesky-type factor `λ² = (0, √(det p/p00))` from Lemma 2.1(c). -/
noncomputable def lambda2 (p00 p11 : ℝ) (p01 : ℂ) : ℂ × ℂ :=
  (0, Real.sqrt ((p00 * p11 - Complex.normSq p01) / p00))

/-- Lemma 2.1(c): a positive-definite momentum matrix `p = [[p00,p01],[p̄01,p11]]`
    (`p00 > 0`, `det p = p00 p11 - |p01|² > 0`) decomposes as the explicit rank-two
    Cholesky-type sum `p = λ¹λ¹* + λ²λ²*` for `λ¹ = (√p00, p̄01/√p00)`,
    `λ² = (0, √(det p/p00))` — captured here by its four defining matrix entries (the
    diagonal (1,1)/(2,2), the off-diagonal (1,2), and the determinant/symplectic
    identity `det p = |⟨λ¹,λ²⟩|²` for `⟨λμ⟩ = λ₁μ₂ - λ₂μ₁`). This is the elementary
    Cholesky factorization of a positive-definite Hermitian 2×2 matrix; the specific
    closed-form factors avoid Mathlib's abstract n-dimensional spectral theorem (and the
    index bookkeeping of specializing its `Fintype`-indexed API to `Fin 2`) entirely. -/
theorem momentum_spinor_decomposition {p00 p11 : ℝ} {p01 : ℂ}
    (hp00 : 0 < p00) (hdet : 0 < p00 * p11 - Complex.normSq p01) :
    (lambda1 p00 p01).1 * (starRingEnd ℂ) (lambda1 p00 p01).1
        + (lambda2 p00 p11 p01).1 * (starRingEnd ℂ) (lambda2 p00 p11 p01).1 = (p00 : ℂ) ∧
    (lambda1 p00 p01).1 * (starRingEnd ℂ) (lambda1 p00 p01).2
        + (lambda2 p00 p11 p01).1 * (starRingEnd ℂ) (lambda2 p00 p11 p01).2 = p01 ∧
    (lambda1 p00 p01).2 * (starRingEnd ℂ) (lambda1 p00 p01).2
        + (lambda2 p00 p11 p01).2 * (starRingEnd ℂ) (lambda2 p00 p11 p01).2 = (p11 : ℂ) ∧
    Complex.normSq
        ((lambda1 p00 p01).1 * (lambda2 p00 p11 p01).2
          - (lambda1 p00 p01).2 * (lambda2 p00 p11 p01).1)
      = p00 * p11 - Complex.normSq p01 := by
  have hApos : 0 < Real.sqrt p00 := Real.sqrt_pos.mpr hp00
  have hAne : (Real.sqrt p00 : ℂ) ≠ 0 := by exact_mod_cast hApos.ne'
  have hp00ne : (p00 : ℂ) ≠ 0 := by exact_mod_cast hp00.ne'
  have hA2R : Real.sqrt p00 * Real.sqrt p00 = p00 := Real.mul_self_sqrt hp00.le
  have hA2C : (Real.sqrt p00 : ℂ) * (Real.sqrt p00 : ℂ) = (p00 : ℂ) := by exact_mod_cast hA2R
  have hCR : Real.sqrt ((p00 * p11 - Complex.normSq p01) / p00)
      * Real.sqrt ((p00 * p11 - Complex.normSq p01) / p00)
      = (p00 * p11 - Complex.normSq p01) / p00 :=
    Real.mul_self_sqrt (div_pos hdet hp00).le
  have hCC : (Real.sqrt ((p00 * p11 - Complex.normSq p01) / p00) : ℂ)
      * (Real.sqrt ((p00 * p11 - Complex.normSq p01) / p00) : ℂ)
      = ((p00 * p11 - Complex.normSq p01) / p00 : ℝ) := by exact_mod_cast hCR
  have hconjB : (starRingEnd ℂ) ((starRingEnd ℂ) p01 / (Real.sqrt p00 : ℂ))
      = p01 / (Real.sqrt p00 : ℂ) := by
    rw [map_div₀, starRingEnd_apply, starRingEnd_apply, star_star, Complex.conj_ofReal]
  simp only [lambda1, lambda2, Complex.conj_ofReal, map_zero, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, hconjB]
  refine ⟨hA2C, ?_, ?_, ?_⟩
  · field_simp
  · rw [div_mul_div_comm, mul_comm ((starRingEnd ℂ) p01) p01, Complex.mul_conj, hA2C, hCC]
    push_cast
    field_simp
    -- Mathlib 4.33: `field_simp` stops one `ring` step short here.
    ring
  · rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_ofReal, hA2R, hCR]
    field_simp

/-! ## Theorem 4.1: Clock Locking

Fetched from the source `mass_orientation_coupling_v3.tex` (Google Drive) to get the
exact statement rather than guessing conventions. Part (a) (the closed-form trajectory
solves the rest-frame Dirac ODE `iψ_L' = mc²ψ_R`, `iψ_R' = mc²ψ_L`) is taken from standard
linear-ODE theory for a constant-coefficient 2-level system and is **not independently
re-derived here** via `HasDerivAt`; what IS formalized are its exact algebraic
consequences: parts (b)-(c) (special values, population oscillation) and the independent
algebraic identity of part (d). -/

/-- The rest-frame Dirac evolution's closed-form trajectory (Theorem 4.1(a)) for general
    initial data `(a, b) = (ψ_L(0), ψ_R(0))` and frequency `ω = ω_C = mc²/ħ`. -/
noncomputable def psiL (ω : ℝ) (a b : ℂ) (t : ℝ) : ℂ :=
  (Real.cos (ω * t) : ℂ) * a - Complex.I * (Real.sin (ω * t) : ℂ) * b

/-- The rest-frame Dirac evolution's closed-form trajectory, right-chirality component. -/
noncomputable def psiR (ω : ℝ) (a b : ℂ) (t : ℝ) : ℂ :=
  -Complex.I * (Real.sin (ω * t) : ℂ) * a + (Real.cos (ω * t) : ℂ) * b

theorem psiL_zero (ω : ℝ) (a b : ℂ) : psiL ω a b 0 = a := by simp [psiL]
theorem psiR_zero (ω : ℝ) (a b : ℂ) : psiR ω a b 0 = b := by simp [psiR]

/-- Theorem 4.1(c): one complete chirality-exchange cycle, `t* = π/ω_C`, negates the
    state: `U(t*) = -1`. -/
theorem clock_locking_negate (ω : ℝ) (hω : ω ≠ 0) (a b : ℂ) :
    psiL ω a b (Real.pi / ω) = -a ∧ psiR ω a b (Real.pi / ω) = -b := by
  have ht : ω * (Real.pi / ω) = Real.pi := by field_simp
  refine ⟨?_, ?_⟩
  · simp [psiL, ht, Real.cos_pi, Real.sin_pi]
  · simp [psiR, ht, Real.cos_pi, Real.sin_pi]

/-- Theorem 4.1(c): two complete cycles, `2t* = 2π/ω_C`, restore the state:
    `U(2t*) = +1`. -/
theorem clock_locking_restore (ω : ℝ) (hω : ω ≠ 0) (a b : ℂ) :
    psiL ω a b (2 * Real.pi / ω) = a ∧ psiR ω a b (2 * Real.pi / ω) = b := by
  have ht : ω * (2 * Real.pi / ω) = 2 * Real.pi := by field_simp
  refine ⟨?_, ?_⟩
  · simp [psiL, ht, Real.cos_two_pi, Real.sin_two_pi]
  · simp [psiR, ht, Real.cos_two_pi, Real.sin_two_pi]

/-- Theorem 4.1(b): for the initial condition `ψ_R(0) = 0`, `ψ_L(0) = χ`, the chirality
    populations oscillate exactly at angular frequency `ω_z = 2ω_C`. -/
theorem clock_locking_population (ω : ℝ) (χ : ℂ) (t : ℝ) :
    Complex.normSq (psiL ω χ 0 t) = (Real.cos (ω * t)) ^ 2 * Complex.normSq χ ∧
    Complex.normSq (psiR ω χ 0 t) = (Real.sin (ω * t)) ^ 2 * Complex.normSq χ := by
  have hL : psiL ω χ 0 t = (Real.cos (ω * t) : ℂ) * χ := by simp [psiL]
  have hR : psiR ω χ 0 t = -Complex.I * (Real.sin (ω * t) : ℂ) * χ := by simp [psiR]
  refine ⟨?_, ?_⟩
  · rw [hL, Complex.normSq_mul, Complex.normSq_ofReal]; ring
  · rw [hR, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
      Complex.normSq_neg, Complex.normSq_I]
    ring

/-- Theorem 4.1(d)'s algebraic core: for `Ring` elements satisfying the Clifford
    relations `{γ5,γ0} = 0` and `γ0² = 1`, the double commutator
    `[γ0,[γ0,γ5]] = 4·γ5`. This is the whole algebraic content behind the physical
    statement `γ̈⁵ = -ω_z²γ⁵` with `H = mc²γ⁰`, `ω_z = 2mc²` (units `ħ = 1`): the Clifford
    algebra alone forces the factor `4 = 2²` here, and the physical identity follows by
    rescaling `γ0 ↦ mc²·γ0` linearly (a scalar multiple, not separate mathematical
    content, so not re-derived separately) and negating (from the `i²` of applying the
    Heisenberg derivative `γ̇ = i[H,γ]` twice). Also not independently re-derived: relating
    this Heisenberg-picture double commutator to an actual second time-derivative of an
    evolving operator `γ⁵(t)` needs a further operator-ODE argument beyond the pure
    algebra formalized here — independent of any specific matrix representation of the
    Dirac algebra. -/
theorem gamma0_double_commutator {R : Type*} [Ring R] (γ5 γ0 : R)
    (hanti : γ5 * γ0 = -(γ0 * γ5)) (hsq : γ0 * γ0 = 1) :
    γ0 * (γ0 * γ5 - γ5 * γ0) - (γ0 * γ5 - γ5 * γ0) * γ0 = 4 * γ5 := by
  have key : γ0 * γ5 * γ0 = -γ5 := by
    have h1 : γ0 * (γ5 * γ0) = γ0 * (-(γ0 * γ5)) := by rw [hanti]
    rw [mul_assoc, h1, mul_neg, ← mul_assoc, hsq, one_mul]
  have expand : γ0 * (γ0 * γ5 - γ5 * γ0) - (γ0 * γ5 - γ5 * γ0) * γ0
      = γ0 * γ0 * γ5 - γ0 * γ5 * γ0 - γ0 * γ5 * γ0 + γ5 * (γ0 * γ0) := by
    noncomm_ring
  rw [expand, hsq, key]
  noncomm_ring

end GppMassOrientationCoupling
