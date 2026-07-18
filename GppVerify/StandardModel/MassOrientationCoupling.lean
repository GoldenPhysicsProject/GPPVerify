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

Theorem 3.3(iv) (the differential dτ_A has characteristic polynomial
t⁴ - Δ⁻⁴, Δ = det A, with explicit eigenvectors) is the derivative-level
refinement of τ² = -id and is not formalized here: it needs the Jacobian
of τ as an actual endomorphism together with Mathlib's eigenvalue/spectrum
machinery for a non-symmetric real matrix, which is a substantial further
undertaking (see the discussion in `GrassmannianMass.lean`).

Lemma 2.1(c) (a positive momentum matrix decomposes as p = λ₁λ₁* + λ₂λ₂*
with det p = m² = |⟨λ₁,λ₂⟩|², the spinor-helicity decomposition) requires
the spectral decomposition of a Hermitian matrix and is not formalized here.

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

/-- Theorem 3.3(i), second clause: τ⁴ = id, since (-id)² = id. Not stated
    as a further Lean theorem beyond `tau_tau_eq_neg`, since it is an
    immediate one-line consequence (apply the above to the negated tuple,
    whose determinant (-a)(-d)-(-b)(-c) = ad-bc is unchanged) rather than
    separate mathematical content. -/
theorem tau_pow_four_remark : True := trivial

/-- Theorem 3.3(iv): the differential dτ_A has characteristic polynomial
    t⁴ - Δ⁻⁴ (Δ = det A) with explicit eigenvectors A(1∓ε)/2 for
    eigenvalues ±Δ⁻¹. Not formalized: needs the Jacobian of τ as an
    endomorphism of M₂(ℝ) together with eigenvalue/spectrum theory for a
    non-symmetric real matrix. Verified symbolically and numerically in
    the companion script (charpoly, eigenvectors, ensemble of 500 random
    matrices, unit-determinant fourth-roots-of-unity locus). -/
theorem differential_charpoly : True := trivial

/-- Lemma 2.1(c): a future timelike momentum matrix p decomposes as
    p = λ₁λ₁* + λ₂λ₂* with det p = m² = |⟨λ₁,λ₂⟩|² (spinor-helicity
    decomposition). Not formalized: needs the spectral decomposition of a
    Hermitian matrix. Verified numerically on 200 random samples in the
    companion script. -/
theorem momentum_spinor_decomposition : True := trivial

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
  have ht : ω * (2 * Real.pi / ω) = 2 * Real.pi := by field_simp; ring
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
