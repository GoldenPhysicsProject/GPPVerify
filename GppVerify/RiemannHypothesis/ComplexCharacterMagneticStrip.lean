import Mathlib.Tactic

/-!
# Complex Dirichlet prime phases: magnetic two-strip involution and real-test blind spot

Source: Daniel Toupin / Golden Physics Project,
GPP-bridge work/codex/2026-10-15_complex_character_two_strip_magnetic_phase_obstruction.md.

In the first p=2-active Mellin window, the compressed prime shift acts on two
disjoint edge strips. A unit Euler phase a+i*b yields a Hermitian exchange
whose four-real-coordinate matrix is an involution when a^2+b^2=1.

Crucially: a Hermitian quadratic can be nonnegative on ALL real vectors but
negative on a complex vector. A first-window real-g certificate for a complex
Dirichlet character is therefore NOT automatically a GRH/complex-test certificate.

Only finite real algebra is formalized here. Neither the L² strip realization
nor the full signed Dirichlet Weil formula, RH or GRH is proved here.
-/

namespace GppComplexCharacterMagneticStrip

structure TwoComplexCoords where
  x : ℝ
  u : ℝ
  y : ℝ
  v : ℝ

/-- Multiplication by the Hermitian two-edge matrix with phase a+i*b,
written in four real coordinates z₁=x+i*u and z₂=y+i*v. -/
def magneticSwap (a b : ℝ) (z : TwoComplexCoords) : TwoComplexCoords :=
  ⟨a*z.y+b*z.v, a*z.v-b*z.y,
   a*z.x-b*z.u, a*z.u+b*z.x⟩

/-- The magnetic edge matrix squares to its squared phase modulus. -/
theorem magnetic_swap_square_scaled (a b : ℝ) (z : TwoComplexCoords) :
    magneticSwap a b (magneticSwap a b z) =
      ⟨(a*a+b*b)*z.x, (a*a+b*b)*z.u,
       (a*a+b*b)*z.y, (a*a+b*b)*z.v⟩ := by
  cases z with
  | mk x u y v =>
    simp [magneticSwap]
    <;> ring

/-- Every unit-phase prime strip exchange has exact square +1. -/
theorem magnetic_swap_involution (a b : ℝ) (h : a*a+b*b=1)
    (z : TwoComplexCoords) :
    magneticSwap a b (magneticSwap a b z) = z := by
  rw [magnetic_swap_square_scaled]
  cases z
  simp [h]

def magneticPairing (a b : ℝ) (z : TwoComplexCoords) : ℝ :=
  z.x*(magneticSwap a b z).x +
  z.u*(magneticSwap a b z).u +
  z.y*(magneticSwap a b z).y +
  z.v*(magneticSwap a b z).v

/-- The imaginary Euler phase contributes a distinct symplectic cross term. -/
theorem magnetic_pairing_components (a b : ℝ) (z : TwoComplexCoords) :
    magneticPairing a b z =
      2*a*(z.x*z.y+z.u*z.v) + 2*b*(z.x*z.v-z.u*z.y) := by
  cases z with
  | mk x u y v =>
    simp [magneticPairing, magneticSwap]
    <;> ring

/-- A real two-component test sees only Re(η(p))=a, never b=Im η(p). -/
theorem real_tests_invisible_imaginary_phase (a b x y : ℝ) :
    magneticPairing a b ⟨x,0,y,0⟩ = 2*a*x*y := by
  rw [magnetic_pairing_components]
  ring

def magneticEnergy (a b m : ℝ) (z : TwoComplexCoords) : ℝ :=
  m*(z.x^2+z.u^2+z.y^2+z.v^2) + magneticPairing a b z

/-- Positive on every REAL vector, despite a nontrivial imaginary prime phase. -/
theorem real_subspace_nonnegative (x y : ℝ) :
    0 ≤ magneticEnergy 0 1 (3/4) ⟨x,0,y,0⟩ := by
  simp [magneticEnergy, magnetic_pairing_components]
  positivity

/-- An explicitly negative COMPLEX vector for the same Hermitian quadratic. -/
theorem complex_witness_negative :
    magneticEnergy 0 1 (3/4) ⟨1,0,0,-1⟩ < 0 := by
  norm_num [magneticEnergy, magneticPairing, magneticSwap]

end GppComplexCharacterMagneticStrip
