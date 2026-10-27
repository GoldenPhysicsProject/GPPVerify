import Mathlib.Tactic

/-!
# Hidden zeros of Tr(φ³) tree amplitudes — finite instances (n = 4, 5, 6)

FORMALIZATION-OF-KNOWN. This module kernel-checks the first finite instances
of the hidden-zeros theorem of

  N. Arkani-Hamed, Q. Cao, J. Dong, C. Figueiredo, S. He,
  "Hidden zeros for particle/string amplitudes and the unity of colored
  scalars, pions and gluons", arXiv:2312.16282v3 [hep-th] (30 Dec 2024), §§2–3.

Only finite instances are proved here (n = 4, n = 5 and n = 6 below); the
general causal-diamond statement of §3.2 of the paper is *not* formalized.

## The paper's setup (verbatim content)

Kinematic basis (§2): for a fixed color ordering `(1, …, n)` and momenta
`pᵢ` drawn as the edges of the momentum polygon, the planar variables are

  `X_{i,j} = (p_i + ⋯ + p_{j-1})²`                        (eq. (2.2))

and the non-planar variables are `c_{i,j} = -2 p_i · p_j` (eq. (2.3)), related by

  `c_{i,j} = X_{i,j} + X_{i+1,j+1} - X_{i,j+1} - X_{i+1,j}`  (eq. (2.4))

with `X_{i,i+1} = p_i² = 0` (massless particles).

The amplitude `𝒜ₙ` is the sum over triangulations `𝒯` of the `n`-gon of
`∏_{(i,j) ∈ 𝒯} 1/X_{i,j}` (the Feynman-diagram expansion; exhibited explicitly
in eqs. (3.1) and (3.6) of the paper).

Abstract: "the tree-level Tr(φ³) field theory amplitudes have a hidden pattern
of zeros when a special set of non-planar Mandelstam invariants is set to
zero."

General statement (§3.2, "Zeros"): "Pick a point in the mesh, i.e. a planar
variable `X_B`, and consider the causal diamond anchored in this variable …
Setting all the `c_{i,j}` inside this causal diamond to zero will make the
amplitude vanish."

## Translation used below

Everything is stated over an arbitrary field `K`; the `X`'s and `c`'s are
independent elements of `K` subject only to the relations (2.4) (with the
boundary values `X_{i,i+1} = 0`), exactly as the paper treats a choice of
kinematic basis (e.g. the ray-like basis of §2.2.2, eq. (2.7)).
-/

namespace GppHiddenZeros

variable {K : Type*} [Field K]

/-! ## n = 4 -/

/-- The 4-point Tr(φ³) amplitude: the sum over the two triangulations of the
quadrilateral, `𝒜₄ = 1/X_{1,3} + 1/X_{2,4}`. -/
def amp4 (X13 X24 : K) : K := 1 / X13 + 1 / X24

/-- The 4-point hidden zero, in the paper's variables. By eq. (2.5),
`X_{1,3} + X_{2,4} = c_{1,3}`, where `c_{1,3} = -u` is (minus) the non-planar
Mandelstam invariant. Hence, under the momentum-conservation constraint
`X_{1,3} + X_{2,4} + u = 0`,

  `𝒜₄ = -u / (X_{1,3} X_{2,4})`. -/
theorem amp4_eq_neg_u_div (X13 X24 u : K) (h13 : X13 ≠ 0) (h24 : X24 ≠ 0)
    (hstu : X13 + X24 + u = 0) :
    amp4 X13 X24 = -u / (X13 * X24) := by
  have h : X13 + X24 = -u := by linear_combination hstu
  unfold amp4
  rw [div_add_div _ _ h13 h24, one_mul, mul_one, add_comm X24 X13, h]

/-- The same identity phrased with the paper's `c_{1,3}` (eq. (2.5)):
if `X_{1,3} + X_{2,4} = c_{1,3}` then `𝒜₄ = c_{1,3} / (X_{1,3} X_{2,4})`. -/
theorem amp4_eq_c13_div (X13 X24 c13 : K) (h13 : X13 ≠ 0) (h24 : X24 ≠ 0)
    (h : X13 + X24 = c13) :
    amp4 X13 X24 = c13 / (X13 * X24) := by
  unfold amp4
  rw [div_add_div _ _ h13 h24, one_mul, mul_one, add_comm X24 X13, h]

/-- The 4-point hidden zero itself: `𝒜₄ = 0` when the non-planar invariant
vanishes, i.e. when `u = 0`, equivalently `X_{1,3} + X_{2,4} = 0`
(`c_{1,3} = 0`). -/
theorem amp4_eq_zero_of_u_eq_zero (X13 X24 : K) (h13 : X13 ≠ 0) (h24 : X24 ≠ 0)
    (h : X13 + X24 = 0) : amp4 X13 X24 = 0 := by
  have hstu : X13 + X24 + (0 : K) = 0 := by simpa using h
  simpa using amp4_eq_neg_u_div X13 X24 0 h13 h24 hstu

/-! ## n = 5 -/

/-- The 5-point Tr(φ³) amplitude, eq. (3.1) of the paper verbatim: the sum
over the five triangulations of the pentagon,

  `𝒜₅ = 1/(X_{1,3}X_{1,4}) + 1/(X_{2,4}X_{2,5}) + 1/(X_{1,3}X_{3,5})
      + 1/(X_{1,4}X_{2,4}) + 1/(X_{2,5}X_{3,5})`. -/
def amp5 (X13 X14 X24 X25 X35 : K) : K :=
  1 / (X13 * X14) + 1 / (X24 * X25) + 1 / (X13 * X35)
    + 1 / (X14 * X24) + 1 / (X25 * X35)

/-- Factorization near the zero, eq. (3.3) of the paper: on the locus
`c_{1,4} = 0` — i.e., by eq. (2.4) with `X_{1,5} = 0`,
`X_{1,4} + X_{2,5} - X_{2,4} = 0` — the 5-point amplitude factors as the
product of two 4-point amplitudes,
`𝒜₅ = 𝒜₄(X_{1,3}, X_{2,5}) · 𝒜₄(X_{1,4}, X_{3,5})`. -/
theorem amp5_factor_of_c14_eq_zero (X13 X14 X24 X25 X35 : K)
    (h13 : X13 ≠ 0) (h14 : X14 ≠ 0) (h24 : X24 ≠ 0) (h25 : X25 ≠ 0)
    (h35 : X35 ≠ 0) (hc14 : X14 + X25 - X24 = 0) :
    amp5 X13 X14 X24 X25 X35 = amp4 X13 X25 * amp4 X14 X35 := by
  have e24 : X24 = X14 + X25 := by linear_combination -hc14
  rw [e24] at h24
  unfold amp5 amp4
  rw [e24]
  field_simp
  ring

/-- Factorization near the zero, eq. (3.5) of the paper: on the locus
`c_{1,3} = 0` — i.e., by eq. (2.4) with `X_{2,3} = 0`,
`X_{1,3} + X_{2,4} - X_{1,4} = 0` — the 5-point amplitude factors as
`𝒜₅ = 𝒜₄(X_{1,3}, X_{2,5}) · 𝒜₄(X_{2,4}, X_{3,5})`. -/
theorem amp5_factor_of_c13_eq_zero (X13 X14 X24 X25 X35 : K)
    (h13 : X13 ≠ 0) (h14 : X14 ≠ 0) (h24 : X24 ≠ 0) (h25 : X25 ≠ 0)
    (h35 : X35 ≠ 0) (hc13 : X13 + X24 - X14 = 0) :
    amp5 X13 X14 X24 X25 X35 = amp4 X13 X25 * amp4 X24 X35 := by
  have e14 : X14 = X13 + X24 := by linear_combination -hc13
  rw [e14] at h14
  unfold amp5 amp4
  rw [e14]
  field_simp
  ring

/-- The 5-point hidden zero (§3.1.1 of the paper): "by setting
`c_{1,3} = c_{1,4} = 0` … the pentagon collapses into a line segment, which
then means that the amplitude vanishes in this limit!" Here the locus
conditions are the eq. (2.4) expressions
`c_{1,3} = X_{1,3} + X_{2,4} - X_{1,4}` (using `X_{2,3} = 0`) and
`c_{1,4} = X_{1,4} + X_{2,5} - X_{2,4}` (using `X_{1,5} = 0`). -/
theorem amp5_eq_zero_of_c13_c14_eq_zero (X13 X14 X24 X25 X35 : K)
    (h13 : X13 ≠ 0) (h14 : X14 ≠ 0) (h24 : X24 ≠ 0) (_h25 : X25 ≠ 0)
    (h35 : X35 ≠ 0) (hc13 : X13 + X24 - X14 = 0) (hc14 : X14 + X25 - X24 = 0) :
    amp5 X13 X14 X24 X25 X35 = 0 := by
  have e24 : X24 = X14 - X13 := by linear_combination hc13
  have e25 : X25 = -X13 := by linear_combination hc13 + hc14
  rw [e24] at h24
  rw [e25] at _h25
  unfold amp5
  rw [e24, e25]
  field_simp
  ring

/-- The second 5-point zero family of §3.1.1: the amplitude also vanishes on
`c_{1,4} = c_{2,4} = 0`, where by eq. (2.4) with `X_{3,4} = 0`,
`c_{2,4} = X_{2,4} + X_{3,5} - X_{2,5}`. (The paper: "by setting
`c_{1,3} = c_{1,4} = 0` or `c_{1,4} = c_{2,4} = 0`, the pentagon collapses
into a line segment.") -/
theorem amp5_eq_zero_of_c14_c24_eq_zero (X13 X14 X24 X25 X35 : K)
    (h13 : X13 ≠ 0) (h14 : X14 ≠ 0) (h24 : X24 ≠ 0) (h25 : X25 ≠ 0)
    (_h35 : X35 ≠ 0) (hc14 : X14 + X25 - X24 = 0) (hc24 : X24 + X35 - X25 = 0) :
    amp5 X13 X14 X24 X25 X35 = 0 := by
  have e24 : X24 = X14 + X25 := by linear_combination -hc14
  have e35 : X35 = -X14 := by linear_combination hc14 + hc24
  rw [e24] at h24
  rw [e35] at _h35
  unfold amp5
  rw [e24, e35]
  field_simp
  ring

/-! ## n = 6 -/

/-- The 6-point Tr(φ³) amplitude: the sum over the 14 triangulations of the
hexagon. The paper (§3.1.2) says: "The six-particle amplitude is a sum of
14 terms, corresponding to the Feynman diagrams in three cyclic classes",
and displays in eq. (3.6) the fan representative `1/(X_{1,3}X_{1,4}X_{1,5})`,
the representative `1/(X_{1,3}X_{3,6}X_{4,6})` "+ cyclic", and the two
alternating triangulations `1/(X_{1,3}X_{3,5}X_{1,5})`,
`1/(X_{2,4}X_{4,6}X_{2,6})`.

The terms below are grouped as: the six fans; the cyclic class of
`{X_{1,3}, X_{3,6}, X_{4,6}}` (3 terms); its reflection class
`{X_{1,3}, X_{1,4}, X_{4,6}}` (3 terms); and the two alternating
triangulations. Note: expanding the "+ cyclic" of eq. (3.6) as bare ℤ₆
rotations of the two displayed terms yields only 11 distinct terms, and
that 11-term sum does *not* vanish on the zero locus below (checked in
exact rational arithmetic); the reflection class is required for the
paper's stated count of 14. This definition is the full sum over all 14
triangulations of the hexagon. -/
def amp6 (X13 X14 X15 X24 X25 X26 X35 X36 X46 : K) : K :=
  1 / (X13 * X14 * X15) + 1 / (X24 * X25 * X26) + 1 / (X35 * X36 * X13)
    + 1 / (X14 * X24 * X46) + 1 / (X15 * X25 * X35) + 1 / (X26 * X36 * X46)
    + 1 / (X13 * X36 * X46) + 1 / (X14 * X15 * X24) + 1 / (X25 * X26 * X35)
    + 1 / (X13 * X14 * X46) + 1 / (X15 * X24 * X25) + 1 / (X26 * X35 * X36)
    + 1 / (X13 * X35 * X15) + 1 / (X24 * X46 * X26)

/-- The 6-point "skinny rectangle" hidden zero (§3.1.2 of the paper): "If we
set `c_{1,3}, c_{1,4}, c_{1,5} → 0`, then the three-dimensional associahedron
collapses in the `X_{1,3}` direction … showing that the amplitude vanishes
in this limit."

The locus conditions are the eq. (2.4) expressions for the three `c`'s of
the bottom causal diamond, using the boundary values `X_{2,3} = X_{1,6} = 0`:
`c_{1,3} = X_{1,3} + X_{2,4} - X_{1,4}`,
`c_{1,4} = X_{1,4} + X_{2,5} - X_{1,5} - X_{2,4}`,
`c_{1,5} = X_{1,5} + X_{2,6} - X_{2,5}`.
No condition on `X_{3,5}, X_{3,6}, X_{4,6}` is needed: on this locus the
amplitude vanishes for all their (nonzero) values, since the remaining
mesh variables `c_{2,4}, c_{2,5}, c_{3,5}` range freely. -/
theorem amp6_eq_zero_skinny_rectangle (X13 X14 X15 X24 X25 X26 X35 X36 X46 : K)
    (h13 : X13 ≠ 0) (h14 : X14 ≠ 0) (h15 : X15 ≠ 0) (h24 : X24 ≠ 0)
    (h25 : X25 ≠ 0) (_h26 : X26 ≠ 0) (h35 : X35 ≠ 0) (h36 : X36 ≠ 0)
    (h46 : X46 ≠ 0)
    (hc13 : X13 + X24 - X14 = 0)
    (hc14 : X14 + X25 - X15 - X24 = 0)
    (hc15 : X15 + X26 - X25 = 0) :
    amp6 X13 X14 X15 X24 X25 X26 X35 X36 X46 = 0 := by
  have e24 : X24 = X14 - X13 := by linear_combination hc13
  have e25 : X25 = X15 - X13 := by linear_combination hc13 + hc14
  have e26 : X26 = -X13 := by linear_combination hc13 + hc14 + hc15
  rw [e24] at h24
  rw [e25] at h25
  rw [e26] at _h26
  unfold amp6
  rw [e24, e25, e26]
  field_simp
  ring

end GppHiddenZeros
