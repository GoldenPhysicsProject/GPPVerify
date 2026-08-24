import Mathlib.Tactic

/-!
# The antipodal-pairing solution of the two-particle massless constraint (algebraic core)

From `Loops_from_Cuts_in_Celestial_Holography.tex`, Theorem "Cut geometry: antipodal
pairing and uniform measure" (`thm:measure`) — the first, most novel, and most important
link (`L1`) of the whole new canonical loop paper: two massless momenta `ℓ₅ = ω₅q(z₅,z̄₅)`,
`ℓ₆ = ω₆q(z₆,z̄₆)` summing to a rest-frame total `P = (M,0,0,0)` are forced onto **antipodal**
celestial points, with
```
z₆ = -1/z̄₅,   ω₅ = M/(2(1+|z₅|²)),   ω₆ = M|z₅|²/(2(1+|z₅|²)).
```

## What this file proves

The **algebraic core** of `thm:measure`: `antipodal_solves_conservation` verifies, by direct
vector computation (no measure theory), that the paper's stated formulas genuinely solve all
four components of `P = ℓ₅ + ℓ₆`, for every `z₅ ≠ 0` and every `M`. This is the concrete,
checkable content the theorem's uniqueness claim rests on — the paper asserts this solution
is the *unique* one, which this file does not attempt (see below), but does not need to be
taken on faith either: the solution stated genuinely works, verified here from the bare
null-vector parametrization
`q(x,y) = (1+x²+y², 2x, 2y, 1-x²-y²)` (`x,y` the real/imaginary parts of the celestial
coordinate `z`, the real-Lorentzian convention already used elsewhere in this repo, e.g.
`ShadowSignOpposition.lean`), with the Minkowski inner product `⟨u,v⟩ = u₀v₀-u₁v₁-u₂v₂-u₃v₃`
(metric `(+,-,-,-)`, matching the paper's own convention).

`qVec_isNull`: every `q(x,y)` is null (`⟨q,q⟩=0`) — the general fact that makes `ω·q(x,y)`
a genuine massless on-shell momentum for any energy `ω`, verified independently of the
antipodal solution itself (needed to confirm `ℓ₅`, `ℓ₆` are honestly massless, not merely
that their sum happens to equal `P`).

## What this file does NOT do

Does not attempt uniqueness of the solution (the paper's own claim that this is the *only*
way to solve the constraint — a genuinely separate fact, needing an argument about the
`SO(3)`-orbit structure of the two-sphere of null directions, not attempted here), and does
not attempt the phase-space **measure** reduction itself (`dΠ₂ = d²z/[8π²(1+|z|²)²]`,
`∫dΠ₂=1/(8π)`) — that requires genuine measure-theoretic machinery (a `δ⁴`-constrained
pushforward measure and its Jacobian) this repo has never built, and is a substantially
larger undertaking left open, precisely, as the next step of this thread. No axiom, no sorry.
-/

namespace GppAntipodalPairing

/-- The null celestial-sphere momentum direction `q(x,y) = (1+x²+y², 2x, 2y, 1-x²-y²)`,
matching the paper's `q(z,z̄)` on the real-Lorentzian slice `z = x+iy`, `z̄ = x-iy`. Indexed
by `Fin 4` as `(q₀,q₁,q₂,q₃)`, metric `(+,-,-,-)`. -/
def qVec (x y : ℝ) : Fin 4 → ℝ :=
  ![1 + x ^ 2 + y ^ 2, 2 * x, 2 * y, 1 - x ^ 2 - y ^ 2]

/-- The Minkowski inner product, metric `(+,-,-,-)`. -/
def mink (u v : Fin 4 → ℝ) : ℝ := u 0 * v 0 - u 1 * v 1 - u 2 * v 2 - u 3 * v 3

/-- **Every `q(x,y)` is null**: `⟨q,q⟩ = 0`, for every `x,y`. -/
theorem qVec_isNull (x y : ℝ) : mink (qVec x y) (qVec x y) = 0 := by
  simp only [mink, qVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  ring

/-- **The antipodal-pairing solution genuinely solves momentum conservation**: for every
`x₅ y₅ : ℝ` with `(x₅,y₅) ≠ (0,0)` and every `M : ℝ`, the paper's stated formulas
`z₆ = -z₅/|z₅|²`, `ω₅ = M/(2(1+|z₅|²))`, `ω₆ = M|z₅|²/(2(1+|z₅|²))` give
`ω₅·q(x₅,y₅) + ω₆·q(x₆,y₆) = (M,0,0,0)`, componentwise. -/
theorem antipodal_solves_conservation (x5 y5 M : ℝ) (h5 : x5 ^ 2 + y5 ^ 2 ≠ 0) :
    let r2 := x5 ^ 2 + y5 ^ 2
    let x6 := -x5 / r2
    let y6 := -y5 / r2
    let ω5 := M / (2 * (1 + r2))
    let ω6 := M * r2 / (2 * (1 + r2))
    (fun i => ω5 * qVec x5 y5 i + ω6 * qVec x6 y6 i) = ![M, 0, 0, 0] := by
  intro r2 x6 y6 ω5 ω6
  have hr2 : r2 ≠ 0 := h5
  have h1r2 : (1 : ℝ) + r2 ≠ 0 := by positivity
  funext i
  fin_cases i <;>
    simp only [qVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, x6, y6, ω5, ω6, r2] <;>
    field_simp <;> ring

end GppAntipodalPairing
