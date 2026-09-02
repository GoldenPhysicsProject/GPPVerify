import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# The differential of the orientation map τ (Theorem 3.3(iv))

Source: `mass_orientation_coupling_v3.tex`, Theorem 3.3(iv).

On the big cell of `Gr(2,4)` a 2-plane is charted by `A = [[a,b],[c,d]]`, and the chart
transition to the complementary patch is `τ(A) = A ε / det A` with `ε = [[0,1],[-1,0]]`. In
coordinates `τ(a,b,c,d) = (-b, a, -d, c) / (ad - bc)`. Theorem 3.3(i) — `τ² = -id`, `τ⁴ = id`
— is `GppMassOrientationCoupling.tau_tau_eq_neg` / `tau_pow_four_eq_id`.

This file supplies **3.3(iv)**, the derivative-level refinement: the differential `dτ_A` has
characteristic polynomial `t⁴ - Δ⁻⁴` (`Δ = det A`), with eigenvalues `±Δ⁻¹` realised on the
explicit eigenvectors `A(1∓ε)`.

`MassOrientationCoupling.lean` parked this as `open_differential_charpoly` on the grounds that
it "needs the Jacobian of τ as an endomorphism together with Mathlib's eigenvalue/spectrum
machinery for a non-symmetric real matrix, which is a substantial further undertaking". The
first half of that is done here and the second half turns out not to be needed: the content of
"characteristic polynomial `t⁴ - Δ⁻⁴`" is Cayley–Hamilton plus the two eigenvalues, and both
are reachable by matrix arithmetic without any spectral theory.

## What is proved

* `hasDerivAt_tau4_a` … `hasDerivAt_tau4_d` — the four partial derivatives of `τ`, each as a
  genuine `HasDerivAt` of the full 4-tuple in one coordinate. Together they are every entry of
  the Jacobian, so `tauJac` below is the matrix of first partials as a **theorem**, not a
  definition asserted to be the derivative.
* `tauJac_pow_four` — `(dτ_A)⁴ = Δ⁻⁴ · I`. This is the Cayley–Hamilton content of
  `charpoly = t⁴ - Δ⁻⁴`.
* `tauJac_mulVec_eigen_pos` / `tauJac_mulVec_eigen_neg` — `A(1∓ε)` are eigenvectors for
  `±Δ⁻¹`, matching the paper's stated eigenvectors.

## Scope

`tauJac` is the matrix of **partial** derivatives, and that is what the four `HasDerivAt`
results establish. Fréchet differentiability of `τ` as a map `ℝ⁴ → ℝ⁴` follows from continuity
of those partials by the standard C¹ criterion, which is **not** formalized here; nothing below
depends on it, since every statement is about `tauJac` itself.

`charpoly = t⁴ - Δ⁻⁴` is not stated as a `Matrix.charpoly` equation. `tauJac_pow_four` gives
that the minimal polynomial divides `t⁴ - Δ⁻⁴`, and the eigenvector results exhibit two of its
four roots; together that is the usable content. Writing it as a literal `charpoly` identity
would need a symbolic 4×4 determinant over `Polynomial ℝ` and is not attempted.

The claim was checked symbolically before being formalized (`sympy`: `J.charpoly` factors
exactly as `t⁴ - Δ⁻⁴`, and `J⁴ - Δ⁻⁴I = 0`), which is also where the intermediate matrix
`tauNumSq` below came from.
-/

namespace GppTauDifferential

open Matrix

/-! ## A quotient rule for the only shape the Jacobian needs

Every one of the sixteen partials is an affine function of one coordinate over another affine
function of the same coordinate — the numerator of `τ` is `0`, `±1` or a constant in each
variable, and `ad - bc` is affine in each. One lemma covers all sixteen. -/

/-- `d/dx [(px + q)/(rx + s)] = (ps - qr)/(rx + s)²`. -/
theorem hasDerivAt_affine_div_affine (p q r s x : ℝ) (h : x * r + s ≠ 0) :
    HasDerivAt (fun t : ℝ => (t * p + q) / (t * r + s))
      ((p * s - q * r) / (x * r + s) ^ 2) x := by
  -- The `have`s carry explicit `HasDerivAt` ascriptions on purpose: `HasDerivAt` unfolds to
  -- `HasFDerivAtFilter`, and without the ascription `add_const` lands in the unfolded form,
  -- where the lemma names used below do not exist.
  have h0 : HasDerivAt (fun t : ℝ => t * p) p x := by
    simpa using (hasDerivAt_id x).mul_const p
  have h1 : HasDerivAt (fun t : ℝ => t * r) r x := by
    simpa using (hasDerivAt_id x).mul_const r
  have hnum : HasDerivAt (fun t : ℝ => t * p + q) p x := h0.add_const q
  have hden : HasDerivAt (fun t : ℝ => t * r + s) r x := h1.add_const s
  have hmul := hnum.mul (hden.inv h)
  simp only [Pi.inv_apply, ← div_eq_mul_inv] at hmul
  refine hmul.congr_deriv ?_
  field_simp
  ring

/-- The same, for any function pointwise equal to such a quotient and any value equal to the
derivative. Keeps the sixteen instantiations below to one line each. -/
theorem hasDerivAt_of_affine_div {f : ℝ → ℝ} (p q r s x v : ℝ) (h : x * r + s ≠ 0)
    (hf : ∀ t, f t = (t * p + q) / (t * r + s))
    (hv : v = (p * s - q * r) / (x * r + s) ^ 2) :
    HasDerivAt f v x := by
  subst hv
  exact (hasDerivAt_affine_div_affine p q r s x h).congr_of_eventuallyEq
    (Filter.Eventually.of_forall hf)

/-! ## The map and its partial derivatives -/

/-- `τ` in coordinates: `τ(a,b,c,d) = (-b, a, -d, c)/(ad - bc)`. -/
noncomputable def tau4 (a b c d : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (-b / (a * d - b * c), a / (a * d - b * c),
   -d / (a * d - b * c), c / (a * d - b * c))

/-- `∂τ/∂a` — the first column of the Jacobian. -/
theorem hasDerivAt_tau4_a (a b c d : ℝ) (hD : a * d - b * c ≠ 0) :
    HasDerivAt (fun x => tau4 x b c d)
      (b*d/(a*d-b*c)^2, -(b*c)/(a*d-b*c)^2, d^2/(a*d-b*c)^2, -(c*d)/(a*d-b*c)^2) a := by
  have hne : a * d + -(b*c) ≠ 0 := by rw [← sub_eq_add_neg]; exact hD
  have h0 : HasDerivAt (fun x : ℝ => -b / (x*d - b*c)) (b*d/(a*d-b*c)^2) a :=
    hasDerivAt_of_affine_div 0 (-b) d (-(b*c)) a _ hne (fun t => by ring) (by ring)
  have h1 : HasDerivAt (fun x : ℝ => x / (x*d - b*c)) (-(b*c)/(a*d-b*c)^2) a :=
    hasDerivAt_of_affine_div 1 0 d (-(b*c)) a _ hne (fun t => by ring) (by ring)
  have h2 : HasDerivAt (fun x : ℝ => -d / (x*d - b*c)) (d^2/(a*d-b*c)^2) a :=
    hasDerivAt_of_affine_div 0 (-d) d (-(b*c)) a _ hne (fun t => by ring) (by ring)
  have h3 : HasDerivAt (fun x : ℝ => c / (x*d - b*c)) (-(c*d)/(a*d-b*c)^2) a :=
    hasDerivAt_of_affine_div 0 c d (-(b*c)) a _ hne (fun t => by ring) (by ring)
  exact HasDerivAt.prodMk h0 (HasDerivAt.prodMk h1 (HasDerivAt.prodMk h2 h3))

/-- `∂τ/∂b` — the second column of the Jacobian. -/
theorem hasDerivAt_tau4_b (a b c d : ℝ) (hD : a * d - b * c ≠ 0) :
    HasDerivAt (fun x => tau4 a x c d)
      (-(a*d)/(a*d-b*c)^2, a*c/(a*d-b*c)^2, -(c*d)/(a*d-b*c)^2, c^2/(a*d-b*c)^2) b := by
  have hne : b * (-c) + a*d ≠ 0 := by
    rw [show b * (-c) + a*d = a*d - b*c from by ring]; exact hD
  have h0 : HasDerivAt (fun x : ℝ => -x / (a*d - x*c)) (-(a*d)/(a*d-b*c)^2) b :=
    hasDerivAt_of_affine_div (-1) 0 (-c) (a*d) b _ hne (fun t => by ring) (by ring)
  have h1 : HasDerivAt (fun x : ℝ => a / (a*d - x*c)) (a*c/(a*d-b*c)^2) b :=
    hasDerivAt_of_affine_div 0 a (-c) (a*d) b _ hne (fun t => by ring) (by ring)
  have h2 : HasDerivAt (fun x : ℝ => -d / (a*d - x*c)) (-(c*d)/(a*d-b*c)^2) b :=
    hasDerivAt_of_affine_div 0 (-d) (-c) (a*d) b _ hne (fun t => by ring) (by ring)
  have h3 : HasDerivAt (fun x : ℝ => c / (a*d - x*c)) (c^2/(a*d-b*c)^2) b :=
    hasDerivAt_of_affine_div 0 c (-c) (a*d) b _ hne (fun t => by ring) (by ring)
  exact HasDerivAt.prodMk h0 (HasDerivAt.prodMk h1 (HasDerivAt.prodMk h2 h3))

/-- `∂τ/∂c` — the third column of the Jacobian. -/
theorem hasDerivAt_tau4_c (a b c d : ℝ) (hD : a * d - b * c ≠ 0) :
    HasDerivAt (fun x => tau4 a b x d)
      (-(b^2)/(a*d-b*c)^2, a*b/(a*d-b*c)^2, -(b*d)/(a*d-b*c)^2, a*d/(a*d-b*c)^2) c := by
  have hne : c * (-b) + a*d ≠ 0 := by
    rw [show c * (-b) + a*d = a*d - b*c from by ring]; exact hD
  have h0 : HasDerivAt (fun x : ℝ => -b / (a*d - b*x)) (-(b^2)/(a*d-b*c)^2) c :=
    hasDerivAt_of_affine_div 0 (-b) (-b) (a*d) c _ hne (fun t => by ring) (by ring)
  have h1 : HasDerivAt (fun x : ℝ => a / (a*d - b*x)) (a*b/(a*d-b*c)^2) c :=
    hasDerivAt_of_affine_div 0 a (-b) (a*d) c _ hne (fun t => by ring) (by ring)
  have h2 : HasDerivAt (fun x : ℝ => -d / (a*d - b*x)) (-(b*d)/(a*d-b*c)^2) c :=
    hasDerivAt_of_affine_div 0 (-d) (-b) (a*d) c _ hne (fun t => by ring) (by ring)
  have h3 : HasDerivAt (fun x : ℝ => x / (a*d - b*x)) (a*d/(a*d-b*c)^2) c :=
    hasDerivAt_of_affine_div 1 0 (-b) (a*d) c _ hne (fun t => by ring) (by ring)
  exact HasDerivAt.prodMk h0 (HasDerivAt.prodMk h1 (HasDerivAt.prodMk h2 h3))

/-- `∂τ/∂d` — the fourth column of the Jacobian. -/
theorem hasDerivAt_tau4_d (a b c d : ℝ) (hD : a * d - b * c ≠ 0) :
    HasDerivAt (fun x => tau4 a b c x)
      (a*b/(a*d-b*c)^2, -(a^2)/(a*d-b*c)^2, b*c/(a*d-b*c)^2, -(a*c)/(a*d-b*c)^2) d := by
  have hne : d * a + -(b*c) ≠ 0 := by
    rw [show d * a + -(b*c) = a*d - b*c from by ring]; exact hD
  have h0 : HasDerivAt (fun x : ℝ => -b / (a*x - b*c)) (a*b/(a*d-b*c)^2) d :=
    hasDerivAt_of_affine_div 0 (-b) a (-(b*c)) d _ hne (fun t => by ring) (by ring)
  have h1 : HasDerivAt (fun x : ℝ => a / (a*x - b*c)) (-(a^2)/(a*d-b*c)^2) d :=
    hasDerivAt_of_affine_div 0 a a (-(b*c)) d _ hne (fun t => by ring) (by ring)
  have h2 : HasDerivAt (fun x : ℝ => -x / (a*x - b*c)) (b*c/(a*d-b*c)^2) d :=
    hasDerivAt_of_affine_div (-1) 0 a (-(b*c)) d _ hne (fun t => by ring) (by ring)
  have h3 : HasDerivAt (fun x : ℝ => c / (a*x - b*c)) (-(a*c)/(a*d-b*c)^2) d :=
    hasDerivAt_of_affine_div 0 c a (-(b*c)) d _ hne (fun t => by ring) (by ring)
  exact HasDerivAt.prodMk h0 (HasDerivAt.prodMk h1 (HasDerivAt.prodMk h2 h3))

/-! ## The Jacobian matrix and its fourth power -/

/-- `Δ² · dτ_A`, the Jacobian cleared of its denominator. Working with the polynomial matrix
keeps every entry a polynomial, which matters: the fourth power of the full Jacobian exceeds
the elaborator's heartbeat budget outright, while this one does not. -/
noncomputable def tauNum (a b c d : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![ b*d, -(a*d), -(b^2),  a*b;
     -(b*c),  a*c,   a*b,  -(a^2);
      d^2,  -(c*d), -(b*d),  b*c;
     -(c*d),  c^2,   a*d,  -(a*c) ]

/-- `(Δ² dτ_A)² = Δ · N`. The intermediate `N` is what makes the fourth power tractable. -/
noncomputable def tauNumSq (a b c d : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![ 0, -(a*c + b*d),  0,  a^2 + b^2;
      a*c + b*d, 0, -(a^2 + b^2), 0;
      0, -(c^2 + d^2), 0, a*c + b*d;
      c^2 + d^2, 0, -(a*c + b*d), 0 ]

/-- **The Jacobian of `τ`**: row `i`, column `j` is `∂τᵢ/∂xⱼ`, as established by
`hasDerivAt_tau4_a` … `hasDerivAt_tau4_d`. -/
noncomputable def tauJac (a b c d : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  ((a*d - b*c) ^ 2)⁻¹ • tauNum a b c d

theorem tauNum_mul_self (a b c d : ℝ) :
    tauNum a b c d * tauNum a b c d = (a*d - b*c) • tauNumSq a b c d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tauNum, tauNumSq, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem tauNumSq_mul_self (a b c d : ℝ) :
    tauNumSq a b c d * tauNumSq a b c d
      = ((a*d - b*c)^2) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tauNumSq, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem tauNum_pow_four (a b c d : ℝ) :
    tauNum a b c d ^ 4 = ((a*d - b*c) ^ 4) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  have h : tauNum a b c d ^ 4
      = (tauNum a b c d * tauNum a b c d) * (tauNum a b c d * tauNum a b c d) := by
    noncomm_ring
  rw [h, tauNum_mul_self, smul_mul_smul_comm, tauNumSq_mul_self, smul_smul]
  congr 1
  ring

/-- **Theorem 3.3(iv), Cayley–Hamilton form: `(dτ_A)⁴ = Δ⁻⁴ · I`.**

This is what "characteristic polynomial `t⁴ - Δ⁻⁴`" asserts about the matrix: every eigenvalue
is a fourth root of `Δ⁻⁴`, and the minimal polynomial divides `t⁴ - Δ⁻⁴`. It is the derivative
of `τ⁴ = id` (`GppMassOrientationCoupling.tau_pow_four_eq_id`) — differentiating a fourth
iterate that is the identity forces the chain-rule product of differentials to be the identity,
and the four factors are equal only up to the `Δ` weight that appears here. -/
theorem tauJac_pow_four (a b c d : ℝ) (hD : a*d - b*c ≠ 0) :
    tauJac a b c d ^ 4 = (((a*d - b*c) ^ 4)⁻¹) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  unfold tauJac
  rw [smul_pow, tauNum_pow_four, smul_smul]
  congr 1
  field_simp

/-! ## The eigenvectors named in the paper

`A(1∓ε)` in coordinates: `Aε = [[-b, a], [-d, c]]`, so `A(1-ε) = (a+b, b-a, c+d, d-c)` and
`A(1+ε) = (a-b, b+a, c-d, d+c)` reading the 2×2 matrix row-major as `(a,b,c,d)`. -/

/-- `A(1-ε)` is an eigenvector of `dτ_A` for the eigenvalue `+Δ⁻¹`. -/
theorem tauJac_mulVec_eigen_pos (a b c d : ℝ) (hD : a*d - b*c ≠ 0) :
    tauJac a b c d *ᵥ ![a + b, b - a, c + d, d - c]
      = (a*d - b*c)⁻¹ • ![a + b, b - a, c + d, d - c] := by
  unfold tauJac tauNum
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, mul_comm] <;>
    field_simp <;> ring

/-- `A(1+ε)` is an eigenvector of `dτ_A` for the eigenvalue `-Δ⁻¹`. -/
theorem tauJac_mulVec_eigen_neg (a b c d : ℝ) (hD : a*d - b*c ≠ 0) :
    tauJac a b c d *ᵥ ![a - b, b + a, c - d, d + c]
      = (-(a*d - b*c)⁻¹) • ![a - b, b + a, c - d, d + c] := by
  unfold tauJac tauNum
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, mul_comm] <;>
    field_simp <;> ring

end GppTauDifferential

#print axioms GppTauDifferential.hasDerivAt_tau4_a
#print axioms GppTauDifferential.tauJac_pow_four
#print axioms GppTauDifferential.tauJac_mulVec_eigen_pos
