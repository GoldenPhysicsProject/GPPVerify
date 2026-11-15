import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The quaternionic Hopf clutching data: the finite identities

Discovery 2 (PR #11, comment 6887243177; GPPDiscovery2 `codex/discovery-workbench` 2baeedb) embeds
`HP¹ ≅ S⁴` in `Gr₂(ℂ⁴)` and finds the quaternionic Hopf `SU(2)` instanton of unit charge, glued by the
clutching map `g(q) = Q(q)/|q| : S³ → SU(2)`. Turbo audited it at paper level (bridge CONVERSATION.md,
2026-11-14 ~20:26 EST, PASS). This file proves the finite identities that construction rests on.

`Q(q)` is the `2 × 2` complex matrix of the quaternion `q = a + bi + cj + dk` (`qmat`):

* `qmat_conjTranspose_mul_self`: `Q(q)ᴴ Q(q) = |q|² · 1` (the audit's `Q†Q = r² I`);
* `det_qmat`: `det Q(q) = |q|²`;
* **`clutch_mem_SU2`**: for `q ≠ 0`, `Q(q)/|q| ∈ SU(2)`, the clutching map lands in `SU(2)`;
* **`qmat_mem_unitary_iff`**: `Q(q) ∈ U(2) ↔ |q| = 1`, i.e. on the quaternionic graph chart the
  `U(2)` (Shilov) locus is exactly the unit sphere `S³`, the clutching sphere;
* **`radial_integral`**: `∫₀^∞ r³/(1 + r²)⁴ dr = 1/12`, the radial factor of the charge integral
  `(1/8π²) ∫_{ℝ⁴} 48 (1 + r²)⁻⁴ d⁴q = (1/8π²) · 48 · 2π² · (1/12) = 1`.

**Not formalised here:** the curvature formula `F = dQ†∧dQ/(1 + r²)²` and the density
`tr(F∧F) = 48 (1 + r²)⁻⁴ d⁴q` (no differential forms on `ℝ⁴`-valued matrix connections in Mathlib); the
polar-coordinate reduction of the `ℝ⁴` integral with `vol(S³) = 2π²`; the degree of the clutching map
and `c₂ = 1` (no Chern classes or homotopy groups of spheres in Mathlib). The `SU(3)` classification
corollary (Discovery 2, comment 6887256936) is likewise not formalised. Nothing here concerns dynamics,
the colour obstruction of `G₂/SU(3)`, or the Riemann hypothesis. No `sorry`, no axioms.
-/

namespace GppQuaternionicHopf

open Matrix Complex MeasureTheory Set Filter Topology

/-- The `2 × 2` complex matrix of `a + bi + cj + dk`: `[[a + bi, c + di], [-c + di, a - bi]]`. -/
def qmat (q : Quaternion ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩; ⟨-q.imJ, q.imK⟩, ⟨q.re, -q.imI⟩]

/-- `Q(q)ᴴ Q(q) = |q|² · 1`. -/
theorem qmat_conjTranspose_mul_self (q : Quaternion ℝ) :
    (qmat q)ᴴ * qmat q = ((Quaternion.normSq q : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Quaternion.normSq_def']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qmat, Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply] <;>
    apply Complex.ext <;> simp [pow_two] <;> ring

/-- `Q(q) Q(q)ᴴ = |q|² · 1`. -/
theorem qmat_mul_conjTranspose_self (q : Quaternion ℝ) :
    qmat q * (qmat q)ᴴ = ((Quaternion.normSq q : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Quaternion.normSq_def']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qmat, Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply] <;>
    apply Complex.ext <;> simp [pow_two] <;> ring

/-- `det Q(q) = |q|²`. -/
theorem det_qmat (q : Quaternion ℝ) : (qmat q).det = ((Quaternion.normSq q : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two, Quaternion.normSq_def']
  simp only [qmat, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  apply Complex.ext <;> simp [pow_two] <;> ring

/-- **The clutching map lands in `SU(2)`.** For `q ≠ 0`, `Q(q)/|q| ∈ SU(2)`. -/
theorem clutch_mem_SU2 {q : Quaternion ℝ} (hq : q ≠ 0) :
    ((Real.sqrt (Quaternion.normSq q))⁻¹ : ℂ) • qmat q ∈ specialUnitaryGroup (Fin 2) ℂ := by
  have hn : 0 < Quaternion.normSq q :=
    lt_of_le_of_ne Quaternion.normSq_nonneg (Ne.symm (Quaternion.normSq_ne_zero.mpr hq))
  set s : ℝ := Real.sqrt (Quaternion.normSq q)
  have hs : 0 < s := Real.sqrt_pos.mpr hn
  have hs2 : s ^ 2 = Quaternion.normSq q := Real.sq_sqrt hn.le
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff]
  constructor
  · rw [star_smul, Matrix.star_eq_conjTranspose, smul_mul_smul_comm, qmat_mul_conjTranspose_self,
      smul_smul, ← hs2]
    have : ((s : ℂ)⁻¹ * star ((s : ℂ)⁻¹)) * ((s ^ 2 : ℝ) : ℂ) = 1 := by
      rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
      push_cast
      field_simp
    rw [this, one_smul]
  · rw [Matrix.det_smul, det_qmat, Fintype.card_fin, ← hs2]
    push_cast
    field_simp

/-- **The equatorial sphere.** `Q(q)` is unitary exactly when `|q| = 1`. -/
theorem qmat_mem_unitary_iff (q : Quaternion ℝ) :
    qmat q ∈ unitaryGroup (Fin 2) ℂ ↔ Quaternion.normSq q = 1 := by
  rw [mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, qmat_mul_conjTranspose_self]
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp at h00
    exact_mod_cast h00
  · intro h
    rw [h]; simp

/-! ### The radial factor of the charge integral -/

/-- An antiderivative of `r³/(1 + r²)⁴`: `-1/(4(1 + r²)²) + 1/(6(1 + r²)³)`. -/
noncomputable def radAnti (r : ℝ) : ℝ := -1 / (4 * (1 + r ^ 2) ^ 2) + 1 / (6 * (1 + r ^ 2) ^ 3)

theorem hasDerivAt_radAnti (r : ℝ) : HasDerivAt radAnti (r ^ 3 / (1 + r ^ 2) ^ 4) r := by
  have hs : (0 : ℝ) < 1 + r ^ 2 := by positivity
  have h1 : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * r) r := by
    simpa using (hasDerivAt_pow 2 r).const_add 1
  have hA : HasDerivAt (fun r : ℝ => -1 / (4 * (1 + r ^ 2) ^ 2))
      ((0 * (4 * (1 + r ^ 2) ^ 2) - (-1) * (4 * (2 * (1 + r ^ 2) * (2 * r)))) /
        (4 * (1 + r ^ 2) ^ 2) ^ 2) r := by
    have hd : HasDerivAt (fun r : ℝ => 4 * (1 + r ^ 2) ^ 2) (4 * (2 * (1 + r ^ 2) * (2 * r))) r := by
      exact ((h1.pow 2).const_mul 4).congr_deriv (by push_cast; ring)
    exact (hasDerivAt_const r (-1 : ℝ)).div hd (by positivity)
  have hB : HasDerivAt (fun r : ℝ => 1 / (6 * (1 + r ^ 2) ^ 3))
      ((0 * (6 * (1 + r ^ 2) ^ 3) - 1 * (6 * (3 * (1 + r ^ 2) ^ 2 * (2 * r)))) /
        (6 * (1 + r ^ 2) ^ 3) ^ 2) r := by
    have hd : HasDerivAt (fun r : ℝ => 6 * (1 + r ^ 2) ^ 3) (6 * (3 * (1 + r ^ 2) ^ 2 * (2 * r))) r := by
      exact ((h1.pow 3).const_mul 6).congr_deriv (by push_cast; ring)
    exact (hasDerivAt_const r (1 : ℝ)).div hd (by positivity)
  have h := hA.add hB
  have e : (0 * (4 * (1 + r ^ 2) ^ 2) - -1 * (4 * (2 * (1 + r ^ 2) * (2 * r)))) /
        (4 * (1 + r ^ 2) ^ 2) ^ 2 +
      (0 * (6 * (1 + r ^ 2) ^ 3) - 1 * (6 * (3 * (1 + r ^ 2) ^ 2 * (2 * r)))) /
        (6 * (1 + r ^ 2) ^ 3) ^ 2 = r ^ 3 / (1 + r ^ 2) ^ 4 := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_eq_div_iff (by positivity) (by positivity)]
    ring
  exact h.congr_deriv e

theorem tendsto_radAnti : Tendsto radAnti atTop (𝓝 0) := by
  have h : Tendsto (fun r : ℝ => 1 + r ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop two_ne_zero)
  have h2 : Tendsto (fun r : ℝ => (4 * (1 + r ^ 2) ^ 2)⁻¹) atTop (𝓝 0) :=
    (Tendsto.const_mul_atTop (by norm_num) ((tendsto_pow_atTop two_ne_zero).comp h)).inv_tendsto_atTop
  have h3 : Tendsto (fun r : ℝ => (6 * (1 + r ^ 2) ^ 3)⁻¹) atTop (𝓝 0) :=
    (Tendsto.const_mul_atTop (by norm_num) ((tendsto_pow_atTop three_ne_zero).comp h)).inv_tendsto_atTop
  have := h2.neg.add h3
  simp only [neg_zero, add_zero] at this
  refine this.congr fun r => ?_
  unfold radAnti; ring

/-- **`∫₀^∞ r³/(1 + r²)⁴ dr = 1/12`.** -/
theorem radial_integral : ∫ r in Ioi (0 : ℝ), r ^ 3 / (1 + r ^ 2) ^ 4 = 1 / 12 := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun r _ => hasDerivAt_radAnti r)
    (fun r hr => by have : (0 : ℝ) < r := hr; positivity) tendsto_radAnti]
  unfold radAnti; norm_num

end GppQuaternionicHopf

#print axioms GppQuaternionicHopf.clutch_mem_SU2
#print axioms GppQuaternionicHopf.qmat_mem_unitary_iff
#print axioms GppQuaternionicHopf.radial_integral
