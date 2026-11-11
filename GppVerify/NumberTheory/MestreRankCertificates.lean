import GppVerify.NumberTheory.MestreRankBound
import Mathlib.Tactic

/-!
# Kernel-checked finite step of the Mestre rank certificates for 11a1 and 37a1

The rational boxes below come from `/workspace/bsd/numerics/arb_cert.py export`
(`arb_export.log`; python-flint / Arb ball arithmetic, outward-rounded to 24 decimals).
They enclose the nb = 2 Galerkin matrix `Q` and the vector `v = f̂(0)` of the elliptic
Weil form `Q_L^E`. The basis is `cos((j+1/2)πx/L)` on `[-L, L]`. The window is L = 1/2 for 11a1
and L = 1 for 37a1.

Kernel-checked here, for every real symmetric `Q` and every `v` inside the boxes:

* `Q` is positive definite.
* If `Q = Q' + r • vvᵀ` with `Q' ⪰ 0` (the GRH(E) shape), then `r ≤ 1/(vᵀQ⁻¹v)`. The test-vector
  certificate gives `r < 1` (11a1) and `r < 2` (37a1).
* For a natural `r` of the parity fixed by the root number, `r = 0` (11a1) and `r = 1` (37a1).

Honest boundary: NOT kernel-checked.

1. The boxes contain the true matrix entries. That is the Arb computation, which is rigorous but
   lies outside Lean.
2. The explicit formula, and the identification of `r` with the order of vanishing of L(E,s) at
   s = 1.
3. GRH(E). It enters only through the decomposition hypothesis. That hypothesis is an
   assumption here, not a result.
4. The root numbers, w(11a1) = +1 and w(37a1) = −1.

Nothing here concerns BSD itself.

Superseded on the trust side by `GppVerify.NumberTheory.MestreRankKernel`. That module proves the
same conclusions (`r = 0` for 11a1, and `r ≤ 1`, or `r = 1` with odd parity, for 37a1) with
every numerical input kernel-proved. It uses a Fejér test function instead of these Arb boxes.
-/

namespace GppMestreRankCertificates

open Matrix GppMestreRankBound

/-- Sylvester's criterion for a real symmetric 2 × 2 matrix. -/
theorem posDef_fin2 (Q : Matrix (Fin 2) (Fin 2) ℝ) (hs : Q 1 0 = Q 0 1) (ha : 0 < Q 0 0)
    (hd : 0 < Q 0 0 * Q 1 1 - Q 0 1 ^ 2) : Q.PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [conjTranspose_apply, hs]
  · intro x hx
    simp only [star_trivial, dotProduct, mulVec, Fin.sum_univ_two, hs]
    have key : Q 0 0 * (x 0 * (Q 0 0 * x 0 + Q 0 1 * x 1) + x 1 * (Q 0 1 * x 0 + Q 1 1 * x 1)) =
        (Q 0 0 * x 0 + Q 0 1 * x 1) ^ 2 + (Q 0 0 * Q 1 1 - Q 0 1 ^ 2) * x 1 ^ 2 := by ring
    by_cases h1 : x 1 = 0
    · have h0 : x 0 ≠ 0 := by
        intro h0; apply hx; ext i; fin_cases i <;> simp [h0, h1]
      rw [h1]
      have : 0 < x 0 ^ 2 := by positivity
      nlinarith
    · have : 0 < x 1 ^ 2 := by positivity
      have hpos : 0 < Q 0 0 * (x 0 * (Q 0 0 * x 0 + Q 0 1 * x 1) +
          x 1 * (Q 0 1 * x 0 + Q 1 1 * x 1)) := by
        rw [key]; nlinarith [sq_nonneg (Q 0 0 * x 0 + Q 0 1 * x 1)]
      exact pos_of_mul_pos_right hpos ha.le

/-- 11a1, L = 0.5, nb = 2: every symmetric `Q` in the Arb box is positive definite. -/
theorem posDef_11a1 (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hQ00 : (2420732452734403944817 / 25000000000000000000000 : ℝ) ≤ Q 0 0 ∧ Q 0 0 ≤ (96829298109376157792681 / 1000000000000000000000000 : ℝ))
    (hQ01 : (124582878654165916413339 / 1000000000000000000000000 : ℝ) ≤ Q 0 1 ∧ Q 0 1 ≤ (6229143932708295820667 / 50000000000000000000000 : ℝ))
    (hQ11 : (1661969541840930422617273 / 1000000000000000000000000 : ℝ) ≤ Q 1 1 ∧ Q 1 1 ≤ (830984770920465211308637 / 500000000000000000000000 : ℝ))
    (hs : Q 1 0 = Q 0 1) : Q.PosDef := by
  obtain ⟨a1, a2⟩ := hQ00; obtain ⟨b1, b2⟩ := hQ01; obtain ⟨c1, c2⟩ := hQ11
  refine posDef_fin2 Q hs (by linarith) ?_
  nlinarith [mul_le_mul_of_nonneg_left c1 (by linarith : (0 : ℝ) ≤ Q 0 0),
    mul_le_mul_of_nonneg_right a1 (by norm_num : (0 : ℝ) ≤ (1661969541840930422617273 / 1000000000000000000000000 : ℝ)),
    mul_nonneg (sub_nonneg.2 b1) (sub_nonneg.2 b2)]

/-- 11a1: the GRH(E)-shaped decomposition with `Q` in the Arb box forces `r < 1`. -/
theorem rank_bound_11a1 (Q Q' : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) (r : ℝ)
    (hQ00 : (2420732452734403944817 / 25000000000000000000000 : ℝ) ≤ Q 0 0 ∧ Q 0 0 ≤ (96829298109376157792681 / 1000000000000000000000000 : ℝ))
    (hQ01 : (124582878654165916413339 / 1000000000000000000000000 : ℝ) ≤ Q 0 1 ∧ Q 0 1 ≤ (6229143932708295820667 / 50000000000000000000000 : ℝ))
    (hQ11 : (1661969541840930422617273 / 1000000000000000000000000 : ℝ) ≤ Q 1 1 ∧ Q 1 1 ≤ (830984770920465211308637 / 500000000000000000000000 : ℝ))
    (hs : Q 1 0 = Q 0 1)
    (hv0 : (127323954473516268615107 / 200000000000000000000000 : ℝ) ≤ v 0 ∧ v 0 ≤ (39788735772973833942221 / 62500000000000000000000 : ℝ))
    (hv1 : (-212206590789193781025179 / 1000000000000000000000000 : ℝ) ≤ v 1 ∧ v 1 ≤ (-106103295394596890512589 / 500000000000000000000000 : ℝ))
    (hQ' : Q'.PosSemidef) (h : Q = Q' + r • vecMulVec v v) : r < 1 := by
  have H := rankOne_lower hQ' h ![7458 / 1000, -687 / 1000]
  simp only [qf, dotProduct, mulVec, Fin.sum_univ_two, hs, Matrix.cons_val_zero,
    Matrix.cons_val_one] at H
  obtain ⟨a1, a2⟩ := hQ00; obtain ⟨b1, b2⟩ := hQ01; obtain ⟨c1, c2⟩ := hQ11
  obtain ⟨d1, d2⟩ := hv0; obtain ⟨e1, e2⟩ := hv1
  set w := v 0 * (7458 / 1000) + v 1 * (-687 / 1000) with hw
  have hwlo : 0 < w := by rw [hw]; linarith
  by_contra hr'
  have hr := not_lt.mp hr'
  have hw2 : 0 < w ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hr hw2.le]

/-- 11a1: inverse-form version, `r ≤ 1/(vᵀQ⁻¹v)` (the minimum over test vectors). -/
theorem rank_le_invForm_11a1 (Q Q' : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) (r : ℝ)
    (hQ00 : (2420732452734403944817 / 25000000000000000000000 : ℝ) ≤ Q 0 0 ∧ Q 0 0 ≤ (96829298109376157792681 / 1000000000000000000000000 : ℝ))
    (hQ01 : (124582878654165916413339 / 1000000000000000000000000 : ℝ) ≤ Q 0 1 ∧ Q 0 1 ≤ (6229143932708295820667 / 50000000000000000000000 : ℝ))
    (hQ11 : (1661969541840930422617273 / 1000000000000000000000000 : ℝ) ≤ Q 1 1 ∧ Q 1 1 ≤ (830984770920465211308637 / 500000000000000000000000 : ℝ))
    (hs : Q 1 0 = Q 0 1)
    (hv0 : (127323954473516268615107 / 200000000000000000000000 : ℝ) ≤ v 0 ∧ v 0 ≤ (39788735772973833942221 / 62500000000000000000000 : ℝ))
    (hQ' : Q'.PosSemidef) (h : Q = Q' + r • vecMulVec v v) :
    r ≤ 1 / (v ⬝ᵥ (Q⁻¹ *ᵥ v)) := by
  have hv : v ≠ 0 := fun h0 => by
    have := hv0.1; rw [h0] at this; norm_num at this
  exact mestre_rank_bound (posDef_11a1 Q hQ00 hQ01 hQ11 hs) hQ' h hv

/-- 37a1, L = 1.0, nb = 2: every symmetric `Q` in the Arb box is positive definite. -/
theorem posDef_37a1 (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hQ00 : (1635363466036555815685013 / 1000000000000000000000000 : ℝ) ≤ Q 0 0 ∧ Q 0 0 ≤ (817681733018277907842507 / 500000000000000000000000 : ℝ))
    (hQ01 : (-668280642637212818802951 / 1000000000000000000000000 : ℝ) ≤ Q 0 1 ∧ Q 0 1 ≤ (-13365612852744256376059 / 20000000000000000000000 : ℝ))
    (hQ11 : (282448838591649584960651 / 125000000000000000000000 : ℝ) ≤ Q 1 1 ∧ Q 1 1 ≤ (2259590708733196679685209 / 1000000000000000000000000 : ℝ))
    (hs : Q 1 0 = Q 0 1) : Q.PosDef := by
  obtain ⟨a1, a2⟩ := hQ00; obtain ⟨b1, b2⟩ := hQ01; obtain ⟨c1, c2⟩ := hQ11
  refine posDef_fin2 Q hs (by linarith) ?_
  nlinarith [mul_le_mul_of_nonneg_left c1 (by linarith : (0 : ℝ) ≤ Q 0 0),
    mul_le_mul_of_nonneg_right a1 (by norm_num : (0 : ℝ) ≤ (282448838591649584960651 / 125000000000000000000000 : ℝ)),
    mul_nonneg (sub_nonneg.2 b1) (sub_nonneg.2 b2)]

/-- 37a1: the GRH(E)-shaped decomposition with `Q` in the Arb box forces `r < 2`. -/
theorem rank_bound_37a1 (Q Q' : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) (r : ℝ)
    (hQ00 : (1635363466036555815685013 / 1000000000000000000000000 : ℝ) ≤ Q 0 0 ∧ Q 0 0 ≤ (817681733018277907842507 / 500000000000000000000000 : ℝ))
    (hQ01 : (-668280642637212818802951 / 1000000000000000000000000 : ℝ) ≤ Q 0 1 ∧ Q 0 1 ≤ (-13365612852744256376059 / 20000000000000000000000 : ℝ))
    (hQ11 : (282448838591649584960651 / 125000000000000000000000 : ℝ) ≤ Q 1 1 ∧ Q 1 1 ≤ (2259590708733196679685209 / 1000000000000000000000000 : ℝ))
    (hs : Q 1 0 = Q 0 1)
    (hv0 : (127323954473516268615107 / 100000000000000000000000 : ℝ) ≤ v 0 ∧ v 0 ≤ (1273239544735162686151071 / 1000000000000000000000000 : ℝ))
    (hv1 : (-424413181578387562050357 / 1000000000000000000000000 : ℝ) ≤ v 1 ∧ v 1 ≤ (-106103295394596890512589 / 250000000000000000000000 : ℝ))
    (hQ' : Q'.PosSemidef) (h : Q = Q' + r • vecMulVec v v) : r < 2 := by
  have H := rankOne_lower hQ' h ![798 / 1000, 48 / 1000]
  simp only [qf, dotProduct, mulVec, Fin.sum_univ_two, hs, Matrix.cons_val_zero,
    Matrix.cons_val_one] at H
  obtain ⟨a1, a2⟩ := hQ00; obtain ⟨b1, b2⟩ := hQ01; obtain ⟨c1, c2⟩ := hQ11
  obtain ⟨d1, d2⟩ := hv0; obtain ⟨e1, e2⟩ := hv1
  set w := v 0 * (798 / 1000) + v 1 * (48 / 1000) with hw
  have hwlo : 0 < w := by rw [hw]; linarith
  by_contra hr'
  have hr := not_lt.mp hr'
  have hw2 : 0 < w ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hr hw2.le]

/-- 37a1: inverse-form version, `r ≤ 1/(vᵀQ⁻¹v)` (the minimum over test vectors). -/
theorem rank_le_invForm_37a1 (Q Q' : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) (r : ℝ)
    (hQ00 : (1635363466036555815685013 / 1000000000000000000000000 : ℝ) ≤ Q 0 0 ∧ Q 0 0 ≤ (817681733018277907842507 / 500000000000000000000000 : ℝ))
    (hQ01 : (-668280642637212818802951 / 1000000000000000000000000 : ℝ) ≤ Q 0 1 ∧ Q 0 1 ≤ (-13365612852744256376059 / 20000000000000000000000 : ℝ))
    (hQ11 : (282448838591649584960651 / 125000000000000000000000 : ℝ) ≤ Q 1 1 ∧ Q 1 1 ≤ (2259590708733196679685209 / 1000000000000000000000000 : ℝ))
    (hs : Q 1 0 = Q 0 1)
    (hv0 : (127323954473516268615107 / 100000000000000000000000 : ℝ) ≤ v 0 ∧ v 0 ≤ (1273239544735162686151071 / 1000000000000000000000000 : ℝ))
    (hQ' : Q'.PosSemidef) (h : Q = Q' + r • vecMulVec v v) :
    r ≤ 1 / (v ⬝ᵥ (Q⁻¹ *ᵥ v)) := by
  have hv : v ≠ 0 := fun h0 => by
    have := hv0.1; rw [h0] at this; norm_num at this
  exact mestre_rank_bound (posDef_37a1 Q hQ00 hQ01 hQ11 hs) hQ' h hv

/-- 11a1: if the central multiplicity `r : ℕ` is even (root number), then `r = 0`. -/
theorem rank_eq_11a1 (Q Q' : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) (r : ℕ) (hpar : Even r)
    (hQ00 : (2420732452734403944817 / 25000000000000000000000 : ℝ) ≤ Q 0 0 ∧ Q 0 0 ≤ (96829298109376157792681 / 1000000000000000000000000 : ℝ))
    (hQ01 : (124582878654165916413339 / 1000000000000000000000000 : ℝ) ≤ Q 0 1 ∧ Q 0 1 ≤ (6229143932708295820667 / 50000000000000000000000 : ℝ))
    (hQ11 : (1661969541840930422617273 / 1000000000000000000000000 : ℝ) ≤ Q 1 1 ∧ Q 1 1 ≤ (830984770920465211308637 / 500000000000000000000000 : ℝ))
    (hs : Q 1 0 = Q 0 1)
    (hv0 : (127323954473516268615107 / 200000000000000000000000 : ℝ) ≤ v 0 ∧ v 0 ≤ (39788735772973833942221 / 62500000000000000000000 : ℝ))
    (hv1 : (-212206590789193781025179 / 1000000000000000000000000 : ℝ) ≤ v 1 ∧ v 1 ≤ (-106103295394596890512589 / 500000000000000000000000 : ℝ))
    (hQ' : Q'.PosSemidef) (h : Q = Q' + (r : ℝ) • vecMulVec v v) : r = 0 := by
  have hlt := rank_bound_11a1 Q Q' v r hQ00 hQ01 hQ11 hs hv0 hv1 hQ' h
  have : r < 1 := by exact_mod_cast hlt
  rcases hpar with ⟨k, hk⟩
  omega

/-- 37a1: if the central multiplicity `r : ℕ` is odd (root number), then `r = 1`. -/
theorem rank_eq_37a1 (Q Q' : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) (r : ℕ) (hpar : Odd r)
    (hQ00 : (1635363466036555815685013 / 1000000000000000000000000 : ℝ) ≤ Q 0 0 ∧ Q 0 0 ≤ (817681733018277907842507 / 500000000000000000000000 : ℝ))
    (hQ01 : (-668280642637212818802951 / 1000000000000000000000000 : ℝ) ≤ Q 0 1 ∧ Q 0 1 ≤ (-13365612852744256376059 / 20000000000000000000000 : ℝ))
    (hQ11 : (282448838591649584960651 / 125000000000000000000000 : ℝ) ≤ Q 1 1 ∧ Q 1 1 ≤ (2259590708733196679685209 / 1000000000000000000000000 : ℝ))
    (hs : Q 1 0 = Q 0 1)
    (hv0 : (127323954473516268615107 / 100000000000000000000000 : ℝ) ≤ v 0 ∧ v 0 ≤ (1273239544735162686151071 / 1000000000000000000000000 : ℝ))
    (hv1 : (-424413181578387562050357 / 1000000000000000000000000 : ℝ) ≤ v 1 ∧ v 1 ≤ (-106103295394596890512589 / 250000000000000000000000 : ℝ))
    (hQ' : Q'.PosSemidef) (h : Q = Q' + (r : ℝ) • vecMulVec v v) : r = 1 := by
  have hlt := rank_bound_37a1 Q Q' v r hQ00 hQ01 hQ11 hs hv0 hv1 hQ' h
  have : r < 2 := by exact_mod_cast hlt
  rcases hpar with ⟨k, hk⟩
  omega

end GppMestreRankCertificates
