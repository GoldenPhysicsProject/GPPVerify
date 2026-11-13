/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Flint (GPPDiscovery3 seat), 2026-11-13.

# O2's finite core: the non-spectral side of (C1), machine-checked

`QuartetSpectral.lean` states `(O2)`: on `ker ℓ_c`, the finite partial spectral
sums `Sfin x c (Z k)` along any exhaustion of the nontrivial zeros converge to
`kform Kpsi x c`. In full, (O2) is the Guinand–Weil explicit formula for
`R_c`, the autocorrelation of `Fc x c`. Its only genuinely analytic input is
that explicit formula itself; everything else in (C1) is finite manipulation.
This file machine-checks the finite pieces, in dependency order:

* `Rc x c u = ∑ i, ∑ j, c i * c j * triG (u - (x i - x j))`, the autocorrelation
  of the configuration in kernel-evaluation form (`triG` is the in-tree
  autocorrelation kernel of `KreinHPsi`, and `primeTerm` is built from it).
* (I2) `kform_primeTerm` — PROVED: the prime side of the defect form is
  `kform primeTerm x c = 2 * ∑' m, Λ m / √m * Rc x c (log m)`, an identity of
  finite sums (both sides have finite support in `m`; the finite form
  `kform_primeTerm_finite` is proved first). This is a definition chase
  against the in-tree `primeTerm`, plus `triG` evenness and the symmetry
  `i ↔ j` of the finite configuration.
* (I3) `Fhat_zero`, `Fhat_one` — PROVED: the Mellin–Laplace transform of `Fc`
  at the two pole points is `Fhat x c 1 = bigPsiI2 * ∑ i, c i * exp (-(x i)/2)`
  and `Fhat x c 0 = bigPsiI2 * ∑ i, c i * exp (x i / 2)`, from the single
  integral evaluation `∫ v, tri v * cosh (v/2) dv = bigPsiI2`
  (`tri_integral_cosh`, proved by FTC on `[-1, 1]`). Consequently
  `Fhat_zero_sq_add_one_sq` — PROVED: on `ker ℓ_c`,
  `(Fhat x c 0)^2 + (Fhat x c 1)^2 = poleCorr x c`, the pole correction
  `2 * bigPsiI2^2 * (∑ i, c i * sinh (x i / 2))^2`; and
  `kform_poleTerm_on_ker` — PROVED: `kform poleTerm x c = -poleCorr x c`
  on `ker ℓ_c`.
* (I1), the pieces actually used: `triG_even`, and the global closed form
  `triG_eq_triForm` expressing `triG` through `tri` itself
  (`triG y = (max (2 - |y|) 0)^3 / 6 - (2/3) * (tri y)^3`), which gives
  `continuous_triG` and the compact support of `Rc`
  (`Rc_eq_zero_of_abs_gt`), hence the admissibility of `R_c` for the
  explicit formula (`rcAdmissible`: compact support + continuity).
  The integral autocorrelation identity `triG y = ∫ t, tri t * tri (t - y) dt`
  is *not* used by (I2)/(I3) or by the assembly below: it is the bridge that
  identifies `Rc` (kernel form) with the integral autocorrelation of `Fc`,
  and as such it is part of the content of the analytic premise
  `WeilEFPremise`, whose spectral side is stated in terms of `Fhat`.

What remains of (O2) after this file is exactly one named analytic premise,
`WeilEFPremise`: the Weil explicit formula applied to `R_c` (the spectral
identification itself), with its admissibility hypotheses on `R_c` included
in the statement and discharged by `rcAdmissible`. `O2_of_weilEF` — PROVED:
that premise implies `O2`, using only the finite lemmas above.
-/

import GppVerify.RiemannHypothesis.QuartetSpectral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open MeasureTheory Filter ComplexConjugate
open scoped Topology

namespace GppQuartetFiniteCore

open GppKreinBridge GppKreinHPsi GppQuartetSpectral

/-! ## The autocorrelation of the configuration, in kernel form -/

/-- The autocorrelation values of the finite configuration,
`Rc x c u = ∑ i, ∑ j, c i * c j * triG (u - (x i - x j))`. This is the
function `R_c` of the explicit formula, written with the in-tree kernel
`triG`; `primeTerm` is built from the same kernel. -/
noncomputable def Rc {n : ℕ} (x c : Fin n → ℝ) (u : ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * triG (u - (x i - x j))

/-- A crude finite bound on all lags `|x i - x j|` of the configuration. -/
noncomputable def lagBound {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, |x i - x j|

/-- The pole correction `2 * bigPsiI2^2 * (∑ i, c i * sinh (x i / 2))^2`:
the quantity the pole terms of the explicit formula collapse to on
`ker ℓ_c`. -/
noncomputable def poleCorr {n : ℕ} (x c : Fin n → ℝ) : ℝ :=
  2 * bigPsiI2 ^ 2 * (∑ i, c i * Real.sinh (x i / 2)) ^ 2

private lemma lagBound_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ lagBound x :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _

private lemma lag_le_lagBound {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) :
    |x i - x j| ≤ lagBound x := by
  have h1 : |x i - x j| ≤ ∑ j', |x i - x j'| :=
    Finset.single_le_sum (f := fun j' => |x i - x j'|) (fun b _ => abs_nonneg _)
      (Finset.mem_univ j)
  have h2 : (∑ j', |x i - x j'|) ≤ lagBound x := by
    unfold lagBound
    exact Finset.single_le_sum (f := fun i' => ∑ j', |x i' - x j'|)
      (fun a _ => Finset.sum_nonneg fun b _ => abs_nonneg _) (Finset.mem_univ i)
  exact h1.trans h2

/-! ## (I1) pieces: the kernel `triG` -/

/-- `triG` vanishes at and beyond lag `2` (PROVED from its closed form). -/
theorem triG_eq_zero_of_abs_ge {y : ℝ} (hy : 2 ≤ |y|) : triG y = 0 := by
  unfold triG
  split_ifs with h1 h2
  · exfalso
    linarith
  · have hya : |y| = 2 := le_antisymm h2 hy
    rw [hya]
    norm_num
  · rfl

/-- `triG` is even (PROVED from its closed form, which involves only
`|y|` and `y^2`). -/
theorem triG_even (y : ℝ) : triG (-y) = triG y := by
  simp only [triG, abs_neg, neg_sq]

/-- The global closed form of `triG` through `tri` (PROVED):
`triG y = (max (2 - |y|) 0)^3 / 6 - (2/3) * (tri y)^3` for all `y`. -/
theorem triG_eq_triForm (y : ℝ) :
    triG y = (max (2 - |y|) 0) ^ 3 / 6 - (2 / 3) * (tri y) ^ 3 := by
  have htri : tri y = max (1 - |y|) 0 := rfl
  unfold triG
  split_ifs with h1 h2
  · rw [htri, max_eq_left (by linarith : (0:ℝ) ≤ 2 - |y|),
      max_eq_left (by linarith : (0:ℝ) ≤ 1 - |y|)]
    have key : (2 - |y|) ^ 3 / 6 - (2 / 3) * (1 - |y|) ^ 3
        = 2 / 3 - |y| ^ 2 + |y| ^ 3 / 2 := by ring
    rw [key, sq_abs]
  · rw [htri, max_eq_left (by linarith : (0:ℝ) ≤ 2 - |y|),
      max_eq_right (by linarith : 1 - |y| ≤ 0)]
    simp
  · rw [htri, max_eq_right (by linarith : 2 - |y| ≤ 0),
      max_eq_right (by linarith : 1 - |y| ≤ 0)]
    simp

/-- `tri` is continuous. -/
theorem continuous_tri : Continuous tri := by
  show Continuous (fun u : ℝ => max (1 - |u|) 0)
  fun_prop

/-- `triG` is continuous (PROVED via its global closed form
`triG_eq_triForm`). -/
theorem continuous_triG : Continuous triG := by
  have h : triG = fun y : ℝ => (max (2 - |y|) 0) ^ 3 / 6 - (2 / 3) * (tri y) ^ 3 :=
    funext triG_eq_triForm
  rw [h]
  have h1 : Continuous (fun y : ℝ => (max (2 - |y|) 0) ^ 3 / 6) :=
    (((continuous_const.sub continuous_abs).max continuous_const).pow 3).div_const 6
  have h2 : Continuous (fun y : ℝ => (2 / 3) * (tri y) ^ 3) :=
    (continuous_tri.pow 3).const_mul (2 / 3)
  exact h1.sub h2

/-- `Rc` is even (PROVED): `triG` is even and the configuration sum is
symmetric under `i ↔ j`. -/
theorem Rc_even {n : ℕ} (x c : Fin n → ℝ) (u : ℝ) : Rc x c (-u) = Rc x c u := by
  unfold Rc
  calc (∑ i, ∑ j, c i * c j * triG (-u - (x i - x j)))
      = ∑ i, ∑ j, c i * c j * triG (u + (x i - x j)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          rw [show -u - (x i - x j) = -(u + (x i - x j)) by ring, triG_even]
    _ = ∑ i, ∑ j, c j * c i * triG (u - (x j - x i)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          have hr : u + (x i - x j) = u - (x j - x i) := by ring
          rw [mul_comm (c i) (c j), hr]
    _ = ∑ i, ∑ j, c i * c j * triG (u - (x i - x j)) :=
        Finset.sum_comm

/-- `Rc` has compact support (PROVED): it vanishes beyond
`2 + lagBound x`, since every kernel value `triG (u - (x i - x j))` does. -/
theorem Rc_eq_zero_of_abs_gt {n : ℕ} (x c : Fin n → ℝ) {u : ℝ}
    (hu : 2 + lagBound x < |u|) : Rc x c u = 0 := by
  unfold Rc
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have hlag : (2 : ℝ) ≤ |u - (x i - x j)| := by
    have h1 : |u| - |x i - x j| ≤ |u - (x i - x j)| := abs_sub_abs_le_abs_sub u (x i - x j)
    have h2 := lag_le_lagBound x i j
    linarith
  rw [triG_eq_zero_of_abs_ge hlag, mul_zero]

/-- `Rc` is continuous (PROVED): a finite sum of continuous kernel
translates. -/
theorem continuous_Rc {n : ℕ} (x c : Fin n → ℝ) : Continuous (Rc x c) := by
  unfold Rc
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul
    (continuous_triG.comp (continuous_id.sub continuous_const))

/-- Admissibility of `R_c` for the explicit formula: compact support and
continuity. This is the hypothesis package `WeilEFPremise` asks for; it is
discharged in full by `rcAdmissible`. -/
def RcAdmissible {n : ℕ} (x c : Fin n → ℝ) : Prop :=
  (∃ B : ℝ, ∀ u : ℝ, B < |u| → Rc x c u = 0) ∧ Continuous (Rc x c)

/-- `R_c` is admissible (PROVED). -/
theorem rcAdmissible {n : ℕ} (x c : Fin n → ℝ) : RcAdmissible x c :=
  ⟨⟨2 + lagBound x, fun _ hu => Rc_eq_zero_of_abs_gt x c hu⟩, continuous_Rc x c⟩

/-! ## (I2): the prime side -/

private lemma primeTerm_summand_eq_zero {d B : ℝ} (hB : |d| ≤ B) {m : ℕ}
    (hm : Real.exp (2 + B) ≤ (m : ℝ)) :
    ArithmeticFunction.vonMangoldt m / Real.sqrt m *
      (triG (Real.log m + d) + triG (-Real.log m + d)) = 0 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hm
  have hlog : 2 + B ≤ Real.log (m : ℝ) := (Real.le_log_iff_exp_le hmpos).mpr hm
  have h1 : (2 : ℝ) ≤ |Real.log (m : ℝ) + d| :=
    le_trans (by linarith [hlog, neg_abs_le d, hB]) (le_abs_self _)
  have h2 : (2 : ℝ) ≤ |-Real.log (m : ℝ) + d| :=
    le_trans (by linarith [hlog, le_abs_self d, hB]) (neg_le_abs _)
  rw [triG_eq_zero_of_abs_ge h1, triG_eq_zero_of_abs_ge h2, add_zero, mul_zero]

/-- The prime kernel as a finite sum (PROVED): for any bound `B ≥ |d|`,
`primeTerm d` is the sum over the finite prime-power support
`m < exp (2 + B)`, since `triG` vanishes at lags `≥ 2`. -/
theorem primeTerm_eq_sum_of_bound (d B : ℝ) (hB : |d| ≤ B) :
    primeTerm d = ∑ m ∈ Finset.range (⌊Real.exp (2 + B)⌋₊ + 1),
      ArithmeticFunction.vonMangoldt m / Real.sqrt m *
        (triG (Real.log m + d) + triG (-Real.log m + d)) := by
  unfold primeTerm
  apply tsum_eq_sum
  intro m hm
  apply primeTerm_summand_eq_zero hB
  have h1 : Real.exp (2 + B) < ((⌊Real.exp (2 + B)⌋₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_floor_add_one _
  have h2 : ⌊Real.exp (2 + B)⌋₊ + 1 ≤ m := by
    simpa only [Finset.mem_range, not_lt] using hm
  exact le_of_lt (lt_of_lt_of_le h1 (by exact_mod_cast h2))

/-- **(I2), finite form** (PROVED): the prime side of the defect form is the
finite sum `2 * ∑_{m < exp (2 + lagBound x)} Λ m / √m * Rc x c (log m)`.
Pure finite manipulation of the in-tree `primeTerm`: finite support of the
prime kernel, `triG` evenness, and the symmetry `i ↔ j`. -/
theorem kform_primeTerm_finite {n : ℕ} (x c : Fin n → ℝ) :
    kform primeTerm x c = 2 * ∑ m ∈ Finset.range (⌊Real.exp (2 + lagBound x)⌋₊ + 1),
      ArithmeticFunction.vonMangoldt m / Real.sqrt m * Rc x c (Real.log m) := by
  classical
  set S := Finset.range (⌊Real.exp (2 + lagBound x)⌋₊ + 1) with hS
  have hterm : ∀ i j : Fin n, primeTerm (x i - x j)
      = ∑ m ∈ S, ArithmeticFunction.vonMangoldt m / Real.sqrt m *
          (triG (Real.log m + (x i - x j)) + triG (-Real.log m + (x i - x j))) :=
    fun i j => primeTerm_eq_sum_of_bound _ _ (lag_le_lagBound x i j)
  have key : ∀ m : ℕ, (∑ i, ∑ j, c i * c j *
        (ArithmeticFunction.vonMangoldt m / Real.sqrt m *
          (triG (Real.log m + (x i - x j)) + triG (-Real.log m + (x i - x j)))))
      = 2 * (ArithmeticFunction.vonMangoldt m / Real.sqrt m * Rc x c (Real.log m)) := by
    intro m
    have hA : (∑ i, ∑ j, c i * c j * triG (Real.log m + (x i - x j)))
        = Rc x c (-Real.log m) := by
      unfold Rc
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [show Real.log (m : ℝ) + (x i - x j) = -(-Real.log (m : ℝ) - (x i - x j)) by ring,
        triG_even]
    have hB : (∑ i, ∑ j, c i * c j * triG (-Real.log m + (x i - x j)))
        = Rc x c (-Real.log m) := by
      calc (∑ i, ∑ j, c i * c j * triG (-Real.log m + (x i - x j)))
          = ∑ i, ∑ j, c j * c i * triG (-Real.log m - (x j - x i)) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
              have hr : -Real.log (m : ℝ) + (x i - x j)
                  = -Real.log (m : ℝ) - (x j - x i) := by ring
              rw [mul_comm (c i) (c j), hr]
        _ = Rc x c (-Real.log m) := by
            unfold Rc
            exact Finset.sum_comm
    have hsplit : (∑ i, ∑ j, c i * c j *
          (ArithmeticFunction.vonMangoldt m / Real.sqrt m *
            (triG (Real.log m + (x i - x j)) + triG (-Real.log m + (x i - x j)))))
        = ArithmeticFunction.vonMangoldt m / Real.sqrt m *
            ((∑ i, ∑ j, c i * c j * triG (Real.log m + (x i - x j)))
              + (∑ i, ∑ j, c i * c j * triG (-Real.log m + (x i - x j)))) := by
      calc (∑ i, ∑ j, c i * c j *
            (ArithmeticFunction.vonMangoldt m / Real.sqrt m *
              (triG (Real.log m + (x i - x j)) + triG (-Real.log m + (x i - x j)))))
          = ∑ i, ∑ j, ArithmeticFunction.vonMangoldt m / Real.sqrt m *
              (c i * c j * triG (Real.log m + (x i - x j))
                + c i * c j * triG (-Real.log m + (x i - x j))) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
        _ = ∑ i, ArithmeticFunction.vonMangoldt m / Real.sqrt m *
              ((∑ j, c i * c j * triG (Real.log m + (x i - x j)))
                + (∑ j, c i * c j * triG (-Real.log m + (x i - x j)))) :=
            Finset.sum_congr rfl fun i _ => by
              rw [← Finset.mul_sum, Finset.sum_add_distrib]
        _ = ArithmeticFunction.vonMangoldt m / Real.sqrt m *
              ((∑ i, ∑ j, c i * c j * triG (Real.log m + (x i - x j)))
                + (∑ i, ∑ j, c i * c j * triG (-Real.log m + (x i - x j)))) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib]
    rw [hsplit, hA, hB, ← two_mul, Rc_even]
    ring
  unfold kform
  calc (∑ i, ∑ j, c i * c j * primeTerm (x i - x j))
      = ∑ i, ∑ j, ∑ m ∈ S, c i * c j *
          (ArithmeticFunction.vonMangoldt m / Real.sqrt m *
            (triG (Real.log m + (x i - x j)) + triG (-Real.log m + (x i - x j)))) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          rw [hterm i j, Finset.mul_sum]
    _ = ∑ i, ∑ m ∈ S, ∑ j, c i * c j *
          (ArithmeticFunction.vonMangoldt m / Real.sqrt m *
            (triG (Real.log m + (x i - x j)) + triG (-Real.log m + (x i - x j)))) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m ∈ S, ∑ i, ∑ j, c i * c j *
          (ArithmeticFunction.vonMangoldt m / Real.sqrt m *
            (triG (Real.log m + (x i - x j)) + triG (-Real.log m + (x i - x j)))) :=
        Finset.sum_comm
    _ = ∑ m ∈ S, 2 * (ArithmeticFunction.vonMangoldt m / Real.sqrt m *
          Rc x c (Real.log m)) :=
        Finset.sum_congr rfl fun m _ => key m
    _ = 2 * ∑ m ∈ S, ArithmeticFunction.vonMangoldt m / Real.sqrt m *
          Rc x c (Real.log m) := by
        rw [Finset.mul_sum]

/-- **(I2)** (PROVED): the prime side of the defect form,
`kform primeTerm x c = 2 * ∑' m, Λ m / √m * Rc x c (log m)`. The `∑'` is a
finite sum in disguise: `Rc x c (log m)` vanishes for
`m ≥ exp (2 + lagBound x)`. -/
theorem kform_primeTerm {n : ℕ} (x c : Fin n → ℝ) :
    kform primeTerm x c = 2 * ∑' m : ℕ,
      ArithmeticFunction.vonMangoldt m / Real.sqrt m * Rc x c (Real.log m) := by
  have htsum : (∑' m : ℕ, ArithmeticFunction.vonMangoldt m / Real.sqrt m *
        Rc x c (Real.log m))
      = ∑ m ∈ Finset.range (⌊Real.exp (2 + lagBound x)⌋₊ + 1),
        ArithmeticFunction.vonMangoldt m / Real.sqrt m * Rc x c (Real.log m) := by
    apply tsum_eq_sum
    intro m hm
    have h1 : Real.exp (2 + lagBound x) < ((⌊Real.exp (2 + lagBound x)⌋₊ + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_floor_add_one _
    have h2 : ⌊Real.exp (2 + lagBound x)⌋₊ + 1 ≤ m := by
      simpa only [Finset.mem_range, not_lt] using hm
    have hmexp : Real.exp (2 + lagBound x) < (m : ℝ) :=
      lt_of_lt_of_le h1 (by exact_mod_cast h2)
    have hmpos : (0 : ℝ) < (m : ℝ) := (Real.exp_pos _).trans hmexp
    have hlog : 2 + lagBound x < Real.log (m : ℝ) :=
      (Real.lt_log_iff_exp_lt hmpos).mpr hmexp
    have hRc : Rc x c (Real.log m) = 0 := by
      apply Rc_eq_zero_of_abs_gt
      rw [abs_of_nonneg (by linarith [hlog, lagBound_nonneg x] : (0 : ℝ) ≤ Real.log (m : ℝ))]
      exact hlog
    rw [hRc, mul_zero]
  rw [kform_primeTerm_finite, htsum]

/-! ## The pole side, as finite algebra -/

/-- The pole kernel on a finite configuration (PROVED):
`kform poleTerm x c = 2 * bigPsiI2^2 * ((∑ i, c i * cosh (x i / 2))^2
- (∑ i, c i * sinh (x i / 2))^2)`, by `cosh (a - b) = cosh a cosh b
- sinh a sinh b` and factorisation of the double sum. -/
theorem kform_poleTerm {n : ℕ} (x c : Fin n → ℝ) :
    kform poleTerm x c = 2 * bigPsiI2 ^ 2 *
      ((∑ i, c i * Real.cosh (x i / 2)) ^ 2 - (∑ i, c i * Real.sinh (x i / 2)) ^ 2) := by
  have hcosh : ∀ i j : Fin n, Real.cosh ((x i - x j) / 2)
      = Real.cosh (x i / 2) * Real.cosh (x j / 2)
        - Real.sinh (x i / 2) * Real.sinh (x j / 2) := by
    intro i j
    rw [show (x i - x j) / 2 = x i / 2 - x j / 2 by ring]
    exact Real.cosh_sub _ _
  have step : (∑ i, ∑ j, c i * c j * (2 * bigPsiI2 ^ 2 * Real.cosh ((x i - x j) / 2)))
      = ∑ i, ∑ j, 2 * bigPsiI2 ^ 2 *
          (c i * Real.cosh (x i / 2) * (c j * Real.cosh (x j / 2))
            - c i * Real.sinh (x i / 2) * (c j * Real.sinh (x j / 2))) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [hcosh i j]; ring
  have efac : ∀ (A B : Fin n → Fin n → ℝ),
      (∑ i, ∑ j, 2 * bigPsiI2 ^ 2 * (A i j - B i j))
        = 2 * bigPsiI2 ^ 2 * ((∑ i, ∑ j, A i j) - (∑ i, ∑ j, B i j)) := by
    intro A B
    calc (∑ i, ∑ j, 2 * bigPsiI2 ^ 2 * (A i j - B i j))
        = ∑ i, 2 * bigPsiI2 ^ 2 * ((∑ j, A i j) - (∑ j, B i j)) :=
          Finset.sum_congr rfl fun i _ => by
            rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      _ = 2 * bigPsiI2 ^ 2 * ((∑ i, ∑ j, A i j) - (∑ i, ∑ j, B i j)) := by
          rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  have e1 : (∑ i, ∑ j, c i * Real.cosh (x i / 2) * (c j * Real.cosh (x j / 2)))
      = (∑ i, c i * Real.cosh (x i / 2)) ^ 2 := by
    rw [sq]
    exact (Finset.sum_mul_sum _ _ _ _).symm
  have e2 : (∑ i, ∑ j, c i * Real.sinh (x i / 2) * (c j * Real.sinh (x j / 2)))
      = (∑ i, c i * Real.sinh (x i / 2)) ^ 2 := by
    rw [sq]
    exact (Finset.sum_mul_sum _ _ _ _).symm
  unfold kform poleTerm
  rw [step, efac, e1, e2]

/-- On `ker ℓ_c` the pole kernel is exactly minus the pole correction
(PROVED). -/
theorem kform_poleTerm_on_ker {n : ℕ} (x c : Fin n → ℝ)
    (hker : ∑ i, c i * Real.cosh (x i / 2) = 0) :
    kform poleTerm x c = -poleCorr x c := by
  rw [kform_poleTerm, hker]
  unfold poleCorr
  ring

/-- The defect kernel splits over its three parts (PROVED, pointwise in
the kernel). -/
theorem kform_Kpsi {n : ℕ} (x c : Fin n → ℝ) :
    kform Kpsi x c
      = kform poleTerm x c - kform primeTerm x c + kform archTerm x c := by
  unfold kform Kpsi
  have pt : ∀ i j : Fin n, c i * c j * (poleTerm (x i - x j) - primeTerm (x i - x j)
        + archTerm (x i - x j))
      = c i * c j * poleTerm (x i - x j) - c i * c j * primeTerm (x i - x j)
        + c i * c j * archTerm (x i - x j) := fun i j => by ring
  calc (∑ i, ∑ j, c i * c j * (poleTerm (x i - x j) - primeTerm (x i - x j)
          + archTerm (x i - x j)))
      = ∑ i, ∑ j, (c i * c j * poleTerm (x i - x j) - c i * c j * primeTerm (x i - x j)
          + c i * c j * archTerm (x i - x j)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => pt i j
    _ = (∑ i, ∑ j, c i * c j * poleTerm (x i - x j))
          - (∑ i, ∑ j, c i * c j * primeTerm (x i - x j))
          + (∑ i, ∑ j, c i * c j * archTerm (x i - x j)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-! ## (I3): the pole points of `Fhat` -/

/-- `tri` vanishes at and beyond `1`. -/
theorem tri_eq_zero_of_abs_ge {v : ℝ} (hv : 1 ≤ |v|) : tri v = 0 := by
  have e : tri v = max (1 - |v|) 0 := rfl
  rw [e, max_eq_right (by linarith : 1 - |v| ≤ 0)]

private lemma hasCompactSupport_tri_mul {g : ℝ → ℝ} (a : ℝ) :
    HasCompactSupport (fun u => tri (u - a) * g u) := by
  show IsCompact (closure (Function.support (fun u => tri (u - a) * g u)))
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := a - 1) (b := a + 1)) isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro u hu
  simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hu
  have hlt : |u - a| < 1 := by
    by_contra hc
    exact hu.1 (tri_eq_zero_of_abs_ge (le_of_not_gt hc))
  rw [Set.mem_Icc]
  constructor <;> linarith [abs_lt.mp hlt]

private lemma integrable_tri_sub_mul {g : ℝ → ℝ} (a : ℝ) (hg : Continuous g) :
    Integrable (fun u => tri (u - a) * g u) :=
  ((continuous_tri.comp (continuous_id.sub continuous_const)).mul hg).integrable_of_hasCompactSupport
    (hasCompactSupport_tri_mul a)

private lemma integrable_tri_mul {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable (fun v => tri v * g v) := by
  have h := integrable_tri_sub_mul (g := g) 0 hg
  simpa using h

/-- The odd part of the `tri` transform vanishes (PROVED):
`∫ v, tri v * sinh (v/2) dv = 0`, since `tri` is even and `sinh` is odd. -/
theorem tri_integral_sinh : ∫ v : ℝ, tri v * Real.sinh (v / 2) = 0 := by
  have hodd : ∀ v : ℝ, tri (-v) * Real.sinh (-v / 2) = -(tri v * Real.sinh (v / 2)) := by
    intro v
    have h1 : tri (-v) = tri v := by
      have e : tri (-v) = max (1 - |-v|) 0 := rfl
      have e2 : tri v = max (1 - |v|) 0 := rfl
      rw [e, e2, abs_neg]
    have h2 : Real.sinh (-v / 2) = -Real.sinh (v / 2) := by
      rw [show -v / 2 = -(v / 2) by ring, Real.sinh_neg]
    rw [h1, h2]
    ring
  have hI : (∫ v : ℝ, tri (-v) * Real.sinh (-v / 2))
      = ∫ v : ℝ, tri v * Real.sinh (v / 2) :=
    MeasureTheory.integral_neg_eq_self (fun v => tri v * Real.sinh (v / 2)) volume
  have hI2 : (∫ v : ℝ, tri (-v) * Real.sinh (-v / 2))
      = -(∫ v : ℝ, tri v * Real.sinh (v / 2)) := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall hodd)
  linarith [hI, hI2]

private lemma tri_eq_on_Icc_nonneg {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) : tri v = 1 - v := by
  have e : tri v = max (1 - |v|) 0 := rfl
  rw [e, abs_of_nonneg h0, max_eq_left (by linarith : (0:ℝ) ≤ 1 - v)]

private lemma tri_eq_on_Icc_nonpos {v : ℝ} (h0 : -1 ≤ v) (h1 : v ≤ 0) : tri v = 1 + v := by
  have e : tri v = max (1 - |v|) 0 := rfl
  rw [e, abs_of_nonpos h1, max_eq_left (by linarith : (0:ℝ) ≤ 1 - -v)]
  ring

private lemma integral_tri_cosh_zero_one :
    ∫ v in (0:ℝ)..1, tri v * Real.cosh (v / 2) = 4 * Real.cosh (1 / 2) - 4 := by
  have hcongr : ∫ v in (0:ℝ)..1, tri v * Real.cosh (v / 2)
      = ∫ v in (0:ℝ)..1, (1 - v) * Real.cosh (v / 2) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Icc] at hv
    show tri v * Real.cosh (v / 2) = (1 - v) * Real.cosh (v / 2)
    rw [tri_eq_on_Icc_nonneg hv.1 hv.2]
  rw [hcongr]
  have hF : ∀ v : ℝ, HasDerivAt
      (fun v => 2 * (1 - v) * Real.sinh (v / 2) + 4 * Real.cosh (v / 2))
      ((1 - v) * Real.cosh (v / 2)) v := by
    intro v
    have h1 : HasDerivAt (fun v : ℝ => v / 2) (1 / 2) v := by
      simpa using (hasDerivAt_id v).div_const (2 : ℝ)
    have h2 : HasDerivAt (fun v : ℝ => Real.sinh (v / 2)) (Real.cosh (v / 2) * (1 / 2)) v :=
      h1.sinh
    have h3 : HasDerivAt (fun v : ℝ => Real.cosh (v / 2)) (Real.sinh (v / 2) * (1 / 2)) v :=
      h1.cosh
    have hLin : HasDerivAt (fun v : ℝ => 2 * (1 - v)) (-2) v := by
      simpa using ((hasDerivAt_id v).const_sub (1 : ℝ)).const_mul (2 : ℝ)
    have hsum := (hLin.mul h2).add (h3.const_mul (4 : ℝ))
    refine hsum.congr_deriv ?_
    ring
  have hint : IntervalIntegrable (fun v => (1 - v) * Real.cosh (v / 2)) volume 0 1 :=
    (by fun_prop : Continuous (fun v : ℝ => (1 - v) * Real.cosh (v / 2))).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hF v) hint]
  simp only [zero_div, Real.sinh_zero, Real.cosh_zero]
  ring

private lemma integral_tri_cosh_neg_one_zero :
    ∫ v in (-1:ℝ)..0, tri v * Real.cosh (v / 2) = 4 * Real.cosh (1 / 2) - 4 := by
  have hcongr : ∫ v in (-1:ℝ)..0, tri v * Real.cosh (v / 2)
      = ∫ v in (-1:ℝ)..0, (1 + v) * Real.cosh (v / 2) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 0), Set.mem_Icc] at hv
    show tri v * Real.cosh (v / 2) = (1 + v) * Real.cosh (v / 2)
    rw [tri_eq_on_Icc_nonpos hv.1 hv.2]
  rw [hcongr]
  have hF : ∀ v : ℝ, HasDerivAt
      (fun v => 2 * (1 + v) * Real.sinh (v / 2) - 4 * Real.cosh (v / 2))
      ((1 + v) * Real.cosh (v / 2)) v := by
    intro v
    have h1 : HasDerivAt (fun v : ℝ => v / 2) (1 / 2) v := by
      simpa using (hasDerivAt_id v).div_const (2 : ℝ)
    have h2 : HasDerivAt (fun v : ℝ => Real.sinh (v / 2)) (Real.cosh (v / 2) * (1 / 2)) v :=
      h1.sinh
    have h3 : HasDerivAt (fun v : ℝ => Real.cosh (v / 2)) (Real.sinh (v / 2) * (1 / 2)) v :=
      h1.cosh
    have hLin : HasDerivAt (fun v : ℝ => 2 * (1 + v)) (2) v := by
      simpa using ((hasDerivAt_id v).const_add (1 : ℝ)).const_mul (2 : ℝ)
    have hdiff := (hLin.mul h2).sub (h3.const_mul (4 : ℝ))
    refine hdiff.congr_deriv ?_
    ring
  have hint : IntervalIntegrable (fun v => (1 + v) * Real.cosh (v / 2)) volume (-1) 0 :=
    (by fun_prop : Continuous (fun v : ℝ => (1 + v) * Real.cosh (v / 2))).intervalIntegrable
      (-1) 0
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hF v) hint]
  rw [show (-1 : ℝ) / 2 = -(1 / 2) by ring, Real.cosh_neg]
  simp only [zero_div, Real.sinh_zero, Real.cosh_zero]
  ring

/-- The archimedean normalisation integral (PROVED by FTC on `[-1, 1]`):
`∫ v, tri v * cosh (v/2) dv = bigPsiI2 = 16 sinh^2(1/4)`. -/
theorem tri_integral_cosh : ∫ v : ℝ, tri v * Real.cosh (v / 2) = bigPsiI2 := by
  have hzero : ∀ v : ℝ, v ∉ Set.Ioc (-1) 1 → tri v * Real.cosh (v / 2) = 0 := by
    intro v hv
    have h1 : (1:ℝ) ≤ |v| := by
      by_contra hc
      rw [not_le] at hc
      exact hv ⟨(abs_lt.mp hc).1, le_of_lt (abs_lt.mp hc).2⟩
    rw [tri_eq_zero_of_abs_ge h1, zero_mul]
  have hcont : Continuous (fun v : ℝ => tri v * Real.cosh (v / 2)) :=
    continuous_tri.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (-1) 0) (hcont.intervalIntegrable 0 1),
    integral_tri_cosh_neg_one_zero, integral_tri_cosh_zero_one]
  have h1 : Real.cosh (1 / 2 : ℝ) = Real.cosh (1 / 4) ^ 2 + Real.sinh (1 / 4) ^ 2 := by
    rw [show (1 / 2 : ℝ) = 2 * (1 / 4) by norm_num]
    exact Real.cosh_two_mul _
  have h2 := Real.cosh_sq_sub_sinh_sq (1 / 4 : ℝ)
  unfold bigPsiI2
  linarith [h1, h2]

/-- `∫ v, tri v * exp (v/2) dv = bigPsiI2` (PROVED: `exp = cosh + sinh`). -/
theorem tri_integral_exp_half : ∫ v : ℝ, tri v * Real.exp (v / 2) = bigPsiI2 := by
  have hpt : ∀ v : ℝ, tri v * Real.exp (v / 2)
      = tri v * Real.cosh (v / 2) + tri v * Real.sinh (v / 2) := by
    intro v
    rw [← Real.cosh_add_sinh]
    ring
  have hcosh_cont : Continuous (fun v : ℝ => Real.cosh (v / 2)) :=
    Real.continuous_cosh.comp (continuous_id.div_const 2)
  have hsinh_cont : Continuous (fun v : ℝ => Real.sinh (v / 2)) :=
    Real.continuous_sinh.comp (continuous_id.div_const 2)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_add (integrable_tri_mul hcosh_cont) (integrable_tri_mul hsinh_cont),
    tri_integral_cosh, tri_integral_sinh, add_zero]

/-- `∫ v, tri v * exp (-(v/2)) dv = bigPsiI2` (PROVED: `exp (-t) = cosh t
- sinh t`). -/
theorem tri_integral_exp_neg_half : ∫ v : ℝ, tri v * Real.exp (-(v / 2)) = bigPsiI2 := by
  have hpt : ∀ v : ℝ, tri v * Real.exp (-(v / 2))
      = tri v * Real.cosh (v / 2) - tri v * Real.sinh (v / 2) := by
    intro v
    have h : Real.exp (-(v / 2)) = Real.cosh (v / 2) - Real.sinh (v / 2) := by
      have h1 := Real.cosh_add_sinh (-(v / 2))
      rw [Real.cosh_neg, Real.sinh_neg] at h1
      linarith [h1]
    rw [h]
    ring
  have hcosh_cont : Continuous (fun v : ℝ => Real.cosh (v / 2)) :=
    Real.continuous_cosh.comp (continuous_id.div_const 2)
  have hsinh_cont : Continuous (fun v : ℝ => Real.sinh (v / 2)) :=
    Real.continuous_sinh.comp (continuous_id.div_const 2)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_sub (integrable_tri_mul hcosh_cont) (integrable_tri_mul hsinh_cont),
    tri_integral_cosh, tri_integral_sinh, sub_zero]

private lemma integral_tri_sub_mul_exp_half (a : ℝ) :
    ∫ u : ℝ, tri (u - a) * Real.exp (u / 2) = Real.exp (a / 2) * bigPsiI2 := by
  have hpt : ∀ u : ℝ, tri (u - a) * Real.exp (u / 2)
      = Real.exp (a / 2) * (tri (u - a) * Real.exp ((u - a) / 2)) := by
    intro u
    have hexp : Real.exp (u / 2) = Real.exp (a / 2) * Real.exp ((u - a) / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
  congr 1
  exact (integral_sub_right_eq_self (fun w : ℝ => tri w * Real.exp (w / 2)) a).trans
    tri_integral_exp_half

private lemma integral_tri_sub_mul_exp_neg_half (a : ℝ) :
    ∫ u : ℝ, tri (u - a) * Real.exp (-(u / 2)) = Real.exp (-(a / 2)) * bigPsiI2 := by
  have hpt : ∀ u : ℝ, tri (u - a) * Real.exp (-(u / 2))
      = Real.exp (-(a / 2)) * (tri (u - a) * Real.exp (-((u - a) / 2))) := by
    intro u
    have hexp : Real.exp (-(u / 2))
        = Real.exp (-(a / 2)) * Real.exp (-((u - a) / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
  congr 1
  exact (integral_sub_right_eq_self (fun w : ℝ => tri w * Real.exp (-(w / 2))) a).trans
    tri_integral_exp_neg_half

/-- **(I3), at `s = 0`** (PROVED):
`Fhat x c 0 = bigPsiI2 * ∑ i, c i * exp (x i / 2)`. -/
theorem Fhat_zero {n : ℕ} (x c : Fin n → ℝ) :
    Fhat x c 0 = ((bigPsiI2 * ∑ i, c i * Real.exp (x i / 2) : ℝ) : ℂ) := by
  have hexp : ∀ u : ℝ, (-(0 - 1 / 2 : ℂ)) * (u : ℂ) = ((u / 2 : ℝ) : ℂ) := by
    intro u
    push_cast
    ring
  have hpt : ∀ u : ℝ, (Fc x c u : ℂ) * Complex.exp (-(0 - 1 / 2 : ℂ) * (u : ℂ))
      = ((Fc x c u * Real.exp (u / 2) : ℝ) : ℂ) := by
    intro u
    rw [hexp, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  have hsum : ∀ u : ℝ, Fc x c u * Real.exp (u / 2)
      = ∑ i, c i * (tri (u - x i) * Real.exp (u / 2)) := by
    intro u
    unfold Fc
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hexp_cont : Continuous (fun u : ℝ => Real.exp (u / 2)) :=
    Real.continuous_exp.comp (continuous_id.div_const 2)
  have hcast : (∫ u : ℝ, ((Fc x c u * Real.exp (u / 2) : ℝ) : ℂ))
      = ((∫ u : ℝ, Fc x c u * Real.exp (u / 2) : ℝ) : ℂ) := integral_ofReal
  unfold Fhat
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), hcast,
    integral_congr_ae (Filter.Eventually.of_forall hsum),
    integral_finsetSum _ (fun i _ =>
      (integrable_tri_sub_mul (x i) hexp_cont).const_mul (c i)),
    Finset.mul_sum]
  rw [Complex.ofReal_inj]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, integral_tri_sub_mul_exp_half]
  ring

/-- **(I3), at `s = 1`** (PROVED):
`Fhat x c 1 = bigPsiI2 * ∑ i, c i * exp (-(x i / 2))`. -/
theorem Fhat_one {n : ℕ} (x c : Fin n → ℝ) :
    Fhat x c 1 = ((bigPsiI2 * ∑ i, c i * Real.exp (-(x i / 2)) : ℝ) : ℂ) := by
  have hexp : ∀ u : ℝ, (-(1 - 1 / 2 : ℂ)) * (u : ℂ) = ((-(u / 2) : ℝ) : ℂ) := by
    intro u
    push_cast
    ring
  have hpt : ∀ u : ℝ, (Fc x c u : ℂ) * Complex.exp (-(1 - 1 / 2 : ℂ) * (u : ℂ))
      = ((Fc x c u * Real.exp (-(u / 2)) : ℝ) : ℂ) := by
    intro u
    rw [hexp, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  have hsum : ∀ u : ℝ, Fc x c u * Real.exp (-(u / 2))
      = ∑ i, c i * (tri (u - x i) * Real.exp (-(u / 2))) := by
    intro u
    unfold Fc
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hexp_cont : Continuous (fun u : ℝ => Real.exp (-(u / 2))) :=
    Real.continuous_exp.comp (continuous_id.div_const 2).neg
  have hcast : (∫ u : ℝ, ((Fc x c u * Real.exp (-(u / 2)) : ℝ) : ℂ))
      = ((∫ u : ℝ, Fc x c u * Real.exp (-(u / 2)) : ℝ) : ℂ) := integral_ofReal
  unfold Fhat
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), hcast,
    integral_congr_ae (Filter.Eventually.of_forall hsum),
    integral_finsetSum _ (fun i _ =>
      (integrable_tri_sub_mul (x i) hexp_cont).const_mul (c i)),
    Finset.mul_sum]
  rw [Complex.ofReal_inj]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, integral_tri_sub_mul_exp_neg_half]
  ring

/-- **(I3), assembled** (PROVED): on `ker ℓ_c`, the two pole values of
`Fhat` satisfy `(Fhat x c 0)^2 + (Fhat x c 1)^2 = poleCorr x c`, since
`∑ i, c i * exp (±(x i)/2) = ± ∑ i, c i * sinh (x i / 2)` there. -/
theorem Fhat_zero_sq_add_one_sq {n : ℕ} (x c : Fin n → ℝ)
    (hker : ∑ i, c i * Real.cosh (x i / 2) = 0) :
    (Fhat x c 0) ^ 2 + (Fhat x c 1) ^ 2 = ((poleCorr x c : ℝ) : ℂ) := by
  have hEp : (∑ i, c i * Real.exp (x i / 2)) = ∑ i, c i * Real.sinh (x i / 2) := by
    have hsplit : (∑ i, c i * Real.exp (x i / 2))
        = (∑ i, c i * Real.cosh (x i / 2)) + (∑ i, c i * Real.sinh (x i / 2)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Real.cosh_add_sinh]
      ring
    rw [hsplit, hker, zero_add]
  have hEm : (∑ i, c i * Real.exp (-(x i / 2))) = -(∑ i, c i * Real.sinh (x i / 2)) := by
    have key : ∀ i : Fin n, c i * Real.exp (-(x i / 2))
        = c i * Real.cosh (x i / 2) - c i * Real.sinh (x i / 2) := by
      intro i
      have h : Real.exp (-(x i / 2)) = Real.cosh (x i / 2) - Real.sinh (x i / 2) := by
        have h1 := Real.cosh_add_sinh (-(x i / 2))
        rw [Real.cosh_neg, Real.sinh_neg] at h1
        linarith [h1]
      rw [h]
      ring
    calc (∑ i, c i * Real.exp (-(x i / 2)))
        = ∑ i, (c i * Real.cosh (x i / 2) - c i * Real.sinh (x i / 2)) :=
          Finset.sum_congr rfl fun i _ => key i
      _ = (∑ i, c i * Real.cosh (x i / 2)) - (∑ i, c i * Real.sinh (x i / 2)) := by
          rw [Finset.sum_sub_distrib]
      _ = -(∑ i, c i * Real.sinh (x i / 2)) := by
          rw [hker, zero_sub]
  rw [Fhat_zero, Fhat_one, hEp, hEm]
  unfold poleCorr
  push_cast
  ring

/-! ## The remaining analytic premise, and the assembly -/

/-- **The Weil explicit formula for `R_c`** — the single remaining analytic
input of (O2), stated as a named premise. For every finite configuration
`(x, c)` whose autocorrelation `R_c` is admissible (compactly supported and
continuous — discharged unconditionally by `rcAdmissible`), and for every
exhaustion `Z` of the nontrivial zeros, the partial spectral sums
`Sfin x c (Z k)` converge to the non-spectral side of the explicit formula
for `R_c`: the archimedean term `kform archTerm x c`, minus the prime sum
`2 * ∑' m, Λ m / √m * Rc x c (log m)`, minus the pole contribution
`(Fhat x c 0)^2 + (Fhat x c 1)^2`.

The content of this premise is the Guinand–Weil explicit formula applied
to `R_c` itself: the spectral identification of the zero sum with the
`Fhat` products, including the factorisation of the Mellin transform of
`R_c` at a zero `ρ` as `Fhat x c ρ * Fhat x c (1 - ρ)` — equivalently, the
identification of the kernel-form `Rc` with the integral autocorrelation
of `Fc`, whose kernel identity is `triG y = ∫ t, tri t * tri (t - y) dt`.
Nothing else in (O2) is unproved. -/
structure WeilEFPremise : Prop where
  ef : ∀ (n : ℕ) (x c : Fin n → ℝ), RcAdmissible x c →
    ∀ (Z : ℕ → Finset ℂ), ZeroExhaustion Z →
      Tendsto (fun k => Sfin x c (Z k)) atTop
        (𝓝 (((kform archTerm x c : ℝ) : ℂ)
          - ((2 * ∑' m : ℕ, ArithmeticFunction.vonMangoldt m / Real.sqrt m *
              Rc x c (Real.log m) : ℝ) : ℂ)
          - ((Fhat x c 0) ^ 2 + (Fhat x c 1) ^ 2)))

/-- **(O2) from the premise** (PROVED): `WeilEFPremise` implies `O2`, by
the finite lemmas of this file alone: (I2) identifies the prime sum with
`kform primeTerm x c`; (I3) identifies the pole contribution with
`poleCorr x c` on `ker ℓ_c`; and `kform_poleTerm_on_ker` together with
`kform_Kpsi` reassembles the three parts into `kform Kpsi x c`. -/
theorem O2_of_weilEF (h : WeilEFPremise) : O2 := by
  intro Z hZ n x c hker
  have hEF := h.ef n x c (rcAdmissible x c) Z hZ
  have hlim : ((kform archTerm x c : ℝ) : ℂ)
        - ((2 * ∑' m : ℕ, ArithmeticFunction.vonMangoldt m / Real.sqrt m *
            Rc x c (Real.log m) : ℝ) : ℂ)
        - ((Fhat x c 0) ^ 2 + (Fhat x c 1) ^ 2)
      = ((kform Kpsi x c : ℝ) : ℂ) := by
    rw [← kform_primeTerm x c, Fhat_zero_sq_add_one_sq x c hker,
      ← Complex.ofReal_sub, ← Complex.ofReal_sub]
    congr 1
    have e1 := kform_Kpsi x c
    have e2 := kform_poleTerm_on_ker x c hker
    linarith [e1, e2]
  rw [hlim] at hEF
  exact hEF

end GppQuartetFiniteCore
