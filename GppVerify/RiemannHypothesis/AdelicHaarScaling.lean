/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.RiemannHypothesis.AdelicPoissonStatement
import GppVerify.RiemannHypothesis.AdelicFiniteFourier

/-!
# The scaling law of the adelic Haar measure

Discharges `HaarScaling` (`AdelicPoissonStatement.lean`): for an idele `a`,
`adeleHaar.map (a * ·) = |a|⁻¹ • adeleHaar`, with `|a| = ideleNorm a`.

* `map_haar_mulHomeo`: multiplication by a finite idele pushes `haar` to a multiple of `haar`,
  the multiple being the volume of the preimage of `∏ ℤ_v`.
* `haar_scaling_fin`: that multiple is `(∏_p |u_p|_p)⁻¹`. Units of `∏ ℤ_p` preserve `∏ ℤ_p`, a
  natural number `N` and its inverse send it to `(1/N)∏ℤ_v` and `N∏ℤ_v` (volumes `N`, `N⁻¹`),
  and every finite idele is a positive rational times a unit of `∏ ℤ_p`.
-/
open MeasureTheory IsDedekindDomain GppIdeleQ Rat.FiniteAdeleRing

namespace GlobalTate.Poisson

instance haar_regular : (haar : Measure Af).Regular := by unfold haar; infer_instance

/-- Multiplication by a finite idele as a homeomorphism of the finite adeles. -/
noncomputable def mulHomeo (u : Afˣ) : Af ≃ₜ Af where
  toFun x := (u : Af) * x
  invFun x := ((u⁻¹ : Afˣ) : Af) * x
  left_inv x := by simp [← mul_assoc]
  right_inv x := by simp [← mul_assoc]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

theorem mulHomeo_apply (u : Afˣ) (x : Af) : mulHomeo u x = (u : Af) * x := rfl

theorem map_haar_mulHomeo (u : Afˣ) :
    haar.map (mulHomeo u) = haar ((mulHomeo u) ⁻¹' integralAdeles) • haar := by
  let f : Af →+ Af := AddMonoidHom.mulLeft (u : Af)
  have hf : (f : Af → Af) = mulHomeo u := rfl
  have : (haar.map (mulHomeo u)).IsAddHaarMeasure := by
    have := Measure.isAddHaarMeasure_map haar f (by rw [hf]; exact (mulHomeo u).continuous)
      (by rw [hf]; exact (mulHomeo u).surjective)
      (by rw [hf]; exact (mulHomeo u).map_cocompact.le)
    rw [hf] at this; exact this
  have : (haar.map (mulHomeo u)).Regular := Measure.Regular.map _
  have h := Measure.isAddLeftInvariant_eq_smul_of_regular (haar.map (mulHomeo u)) haar
  have h2 := congrArg (fun m => m integralAdeles) h
  simp only [Measure.smul_apply, haar_integralAdeles, smul_eq_mul, mul_one] at h2
  set c := (haar.map (mulHomeo u)).addHaarScalarFactor haar with hc
  have h3 : haar ((mulHomeo u) ⁻¹' integralAdeles) = (c : ENNReal) := by
    rw [← Measure.map_apply (mulHomeo u).continuous.measurable isOpen_integralAdeles.measurableSet, h2]
    simp [ENNReal.smul_def]
  rw [h3, h]
  refine Measure.ext fun s hs => ?_
  rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

/-- Composition of the multiplication homeomorphisms. -/
theorem mulHomeo_mul (u v : Afˣ) (x : Af) :
    mulHomeo (u * v) x = mulHomeo u (mulHomeo v x) := by
  simp only [mulHomeo_apply, Units.val_mul, mul_assoc]

theorem finNorm_nonneg (u : Afˣ) : 0 ≤ finNorm u :=
  finprod_induction (fun x : ℝ => 0 ≤ x) zero_le_one (fun _ _ ha hb => mul_nonneg ha hb)
    (fun v => norm_nonneg _)

/-- The statement to be proved for each finite idele. -/
def FinScaling (u : Afˣ) : Prop :=
  haar.map (mulHomeo u) = ENNReal.ofReal (finNorm u)⁻¹ • haar

theorem finScaling_mul {u v : Afˣ} (hu : FinScaling u) (hv : FinScaling v) :
    FinScaling (u * v) := by
  unfold FinScaling at *
  have e : (⇑(mulHomeo (u * v)) : Af → Af) = (mulHomeo u) ∘ (mulHomeo v) :=
    funext fun x => mulHomeo_mul u v x
  rw [e, ← Measure.map_map (mulHomeo u).continuous.measurable (mulHomeo v).continuous.measurable,
    hv, Measure.map_smul, hu, smul_smul, finNorm_mul, mul_inv, ENNReal.ofReal_mul (inv_nonneg.2 (finNorm_nonneg u)), mul_comm]

/-- Units of `∏ ℤ_p` preserve `∏ ℤ_p`. -/
theorem finScaling_of_mem_unitBall {w : Afˣ} (hw : w ∈ unitBall.units) : FinScaling w := by
  have hpre : (mulHomeo w) ⁻¹' integralAdeles = integralAdeles := by
    ext x
    have hn := lnorm_of_mem_units hw
    show (w : Af) * x ∈ integralAdeles ↔ x ∈ integralAdeles
    constructor
    · intro h v
      have h1 := (mem_integers_iff v _).1 (h v)
      rw [show ((w : Af) * x) v = (w : Af) v * x v from rfl, lnorm_mul, hn v, one_mul] at h1
      exact (mem_integers_iff v _).2 h1
    · intro h v
      have h1 := (mem_integers_iff v _).1 (h v)
      refine (mem_integers_iff v _).2 ?_
      rw [show ((w : Af) * x) v = (w : Af) v * x v from rfl, lnorm_mul, hn v, one_mul]
      exact h1
  unfold FinScaling
  rw [map_haar_mulHomeo, hpre, haar_integralAdeles, finNorm_eq_one (lnorm_of_mem_units hw),
    inv_one, ENNReal.ofReal_one, one_smul]

/-- A positive natural number as a finite idele. -/
noncomputable def natUnit (N : ℕ) (hN : N ≠ 0) : Afˣ :=
  FiniteAdeleRing.unitEmbedding ℤ ℚ (Units.mk0 (N : ℚ) (by exact_mod_cast hN))

theorem natUnit_val (N : ℕ) (hN : N ≠ 0) : (natUnit N hN : Af) = (N : Af) := by
  show algebraMap ℚ Af (N : ℚ) = (N : Af)
  exact map_natCast _ N

theorem finScaling_natUnit (N : ℕ) (hN : N ≠ 0) : FinScaling (natUnit N hN) := by
  have hpre : (mulHomeo (natUnit N hN)) ⁻¹' integralAdeles = integralDivNat N := by
    ext x
    show (natUnit N hN : Af) * x ∈ integralAdeles ↔ (N : Af) * x ∈ integralAdeles
    rw [natUnit_val]
  have hnorm : finNorm (natUnit N hN) = (N : ℝ)⁻¹ := by
    unfold natUnit
    rw [finNorm_rat]
    simp [abs_of_nonneg]
  unfold FinScaling
  rw [map_haar_mulHomeo, hpre, haar_integralDivNat hN, hnorm, inv_inv, ENNReal.ofReal_natCast]

/-- The inverse of a positive natural number as a finite idele. -/
noncomputable def natInvUnit (N : ℕ) (hN : N ≠ 0) : Afˣ :=
  FiniteAdeleRing.unitEmbedding ℤ ℚ (Units.mk0 ((N : ℚ)⁻¹) (by simpa using hN))

theorem finScaling_natInvUnit (N : ℕ) (hN : N ≠ 0) : FinScaling (natInvUnit N hN) := by
  have hpre : (mulHomeo (natInvUnit N hN)) ⁻¹' integralAdeles = natMulIntegral N := rfl
  have hnorm : finNorm (natInvUnit N hN) = (N : ℝ) := by
    unfold natInvUnit
    rw [finNorm_rat]
    simp [abs_of_nonneg]
  unfold FinScaling
  rw [map_haar_mulHomeo, hpre, haar_natMulIntegral hN, hnorm]
  congr 1
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast]

/-- Positive rational finite ideles. -/
theorem finScaling_rat (r : ℚ) (hr : 0 < r) :
    FinScaling (FiniteAdeleRing.unitEmbedding ℤ ℚ (Units.mk0 r hr.ne')) := by
  have hnum : 0 < r.num := Rat.num_pos.2 hr
  have hden : r.den ≠ 0 := r.den_nz
  have hN : r.num.natAbs ≠ 0 := by omega
  have e : Units.mk0 r hr.ne' = Units.mk0 ((r.num.natAbs : ℕ) : ℚ) (by exact_mod_cast hN) *
      Units.mk0 (((r.den : ℕ) : ℚ)⁻¹) (by simpa using hden) := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_mk0]
    have h1 : ((r.num.natAbs : ℕ) : ℚ) = (r.num : ℚ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hnum)]
    rw [h1, ← div_eq_mul_inv, Rat.num_div_den]
  rw [e, map_mul]
  exact finScaling_mul (finScaling_natUnit _ hN) (finScaling_natInvUnit _ hden)

/-- **Scaling law on the finite adeles**: `haar.map (u * ·) = (∏_p |u_p|_p)⁻¹ • haar`. -/
theorem haar_scaling_fin (u : Afˣ) : FinScaling u := by
  obtain ⟨r, hr, hn⟩ := exists_rat_norm u
  set q : Afˣ := FiniteAdeleRing.unitEmbedding ℤ ℚ (Units.mk0 r hr.ne') with hq
  set w : Afˣ := u * q⁻¹ with hw
  have hu : ∀ v, lnorm v ((w : Af) v) = 1 := by
    intro v
    rw [show (w : Af) v = (u : Af) v * (((q⁻¹ : Afˣ)) : Af) v from rfl, hq, ← map_inv,
      unitEmbedding_apply, lnorm_mul, lnorm_algebraMap, ← hn v]
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0, Rat.cast_inv, norm_inv]
    exact mul_inv_cancel₀ (by rw [ne_eq, norm_eq_zero, Rat.cast_eq_zero]; exact hr.ne')
  have e : u = q * w := by simp [hw]
  rw [e]
  exact finScaling_mul (finScaling_rat r hr) (finScaling_of_mem_unitBall (mem_units_of_lnorm hu))

/-- **The scaling law of the adelic Haar measure**: `HaarScaling`. -/
theorem haarScaling : HaarScaling := by
  intro a
  have hmul : (fun x : AQ => ideleToAdele a * x) =
      Prod.map (fun t : ℝ => (a.1 : ℝ) * t) (fun b : Af => (a.2 : Af) * b) := by
    funext x; ext <;> rfl
  have ha1 : (a.1 : ℝ) ≠ 0 := a.1.ne_zero
  have hR : (volume : Measure ℝ).map (fun t : ℝ => (a.1 : ℝ) * t) =
      ENNReal.ofReal |(a.1 : ℝ)⁻¹| • volume := Real.map_volume_mul_left ha1
  have hF : haar.map (fun b : Af => (a.2 : Af) * b) =
      ENNReal.ofReal (finNorm a.2)⁻¹ • haar := haar_scaling_fin a.2
  unfold adeleHaar
  have hf : Measurable (fun t : ℝ => (a.1 : ℝ) * t) := measurable_const_mul _
  have hg : Measurable (fun b : Af => (a.2 : Af) * b) := (mulHomeo a.2).continuous.measurable
  rw [hmul, ← Measure.map_prod_map (volume : Measure ℝ) haar hf hg, hR, hF,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  congr 1
  show _ = ENNReal.ofReal (|(a.1 : ℝ)| * finNorm a.2)⁻¹
  rw [mul_inv, ENNReal.ofReal_mul (inv_nonneg.2 (abs_nonneg _)), abs_inv, mul_comm]

end GlobalTate.Poisson
