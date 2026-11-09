/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.RiemannHypothesis.AdelicCovolume
import GppVerify.RiemannHypothesis.AdelicCharacter
import GppVerify.RiemannHypothesis.SchwartzTateLocalFE
import Mathlib.Analysis.Fourier.PoissonSummation


/-!
# Adelic Poisson summation: the statement file

Written in-tree on Daniel's decision of 2026-11-09, relayed by Turbo (GPP-bridge PR #11,
6732913698). The spec is the audit trail in that PR: the rev 5 audit (6732755202), the
rejection of revs 6–8 (6732882732), and the build order. The rev 5 sheet text was never
committed to the bridge or the tree, so this file is written from the audits rather than
copied from the sheet.

Everything is stated on the concrete objects: the carrier `AQ = ℝ × 𝔸_f`, the measure
`adeleHaar` (Lebesgue × `Rat.FiniteAdeleRing.haar`, with `covolume_eq_one`), and the
character `adeleChar` (GP-DUAL, `AdelicCharacter.lean`).

## Proved here

* `adeleChar_split`, `adeleChar_real_eq_fourierChar`: `ψ` splits as an archimedean factor
  times a finite factor, and the archimedean factor is Mathlib's `𝐞`, the character
  of Step 3.
* `archimedean_phase_even`, `archimedean_phase_odd`: under the archimedean factor of the
  transform, the Step 3 test vectors `e^{-πx²}` and `x e^{-πx²}` have phases `+1` and `-i`.
  This is the "phases" field, written with `ψ` occurring in it.
* `finChar_integral`: the finite factor is trivial on `∏ ℤ_v`.
* `adelicFourier_pureTensor`: **transform factorization on pure tensors**: the adelic
  transform of `φ ⊗ g` is `𝓕φ ⊗ 𝓕_f g`.
* `tsum_pureTensor_integral`: for `f = φ ⊗ 1_{∏ℤ_v}`, the sum over `ℚ` is the sum over `ℤ`.
* `poissonSummation_pureTensor_integral`: the **ordinary-Poisson control**. For
  `f = φ ⊗ 1_{∏ℤ_v}`, adelic Poisson summation holds and is the classical one, given the
  local fact that `1_{∏ℤ_v}` is its own finite transform (`FinFourierIntegralSelfDual`).
* `boundary_split`: from Poisson summation for `f`, the `q = 0` terms separate off.
* `gp_dual_kernel_collapse`: the forward direction of GP-DUAL.

## Open, stated exactly (named `Prop`s, never assumed as axioms)

* ~~`AdelicPoissonSummation`~~: proved in `AdelicPoissonSummation.lean`
  (`adelicPoissonSummation`); the statement stays here.
* ~~`AdelicFourierInversion`, `AdelicPlancherel`~~: proved in `AdelicFourierInversion.lean`
  (`adelicFourierInversion`, `adelicPlancherel`); the statements stay here.
* ~~`AdelicPoissonScaled`~~, the idele-scaled form (GZ5), through the idele norm `ideleNorm` from
  `IdeleQ` (#510): proved in `AdelicPoissonScaled.lean` (`adelicPoissonScaled`), from
  `adelicPoissonSummation` and `HaarScaling` (`AdelicHaarScaling.lean`, `haarScaling`).
* `FinFourierIntegralSelfDual`: the self-duality of `∏ ℤ_v` for the finite character.
* **GW-EF**, the link from Poisson summation to the Weil form of #520, is OPEN. It is not
  stated here: it belongs to the explicit-formula layer, and no lemma below carries it as
  a hypothesis.

Conventions: the transform has kernel `ψ(-xy)`, so its archimedean factor is Mathlib's `𝓕`
(the convention of Step 3). All sums over `ℚ` and `ℤ` are `tsum`s.
-/

open MeasureTheory IsDedekindDomain GppIdeleQ Complex
open scoped FourierTransform SchwartzMap

namespace GlobalTate.Poisson

/-! ### The character, place by place -/

/-- The archimedean factor of `ψ` is Mathlib's character `𝐞`, the one Step 3 uses. -/
theorem adeleChar_real_eq_fourierChar (t : ℝ) : adeleChar ((t, 0) : AQ) = 𝐞 t := by
  rw [adeleChar_real]; rfl

/-- The finite factor of `ψ`. -/
noncomputable def finChar (a : Af) : Circle := adeleChar ((0 : ℝ), a)

theorem finChar_integral {a : Af} (ha : a ∈ intBox) : finChar a = 1 := adeleChar_integral ha

theorem finChar_add (a b : Af) : finChar (a + b) = finChar a * finChar b := by
  rw [finChar, finChar, finChar, ← AddChar.map_add_eq_mul]
  congr 1
  ext <;> simp

/-- `ψ` splits into its archimedean and finite factors. -/
theorem adeleChar_split (x : ℝ) (a : Af) :
    adeleChar ((x, a) : AQ) = 𝐞 x * finChar a := by
  rw [← adeleChar_real_eq_fourierChar, finChar, ← AddChar.map_add_eq_mul]
  congr 1
  ext <;> simp

/-! ### The Schwartz class and the transform -/

/-- Schwartz–Bruhat functions on the finite adeles: locally constant, compactly supported. -/
def IsSchwartzBruhat (g : Af → ℂ) : Prop := IsLocallyConstant g ∧ HasCompactSupport g

/-- The pure tensor `φ ⊗ g` on `ℝ × 𝔸_f`. -/
noncomputable def pureTensor (φ : 𝓢(ℝ, ℂ)) (g : Af → ℂ) : AQ → ℂ := fun x => φ x.1 * g x.2

/-- The adelic Schwartz class: the span of pure tensors of a Schwartz function at infinity
and a Schwartz–Bruhat function on the finite adeles. -/
def AdelicSchwartz : Submodule ℂ (AQ → ℂ) :=
  Submodule.span ℂ {f | ∃ φ g, IsSchwartzBruhat g ∧ f = pureTensor φ g}

theorem pureTensor_mem {φ : 𝓢(ℝ, ℂ)} {g : Af → ℂ} (hg : IsSchwartzBruhat g) :
    pureTensor φ g ∈ AdelicSchwartz :=
  Submodule.subset_span ⟨φ, g, hg, rfl⟩

/-- The adelic Fourier transform, with kernel `ψ(-xy)` against `adeleHaar`. -/
noncomputable def adelicFourier (f : AQ → ℂ) (y : AQ) : ℂ :=
  ∫ x, (adeleChar (-(x * y)) : ℂ) * f x ∂adeleHaar

/-- The finite-adele Fourier transform, against `Rat.FiniteAdeleRing.haar`. -/
noncomputable def finFourier (g : Af → ℂ) (b : Af) : ℂ :=
  ∫ a, (finChar (-(a * b)) : ℂ) * g a ∂Rat.FiniteAdeleRing.haar

/-- **Transform factorization on pure tensors.** -/
theorem adelicFourier_pureTensor (φ : 𝓢(ℝ, ℂ)) (g : Af → ℂ) (y : ℝ) (b : Af) :
    adelicFourier (pureTensor φ g) ((y, b) : AQ) = 𝓕 (φ : ℝ → ℂ) y * finFourier g b := by
  have key : ∀ x : AQ, (adeleChar (-(x * ((y, b) : AQ))) : ℂ) * pureTensor φ g x =
      ((𝐞 (-(x.1 * y)) : ℂ) * φ x.1) * ((finChar (-(x.2 * b)) : ℂ) * g x.2) := by
    intro x
    have hx : -(x * ((y, b) : AQ)) = ((-(x.1 * y), -(x.2 * b)) : AQ) := by ext <;> simp
    rw [hx, adeleChar_split, pureTensor]
    push_cast
    ring
  unfold adelicFourier adeleHaar
  simp_rw [key]
  rw [integral_prod_mul (fun x : ℝ => (𝐞 (-(x * y)) : ℂ) * φ x)
    (fun a : Af => (finChar (-(a * b)) : ℂ) * g a), Real.fourier_real_eq]
  rfl

/-! ### The archimedean phases of Step 3, through `ψ` -/

/-- The even test vector `e^{-πx²}` has phase `+1` under the archimedean factor of the
transform. -/
theorem archimedean_phase_even (y : ℝ) :
    ∫ x : ℝ, (adeleChar ((-(x * y), 0) : AQ) : ℂ) * cexp (-Real.pi * x ^ 2) =
      cexp (-Real.pi * y ^ 2) := by
  simp_rw [adeleChar_real_eq_fourierChar]
  have h := congrFun (fourier_gaussian_pi (b := 1) (by simp)) y
  rw [Real.fourier_real_eq] at h
  simp only [Circle.smul_def, smul_eq_mul, mul_one, div_one, one_cpow, div_self one_ne_zero,
    one_mul] at h
  exact h

/-- The odd test vector `x e^{-πx²}` has phase `-i` under the archimedean factor of the
transform (Step 3's `fourier_x_gaussian` at `t = 1`). -/
theorem archimedean_phase_odd (y : ℝ) :
    ∫ x : ℝ, (adeleChar ((-(x * y), 0) : AQ) : ℂ) * ((x : ℂ) * cexp (-Real.pi * x ^ 2)) =
      -I * ((y : ℂ) * cexp (-Real.pi * y ^ 2)) := by
  simp_rw [adeleChar_real_eq_fourierChar]
  have h := congrFun (LocalTate.Archimedean.fourier_x_gaussian (t := 1) one_pos) y
  rw [Real.fourier_real_eq] at h
  simp only [Circle.smul_def, smul_eq_mul, Complex.ofReal_one, mul_one, div_one, one_cpow,
    one_div, one_mul] at h
  rw [h]
  ring

/-! ### Open statements -/

/-- Poisson summation for one function: both sums over `ℚ` converge and agree. -/
def PoissonSummationFor (f : AQ → ℂ) : Prop :=
  Summable (fun q : ℚ => f (principal q)) ∧
    Summable (fun q : ℚ => adelicFourier f (principal q)) ∧
      ∑' q : ℚ, f (principal q) = ∑' q : ℚ, adelicFourier f (principal q)

/-- **Adelic Poisson summation** at covolume 1 (`covolume_eq_one`). Proved as
`adelicPoissonSummation` (`AdelicPoissonSummation.lean`). -/
def AdelicPoissonSummation : Prop := ∀ f ∈ AdelicSchwartz, PoissonSummationFor f

/-- Fourier inversion for the self-dual measure `adeleHaar`. Proved as `adelicFourierInversion`
(`AdelicFourierInversion.lean`). -/
def AdelicFourierInversion : Prop :=
  ∀ f ∈ AdelicSchwartz, ∀ x, adelicFourier (adelicFourier f) x = f (-x)

/-- Plancherel for `adeleHaar`. Proved as `adelicPlancherel` (`AdelicFourierInversion.lean`). -/
def AdelicPlancherel : Prop :=
  ∀ f ∈ AdelicSchwartz,
    ∫ x, ‖adelicFourier f x‖ ^ 2 ∂adeleHaar = ∫ x, ‖f x‖ ^ 2 ∂adeleHaar

/-- An idele as an adele. -/
def ideleToAdele (a : Idele) : AQ := ((a.1 : ℝ), (a.2 : Af))

/-- The scaling law of `adeleHaar` under an idele, through the idele norm of `IdeleQ`. Proved as `haarScaling` (`AdelicHaarScaling.lean`). -/
def HaarScaling : Prop :=
  ∀ a : Idele, adeleHaar.map (ideleToAdele a * ·) = ENNReal.ofReal (ideleNorm a)⁻¹ • adeleHaar

/-- **The idele-scaled Poisson summation (GZ5)**:
`∑ f(aq) = |a|⁻¹ ∑ 𝓕f(a⁻¹q)`. Proved as `adelicPoissonScaled`
(`AdelicPoissonScaled.lean`). -/
def AdelicPoissonScaled : Prop :=
  ∀ f ∈ AdelicSchwartz, ∀ a : Idele,
    ∑' q : ℚ, f (ideleToAdele a * principal q) =
      (ideleNorm a)⁻¹ * ∑' q : ℚ, adelicFourier f (ideleToAdele a⁻¹ * principal q)

/-- The indicator of `∏ ℤ_v`. -/
noncomputable def intIndicator : Af → ℂ := intBox.indicator fun _ => 1

/-- `∏ ℤ_v` is self-dual: its indicator is its own finite transform. OPEN (local). -/
def FinFourierIntegralSelfDual : Prop := finFourier intIndicator = intIndicator

/-! ### Consequences proved from the statements -/

/-- The `q = 0` terms separate off. This needs only Poisson summation for `f`; the link
to the Weil form (GW-EF) is a separate, open step. -/
theorem boundary_split {f : AQ → ℂ} (h : PoissonSummationFor f) :
    ∑' q : ℚ, (if q = 0 then 0 else f (principal q)) -
        ∑' q : ℚ, (if q = 0 then 0 else adelicFourier f (principal q)) =
      adelicFourier f 0 - f 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  have e1 := h1.tsum_eq_add_tsum_ite 0
  have e2 := h2.tsum_eq_add_tsum_ite 0
  simp only [map_zero] at e1 e2
  linear_combination -e1 + e2 + h3

/-- **GP-DUAL, forward direction**: an adele on which every principal character is trivial
is principal. -/
theorem gp_dual_kernel_collapse {a : AQ} (h : ∀ q : ℚ, adeleChar (principal q * a) = 1) :
    a ∈ Set.range principal := by
  obtain ⟨r, hr⟩ := (forall_adeleChar_principal_mul_eq_one_iff a).1 h
  exact ⟨r, hr.symm⟩

/-! ### The ordinary-Poisson control -/

/-- A rational is integral at every place exactly when it is an integer. -/
theorem principal_snd_mem_intBox_iff (q : ℚ) :
    (principal q).2 ∈ intBox ↔ q ∈ Set.range ((↑) : ℤ → ℚ) := by
  constructor
  · intro h
    exact ⟨q.num, (eq_num_of_integral q fun v => h v).symm⟩
  · rintro ⟨n, rfl⟩ v
    exact intCast_mem_integers v n

open Classical in
/-- A function `h` on `ℝ`, cut down to rationals integral at every place. -/
theorem integral_cutoff_eq (h : ℝ → ℂ) (q : ℚ) :
    h (principal q).1 * intIndicator (principal q).2 =
      if q ∈ Set.range ((↑) : ℤ → ℚ) then h q else 0 := by
  rw [intIndicator, Set.indicator_apply]
  simp only [principal_snd_mem_intBox_iff]
  split_ifs <;> simp [principal]

theorem support_integral_cutoff (h : ℝ → ℂ) :
    Function.support (fun q : ℚ => h (principal q).1 * intIndicator (principal q).2) ⊆
      Set.range ((↑) : ℤ → ℚ) := by
  intro q hq
  by_contra hn
  exact hq (by show h _ * _ = 0; rw [integral_cutoff_eq, if_neg hn])

open Classical in
theorem integral_cutoff_int (h : ℝ → ℂ) (n : ℤ) :
    h (principal (n : ℚ)).1 * intIndicator (principal (n : ℚ)).2 = h n := by
  rw [integral_cutoff_eq, if_pos ⟨n, rfl⟩]
  simp

/-- The sum over `ℚ` of `h ⊗ 1_{∏ℤ_v}` is the sum of `h` over `ℤ`. -/
theorem tsum_integral_cutoff (h : ℝ → ℂ) :
    ∑' q : ℚ, h (principal q).1 * intIndicator (principal q).2 = ∑' n : ℤ, h n := by
  rw [← (Int.cast_injective (α := ℚ)).tsum_eq (support_integral_cutoff h)]
  simp only [integral_cutoff_int]

theorem summable_integral_cutoff_iff (h : ℝ → ℂ) :
    Summable (fun q : ℚ => h (principal q).1 * intIndicator (principal q).2) ↔
      Summable (fun n : ℤ => h n) := by
  rw [← (Int.cast_injective (α := ℚ)).summable_iff
    (fun q hq => Function.notMem_support.1 fun h' => hq (support_integral_cutoff h h'))]
  simp only [Function.comp_def, integral_cutoff_int]

theorem tsum_pureTensor_integral (φ : 𝓢(ℝ, ℂ)) :
    ∑' q : ℚ, pureTensor φ intIndicator (principal q) = ∑' n : ℤ, φ n :=
  tsum_integral_cutoff φ

/-- Summability of a Schwartz function over the integers. -/
theorem summable_schwartz_int (φ : 𝓢(ℝ, ℂ)) : Summable (fun n : ℤ => φ n) :=
  summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    ((φ.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)

/-- **The ordinary-Poisson control.** For `f = φ ⊗ 1_{∏ℤ_v}`, adelic Poisson summation
holds, and it is the classical Poisson summation `∑ φ(n) = ∑ 𝓕φ(n)` (Mathlib), given that
`∏ ℤ_v` is self-dual. -/
theorem poissonSummation_pureTensor_integral (φ : 𝓢(ℝ, ℂ))
    (hsd : FinFourierIntegralSelfDual) :
    PoissonSummationFor (pureTensor φ intIndicator) := by
  have hF : ∀ q : ℚ, adelicFourier (pureTensor φ intIndicator) (principal q) =
      (𝓕 φ : 𝓢(ℝ, ℂ)) (principal q).1 * intIndicator (principal q).2 := by
    intro q
    rw [show principal q = ((principal q).1, (principal q).2) from rfl,
      adelicFourier_pureTensor, hsd, SchwartzMap.fourier_coe]
  unfold PoissonSummationFor
  simp_rw [hF]
  refine ⟨(summable_integral_cutoff_iff φ).2 (summable_schwartz_int φ),
    (summable_integral_cutoff_iff _).2 (summable_schwartz_int _), ?_⟩
  rw [show (fun q : ℚ => pureTensor φ intIndicator (principal q)) =
      fun q => φ (principal q).1 * intIndicator (principal q).2 from rfl,
    tsum_integral_cutoff, tsum_integral_cutoff]
  have := SchwartzMap.tsum_eq_tsum_fourier φ 0
  simpa [fourier_eval_zero] using this

end GlobalTate.Poisson
