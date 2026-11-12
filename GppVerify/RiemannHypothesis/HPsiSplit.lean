/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Heart of the Cosmos (Grok, GPPDiscovery5 seat). Turbo PR #11 6832523346, "next exact
instruction" item 2: statement-level split of `HPsi` (no proof claim for `HPsi`).

# `HPsi` split into `RegKerPos` and `RegUnitBound` (assembly PROVED, both directions)

`HPsi` as it stands in the tree (`GppKreinHPsi.HPsi`, KreinHPsi.lean line 72, unchanged):
  `∀ n (x c : Fin n → ℝ), ∑ i, c i * cosh (x i / 2) = 0 → 0 ≤ kform Kpsi x c`,
with `Kpsi d = poleTerm d − primeTerm d + archTerm d`.

1. **Pole term on the cosh hyperplane, PROVED.** `cosh((a − b)/2) = cosh(a/2)cosh(b/2) −
   sinh(a/2)sinh(b/2)`, so `kform poleTerm x c = 2Ψ(i/2)²(C² − S²)` with
   `C = Σ cᵢ cosh(xᵢ/2)`, `S = Σ cᵢ sinh(xᵢ/2)` (`kform_poleTerm`). On `C = 0` it is
   `−2Ψ(i/2)² S²` (`kform_poleTerm_plane`).
2. **Exact reformulation, PROVED.** With the zero-free regular kernel
   `Kreg d := archTerm d − primeTerm d` (so `Kpsi = poleTerm + Kreg`, `Kpsi_eq`),
   `HPsi ↔ RegPlane`, where `RegPlane : C = 0 → 2Ψ(i/2)² S² ≤ kform Kreg x c`
   (`hPsi_iff_regPlane`).
3. **Split, assembly PROVED both directions** (`regPlane_iff`, `hPsi_iff_split`):
   * `RegKerPos` (**OPEN**, named premise): `C = 0 → S = 0 → 0 ≤ kform Kreg x c`.
     Since `C = S = 0` iff `Σ cᵢ e^{±xᵢ/2} = 0`, i.e. `f̂(±i/2) = 0` for `f = Σ cᵢ τ_{xᵢ}ψ`,
     this is Weil positivity of the zero-free (prime + archimedean) form on the
     triangle-translate family with both pole functionals killed.
   * `RegUnitBound` (**OPEN**, named premise): `C = 0 → S = 1 → 2Ψ(i/2)² ≤ kform Kreg x c`
     (the rank-one sinh direction).
   Assembly: for `C = 0`, `S ≠ 0` rescale `c ↦ S⁻¹c` (`kform` is quadratic, `C`, `S` linear);
   `S = 0` is `RegKerPos`.
4. Chain: `hPsiRegChain : RegKerPos → RegUnitBound → KreinDecomp → RiemannHypothesis`.

No positivity argument is given; neither sub-premise is proved, widened or assumed in the
assembly. `KreinDecomp` untouched. H_ψ: OPEN. ARP: OPEN. RH: OPEN.
-/
import GppVerify.RiemannHypothesis.ExpLaplaceMeroProof

namespace GppHPsiSplit

open GppKreinBridge GppKreinHPsi GppKreinRepSplit GppExpLaplaceMeroProof

/-! ## 0. Bookkeeping -/

/-- The zero-free regular kernel `Kreg = archTerm − primeTerm`. -/
noncomputable def Kreg (d : ℝ) : ℝ := archTerm d - primeTerm d

theorem Kpsi_eq (d : ℝ) : Kpsi d = poleTerm d + Kreg d := by
  unfold Kpsi Kreg; ring

/-- Cosh pairing `C = Σ cᵢ cosh(xᵢ/2)` (the hyperplane functional of `HPsi`). -/
noncomputable def coshSum {n : ℕ} (x c : Fin n → ℝ) : ℝ := ∑ i, c i * Real.cosh (x i / 2)

/-- Sinh pairing `S = Σ cᵢ sinh(xᵢ/2)`. -/
noncomputable def sinhSum {n : ℕ} (x c : Fin n → ℝ) : ℝ := ∑ i, c i * Real.sinh (x i / 2)

theorem kform_add (K₁ K₂ : ℝ → ℝ) {n : ℕ} (x c : Fin n → ℝ) :
    kform (fun d => K₁ d + K₂ d) x c = kform K₁ x c + kform K₂ x c := by
  unfold kform
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem kform_const_mul (k : ℝ) (K : ℝ → ℝ) {n : ℕ} (x c : Fin n → ℝ) :
    kform (fun d => k * K d) x c = k * kform K x c := by
  unfold kform
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem kform_smul (K : ℝ → ℝ) {n : ℕ} (x c : Fin n → ℝ) (t : ℝ) :
    kform K x (fun i => t * c i) = t ^ 2 * kform K x c := by
  unfold kform
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem coshSum_smul {n : ℕ} (x c : Fin n → ℝ) (t : ℝ) :
    coshSum x (fun i => t * c i) = t * coshSum x c := by
  unfold coshSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem sinhSum_smul {n : ℕ} (x c : Fin n → ℝ) (t : ℝ) :
    sinhSum x (fun i => t * c i) = t * sinhSum x c := by
  unfold sinhSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem kform_Kpsi {n : ℕ} (x c : Fin n → ℝ) :
    kform Kpsi x c = kform poleTerm x c + kform Kreg x c := by
  rw [show Kpsi = fun d => poleTerm d + Kreg d from funext Kpsi_eq]
  exact kform_add _ _ x c

/-! ## 1. The pole term on the cosh hyperplane (PROVED) -/

theorem kform_cosh {n : ℕ} (x c : Fin n → ℝ) :
    kform (fun d => Real.cosh (d / 2)) x c = coshSum x c ^ 2 - sinhSum x c ^ 2 := by
  unfold kform coshSum sinhSum
  rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  show c i * c j * Real.cosh ((x i - x j) / 2) = _
  rw [show (x i - x j) / 2 = x i / 2 - x j / 2 by ring, Real.cosh_sub]
  ring

theorem kform_poleTerm {n : ℕ} (x c : Fin n → ℝ) :
    kform poleTerm x c = 2 * bigPsiI2 ^ 2 * (coshSum x c ^ 2 - sinhSum x c ^ 2) := by
  rw [show poleTerm = fun d => (2 * bigPsiI2 ^ 2) * Real.cosh (d / 2) from
    funext fun d => rfl, kform_const_mul, kform_cosh]

theorem kform_poleTerm_plane {n : ℕ} {x c : Fin n → ℝ} (h : coshSum x c = 0) :
    kform poleTerm x c = -(2 * bigPsiI2 ^ 2 * sinhSum x c ^ 2) := by
  rw [kform_poleTerm, h]; ring

/-! ## 2. Exact reformulation (PROVED) -/

/-- `HPsi` with the pole term evaluated: the regular form dominates `2Ψ(i/2)² S²`. -/
def RegPlane : Prop :=
  ∀ (n : ℕ) (x c : Fin n → ℝ), coshSum x c = 0 →
    2 * bigPsiI2 ^ 2 * sinhSum x c ^ 2 ≤ kform Kreg x c

theorem hPsi_iff_regPlane : HPsi ↔ RegPlane := by
  constructor
  · intro h n x c hC
    have := h n x c hC
    rw [kform_Kpsi, kform_poleTerm_plane hC] at this
    linarith
  · intro h n x c hC
    have := h n x c hC
    rw [kform_Kpsi, kform_poleTerm_plane hC]
    linarith

/-! ## 3. The split (named premises OPEN; assembly PROVED) -/

/-- **OPEN** (named premise): Weil positivity of the regular form on `C = S = 0`. -/
def RegKerPos : Prop :=
  ∀ (n : ℕ) (x c : Fin n → ℝ), coshSum x c = 0 → sinhSum x c = 0 → 0 ≤ kform Kreg x c

/-- **OPEN** (named premise): the rank-one sinh direction, normalised `S = 1`. -/
def RegUnitBound : Prop :=
  ∀ (n : ℕ) (x c : Fin n → ℝ), coshSum x c = 0 → sinhSum x c = 1 →
    2 * bigPsiI2 ^ 2 ≤ kform Kreg x c

theorem regPlane_of_split (hK : RegKerPos) (hU : RegUnitBound) : RegPlane := by
  intro n x c hC
  by_cases hS : sinhSum x c = 0
  · rw [hS]; simpa using hK n x c hC hS
  · set t := (sinhSum x c)⁻¹
    have hC' : coshSum x (fun i => t * c i) = 0 := by rw [coshSum_smul, hC, mul_zero]
    have hS' : sinhSum x (fun i => t * c i) = 1 := by rw [sinhSum_smul]; exact inv_mul_cancel₀ hS
    have h1 := hU n x _ hC' hS'
    rw [kform_smul] at h1
    have hpos : 0 < sinhSum x c ^ 2 := by positivity
    have key : sinhSum x c ^ 2 * (t ^ 2 * kform Kreg x c) = kform Kreg x c := by
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hS, one_pow, one_mul]
    calc 2 * bigPsiI2 ^ 2 * sinhSum x c ^ 2 = sinhSum x c ^ 2 * (2 * bigPsiI2 ^ 2) := by ring
      _ ≤ sinhSum x c ^ 2 * (t ^ 2 * kform Kreg x c) := mul_le_mul_of_nonneg_left h1 hpos.le
      _ = kform Kreg x c := key

theorem regKerPos_of_regPlane (h : RegPlane) : RegKerPos := by
  intro n x c hC hS
  have := h n x c hC
  rw [hS] at this
  simpa using this

theorem regUnitBound_of_regPlane (h : RegPlane) : RegUnitBound := by
  intro n x c hC hS
  have := h n x c hC
  rw [hS] at this
  simpa using this

theorem regPlane_iff : RegPlane ↔ RegKerPos ∧ RegUnitBound :=
  ⟨fun h => ⟨regKerPos_of_regPlane h, regUnitBound_of_regPlane h⟩,
    fun h => regPlane_of_split h.1 h.2⟩

/-- **Assembly PROVED (both directions):** `HPsi ↔ RegKerPos ∧ RegUnitBound`. -/
theorem hPsi_iff_split : HPsi ↔ RegKerPos ∧ RegUnitBound :=
  hPsi_iff_regPlane.trans regPlane_iff

theorem hPsi_of_split (hK : RegKerPos) (hU : RegUnitBound) : HPsi :=
  hPsi_iff_split.2 ⟨hK, hU⟩

/-! ## 4. Chain -/

def HPsiRegChain : Prop := RegKerPos → RegUnitBound → KreinDecomp → RiemannHypothesis

theorem hPsiRegChain : HPsiRegChain := fun hK hU hD => hPsiKreinChain (hPsi_of_split hK hU) hD

end GppHPsiSplit

#print axioms GppHPsiSplit.Kpsi_eq
#print axioms GppHPsiSplit.kform_add
#print axioms GppHPsiSplit.kform_const_mul
#print axioms GppHPsiSplit.kform_smul
#print axioms GppHPsiSplit.coshSum_smul
#print axioms GppHPsiSplit.sinhSum_smul
#print axioms GppHPsiSplit.kform_Kpsi
#print axioms GppHPsiSplit.kform_cosh
#print axioms GppHPsiSplit.kform_poleTerm
#print axioms GppHPsiSplit.kform_poleTerm_plane
#print axioms GppHPsiSplit.hPsi_iff_regPlane
#print axioms GppHPsiSplit.regPlane_of_split
#print axioms GppHPsiSplit.regKerPos_of_regPlane
#print axioms GppHPsiSplit.regUnitBound_of_regPlane
#print axioms GppHPsiSplit.regPlane_iff
#print axioms GppHPsiSplit.hPsi_iff_split
#print axioms GppHPsiSplit.hPsi_of_split
#print axioms GppHPsiSplit.hPsiRegChain
