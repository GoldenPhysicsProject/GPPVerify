import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Spectral orbitals: the per-zero Gram object and the finite-sector ledger

Source: Turbo's audits of the SpectralOrbitals blueprint (GPP-bridge
`MuseResearch/turbo-note-2026-11-07-spectral-orbitals-blueprint-audit*.md`, revisions 1–3)
and the K = 5 spectral / augmented-span notes of 2026-11-07.

Two independent pieces, both elementary and both stated without numerical constants:

* **The per-zero object, shape-exact.** The pipeline's amplitude is a vector over the
  signed basis `Fin K ⊕ Fin K`,
  `Aval (inl j) s = exp((s-1/2) a_j) S(s-1/2)`, `Aval (inr j) s = exp(-(s-1/2) a_j) S(-(s-1/2))`,
  with `a_j = 0.35 + 0.7 j`, `S z = Ec z / 2 - (Ec (z + 2πi) + Ec (z - 2πi)) / 4` and
  `Ec z = (e^z - 1)/z` (defined here by its power series, so `Ec 0 = 1`). The per-zero
  matrix is the outer product `Z_ik = 2 Re[A_i conj(A_k)]`. We prove `Ec` agrees with
  `(e^z - 1)/z` off `0`, that `Z` is symmetric, and that its quadratic form is
  `2 |∑ c_i A_i|²`, so every per-zero piece (and every finite sum of them) is positive
  semidefinite of rank ≤ 2.
* **The finite-sector ledger.** With the sector explicit formula
  `arch - prime = ∑_γ orb γ - pole` as a *premise field* and the pole vector in a pole
  subspace `W`, the projection onto `Uᗮ` (for any `U ⊇ W` that also contains the orbitals
  of a chosen zero set `S`) of `arch - prime` equals the sum of the projected orbitals over
  the remaining zeros. `S = ∅` is the pole-only statement; `S = {γ₁}`, `{γ₁, γ₂}` are the
  augmented spans of the K = 5 note.

**Scope.** Nothing here proves the explicit formula; it is a hypothesis field of
`ExplicitFormulaLedger`, to be discharged by the assembled explicit formula (stages E3–E6).
No continuum tail is claimed. The numerical agreements reported by Turbo (cosines,
residue ratios) are not asserted. This is not a positivity source and says nothing about
the Riemann Hypothesis, which remains open.

Daniel Toupin / Golden Physics Project, with AI assistance from Claude Code; the object's
shape is Turbo's audit.
-/

namespace GppSpectralOrbitals

open Complex

open scoped Nat ComplexConjugate

/-! ## The kernel `Ec z = (e^z - 1)/z`, by its power series -/

/-- `Ec z = ∑ zⁿ/(n+1)!`, the entire function equal to `(e^z - 1)/z` off `0`. -/
noncomputable def Ec (z : ℂ) : ℂ := ∑' n : ℕ, z ^ n / ((n + 1)! : ℂ)

lemma summable_Ec (z : ℂ) : Summable fun n : ℕ => z ^ n / ((n + 1)! : ℂ) := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => ‖z‖ ^ n / (n ! : ℝ))
    (Real.summable_pow_div_factorial ‖z‖) fun n => ?_
  rw [norm_div, norm_pow, Complex.norm_natCast]
  gcongr
  omega

lemma Ec_zero : Ec 0 = 1 := by
  rw [Ec, tsum_eq_single 0 fun n hn => by simp [zero_pow hn]]
  simp

/-- The defining identity: `z * Ec z = exp z - 1`. -/
lemma mul_Ec (z : ℂ) : z * Ec z = exp z - 1 := by
  have hs : Summable fun n : ℕ => z ^ n / (n ! : ℂ) := by
    simpa using NormedSpace.expSeries_div_summable z
  have hexp : exp z = ∑' n : ℕ, z ^ n / (n ! : ℂ) := by
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  rw [hexp, hs.tsum_eq_zero_add, Ec, ← tsum_mul_left]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, add_sub_cancel_left]
  refine tsum_congr fun n => ?_
  rw [pow_succ']
  ring

lemma Ec_eq_div {z : ℂ} (hz : z ≠ 0) : Ec z = (exp z - 1) / z := by
  rw [← mul_Ec, mul_div_cancel_left₀ _ hz]

/-! ## The amplitude vector on the signed basis -/

/-- The pipeline's window kernel `S z = Ec z / 2 - (Ec (z + 2πi) + Ec (z - 2πi)) / 4`. -/
noncomputable def Sfun (z : ℂ) : ℂ :=
  Ec z / 2 - (Ec (z + 2 * (Real.pi : ℂ) * I) + Ec (z - 2 * (Real.pi : ℂ) * I)) / 4

/-- The basis exponents `a_j = 0.35 + 0.7 j` (wave 229/232 conventions). -/
noncomputable def a {K : ℕ} (j : Fin K) : ℝ := 0.35 + 0.7 * (j : ℝ)

/-- The amplitude over the signed basis `[+0..+(K-1), -0..-(K-1)]`. -/
noncomputable def Aval {K : ℕ} : Fin K ⊕ Fin K → ℂ → ℂ
  | Sum.inl j, s => exp ((s - 1 / 2) * (a j : ℂ)) * Sfun (s - 1 / 2)
  | Sum.inr j, s => exp (-(s - 1 / 2) * (a j : ℂ)) * Sfun (-(s - 1 / 2))

/-- The point `ρ = 1/2 + iγ` on the critical line. -/
noncomputable def rho (γ : ℝ) : ℂ := 1 / 2 + γ * I

/-- The per-zero matrix: the outer product `Z_ik = 2 Re[A_i(ρ) conj(A_k(ρ))]`. -/
noncomputable def Zgamma (K : ℕ) (γ : ℝ) : Matrix (Fin K ⊕ Fin K) (Fin K ⊕ Fin K) ℝ :=
  fun i k => 2 * (Aval i (rho γ) * conj (Aval k (rho γ))).re

/-- The `Q` block: `(+,+)` index restriction. -/
noncomputable def Qblock (K : ℕ) (γ : ℝ) : Matrix (Fin K) (Fin K) ℝ :=
  fun i k => Zgamma K γ (Sum.inl i) (Sum.inl k)

/-- The `C` block: `(+,-)` index restriction. -/
noncomputable def Cblock (K : ℕ) (γ : ℝ) : Matrix (Fin K) (Fin K) ℝ :=
  fun i k => Zgamma K γ (Sum.inl i) (Sum.inr k)

/-- The parity blocks `P± = Q ± C`. -/
noncomputable def Pplus (K : ℕ) (γ : ℝ) : Matrix (Fin K) (Fin K) ℝ := Qblock K γ + Cblock K γ

/-- The parity blocks `P± = Q ± C`. -/
noncomputable def Pminus (K : ℕ) (γ : ℝ) : Matrix (Fin K) (Fin K) ℝ := Qblock K γ - Cblock K γ

lemma re_mul_conj_comm (x y : ℂ) : (x * conj y).re = (y * conj x).re := by
  simp only [mul_re, conj_re, conj_im]
  ring

/-- The per-zero matrix is symmetric. -/
theorem Zgamma_symm (K : ℕ) (γ : ℝ) (i k : Fin K ⊕ Fin K) :
    Zgamma K γ i k = Zgamma K γ k i := by
  simp only [Zgamma, re_mul_conj_comm (Aval i (rho γ))]

/-- The quadratic form of a Gram outer product: `cᵀ Z c = 2 |∑ cᵢ Aᵢ|²`. -/
theorem quadForm_outer {ι : Type*} [Fintype ι] (A : ι → ℂ) (c : ι → ℝ) :
    ∑ i, ∑ k, c i * c k * (2 * (A i * conj (A k)).re) =
      2 * Complex.normSq (∑ i, (c i : ℂ) * A i) := by
  have h := Complex.mul_conj (∑ i, (c i : ℂ) * A i)
  have h2 : Complex.normSq (∑ i, (c i : ℂ) * A i) =
      ((∑ i, (c i : ℂ) * A i) * conj (∑ i, (c i : ℂ) * A i)).re := by
    rw [h, Complex.ofReal_re]
  rw [h2, map_sum, Finset.sum_mul_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, Complex.conj_ofReal]
  have : (c i : ℂ) * A i * ((c k : ℂ) * conj (A k)) = ((c i * c k : ℝ) : ℂ) *
      (A i * conj (A k)) := by push_cast; ring
  rw [this, Complex.re_ofReal_mul]
  ring

/-- Every per-zero piece is positive semidefinite: `cᵀ Z(γ) c = 2 |∑ cᵢ Aᵢ(ρ)|² ≥ 0`. -/
theorem Zgamma_quadForm (K : ℕ) (γ : ℝ) (c : Fin K ⊕ Fin K → ℝ) :
    ∑ i, ∑ k, c i * c k * Zgamma K γ i k =
      2 * Complex.normSq (∑ i, (c i : ℂ) * Aval i (rho γ)) :=
  quadForm_outer (fun i => Aval i (rho γ)) c

theorem Zgamma_quadForm_nonneg (K : ℕ) (γ : ℝ) (c : Fin K ⊕ Fin K → ℝ) :
    0 ≤ ∑ i, ∑ k, c i * c k * Zgamma K γ i k := by
  rw [Zgamma_quadForm]
  exact mul_nonneg zero_le_two (Complex.normSq_nonneg _)

/-- A finite sum of per-zero pieces (the spectral block over a finite zero set) is
positive semidefinite. -/
theorem sum_Zgamma_quadForm_nonneg (K : ℕ) (zeros : Finset ℝ) (c : Fin K ⊕ Fin K → ℝ) :
    0 ≤ ∑ i, ∑ k, c i * c k *
      (∑ γ ∈ zeros, Zgamma K γ : Matrix (Fin K ⊕ Fin K) (Fin K ⊕ Fin K) ℝ) i k := by
  have : ∑ i, ∑ k, c i * c k * (∑ γ ∈ zeros, Zgamma K γ : Matrix (Fin K ⊕ Fin K) (Fin K ⊕ Fin K) ℝ) i k =
      ∑ γ ∈ zeros, ∑ i, ∑ k, c i * c k * Zgamma K γ i k := by
    simp only [Matrix.sum_apply, Finset.mul_sum]
    symm
    rw [Finset.sum_comm (s := zeros) (t := (Finset.univ : Finset (Fin K ⊕ Fin K)))]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [this]
  exact Finset.sum_nonneg fun γ _ => Zgamma_quadForm_nonneg K γ c

/-! ## The finite-sector ledger -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- A sector's explicit-formula ledger in the named-premise shape: the blocks are fields,
the pole vector lies in the pole subspace `W`, and the sector explicit formula
`arch - prime = ∑_γ orb γ - pole` is a premise field (not proved here). -/
structure ExplicitFormulaLedger (W : Submodule ℝ V) (ι : Type*) where
  /-- The finite zero set of the sector. -/
  zeros : Finset ι
  /-- The per-zero spectral orbital. -/
  orb : ι → V
  /-- The archimedean block. -/
  arch : V
  /-- The prime block. -/
  prime : V
  /-- The pole block. -/
  pole : V
  /-- The pole block lies in the pole subspace. -/
  pole_mem : pole ∈ W
  /-- The sector explicit formula (premise). -/
  balance_eq : arch - prime = ∑ γ ∈ zeros, orb γ - pole

namespace ExplicitFormulaLedger

variable {W : Submodule ℝ V} {ι : Type*} [DecidableEq ι]

/-- **Augmented-span complement identity.** If `U ⊇ W` also contains the orbitals of the
zeros in `S`, then the `Uᗮ` component of `arch - prime` is exactly the sum of the `Uᗮ`
components of the remaining orbitals. -/
theorem complement_eq_sum_remaining (L : ExplicitFormulaLedger W ι) (U : Submodule ℝ V)
    (hWU : W ≤ U) (S : Finset ι) (hS : ∀ γ ∈ S, L.orb γ ∈ U) :
    Uᗮ.starProjection (L.arch - L.prime) =
      ∑ γ ∈ L.zeros \ S, Uᗮ.starProjection (L.orb γ) := by
  have hzero : ∀ v ∈ U, Uᗮ.starProjection v = 0 := fun v hv =>
    (Uᗮ.starProjection_apply_eq_zero_iff).mpr (Submodule.le_orthogonal_orthogonal U hv)
  rw [L.balance_eq, map_sub, hzero _ (hWU L.pole_mem), sub_zero, map_sum,
    ← Finset.sum_sdiff (Finset.inter_subset_left (s₁ := L.zeros) (s₂ := S)),
    Finset.sdiff_inter_self_left,
    Finset.sum_eq_zero fun γ hγ => hzero _ (hS γ (Finset.mem_inter.mp hγ).2), add_zero]

/-- The pole-only case: the `Wᗮ` component of `arch - prime` is the sum of the `Wᗮ`
components of all orbitals. -/
theorem complement_eq_sum (L : ExplicitFormulaLedger W ι) :
    Wᗮ.starProjection (L.arch - L.prime) = ∑ γ ∈ L.zeros, Wᗮ.starProjection (L.orb γ) := by
  simpa using L.complement_eq_sum_remaining W le_rfl ∅ (by simp)

/-- The complement residue is bounded by the norms of the orbitals left outside the span. -/
theorem norm_complement_le (L : ExplicitFormulaLedger W ι) (U : Submodule ℝ V)
    (hWU : W ≤ U) (S : Finset ι) (hS : ∀ γ ∈ S, L.orb γ ∈ U) :
    ‖Uᗮ.starProjection (L.arch - L.prime)‖ ≤ ∑ γ ∈ L.zeros \ S, ‖L.orb γ‖ := by
  rw [L.complement_eq_sum_remaining U hWU S hS]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun γ _ => ?_)
  exact Submodule.norm_starProjection_apply_le Uᗮ (L.orb γ)

end ExplicitFormulaLedger

/-! ## Linking the ledger to the per-zero parity blocks -/

/-- A `K × K` parity block as a vector of the Euclidean space on pair indices (the `PiLp`
route to the Frobenius inner product). Linear. -/
noncomputable def parityVec (K : ℕ) :
    Matrix (Fin K) (Fin K) ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin K × Fin K) where
  toFun P := (WithLp.linearEquiv 2 ℝ (Fin K × Fin K → ℝ)).symm fun ij => P ij.1 ij.2
  map_add' P Q := by rw [← map_add]; rfl
  map_smul' c P := by rw [← map_smul]; rfl

/-- A ledger on the `K × K` parity channel whose orbitals are the parity blocks of the
per-zero matrices: `blk = Pplus K` or `blk = Pminus K`. The sector explicit formula is still
a premise, stated against the measured block `∑_γ blk γ`. -/
noncomputable def ExplicitFormulaLedger.ofParity (K : ℕ) (blk : ℝ → Matrix (Fin K) (Fin K) ℝ)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin K × Fin K))) (zeros : Finset ℝ)
    (arch prime pole : EuclideanSpace ℝ (Fin K × Fin K)) (hpole : pole ∈ W)
    (hbal : arch - prime = parityVec K (∑ γ ∈ zeros, blk γ) - pole) :
    ExplicitFormulaLedger W ℝ where
  zeros := zeros
  orb γ := parityVec K (blk γ)
  arch := arch
  prime := prime
  pole := pole
  pole_mem := hpole
  balance_eq := by rw [hbal, map_sum]

/-- On the parity channel, the complement of the pole span sees exactly the parity blocks of
the zeros left outside the span. -/
theorem parity_complement_eq_sum (K : ℕ) (blk : ℝ → Matrix (Fin K) (Fin K) ℝ)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin K × Fin K))) (zeros : Finset ℝ)
    (arch prime pole : EuclideanSpace ℝ (Fin K × Fin K)) (hpole : pole ∈ W)
    (hbal : arch - prime = parityVec K (∑ γ ∈ zeros, blk γ) - pole)
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin K × Fin K))) (hWU : W ≤ U) (S : Finset ℝ)
    (hS : ∀ γ ∈ S, parityVec K (blk γ) ∈ U) :
    Uᗮ.starProjection (arch - prime) =
      ∑ γ ∈ zeros \ S, Uᗮ.starProjection (parityVec K (blk γ)) :=
  (ExplicitFormulaLedger.ofParity K blk W zeros arch prime pole hpole hbal).complement_eq_sum_remaining
    U hWU S hS

end GppSpectralOrbitals
