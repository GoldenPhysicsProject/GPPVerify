import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Bost–Connes `ax+b` midpoint algebra: the exact finite pieces

Source: Codex, GPPDiscovery2 `research/2026-09-28_bost_connes_axb_midpoint_gram.md`, §§4, 5, 7.

* `torsion_average` (§4): the range projection `P_n = μ_n μ_n^* = (1/n) Σ_{nδ=0} e(δ)` acts on the
  additive character of index `k` as the divisibility indicator:
  `(1/n) Σ_{m ∈ ℤ/n} e(km/n) = 1_{n ∣ k}`.
* `midpoint_two_point` (§5): for an algebra with a linear functional `ω` and isometry-like
  elements `μ_n` with `ω(μ_m^* μ_n) = δ_{mn}`, the current `J_N = Σ_{n ≤ N} √Λ(n) μ_n` has
  midpoint two-point function `Σ_{n ≤ N} Λ(n) e^{(iu − ½) log n}`, i.e.
  `Σ Λ(n) n^{-1/2} e^{iu log n}` (`half_shift`): the critical finite-place explicit-formula current.
  The modular flow enters only through `σ_z(μ_n) = n^{iz} μ_n` evaluated at `z = u + i/2`.
* `jump_energy` (§7): for a norm-preserving family `T_n` on a Hilbert space,
  `Σ_n c_n ‖f − T_n f‖² = 2 Σ_n c_n (‖f‖² − Re⟨f, T_n f⟩)`, the positive Dirichlet/jump norm
  built from the channel weights.

## Checks and scope

All three claims check. **Not formalized:** the Bost–Connes `C*`-algebra itself, its KMS states
(`ω_β(e(a/b))`), the ordered-basis Gram matrices `⟨A_{m,r}, A_{n,s}⟩_mid`, and the §6
"variable mismatch" discussion (a comparison of two expressions, not a theorem). The abstract
two-point statement assumes the orthonormality `ω(μ_m^* μ_n) = δ_{mn}` as a hypothesis, which is
what the note derives from the relations. No RH claim.
-/

open Complex

namespace GppBostConnesKms

/-! ### The range projection as an additive average -/

/-- **`P_n` acts as the divisibility indicator on the additive character of index `k`.** -/
theorem torsion_average (n : ℕ) [NeZero n] (k : ℤ) :
    (n : ℂ)⁻¹ * ∑ m : ZMod n, ZMod.stdAddChar (m * (k : ZMod n)) =
      if (n : ℤ) ∣ k then 1 else 0 := by
  have h := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod n) ℂ)) (k : ZMod n)
    (ZMod.isPrimitive_stdAddChar n)
  rw [h]
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  by_cases hk : (n : ℤ) ∣ k
  · have : (k : ZMod n) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd k n).mpr hk
    simp [this, hk, ZMod.card, hn]
  · have : (k : ZMod n) ≠ 0 := fun h => hk ((ZMod.intCast_zmod_eq_zero_iff_dvd k n).mp h)
    simp [this, hk]

/-! ### The KMS midpoint two-point function of the prime current -/

section TwoPoint

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]

/-- `n^{i z}` for the modular flow evaluated at complex time `z`. -/
noncomputable def modFactor (z : ℂ) (n : ℕ) : ℂ := Complex.exp (I * z * (Real.log n : ℂ))

/-- At `z = u + i/2` the modular factor is `n^{-1/2} e^{i u log n}`. -/
theorem half_shift (u : ℝ) (n : ℕ) :
    modFactor ((u : ℂ) + I / 2) n =
      Complex.exp (-(Real.log n : ℂ) / 2) * Complex.exp (I * u * (Real.log n : ℂ)) := by
  rw [modFactor, ← Complex.exp_add]
  congr 1
  have : I * (I / 2) = -1 / 2 := by
    rw [show I * (I / 2) = I * I / 2 by ring, I_mul_I]
  linear_combination (Real.log n : ℂ) * this

/-- **Midpoint two-point function of the prime current.** If `ω(μ_m^* μ_n) = δ_{mn}`, then
`ω(J_N^* σ_{u+i/2}(J_N)) = Σ_{n ≤ N} Λ(n) · modFactor_{u+i/2}(n)`. -/
theorem midpoint_two_point (ω : R →ₗ[ℂ] ℂ) (μ : ℕ → R)
    (hω : ∀ m n, ω (star (μ m) * μ n) = if m = n then 1 else 0) (N : ℕ) (u : ℝ) :
    ω (star (∑ m ∈ Finset.range (N + 1),
          ((Real.sqrt (ArithmeticFunction.vonMangoldt m) : ℝ) : ℂ) • μ m) *
        ∑ n ∈ Finset.range (N + 1),
          (((Real.sqrt (ArithmeticFunction.vonMangoldt n) : ℝ) : ℂ) *
              modFactor ((u : ℂ) + I / 2) n) • μ n) =
      ∑ n ∈ Finset.range (N + 1),
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * modFactor ((u : ℂ) + I / 2) n := by
  rw [star_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum, map_sum]
  simp only [star_smul, smul_mul_smul_comm, map_smul, hω, smul_eq_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.sum_eq_single m (fun b _ hb => by simp [Ne.symm hb]) (fun h => absurd hm h)]
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt m := ArithmeticFunction.vonMangoldt_nonneg
  simp only [if_true, mul_one]
  have hs : ((Real.sqrt (ArithmeticFunction.vonMangoldt m) : ℝ) : ℂ) *
      ((Real.sqrt (ArithmeticFunction.vonMangoldt m) : ℝ) : ℂ) =
      ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hΛ]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [← hs]
  ring

end TwoPoint

/-! ### The jump energy -/

/-- **Jump-energy identity.** For norm-preserving `T_n`, the weighted sum of
`‖f − T_n f‖²` equals `2 Σ c_n (‖f‖² − Re⟨f, T_n f⟩)`. -/
theorem jump_energy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}
    (S : Finset ι) (c : ι → ℝ) (T : ι → E → E) (f : E) (hT : ∀ i, ‖T i f‖ = ‖f‖) :
    ∑ i ∈ S, c i * ‖f - T i f‖ ^ 2 =
      2 * ∑ i ∈ S, c i * (‖f‖ ^ 2 - (inner ℂ f (T i f)).re) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_sub_sq (𝕜 := ℂ), hT i, RCLike.re_to_complex]
  ring

end GppBostConnesKms
