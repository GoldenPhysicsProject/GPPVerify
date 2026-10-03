import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Finite Bost–Connes divisibility projections cannot give a lower frame (two no-gos)

Sources: Codex, bridge `research/codex/2026-09-30_bc_range_projection_no_go.md` and
`research/codex/2026-09-30_bc_fourier_selfdual_no_go.md`.

Work on `ZMod N` in the additive-character *index* basis `k`. The finite analogue of the
Bost–Connes range projection `P_d = μ_d μ_d^*` acts diagonally: `P_d χ_k = 1_{d ∣ k} χ_k`
(`Pproj`). Both notes ask whether a positive combination of such projections can dominate the
identity on the mean-zero sector; both answer no, by exhibiting exact null vectors.

* `H_apply`, `eigenvalue_eq_zero_of_coprime`: for *any* weights `w`, the operator
  `H = Σ_{d ∣ N, d ≥ 2} w_d P_d` is diagonal and kills every index `k` coprime to `N`.
* `vonMangoldt_eigenvalue`: with the weights `Λ(d)` its eigenvalue on `k` is `log gcd(k, N)`
  (from `Σ_{d ∣ m} Λ(d) = log m`); the `Λ(d)/d` weighting also vanishes at coprime `k`.
* `selfDual_frame_annihilates`: for `N = p^K` (with `p ≠ 2` or `K ≥ 2`) the vector
  `f = δ₁ − δ_{1+p^{K−1}}` is killed by every `P_{p^j}` and, because its Fourier transform is
  supported off multiples of `p`, by every `F^{-1} P_{p^j} F` as well; hence by
  `Σ_j w_j (P_{p^j} + F^{-1} P_{p^j} F)` for **every** choice of weights.

## Checks and scope

All claims of both notes check. Two remarks. (1) The notes normalise `F` to be unitary; we use
Mathlib's unnormalised `ZMod.dft` and its inverse, which changes nothing about supports and
null vectors. (2) The note's `p = 2, K = 1` exception is reproduced as the hypothesis
`p ≠ 2 ∨ 2 ≤ K`. This is a statement about the *static* projections only: it does not
invalidate the Bost–Connes / `ax+b` architecture, which must supply the dynamical channels the
notes list, and no RH claim is made.
-/

open scoped ZMod

namespace GppBostConnesNoGo

variable {N : ℕ} [NeZero N]

/-- The finite divisibility projection `P_d χ_k = 1_{d ∣ k} χ_k`, in the index basis. -/
def Pproj (d : ℕ) (f : ZMod N → ℂ) : ZMod N → ℂ := fun k => if d ∣ k.val then f k else 0

/-- The weighted sum of projections over the divisors `d ≥ 2` of `N`. -/
noncomputable def H (w : ℕ → ℝ) (f : ZMod N → ℂ) : ZMod N → ℂ :=
  ∑ d ∈ N.divisors.filter (2 ≤ ·), (w d : ℂ) • Pproj d f

omit [NeZero N] in
/-- `H` is diagonal in the index basis. -/
theorem H_apply (w : ℕ → ℝ) (f : ZMod N → ℂ) (k : ZMod N) :
    H w f k = ((∑ d ∈ N.divisors.filter (2 ≤ ·), if d ∣ k.val then w d else 0 : ℝ) : ℂ) * f k := by
  simp only [H, Finset.sum_apply, Pi.smul_apply, Pproj, smul_eq_mul]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs <;> simp

omit [NeZero N] in
/-- **Coprime indices lie in the kernel**, for every choice of weights. -/
theorem eigenvalue_eq_zero_of_coprime (w : ℕ → ℝ) (k : ZMod N) (hk : Nat.Coprime k.val N) :
    (∑ d ∈ N.divisors.filter (2 ≤ ·), if d ∣ k.val then w d else 0 : ℝ) = 0 := by
  refine Finset.sum_eq_zero fun d hd => ?_
  rw [Finset.mem_filter, Nat.mem_divisors] at hd
  have : ¬ d ∣ k.val := by
    intro h
    have h1 : d ∣ Nat.gcd k.val N := Nat.dvd_gcd h hd.1.1
    rw [hk] at h1
    have := Nat.le_of_dvd one_pos h1
    omega
  simp [this]

omit [NeZero N] in
/-- Consequently `H f` vanishes at every index coprime to `N`. -/
theorem H_apply_eq_zero_of_coprime (w : ℕ → ℝ) (f : ZMod N → ℂ) (k : ZMod N)
    (hk : Nat.Coprime k.val N) : H w f k = 0 := by
  rw [H_apply, eigenvalue_eq_zero_of_coprime w k hk]
  simp

/-- **Exact eigenvalue.** With the von Mangoldt weights the eigenvalue at index `k` is
`log gcd(k, N)`. -/
theorem vonMangoldt_eigenvalue (k : ZMod N) :
    (∑ d ∈ N.divisors.filter (2 ≤ ·),
        if d ∣ k.val then ArithmeticFunction.vonMangoldt d else 0 : ℝ) =
      Real.log (Nat.gcd k.val N) := by
  have hN : N ≠ 0 := NeZero.ne N
  have h1 : (∑ d ∈ N.divisors.filter (2 ≤ ·),
        if d ∣ k.val then ArithmeticFunction.vonMangoldt d else 0 : ℝ) =
      ∑ d ∈ N.divisors, if d ∣ k.val then ArithmeticFunction.vonMangoldt d else 0 := by
    refine Finset.sum_filter_of_ne fun d hd hne => ?_
    by_contra h
    have : d = 1 := by
      have := Nat.pos_of_mem_divisors hd
      omega
    subst this
    simp at hne
  rw [h1, ← Finset.sum_filter]
  have h2 : N.divisors.filter (· ∣ k.val) = (Nat.gcd k.val N).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hdN, _⟩, hdk⟩
      exact ⟨⟨hdk, hdN⟩, Nat.gcd_ne_zero_right hN⟩
    · rintro ⟨⟨hdk, hdN⟩, _⟩
      exact ⟨⟨hdN, hN⟩, hdk⟩
  rw [h2]
  exact ArithmeticFunction.vonMangoldt_sum

omit [NeZero N] in
/-- The `Λ(d)/d`-weighted version also has a coprime kernel (immediate from the general
statement). -/
theorem expectation_weighted_kernel (k : ZMod N) (hk : Nat.Coprime k.val N) (f : ZMod N → ℂ) :
    H (fun d => ArithmeticFunction.vonMangoldt d / d) f k = 0 :=
  H_apply_eq_zero_of_coprime _ f k hk

/-! ### The Fourier-self-dual frame on a prime power -/

section PrimePower

variable (p K : ℕ) [Fact p.Prime]

private theorem pow_pos' : 0 < p ^ K := pow_pos (Fact.out : p.Prime).pos K

instance : NeZero (p ^ K) := ⟨(pow_pos' p K).ne'⟩

/-- The second support point `1 + p^{K-1}`. -/
def bpt : ZMod (p ^ K) := ((1 + p ^ (K - 1) : ℕ) : ZMod (p ^ K))

/-- The null vector `δ₁ − δ_{1 + p^{K-1}}`. -/
noncomputable def nullVec : ZMod (p ^ K) → ℂ := Pi.single 1 1 - Pi.single (bpt p K) 1

variable {p K}

theorem lt_pow_of_hyp (hK : 1 ≤ K) (hp : p ≠ 2 ∨ 2 ≤ K) : 1 + p ^ (K - 1) < p ^ K := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ]
  rcases hp with hp | hm
  · have : 3 ≤ p := by omega
    have : 1 ≤ p ^ m := Nat.one_le_pow _ _ (by omega)
    nlinarith
  · have : 2 ≤ p ^ m := by
      calc 2 ≤ p := hp2
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ m := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith

theorem not_dvd_bpt (hK : 1 ≤ K) (hp : p ≠ 2 ∨ 2 ≤ K) : ¬ p ∣ 1 + p ^ (K - 1) := by
  intro h
  have hp2 := (Fact.out : p.Prime)
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp at h
    have := Nat.le_of_dvd (by norm_num) h
    have := hp2.two_le
    have : p = 2 := by omega
    exact hp.elim (fun h => h this) (fun h => by omega)
  · have : p ∣ p ^ m := dvd_pow_self p (by omega)
    have := (Nat.dvd_add_right this).mp (by rwa [add_comm] at h)
    exact hp2.one_lt.ne' (Nat.dvd_one.mp this)

theorem val_one (hK : 1 ≤ K) : (1 : ZMod (p ^ K)).val = 1 := by
  have h : 1 < p ^ K := by
    calc 1 < p := (Fact.out : p.Prime).one_lt
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ K := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hK
  rw [← Nat.cast_one, ZMod.val_natCast, Nat.mod_eq_of_lt h]

theorem val_bpt (hK : 1 ≤ K) (hp : p ≠ 2 ∨ 2 ≤ K) : (bpt p K).val = 1 + p ^ (K - 1) := by
  rw [bpt, ZMod.val_natCast, Nat.mod_eq_of_lt (lt_pow_of_hyp hK hp)]

theorem one_ne_bpt (hK : 1 ≤ K) (hp : p ≠ 2 ∨ 2 ≤ K) : (1 : ZMod (p ^ K)) ≠ bpt p K := by
  intro h
  have := congrArg ZMod.val h
  rw [val_one hK, val_bpt hK hp] at this
  have : 0 < p ^ (K - 1) := pow_pos (Fact.out : p.Prime).pos _
  omega

/-- The null vector is not zero. -/
theorem nullVec_ne_zero (hK : 1 ≤ K) (hp : p ≠ 2 ∨ 2 ≤ K) : nullVec p K ≠ 0 := by
  intro h
  have := congrFun h 1
  simp [nullVec, one_ne_bpt hK hp] at this

/-- Every `P_{p^j}` (`j ≥ 1`) annihilates the null vector: its support is on units. -/
theorem Pproj_nullVec (hK : 1 ≤ K) (hp : p ≠ 2 ∨ 2 ≤ K) {j : ℕ} (hj : 1 ≤ j) :
    Pproj (p ^ j) (nullVec p K) = 0 := by
  funext k
  have hpj : p ∣ p ^ j := dvd_pow_self p (by omega)
  simp only [Pproj, Pi.zero_apply]
  split_ifs with hd
  · have hpk : p ∣ k.val := hpj.trans hd
    by_cases h1 : k = 1
    · subst h1
      rw [val_one hK] at hpk
      exact absurd (Nat.le_of_dvd one_pos hpk) (by have := (Fact.out : p.Prime).two_le; omega)
    · by_cases hb : k = bpt p K
      · subst hb
        rw [val_bpt hK hp] at hpk
        exact absurd hpk (not_dvd_bpt hK hp)
      · simp [nullVec, h1, hb]
  · rfl

/-- The Fourier transform of the null vector vanishes at every multiple of `p`. -/
theorem dft_nullVec (hK : 1 ≤ K) (hp : p ≠ 2 ∨ 2 ≤ K) (k : ZMod (p ^ K)) (hk : p ∣ k.val) :
    𝓕 (nullVec p K) k = 0 := by
  have hbk : bpt p K * k = k := by
    obtain ⟨m, hm⟩ := hk
    have hk' : k = ((p * m : ℕ) : ZMod (p ^ K)) := by
      rw [← hm, ZMod.natCast_zmod_val]
    have h0 : ((p ^ (K - 1) * k : ZMod (p ^ K))) = 0 := by
      rw [hk']
      have : p ^ (K - 1) * (p * m) = p ^ K * m := by
        obtain ⟨n, rfl⟩ : ∃ n, K = n + 1 := ⟨K - 1, by omega⟩
        simp [pow_succ]; ring
      have h2 : (((p ^ (K - 1) * (p * m) : ℕ)) : ZMod (p ^ K)) = 0 := by
        rw [this]
        exact (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_mul_right _ _)
      simpa using h2
    simp only [bpt]
    push_cast
    linear_combination h0
  simp only [ZMod.dft_apply, nullVec, Pi.sub_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hbk, one_mul, sub_self]

/-- Hence each Fourier-conjugated projection annihilates it too. -/
theorem Pproj_dft_nullVec (hK : 1 ≤ K) (hp : p ≠ 2 ∨ 2 ≤ K) {j : ℕ} (hj : 1 ≤ j) :
    Pproj (p ^ j) (𝓕 (nullVec p K)) = 0 := by
  funext k
  simp only [Pproj, Pi.zero_apply]
  split_ifs with hd
  · exact dft_nullVec hK hp k ((dvd_pow_self p (by omega)).trans hd)
  · rfl

/-- **The Fourier-self-dual static frame has an exact weight-independent null mode.**
For every weight function `w`, the operator `Σ_{j=1}^K w_j (P_{p^j} + F^{-1} P_{p^j} F)`
annihilates the nonzero vector `δ₁ − δ_{1+p^{K-1}}`. -/
theorem selfDual_frame_annihilates (hK : 1 ≤ K) (hp : p ≠ 2 ∨ 2 ≤ K) (w : ℕ → ℝ) :
    nullVec p K ≠ 0 ∧
      ∑ j ∈ Finset.Icc 1 K, (w j : ℂ) •
          (Pproj (p ^ j) (nullVec p K) + 𝓕⁻ (Pproj (p ^ j) (𝓕 (nullVec p K)))) = 0 := by
  refine ⟨nullVec_ne_zero hK hp, Finset.sum_eq_zero fun j hj => ?_⟩
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  rw [Pproj_nullVec hK hp hj1, Pproj_dft_nullVec hK hp hj1]
  simp

end PrimePower

end GppBostConnesNoGo
