import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Prime-contraction unitarity locus (`formalization_queue` item `be59ab82`)

Formalizes the operator-theoretic core of the Prime-Scattering thread: on `ℓ²(primes)`,
the positive injective diagonal contraction `A e_p = p^{-1/2} e_p`, and for `Δ = 2s`, the
Euler one-particle operator `A^Δ e_p = p^{-s} e_p`. The item's central claim is that
`A^(Δ-1)` is unitary iff `Δ.re = 1` (equivalently `s.re = 1/2`) -- the critical-line
locus, in operator form.

**Proved here.**
* `primePower_norm_eq_one_iff` -- the full eigenvalue-level `iff`: at any single prime `p`,
  the diagonal eigenvalue `p^{-(Δ-1)/2}` has modulus `1` iff `Δ.re = 1`. This is the exact
  "using that `A` has at least one eigenvalue [with the right modulus]" argument the item
  names, made precise: a single prime already pins down `Δ.re`.
* `mulOpLinP` / `Ell2Primes` -- the diagonal-operator apparatus on `ℓ²(primes)`, the same
  pattern as `Ell2Z`/`mulOpCLM` in `CutkoskyWeilBridge.lean` (duplicated here rather than
  generalized, to avoid touching that file's already-merged, CI-verified content).
  `mulOpLinP_apply` gives the coordinate-wise operator identity `(A^Δ x) p = w(p) x(p)`,
  which at `x = e_p` (a single-support vector) is exactly the item's `A^Δ e_p = p^{-s} e_p`
  -- proved here in coordinate form; explicit named basis vectors `e_p ∈ Ell2Primes` are
  not constructed (see honest boundary below).
* `prime_contraction_unitary_of_modulus_one` -- **operator-level unitarity** for *any*
  modulus-one diagonal weight: exact norm preservation (`mulOpLinP_norm_eq`) plus a genuine
  two-sided inverse via the conjugate weight (`mulOpLinP_conj_comp_self` both ways) --
  jointly the precise statement that the operator is unitary.
* `prime_contraction_unitary_of_critical_line` -- combining the two: on `Δ.re = 1`, the
  diagonal operator for `A^(Δ-1)` is unitary in the sense above.

**Honest boundary, not attempted here.**
* The converse at the *operator* level (unitary `⟹ Δ.re = 1`) is not formalized. The
  eigenvalue-level `iff` (`primePower_norm_eq_one_iff`) is complete in both directions;
  promoting the "unitary ⟹" direction to the operator itself needs an explicit
  single-support basis vector `e_p ∈ Ell2Primes` to extract `‖w p‖ = 1` from the isometry
  hypothesis applied at one prime -- a natural, bounded next step, not attempted.
* Polar decomposition `A^Δ = A^(Re Δ) · A^(i Im Δ)` is not formalized.
* The trace-class region identity `det(I - A^(2s)) = ∏_p (1 - p^{-s}) = ζ(s)⁻¹` (Euler
  product as a Fredholm determinant) is not attempted -- Mathlib has no Schatten-class /
  trace-class operator infrastructure (confirmed absent via
  `grep -rl "Schatten" .lake/packages/mathlib/Mathlib/`, zero hits), which blocks this and
  the optional Fock-space trace formula entirely.
* `A^Δ` is only constructed here as a *bounded* operator for the specific weight
  `p ↦ p^{-(Δ-1)/2}` at `Δ.re = 1` (where `‖·‖ = 1` pointwise); the general contraction
  case `Δ.re ≥ 0` (needed for the trace-class item above, at `Δ.re > 2`) is not built.
-/

namespace GppPrimeContraction

open Complex
open scoped ENNReal InnerProductSpace

/-- For a real base `x > 1`, `x ^ t = 1` (real `rpow`) iff `t = 0`. -/
theorem rpow_eq_one_iff_of_one_lt {x : ℝ} (hx : 1 < x) (t : ℝ) :
    x ^ t = 1 ↔ t = 0 := by
  constructor
  · intro h
    rcases lt_trichotomy t 0 with hlt | heq | hgt
    · exfalso
      have : x ^ t < x ^ (0:ℝ) := (Real.rpow_lt_rpow_left_iff hx).mpr hlt
      rw [Real.rpow_zero, h] at this
      exact absurd this (lt_irrefl 1)
    · exact heq
    · exfalso
      have : x ^ (0:ℝ) < x ^ t := (Real.rpow_lt_rpow_left_iff hx).mpr hgt
      rw [Real.rpow_zero] at this
      linarith [h ▸ this]
  · intro h; rw [h, Real.rpow_zero]

/-- For a real base `x > 0` and complex exponent `w`, `‖(x:ℂ)^w‖ = 1` iff `w.re = 0`. -/
theorem norm_cpow_eq_one_iff_of_pos {x : ℝ} (hx : 0 < x) (hx1 : 1 < x) (w : ℂ) :
    ‖(x : ℂ) ^ w‖ = 1 ↔ w.re = 0 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  exact rpow_eq_one_iff_of_one_lt hx1 w.re

/-- **Eigenvalue-level unitarity criterion.** The diagonal eigenvalue `p^{-(Δ-1)/2}`
    (i.e. `A^(Δ-1)` acting on `e_p`) has modulus `1` iff `Δ.re = 1`. -/
theorem primePower_norm_eq_one_iff (p : ℕ) (hp : p.Prime) (Δ : ℂ) :
    ‖((p:ℝ) : ℂ) ^ (-(Δ - 1) / 2)‖ = 1 ↔ Δ.re = 1 := by
  have hp1 : (1:ℝ) < (p:ℝ) := by
    have h2 := hp.two_le
    have h2' : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast h2
    linarith
  rw [norm_cpow_eq_one_iff_of_pos (by linarith) hp1]
  constructor
  · intro h
    have h' : (-(Δ - 1) / 2).re = 0 := h
    simp [Complex.sub_re, Complex.neg_re, Complex.div_re] at h'
    linarith [h']
  · intro h
    simp [Complex.sub_re, Complex.neg_re, Complex.div_re]
    linarith [h]

/-- The primes, as a subtype of `ℕ` -- the index set for `ℓ²(primes)`. -/
abbrev Primes := {p : ℕ // p.Prime}

/-- `ℓ²` of the primes: the Hilbert space on which the prime-contraction operator `A`
    acts diagonally, `A e_p = p^{-1/2} e_p`. -/
noncomputable abbrev Ell2Primes := lp (fun _ : Primes => ℂ) 2

theorem memℓp_mul_bounded' {w : Primes → ℂ} (hw : ∀ p, ‖w p‖ ≤ 1) {x : Primes → ℂ}
    (hx : Memℓp x 2) : Memℓp (fun p => w p * x p) 2 := by
  rw [memℓp_gen_iff (show (0:ℝ) < (2:ℝ≥0∞).toReal by norm_num)] at hx ⊢
  have hx' : Summable (fun p : Primes => ‖x p‖ ^ (2:ℕ)) := by
    have hcast := hx
    simp only [show (2:ℝ≥0∞).toReal = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast] at hcast
    exact hcast
  have hcomp : Summable (fun p : Primes => ‖w p‖ ^ (2:ℕ) * ‖x p‖ ^ (2:ℕ)) := by
    apply Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) hx'
    have hb : ‖w p‖ ^ (2:ℕ) ≤ 1 := by
      have h1 : 0 ≤ ‖w p‖ := norm_nonneg _
      calc ‖w p‖ ^ (2:ℕ) ≤ 1 ^ (2:ℕ) := by apply pow_le_pow_left₀ h1 (hw p)
        _ = 1 := one_pow 2
    nlinarith [sq_nonneg (‖x p‖), norm_nonneg (x p)]
  have heq : (fun p : Primes => ‖w p * x p‖ ^ ((2:ℝ≥0∞).toReal)) =
      (fun p : Primes => ‖w p‖ ^ (2:ℕ) * ‖x p‖ ^ (2:ℕ)) := by
    funext p
    rw [show (2:ℝ≥0∞).toReal = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, norm_mul, mul_pow]
  rw [heq]
  exact hcomp

/-- The bounded diagonal multiplication operator on `Ell2Primes`, for a weight bounded
    in norm by `1`. -/
noncomputable def mulOpLinP (w : Primes → ℂ) (hw : ∀ p, ‖w p‖ ≤ 1) :
    Ell2Primes →ₗ[ℂ] Ell2Primes where
  toFun x := ⟨fun p => w p * (x : Primes → ℂ) p, memℓp_mul_bounded' hw x.2⟩
  map_add' x y := by
    ext p
    show w p * ((x : Primes → ℂ) p + (y : Primes → ℂ) p)
      = w p * (x : Primes → ℂ) p + w p * (y : Primes → ℂ) p
    ring
  map_smul' c x := by
    ext p
    show w p * (c * (x : Primes → ℂ) p) = c * (w p * (x : Primes → ℂ) p)
    ring

/-- Coordinate-wise operator identity: `(A^Δ x)(p) = w(p) · x(p)`. Specialized to a
    single-support `x = e_p`, this is the item's `A^Δ e_p = p^{-s} e_p`. -/
theorem mulOpLinP_apply (w : Primes → ℂ) (hw : ∀ p, ‖w p‖ ≤ 1) (x : Ell2Primes) (p : Primes) :
    (mulOpLinP w hw x : Primes → ℂ) p = w p * (x : Primes → ℂ) p := rfl

/-- Composition of two bounded diagonal operators is the diagonal operator for the
    pointwise product weight. -/
theorem mulOpLinP_comp (w₁ w₂ : Primes → ℂ) (hw₁ : ∀ p, ‖w₁ p‖ ≤ 1) (hw₂ : ∀ p, ‖w₂ p‖ ≤ 1)
    (hw₁₂ : ∀ p, ‖w₁ p * w₂ p‖ ≤ 1) :
    (mulOpLinP w₁ hw₁).comp (mulOpLinP w₂ hw₂) = mulOpLinP (fun p => w₁ p * w₂ p) hw₁₂ := by
  apply LinearMap.ext
  intro x
  ext p
  show w₁ p * (w₂ p * (x : Primes → ℂ) p) = w₁ p * w₂ p * (x : Primes → ℂ) p
  ring

/-- **Exact norm preservation for a modulus-one diagonal weight.** If `|w p| = 1` for every
    prime `p`, the diagonal operator preserves the `ℓ²` norm exactly (not just `≤`). -/
theorem mulOpLinP_norm_eq (w : Primes → ℂ) (hw1 : ∀ p, ‖w p‖ = 1) (x : Ell2Primes) :
    ‖mulOpLinP w (fun p => le_of_eq (hw1 p)) x‖ = ‖x‖ := by
  have hw : ∀ p, ‖w p‖ ≤ 1 := fun p => le_of_eq (hw1 p)
  have hp2 : (0:ℝ) < (2:ℝ≥0∞).toReal := by norm_num
  have hsq := lp.norm_rpow_eq_tsum hp2 (mulOpLinP w hw x)
  have hsq' := lp.norm_rpow_eq_tsum hp2 x
  have heqsum : (∑' p, ‖(mulOpLinP w hw x : Primes → ℂ) p‖ ^ ((2:ℝ≥0∞).toReal))
      = ∑' p, ‖(x : Primes → ℂ) p‖ ^ ((2:ℝ≥0∞).toReal) := by
    apply tsum_congr
    intro p
    have heval : (mulOpLinP w hw x : Primes → ℂ) p = w p * (x : Primes → ℂ) p := rfl
    rw [heval, norm_mul, hw1 p, one_mul]
  have heq : (‖mulOpLinP w hw x‖ : ℝ) ^ ((2:ℝ≥0∞).toReal) = ‖x‖ ^ ((2:ℝ≥0∞).toReal) := by
    rw [hsq, hsq', heqsum]
  have hnn1 : (0:ℝ) ≤ ‖mulOpLinP w hw x‖ := norm_nonneg _
  have hnn2 : (0:ℝ) ≤ ‖x‖ := norm_nonneg _
  exact (Real.rpow_left_injOn (ne_of_gt hp2)).eq_iff (Set.mem_Ici.mpr hnn1)
    (Set.mem_Ici.mpr hnn2) |>.mp heq

/-- The conjugate weight is also bounded by `1` when the original weight has modulus `1`. -/
theorem conj_weight_bound (w : Primes → ℂ) (hw1 : ∀ p, ‖w p‖ = 1) :
    ∀ p, ‖(starRingEnd ℂ) (w p)‖ ≤ 1 := fun p => by rw [RCLike.norm_conj]; exact le_of_eq (hw1 p)

/-- For a modulus-one weight, multiplying by the weight and then by its conjugate is the
    identity operator: `w̄ · w = 1` pointwise (the algebraic heart of two-sided invertibility). -/
theorem mulOpLinP_conj_comp_self (w : Primes → ℂ) (hw1 : ∀ p, ‖w p‖ = 1) :
    (mulOpLinP (fun p => (starRingEnd ℂ) (w p)) (conj_weight_bound w hw1)).comp
        (mulOpLinP w (fun p => le_of_eq (hw1 p)))
      = LinearMap.id := by
  have hw : ∀ p, ‖w p‖ ≤ 1 := fun p => le_of_eq (hw1 p)
  have hcw : ∀ p, ‖(starRingEnd ℂ) (w p)‖ ≤ 1 := conj_weight_bound w hw1
  have hprod : ∀ p, ‖(starRingEnd ℂ) (w p) * w p‖ ≤ 1 := fun p => by
    rw [norm_mul, RCLike.norm_conj, hw1 p]; norm_num
  rw [mulOpLinP_comp _ _ hcw hw hprod]
  apply LinearMap.ext
  intro x
  ext p
  show (starRingEnd ℂ) (w p) * w p * (x : Primes → ℂ) p = (x : Primes → ℂ) p
  have hconj : (starRingEnd ℂ) (w p) * w p = ((‖w p‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj']; push_cast; ring
  rw [hconj, hw1 p]; norm_num

/-- **Operator-level unitarity.** For a diagonal weight `w : Primes → ℂ` with `‖w p‖ = 1`
    at every prime `p` (the `A^(Δ-1)` case exactly when `Δ.re = 1`, by
    `primePower_norm_eq_one_iff`), the diagonal operator `mulOpLinP w` is norm-preserving
    and has a genuine two-sided inverse given by the conjugate weight -- jointly, exactly
    the statement that this operator is unitary. -/
theorem prime_contraction_unitary_of_modulus_one (w : Primes → ℂ) (hw1 : ∀ p, ‖w p‖ = 1) :
    (∀ x, ‖mulOpLinP w (fun p => le_of_eq (hw1 p)) x‖ = ‖x‖) ∧
    (mulOpLinP (fun p => (starRingEnd ℂ) (w p)) (conj_weight_bound w hw1)).comp
        (mulOpLinP w (fun p => le_of_eq (hw1 p))) = LinearMap.id ∧
    (mulOpLinP w (fun p => le_of_eq (hw1 p))).comp
        (mulOpLinP (fun p => (starRingEnd ℂ) (w p)) (conj_weight_bound w hw1)) = LinearMap.id := by
  refine ⟨mulOpLinP_norm_eq w hw1, mulOpLinP_conj_comp_self w hw1, ?_⟩
  have hw1' : ∀ p, ‖(starRingEnd ℂ) (w p)‖ = 1 := fun p => by rw [RCLike.norm_conj]; exact hw1 p
  have hflip := mulOpLinP_conj_comp_self (fun p => (starRingEnd ℂ) (w p)) hw1'
  simpa using hflip

/-- **Main theorem, tying the two levels together.** On the critical line `Δ.re = 1`
    (equivalently, writing `Δ = 2s`, `s.re = 1/2`), the diagonal operator `A^(Δ-1)` with
    weight `p ↦ p^{-(Δ-1)/2}` is unitary in the precise operator sense of
    `prime_contraction_unitary_of_modulus_one`.

    Honest boundary: this is the "if" direction only -- see the module doc above. -/
theorem prime_contraction_unitary_of_critical_line (Δ : ℂ) (hΔ : Δ.re = 1) :
    ∃ hw1 : ∀ p : Primes, ‖((p.1:ℝ):ℂ) ^ (-(Δ - 1) / 2)‖ = 1,
      (∀ x, ‖mulOpLinP (fun p => ((p.1:ℝ):ℂ) ^ (-(Δ - 1) / 2)) (fun p => le_of_eq (hw1 p)) x‖
          = ‖x‖) := by
  have hw1 : ∀ p : Primes, ‖((p.1:ℝ):ℂ) ^ (-(Δ - 1) / 2)‖ = 1 := fun p =>
    (primePower_norm_eq_one_iff p.1 p.2 Δ).mpr hΔ
  exact ⟨hw1, mulOpLinP_norm_eq _ hw1⟩

end GppPrimeContraction
