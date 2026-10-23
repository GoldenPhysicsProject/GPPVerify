import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Riemann's Φ, the theta series ψ, and Λ as a Mellin transform

Source: Claude Code, `work/claude-code/2026-10-23_holographic_dictionary.md` §1 (GPP-bridge),
written at Daniel's direction ("It's all holographic"). Daniel Toupin / Golden Physics Project,
with AI assistance from Claude Code.

Riemann's kernel is `Φ(u) = ∑_{n≥1} (2π²n⁴e^{9u} − 3πn²e^{5u}) e^{−πn²e^{4u}}`, with
`Ξ(t) = 2∫₀^∞ Φ(u) cos(ut) du`. Write `ψ(x) = ∑_{n≥1} e^{−πn²x}`. Then `4√y ψ(y)` is the spin-zero
(scalar) sector of the self-dual `c = 1` compact boson's torus partition function at `τ = iy`.

* `hasSum_psi`, `hasDerivAt_psi`, `hasDerivAt_psi₁`: `ψ` is a convergent series on `x > 0`, and
  it can be differentiated termwise twice, `ψ' = ψ₁`, `ψ₁' = ψ₂`.
* `phi_eq`: **Riemann's identity** `Φ(u) = e^u [2x²ψ''(x) + 3xψ'(x)]` with `x = e^{4u}`.
* `one_add_two_mul_psi`: `1 + 2ψ(x) = ∑_{n∈ℤ} e^{−πn²x}`, which is Mathlib's `evenKernel 0`.
* `psi_functional_equation`: the theta inversion `1 + 2ψ(x) = x^{−1/2}(1 + 2ψ(1/x))`, i.e.
  `S`-invariance of the scalar sector.
* `completedRiemannZeta_eq_mellin_psi`: for `Re s > 1`, `Λ(s) = ∫₀^∞ ψ(x) x^{s/2−1} dx`, i.e.
  completed ζ is the Mellin transform of the boson's scalar sector.

**Scope.** The evenness `Φ(−u) = Φ(u)`, the cosine representation of `Ξ`, and the full
Rankin–Selberg statement `(Z, E_s) = 2Λ(s)(r^{1−2s} + r^{2s−1})` of arXiv 2107.10744 are not
formalized. Nothing here bears on the location of the zeros. No claim about RH.
-/

open Real Filter Topology Complex HurwitzZeta

namespace GppRiemannPhi

/-- The `n`-th theta term `e^{−π(n+1)²x}`. -/
noncomputable def g (n : ℕ) (x : ℝ) : ℝ := rexp (-π * ((n : ℝ) + 1) ^ 2 * x)

/-- `ψ(x) = ∑_{n≥1} e^{−πn²x}`. -/
noncomputable def psi (x : ℝ) : ℝ := ∑' n : ℕ, g n x

/-- `ψ'(x) = −∑_{n≥1} πn² e^{−πn²x}`. -/
noncomputable def psi₁ (x : ℝ) : ℝ := ∑' n : ℕ, -(π * ((n : ℝ) + 1) ^ 2) * g n x

/-- `ψ''(x) = ∑_{n≥1} π²n⁴ e^{−πn²x}`. -/
noncomputable def psi₂ (x : ℝ) : ℝ := ∑' n : ℕ, (π * ((n : ℝ) + 1) ^ 2) ^ 2 * g n x

/-- The `n`-th term of Riemann's `Φ`. -/
noncomputable def phiTerm (n : ℕ) (u : ℝ) : ℝ :=
  (2 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * rexp (9 * u) - 3 * π * ((n : ℝ) + 1) ^ 2 * rexp (5 * u)) *
    rexp (-π * ((n : ℝ) + 1) ^ 2 * rexp (4 * u))

/-- Riemann's kernel `Φ(u)`. -/
noncomputable def phi (u : ℝ) : ℝ := ∑' n : ℕ, phiTerm n u

/-- `(n+1)^k e^{−c(n+1)²}` is summable for `c > 0`. -/
lemma summable_pow_mul_g (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ k * rexp (-c * ((n : ℝ) + 1) ^ 2) := by
  have h := (summable_nat_add_iff 1).mpr (summable_pow_mul_exp_neg_nat_mul k hc)
  refine h.of_nonneg_of_le (fun n => by positivity) fun n => ?_
  push_cast
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have h1 : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  nlinarith

lemma g_eq (n : ℕ) (x : ℝ) : g n x = rexp (-(π * x) * ((n : ℝ) + 1) ^ 2) := by
  unfold g; ring_nf

lemma summable_pow_mul_g' (k : ℕ) {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ k * g n x := by
  simpa only [g_eq] using summable_pow_mul_g k (by positivity : 0 < π * x)

lemma summable_g {x : ℝ} (hx : 0 < x) : Summable fun n : ℕ => g n x := by
  simpa using summable_pow_mul_g' 0 hx

lemma hasSum_psi {x : ℝ} (hx : 0 < x) : HasSum (fun n : ℕ => g n x) (psi x) :=
  (summable_g hx).hasSum

lemma hasDerivAt_g (n : ℕ) (x : ℝ) :
    HasDerivAt (g n) (-(π * ((n : ℝ) + 1) ^ 2) * g n x) x := by
  have := ((hasDerivAt_id' x).const_mul (-π * ((n : ℝ) + 1) ^ 2)).exp
  unfold g
  convert this using 1
  ring

/-- A uniform bound for the termwise derivatives on `y > x/2`. -/
lemma g_le {n : ℕ} {x y : ℝ} (hy : x / 2 < y) : g n y ≤ g n (x / 2) := by
  unfold g
  refine Real.exp_le_exp.mpr ?_
  have : 0 ≤ π * ((n : ℝ) + 1) ^ 2 := by positivity
  nlinarith

lemma hasDerivAt_series {c : ℕ → ℝ} {k : ℕ} (hc : ∀ n, |c n| ≤ π ^ k * ((n : ℝ) + 1) ^ (2 * k))
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun z => ∑' n : ℕ, c n * g n z)
      (∑' n : ℕ, c n * (-(π * ((n : ℝ) + 1) ^ 2) * g n x)) x := by
  have hx2 : 0 < x / 2 := by positivity
  refine hasDerivAt_tsum_of_isPreconnected
    (u := fun n : ℕ => π ^ (k + 1) * (((n : ℝ) + 1) ^ (2 * k + 2) * g n (x / 2)))
    ((summable_pow_mul_g' _ hx2).mul_left _) isOpen_Ioi isPreconnected_Ioi
    (fun n y _ => (hasDerivAt_g n y).const_mul (c n)) (fun n y hy => ?_)
    (show x ∈ Set.Ioi (x / 2) by simp; linarith) ?_ (show x ∈ Set.Ioi (x / 2) by simp; linarith)
  · have hy' : x / 2 < y := hy
    have hg0 : 0 ≤ g n y := (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_nonneg hg0,
      abs_of_nonneg (by positivity : 0 ≤ π * ((n : ℝ) + 1) ^ 2)]
    calc |c n| * (π * ((n : ℝ) + 1) ^ 2 * g n y)
        ≤ (π ^ k * ((n : ℝ) + 1) ^ (2 * k)) * (π * ((n : ℝ) + 1) ^ 2 * g n (x / 2)) := by
          gcongr
          · exact hc n
          · exact g_le hy'
      _ = _ := by ring
  · refine ((summable_pow_mul_g' (2 * k) hx).mul_left (π ^ k)).of_norm_bounded_eventually ?_
    refine Eventually.of_forall fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show 0 ≤ g n x from (Real.exp_pos _).le)]
    calc |c n| * g n x ≤ π ^ k * ((n : ℝ) + 1) ^ (2 * k) * g n x :=
          mul_le_mul_of_nonneg_right (hc n) (Real.exp_pos _).le
      _ = _ := by ring

/-- `ψ' = ψ₁` on `x > 0`. -/
theorem hasDerivAt_psi {x : ℝ} (hx : 0 < x) : HasDerivAt psi (psi₁ x) x := by
  have := hasDerivAt_series (c := fun _ => 1) (k := 0) (fun n => by simp) hx
  simp only [one_mul] at this
  exact this

/-- `ψ₁' = ψ₂` on `x > 0`. -/
theorem hasDerivAt_psi₁ {x : ℝ} (hx : 0 < x) : HasDerivAt psi₁ (psi₂ x) x := by
  have := hasDerivAt_series (c := fun n => -(π * ((n : ℝ) + 1) ^ 2)) (k := 1) (fun n => by
    rw [abs_neg, abs_of_nonneg (by positivity)]; ring_nf; rfl) hx
  unfold psi₁ psi₂
  convert this using 2 with n
  ring_nf

lemma phiTerm_eq (n : ℕ) (u : ℝ) :
    phiTerm n u = rexp u *
      (2 * rexp (4 * u) ^ 2 * ((π * ((n : ℝ) + 1) ^ 2) ^ 2 * g n (rexp (4 * u)))
        + 3 * rexp (4 * u) * (-(π * ((n : ℝ) + 1) ^ 2) * g n (rexp (4 * u)))) := by
  have h9 : rexp (9 * u) = rexp u * rexp (4 * u) ^ 2 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have h5 : rexp (5 * u) = rexp u * rexp (4 * u) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold phiTerm g
  rw [h9, h5]
  ring

/-- **Riemann's identity.** `Φ(u) = e^u [2x²ψ''(x) + 3xψ'(x)]` with `x = e^{4u}`. -/
theorem phi_eq (u : ℝ) :
    phi u = rexp u * (2 * rexp (4 * u) ^ 2 * psi₂ (rexp (4 * u))
      + 3 * rexp (4 * u) * psi₁ (rexp (4 * u))) := by
  set x := rexp (4 * u) with hxdef
  have hx : 0 < x := Real.exp_pos _
  have h2 : Summable fun n : ℕ => (π * ((n : ℝ) + 1) ^ 2) ^ 2 * g n x := by
    exact ((summable_pow_mul_g' 4 hx).mul_left (π ^ 2)).congr fun n => by ring
  have h1 : Summable fun n : ℕ => -(π * ((n : ℝ) + 1) ^ 2) * g n x := by
    exact ((summable_pow_mul_g' 2 hx).mul_left π).neg.congr fun n => by ring
  unfold phi psi₁ psi₂
  simp_rw [phiTerm_eq, ← hxdef]
  rw [← tsum_mul_left, ← tsum_mul_left, ← (h2.mul_left _).tsum_add (h1.mul_left _),
    ← tsum_mul_left]

/-- `1 + 2ψ(x) = ∑_{n∈ℤ} e^{−πn²x}`, Mathlib's `evenKernel 0`. -/
theorem one_add_two_mul_psi {x : ℝ} (hx : 0 < x) : 1 + 2 * psi x = evenKernel 0 x := by
  have hZ := hasSum_int_evenKernel 0 hx
  simp only [add_zero, QuotientAddGroup.mk_zero] at hZ
  have hN := hZ.nat_add_neg_add_one
  set f : ℕ → ℝ := fun n => rexp (-π * ((n : ℤ) : ℝ) ^ 2 * x) with hf
  have hshift : HasSum (fun n : ℕ => f (n + 1)) (1 + psi x - ∑ i ∈ Finset.range 1, f i) := by
    rw [Finset.sum_range_one, show f 0 = 1 by simp [hf], add_sub_cancel_left]
    exact (hasSum_psi hx).congr_fun fun n => by simp only [hf, g]; push_cast; ring_nf
  have hpos : HasSum f (1 + psi x) := (hasSum_nat_add_iff' 1).mp hshift
  have hneg : HasSum (fun n : ℕ => rexp (-π * ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2 * x)) (psi x) :=
    (hasSum_psi hx).congr_fun fun n => by unfold g; congr 1; push_cast; ring
  have := hpos.add hneg
  rw [hN.unique this]; ring

/-- **Theta inversion** (`S`-invariance of the scalar sector):
`1 + 2ψ(x) = x^{−1/2}(1 + 2ψ(1/x))`. -/
theorem psi_functional_equation {x : ℝ} (hx : 0 < x) :
    1 + 2 * psi x = 1 / x ^ (1 / 2 : ℝ) * (1 + 2 * psi (1 / x)) := by
  rw [one_add_two_mul_psi hx, one_add_two_mul_psi (by positivity), evenKernel_functional_equation,
    evenKernel_eq_cosKernel_of_zero]

/-- **Λ is the Mellin transform of ψ.** For `Re s > 1`,
`Λ(s) = ∫₀^∞ ψ(x) x^{s/2−1} dx`. -/
theorem completedRiemannZeta_eq_mellin_psi {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta s = mellin (fun x : ℝ => (psi x : ℂ)) (s / 2) := by
  have hs0 : 0 < s.re := by linarith
  have hF : ∀ t ∈ Set.Ioi (0 : ℝ), HasSum (fun n : ℕ => if (n : ℝ) = 0 then 0 else
      (1 : ℂ) * rexp (-π * (n : ℝ) ^ 2 * t)) (psi t : ℂ) := by
    intro t ht
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one, Nat.cast_zero, if_true, sub_zero, one_mul]
    refine (hasSum_ofReal.mpr (hasSum_psi ht)).congr_fun fun n => ?_
    rw [if_neg (by positivity)]
    simp [g]
  have hsum : Summable fun n : ℕ => ‖(1 : ℂ)‖ / |(n : ℝ)| ^ s.re := by
    simpa [Nat.abs_cast] using Real.summable_one_div_nat_rpow.mpr hs
  have h := hasSum_mellin_pi_mul_sq hs0 hF hsum
  rw [← h.tsum_eq, completedZeta_eq_tsum_of_one_lt_re hs, ← Gammaℝ_def, ← tsum_mul_left]
  congr 1 with n
  simp [Nat.abs_cast, div_eq_mul_inv]

end GppRiemannPhi
