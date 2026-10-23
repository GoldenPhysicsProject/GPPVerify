import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# A single off-line quartet breaks every bounded positive kernel

Source: Astra, `work/2026-10-23_astra_single_quartet_sampling.md` (GPP-bridge), answering Claude
Code's single-quartet injection test (`work/claude-code/2026-10-23_holographic_dictionary.md` §5).
Daniel Toupin / Golden Physics Project, with AI assistance from Astra (statements and proofs) and
Claude Code (formalization).

Inject `z = δ + iγ` with `δ, γ > 0`, together with its quartet, into a real even kernel. With
`b = S(z)S(−z) ≠ 0` the added kernel is `D(u) = 4 Re[b cosh(zu)]`.

* `quartet_lower`: if `b e^{iγu} = |b|`, then `D(u) ≥ 2|b|(e^{δu} − e^{−δu})`.
* `phase_aligned`: `u_n = (2πn − arg b)/γ` satisfies the phase condition.
* `quartet_unbounded`: `D` is unbounded above along `u_n`.
* `not_psd_two`: if `|c| > c₀` then the `2 × 2` block `[[c₀, c], [c, c₀]]` is not positive
  semidefinite.
* `kernel_not_psd`: for a kernel `C = B + D` whose background `B` is bounded, some `2 × 2` block
  `(0, u)` of `C` is not positive semidefinite. This is a full-kernel injection, not a perturbation
  of the residual alone.
* `blind_grid`: on the grid `u = nh` with `γh = πk` and `Re b = 0`, `D(nh) = 0` for every `n`. This
  is the exceptional blind case of Astra's sampling theorem. Its converse (unboundedness off
  resonance) and the two-grid statement are not formalized.

**Scope.** Synthetic control only. `S` is not specialised here, so `b` is an arbitrary nonzero
complex number. Astra's consequence is this: a hypothesis invariant under finite injection (for
example, a leading zero-density asymptotic) cannot by itself imply positivity. That remark is
not a theorem here, and it does not close averaging methods that are sensitive to exceptional
zeros. No claim about RH.
-/

open Complex Real Filter Topology

namespace GppSingleQuartet

/-- The kernel added by one quartet. -/
noncomputable def D (b : ℂ) (δ γ u : ℝ) : ℝ :=
  4 * (b * Complex.cosh ((δ + γ * I) * u)).re

lemma D_eq (b : ℂ) (δ γ u : ℝ) :
    D b δ γ u = 2 * (b * cexp ((δ + γ * I) * u)).re + 2 * (b * cexp (-((δ + γ * I) * u))).re := by
  unfold D
  rw [Complex.cosh, mul_div_assoc', mul_add, Complex.div_re]
  simp only [Complex.add_re, show ((2 : ℂ)).re = 2 by norm_num, show ((2 : ℂ)).im = 0 by norm_num,
    Complex.normSq_ofNat]
  ring

/-- **Growth along an aligned phase.** -/
theorem quartet_lower (b : ℂ) (δ γ u : ℝ) (hphase : b * cexp (γ * u * I) = ‖b‖) :
    2 * ‖b‖ * (rexp (δ * u) - rexp (-(δ * u))) ≤ D b δ γ u := by
  rw [D_eq]
  have hsplit : cexp ((δ + γ * I) * u) = (rexp (δ * u) : ℂ) * cexp (γ * u * I) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
  have h1 : b * cexp ((δ + γ * I) * u) = ((‖b‖ * rexp (δ * u) : ℝ) : ℂ) := by
    rw [hsplit, mul_left_comm, hphase]; push_cast; ring
  have h2 : -(‖b‖ * rexp (-(δ * u))) ≤ (b * cexp (-((δ + γ * I) * u))).re := by
    have := (abs_le.mp (Complex.abs_re_le_norm (b * cexp (-((δ + γ * I) * u))))).1
    refine le_trans (le_of_eq ?_) this
    rw [norm_mul, Complex.norm_exp]
    congr 3
    simp
  rw [h1, Complex.ofReal_re]
  linarith

/-- **The aligned sample points** `u_n = (2πn − arg b)/γ`. -/
theorem phase_aligned (b : ℂ) {γ : ℝ} (hγ : γ ≠ 0) (n : ℤ) {u : ℝ}
    (hu : u = (2 * π * n - arg b) / γ) : b * cexp (γ * u * I) = ‖b‖ := by
  have hγu : (γ : ℂ) * u = 2 * π * n - arg b := by
    have : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
    rw [hu]; push_cast; field_simp
  rw [hγu]
  nth_rewrite 1 [← Complex.norm_mul_exp_arg_mul_I b]
  rw [mul_assoc, ← Complex.exp_add,
    show (arg b : ℂ) * I + (2 * π * n - arg b) * I = n * (2 * π * I) by ring,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **One quartet is unbounded.** For `δ, γ > 0` and `b ≠ 0`, `D` exceeds every bound at some
aligned sample. -/
theorem quartet_unbounded {b : ℂ} (hb : b ≠ 0) {δ γ : ℝ} (hδ : 0 < δ) (hγ : 0 < γ) (M : ℝ) :
    ∃ u : ℝ, M ≤ D b δ γ u := by
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  obtain ⟨n, hn⟩ := exists_int_gt ((γ * (|M| / (4 * ‖b‖ * δ)) + arg b) / (2 * π))
  set u := (2 * π * n - arg b) / γ with hu
  refine ⟨u, le_trans ?_ (quartet_lower b δ γ u (phase_aligned b hγ.ne' n hu))⟩
  have hu_ge : |M| / (4 * ‖b‖ * δ) ≤ u := by
    rw [hu, le_div_iff₀ hγ]
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * π)).mp hn
    nlinarith
  have hc : 0 ≤ |M| / (4 * ‖b‖ * δ) := by positivity
  have hx : 0 ≤ δ * u := mul_nonneg hδ.le (hc.trans hu_ge)
  have hexp : 2 * (δ * u) ≤ rexp (δ * u) - rexp (-(δ * u)) := by
    have := Real.self_le_sinh_iff.mpr hx
    rw [Real.sinh_eq] at this
    linarith
  have hMu : |M| ≤ 4 * ‖b‖ * δ * u := by
    rw [div_le_iff₀ (by positivity)] at hu_ge; linarith
  calc M ≤ |M| := le_abs_self M
    _ ≤ 4 * ‖b‖ * δ * u := hMu
    _ = 2 * ‖b‖ * (2 * (δ * u)) := by ring
    _ ≤ 2 * ‖b‖ * (rexp (δ * u) - rexp (-(δ * u))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)

/-- **A dominant off-diagonal entry breaks a `2 × 2` block.** -/
theorem not_psd_two {c₀ c : ℝ} (h : c₀ < |c|) :
    ∃ x y : ℝ, x ^ 2 * c₀ + 2 * x * y * c + y ^ 2 * c₀ < 0 := by
  rcases le_or_gt 0 c with hc | hc
  · refine ⟨1, -1, ?_⟩
    rw [abs_of_nonneg hc] at h; nlinarith
  · refine ⟨1, 1, ?_⟩
    rw [abs_of_neg hc] at h; nlinarith

/-- **Full-kernel injection.** If `C = B + D` with `|B| ≤ K`, then some `2 × 2` block `(0, u)` of
`C` is not positive semidefinite. -/
theorem kernel_not_psd {b : ℂ} (hb : b ≠ 0) {δ γ : ℝ} (hδ : 0 < δ) (hγ : 0 < γ)
    (B : ℝ → ℝ) {K : ℝ} (hB : ∀ u, |B u| ≤ K) :
    ∃ u x y : ℝ, x ^ 2 * (B 0 + D b δ γ 0) + 2 * x * y * (B u + D b δ γ u)
      + y ^ 2 * (B 0 + D b δ γ 0) < 0 := by
  obtain ⟨u, hu⟩ := quartet_unbounded hb hδ hγ (|B 0 + D b δ γ 0| + K + 1)
  have h1 := le_abs_self (B 0 + D b δ γ 0)
  have h2 := neg_abs_le (B u)
  have h3 := hB u
  have h4 : B u + D b δ γ u ≤ |B u + D b δ γ u| := le_abs_self _
  obtain ⟨x, y, hxy⟩ := not_psd_two (c₀ := B 0 + D b δ γ 0) (c := B u + D b δ γ u)
    (by linarith)
  exact ⟨u, x, y, hxy⟩

/-- **The blind grid.** If `γh = πk` and `Re b = 0`, every sample `D(nh)` vanishes. -/
theorem blind_grid {b : ℂ} (hb : b.re = 0) {δ γ h : ℝ} {k : ℤ} (hk : γ * h = π * k) (n : ℕ) :
    D b δ γ (n * h) = 0 := by
  have hs : Real.sin (γ * (n * h)) = 0 := by
    rw [show γ * (n * h) = ((n * k : ℤ) : ℝ) * π by
      rw [mul_left_comm, hk]; push_cast; ring]
    exact Real.sin_int_mul_pi _
  rw [D_eq]
  simp [Complex.mul_re, Complex.exp_re, Complex.exp_im, hb, hs, Real.sin_neg]

end GppSingleQuartet
