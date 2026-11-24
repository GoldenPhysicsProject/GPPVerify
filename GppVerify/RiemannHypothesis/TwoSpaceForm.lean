import GppVerify.RiemannHypothesis.ShiftSeriesL2

/-!
# The two-positive-space form of OB-6: definitions, and `OB6At ⟺ ‖C_N f‖² ≤ B_N(f)`

Build-order item (iv) of Turbo's relay of Codex's construction (bridge `c11a2d9`; Flint audit PASS WITH
QUALIFICATIONS). At a width `L` and admissible cutoff `N` (`L < log(N+1)`) the Weil form is a difference of
two nonnegative quantities,

  `Q(f) = B_N(f) − ‖C_N f‖²`,   `B_N(f) = poleTerm + archimedeanTerm + θ(N)‖f‖²`  (`BNform`),
  `C_N f = (√((log p)(1 − p^{−1})) · Φ_p f)_{p ≤ N} ∈ ⊕_{p≤N} L²(ℝ)`  (`CN`),

so `Q ≥ 0 ⟺ ‖C_N f‖² ≤ B_N(f)` — *contractivity of `C_N` from the `B_N`-seminorm to `⊕ L²`*.

* `phiL2`, `CN`: `Φ_p f ∈ L²(ℝ)` (`ShiftSeriesL2.memLp_shiftSeries`) as an element of `Lp ℝ 2`, and `C_N f`
  in `PiLp 2` over the primes `≤ N`. Built from the in-tree shift series only; no zero data.
* `normSq_phiL2`, `normSq_CN`: `‖Φ_p f‖²_{L²} = phiNormSq p f` and `‖C_N f‖² = shiftGramSum N f`.
* **`ob6At_iff_contraction`**: `OB6At L ⟺ ∀ f (supported in [−L/2, L/2]), ∀ admissible N, ‖C_N f‖² ≤ B_N(f)`.
* **`ob6At_iff_single_cutoff`**: the same at **any one** admissible `N₀` — `Q = B_N − ‖C_N f‖²` does not
  depend on `N` (`weilForm_regrouped`), so no limit in `N` is involved.
* `contraction_iff_norm_le`: where `B_N ≥ 0` (a hypothesis), `‖C_N f‖ ≤ √(B_N f)` — the operator reading.

**Named obligations, not proved here.**
(O1) `B_N ≥ 0` on the test functions of width `L` for admissible `N` — Codex's `B_N ≥ [θ(N) + κ_L]‖f‖²`
(`κ_L < 0`) from the in-tree archimedean floor; without it `√(B_N f)` is not a norm and `H_{+,N}` (the GNS
completion of the polarised `B_N`, `FormGNS`) is not built here.
(O2) The resolvent identification `Φ_p = (I − p^{−1/2}T_{log p})^{−1}` and the norm bounds
`‖f‖/(1+q_p) ≤ ‖Φ_p f‖ ≤ ‖f‖/(1−q_p)` (paper-level; the in-tree `norm_sq_shiftSeries` identity does not give
the lower bound at `p = 2`).
(O3) Contractivity itself, `‖C_N‖ ≤ 1`, is `OB6At L` — **OPEN**, exactly as open as ARP.

No `sorry`, no axiom.
-/

open MeasureTheory
open GppArithmeticReflection GppArchimedeanFloor
open scoped ContDiff

noncomputable section

namespace GppShiftPresentation

/-- `Φ_p g ∈ L²`, for a prime power base `p ≥ 2`. -/
theorem memLp_phi {p : ℕ} (hp : 2 ≤ p) {g : ℝ → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) :
    MemLp (phi p g) 2 volume := by
  rw [phi_eq hp]
  exact memLp_shiftSeries hg hc (qOf_pos hp) (qOf_lt_one hp)

/-- `Φ_p g` as an element of `L²(ℝ)`. -/
def phiL2 {p : ℕ} (hp : 2 ≤ p) {g : ℝ → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) :
    Lp ℝ 2 (volume : Measure ℝ) :=
  (memLp_phi hp hg hc).toLp (phi p g)

/-- **`‖Φ_p g‖²_{L²} = phiNormSq p g`.** -/
theorem normSq_phiL2 {p : ℕ} (hp : 2 ≤ p) {g : ℝ → ℝ} (hg : Continuous g)
    (hc : HasCompactSupport g) : ‖phiL2 hp hg hc‖ ^ 2 = phiNormSq p g := by
  have h := L2.inner_def (𝕜 := ℝ) (phiL2 hp hg hc) (phiL2 hp hg hc)
  rw [real_inner_self_eq_norm_sq] at h
  rw [h]
  unfold phiNormSq
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_phi hp hg hc)] with y hy
  have : (phiL2 hp hg hc) y = phi p g y := hy
  simp only [this]
  simp [sq]

/-- The primes `≤ N` are `≥ 2`. -/
theorem two_le_of_mem_primesUpTo {N : ℕ} (p : ↥(primesUpTo N)) : 2 ≤ (p : ℕ) :=
  (Finset.mem_filter.mp p.2).2.two_le

/-- **The map `C_N`**: `f ↦ (√((log p)(1 − p^{−1})) · Φ_p f)_{p ≤ N}` into `⊕_{p ≤ N} L²(ℝ)`. -/
def CN (N : ℕ) {g : ℝ → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) :
    PiLp 2 (fun _ : ↥(primesUpTo N) => Lp ℝ 2 (volume : Measure ℝ)) :=
  WithLp.toLp 2 fun p =>
    Real.sqrt (Real.log p * (1 - 1 / (p : ℝ))) • phiL2 (two_le_of_mem_primesUpTo p) hg hc

/-- **`‖C_N g‖² = Σ_{p≤N} (log p)(1 − p^{−1}) ‖Φ_p g‖²`** — the Gram side of I2. -/
theorem normSq_CN (N : ℕ) {g : ℝ → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) :
    ‖CN N hg hc‖ ^ 2 = shiftGramSum N g := by
  rw [PiLp.norm_sq_eq_of_L2]
  unfold shiftGramSum
  rw [← Finset.sum_coe_sort (primesUpTo N)]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp := two_le_of_mem_primesUpTo p
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < (p : ℕ))
  have hlog : 0 ≤ Real.log p := Real.log_nonneg hp1.le
  have hq : 0 ≤ 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]; exact hp1.le
    linarith
  show ‖Real.sqrt (Real.log p * (1 - 1 / (p : ℝ))) • phiL2 hp hg hc‖ ^ 2 = _
  rw [norm_smul, mul_pow, normSq_phiL2, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (mul_nonneg hlog hq)]

/-- **`B_N(g)`**: pole + archimedean block + the total mass defect `θ(N)‖g‖²`. -/
def BNform (N : ℕ) (g : ℝ → ℝ) : ℝ :=
  poleTerm (autocorr g) + archimedeanTerm (autocorr g) + massDefectSum N g

/-- **`OB6At L ⟺ ‖C_N g‖² ≤ B_N(g)`** for all width-`L` tests and all admissible cutoffs `N`. -/
theorem ob6At_iff_contraction (L : ℝ) :
    OB6At L ↔ ∀ g : ℝ → ℝ, ∀ hg : ContDiff ℝ ∞ g, ∀ hc : HasCompactSupport g,
      (∀ y : ℝ, L / 2 < |y| → g y = 0) → ∀ N : ℕ, L < Real.log (N + 1) →
        ‖CN N hg.continuous hc‖ ^ 2 ≤ BNform N g := by
  unfold OB6At
  constructor
  · intro h g hg hc hs N hN
    rw [normSq_CN]
    exact h g hg hc hs N hN
  · intro h g hg hc hs N hN
    have := h g hg hc hs N hN
    rwa [normSq_CN] at this

/-- **One admissible cutoff suffices.** `Q = B_N − ‖C_N g‖²` is independent of `N` (`weilForm_regrouped`),
so `OB6At L` is the contraction inequality at any single admissible `N₀`. -/
theorem ob6At_iff_single_cutoff (L : ℝ) (N₀ : ℕ) (hN₀ : L < Real.log (N₀ + 1)) :
    OB6At L ↔ ∀ g : ℝ → ℝ, ∀ hg : ContDiff ℝ ∞ g, ∀ hc : HasCompactSupport g,
      (∀ y : ℝ, L / 2 < |y| → g y = 0) → ‖CN N₀ hg.continuous hc‖ ^ 2 ≤ BNform N₀ g := by
  rw [ob6At_iff_contraction]
  constructor
  · intro h g hg hc hs
    exact h g hg hc hs N₀ hN₀
  · intro h g hg hc hs N hN
    have h0 := h g hg hc hs
    have e0 := weilForm_regrouped hg.continuous hc hs hN₀
    have e1 := weilForm_regrouped hg.continuous hc hs hN
    rw [normSq_CN] at h0 ⊢
    unfold BNform at h0 ⊢
    linarith

/-- **The operator reading.** Where `B_N ≥ 0`, contractivity is `‖C_N g‖ ≤ √(B_N g)`. -/
theorem contraction_iff_norm_le {N : ℕ} {g : ℝ → ℝ} (hg : Continuous g) (hc : HasCompactSupport g)
    (hB : 0 ≤ BNform N g) : ‖CN N hg hc‖ ^ 2 ≤ BNform N g ↔ ‖CN N hg hc‖ ≤ Real.sqrt (BNform N g) := by
  rw [Real.le_sqrt (norm_nonneg _) hB]

end GppShiftPresentation

#print axioms GppShiftPresentation.normSq_CN
#print axioms GppShiftPresentation.ob6At_iff_contraction
#print axioms GppShiftPresentation.ob6At_iff_single_cutoff
