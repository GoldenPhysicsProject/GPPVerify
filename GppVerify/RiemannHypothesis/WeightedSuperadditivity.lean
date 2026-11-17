import GppVerify.RiemannHypothesis.ExpImagRemainder

/-!
# Monotone reweighting preserves superadditivity

GPP's weighted Chebyshev theorem (Turbo relays `3a0b770`, `560639a`) says `V(xy) ≥ V(x) + V(y)` for
`V(x) = Σ_{n ≤ x} Λ(n)/√n`. The *monotone-reweighting falsifier* is a generic order-theoretic fact, proved
here with no number theory:

Let `a : ℕ → ℝ` with `a n ≥ 0`, `A(x) = Σ_{1 ≤ n ≤ x} a n`, and suppose `A` is superadditive in the
multiplicative sense `A x + A y ≤ A (x y)` for `x, y ≥ 1`. If `g ≥ 0` is nondecreasing on `[1, ∞)` and
`A_g(x) = Σ_{1 ≤ n ≤ x} a n · g n`, then for `1 ≤ x ≤ y`

`g(x) · (A(xy) − A(x) − A(y)) ≤ A_g(xy) − A_g(x) − A_g(y)`,

and in particular `A_g` is again superadditive. With `g(n) = cosh(θ log n)`, `θ ≥ 0`, the off-line prime-weight
deformation `Λ(n) cosh(θ log n)` therefore keeps superadditivity (and the sharp gap, scaled by `g(2)`): prime-mass
positivity is **not** an RH discriminator.

**Scope.** `A`'s superadditivity is a *hypothesis* here (it is the Chebyshev theorem, not proved). Nothing about
Λ or primes, and no positivity statement for the Weil form.

No `sorry`, no axiom.
-/

open Finset

noncomputable section

namespace GppReweight

/-- `A_g(x) = Σ_{1 ≤ n ≤ x} a n · g n`. -/
def wsum (a : ℕ → ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ := ∑ n ∈ Ioc 0 ⌊x⌋₊, a n * g n

/-- `A(x) = Σ_{1 ≤ n ≤ x} a n`. -/
def csum (a : ℕ → ℝ) (x : ℝ) : ℝ := ∑ n ∈ Ioc 0 ⌊x⌋₊, a n

theorem csum_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (x : ℝ) : 0 ≤ csum a x :=
  Finset.sum_nonneg fun n _ => ha n

/-- `A_g(x) ≤ g(x) A(x)` for `x ≥ 1` and `g` nondecreasing on `[1, ∞)`. -/
theorem wsum_le {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {g : ℝ → ℝ} (hg : MonotoneOn g (Set.Ici 1))
    {x : ℝ} (hx : 1 ≤ x) : wsum a g x ≤ g x * csum a x := by
  unfold wsum csum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hn).1
  have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff (by linarith)).mp (Finset.mem_Ioc.mp hn).2
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have := hg (Set.mem_Ici.mpr hn1') (Set.mem_Ici.mpr hx) hnx
  nlinarith [ha n]

/-- `A_g(xy) − A_g(y) ≥ g(y) (A(xy) − A(y))` for `x, y ≥ 1`. -/
theorem wsum_tail_ge {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {g : ℝ → ℝ} (hg : MonotoneOn g (Set.Ici 1))
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    g y * (csum a (x * y) - csum a y) ≤ wsum a g (x * y) - wsum a g y := by
  have hxy : y ≤ x * y := by nlinarith
  have hfl : ⌊y⌋₊ ≤ ⌊x * y⌋₊ := Nat.floor_le_floor hxy
  have hs1 := Finset.sum_Ioc_consecutive (fun n => a n * g n) (Nat.zero_le ⌊y⌋₊) hfl
  have hs2 := Finset.sum_Ioc_consecutive (fun n => a n) (Nat.zero_le ⌊y⌋₊) hfl
  unfold wsum csum
  rw [← hs1, ← hs2]
  have : g y * ((∑ n ∈ Ioc 0 ⌊y⌋₊, a n + ∑ n ∈ Ioc ⌊y⌋₊ ⌊x * y⌋₊, a n) - ∑ n ∈ Ioc 0 ⌊y⌋₊, a n) =
      ∑ n ∈ Ioc ⌊y⌋₊ ⌊x * y⌋₊, g y * a n := by
    rw [add_sub_cancel_left, Finset.mul_sum]
  rw [this]
  have : (∑ n ∈ Ioc 0 ⌊y⌋₊, a n * g n + ∑ n ∈ Ioc ⌊y⌋₊ ⌊x * y⌋₊, a n * g n) -
      ∑ n ∈ Ioc 0 ⌊y⌋₊, a n * g n = ∑ n ∈ Ioc ⌊y⌋₊ ⌊x * y⌋₊, a n * g n := by ring
  rw [this]
  refine Finset.sum_le_sum fun n hn => ?_
  have hnl : ⌊y⌋₊ < n := (Finset.mem_Ioc.mp hn).1
  have hny : y < (n : ℝ) := by
    have := Nat.lt_floor_add_one y
    have h2 : (⌊y⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hnl
    linarith
  have hn1' : (1 : ℝ) ≤ n := by linarith
  have := hg (Set.mem_Ici.mpr hy) (Set.mem_Ici.mpr hn1') hny.le
  nlinarith [ha n]

/-- **Quantitative reweighting inequality.** For `1 ≤ x ≤ y`, if `A` is superadditive then
`g(x) (A(xy) − A(x) − A(y)) ≤ A_g(xy) − A_g(x) − A_g(y)`. -/
theorem reweight_gap {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {g : ℝ → ℝ} (hg : MonotoneOn g (Set.Ici 1))
    (hA : ∀ x y : ℝ, 1 ≤ x → 1 ≤ y → csum a x + csum a y ≤ csum a (x * y))
    {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    g x * (csum a (x * y) - csum a x - csum a y) ≤
      wsum a g (x * y) - wsum a g x - wsum a g y := by
  have hy : 1 ≤ y := hx.trans hxy
  have hD : 0 ≤ csum a (x * y) - csum a x - csum a y := by
    have := hA x y hx hy; linarith
  have h1 := wsum_tail_ge ha hg hx hy
  have h2 := wsum_le ha hg hx
  have hgxy : g x ≤ g y := hg (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hy) hxy
  have hAx := csum_nonneg ha x
  have hAhyp := hA x y hx hy
  nlinarith [mul_nonneg (sub_nonneg.mpr hgxy) hAx, mul_nonneg (sub_nonneg.mpr hgxy) hD]

/-- **Superadditivity is preserved** by monotone reweighting. -/
theorem reweight_superadditive {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {g : ℝ → ℝ}
    (hg : MonotoneOn g (Set.Ici 1)) (hgn : ∀ x, 1 ≤ x → 0 ≤ g x)
    (hA : ∀ x y : ℝ, 1 ≤ x → 1 ≤ y → csum a x + csum a y ≤ csum a (x * y))
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    wsum a g x + wsum a g y ≤ wsum a g (x * y) := by
  have hD : ∀ u v : ℝ, 1 ≤ u → 1 ≤ v → 0 ≤ csum a (u * v) - csum a u - csum a v := fun u v hu hv => by
    have := hA u v hu hv; linarith
  rcases le_total x y with h | h
  · have := reweight_gap ha hg hA hx h
    have := mul_nonneg (hgn x hx) (hD x y hx hy)
    linarith
  · have := reweight_gap ha hg hA hy h
    have hc : y * x = x * y := mul_comm y x
    rw [hc] at this
    have h3 := mul_nonneg (hgn y hy) (hD y x hy hx)
    rw [hc] at h3
    linarith

/-- `x ↦ cosh(θ log x)` is nondecreasing and nonnegative on `[1, ∞)` for `θ ≥ 0`: the off-line
prime-weight deformation `Λ(n) cosh(θ log n)`. -/
theorem cosh_log_monotoneOn {θ : ℝ} (hθ : 0 ≤ θ) :
    MonotoneOn (fun x : ℝ => Real.cosh (θ * Real.log x)) (Set.Ici 1) := by
  intro u hu v hv huv
  have hu1 : (1 : ℝ) ≤ u := hu
  have h0 : 0 ≤ θ * Real.log u := mul_nonneg hθ (Real.log_nonneg hu1)
  have h1 : θ * Real.log u ≤ θ * Real.log v :=
    mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) huv) hθ
  simp only
  exact Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg h0, abs_of_nonneg (h0.trans h1)]; exact h1)

theorem cosh_log_nonneg (θ x : ℝ) : 0 ≤ Real.cosh (θ * Real.log x) := (Real.cosh_pos _).le

end GppReweight

#print axioms GppReweight.reweight_gap
#print axioms GppReweight.reweight_superadditive
#print axioms GppReweight.cosh_log_monotoneOn
