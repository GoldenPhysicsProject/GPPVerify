import GppVerify.QuantumGravity.SpectralWeightIdentities
import GppVerify.QuantumGravity.Digamma
import GppVerify.RiemannHypothesis.ConvolutionSquarePositive
import GppVerify.RiemannHypothesis.HeatTraceCriterion
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The positive Gamma--Plancherel defect: spectral-density and Gram layer

This file formalizes the positive-kernel core of Theorem 62.1 in Toupin's
`arithmetic_principal_series_RH_program-34.tex`.  For `x > 0`, the real-place density

```text
  exp (-q x) / (1 - exp (-2 x))
```

is exactly the celestial principal-series density

```text
  exp (-(q - 1) x) * P (x / pi) / (2 x),
  P lam = pi * lam / sinh (pi * lam).
```

Multiplying this positive density by
`(1 - exp (-a x)) (1 - exp (-b x))` gives a rank-one feature kernel at every `x > 0`.
Consequently every finite Gram matrix is positive semidefinite, pointwise and after any
integral for which the pairwise entries are integrable.  Compact truncations
`x in [eps, R]`, `eps > 0`, satisfy the integrability hypothesis automatically.

There is also an exact infinite family on which the Gamma side can be identified without
developing the general digamma integral representation.  If `q > 0` and
`a = 2m`, `b = 2n` for natural `m,n`, the digamma functional equation and the finite
geometric-series identity give

```text
  gammaDefect q (2m) (2n)
    = integral_0^infinity defectIntegrand q (2m) (2n)
    = sum_{k<n} (1/(q+2k) - 1/(q+2m+2k)).
```

This proves integrability, nonnegativity (strict for `m,n > 0`), and finite Gram
positivity for the actual four-term Gamma defect on the entire even-natural shift lattice.

## Deliberate boundary

For arbitrary positive real shifts `a,b`, the paper identifies the full integral with the
same four-term logarithmic derivative of `Gamma`.  The repo defines real digamma from
Mathlib's Gamma derivative, but Mathlib has no general digamma integral representation at
the pinned revision.  That arbitrary-real bridge is therefore **not** asserted here.
It is proved exactly on `a,b in 2 * Nat` as described above; off that lattice the
Plancherel-density/Gram layer is complete while the digamma identification remains the
precise, auditable target.  No new axiom is introduced.
-/

namespace GppGammaPlancherel

open MeasureTheory Set Finset
open GppStefanBoltzmann

/-- The real-place density occurring in the Gamma--Plancherel defect. -/
noncomputable def density (q x : ℝ) : ℝ :=
  Real.exp (-(q * x)) / (1 - Real.exp (-(2 * x)))

/-- The real feature attached to a shift parameter `a`. -/
noncomputable def feature (a x : ℝ) : ℝ :=
  1 - Real.exp (-(a * x))

/-- The rank-one defect integrand at spectral parameter `x`. -/
noncomputable def defectIntegrand (q a b x : ℝ) : ℝ :=
  density q x * (feature a x * feature b x)

/-- The full positive-kernel candidate on `(0, infinity)`. -/
noncomputable def defectKernel (q a b : ℝ) : ℝ :=
  ∫ x : ℝ in Ioi (0 : ℝ), defectIntegrand q a b x

/-- The compactly truncated defect kernel.  Unlike the full kernel, its integrability is
automatic once `0 < eps`. -/
noncomputable def truncatedDefectKernel (q eps R a b : ℝ) : ℝ :=
  ∫ x : ℝ in Icc eps R, defectIntegrand q a b x

/-- The paper's Archimedean logarithmic derivative
`g_infinity(q) = -log(pi)/2 + digamma(q/2)/2`. -/
noncomputable def archimedeanG (q : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * Real.log Real.pi + (1 / 2 : ℝ) * GppDigamma.digamma (q / 2)

/-- The four-term Gamma defect from Theorem 62.1. -/
noncomputable def gammaDefect (q a b : ℝ) : ℝ :=
  archimedeanG (q + a) + archimedeanG (q + b) - archimedeanG q -
    archimedeanG (q + a + b)

/-- The finite resolvent sum produced by an even natural shift. -/
noncomputable def evenShiftSum (q : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, 1 / (q + 2 * (k : ℝ))

/-- The finite positive resolvent difference for even shifts `2m, 2n`. -/
noncomputable def evenShiftDefectSum (q : ℝ) (m n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    (1 / (q + 2 * (k : ℝ)) - 1 / (q + 2 * (m : ℝ) + 2 * (k : ℝ)))

/-- The finite exponential sum whose Laplace transform is `evenShiftDefectSum`. -/
noncomputable def evenShiftExpSum (q : ℝ) (m n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n,
    (Real.exp (-((q + 2 * (k : ℝ)) * x)) -
      Real.exp (-((q + 2 * (m : ℝ) + 2 * (k : ℝ)) * x)))

/-- Iterating the digamma functional equation on the positive half-line. -/
theorem digamma_add_nat {x : ℝ} (hx : 0 < x) (n : ℕ) :
    GppDigamma.digamma (x + n) = GppDigamma.digamma x +
      ∑ k ∈ Finset.range n, 1 / (x + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hxn : 0 < x + (n : ℝ) := add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg n)
      have hpoles : ∀ m : ℕ, x + (n : ℝ) ≠ -(m : ℝ) := by
        intro m h
        have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
      calc
        GppDigamma.digamma (x + (n.succ : ℝ)) =
            GppDigamma.digamma ((x + (n : ℝ)) + 1) := by
              congr 1
              push_cast
              ring
        _ = GppDigamma.digamma (x + (n : ℝ)) + 1 / (x + (n : ℝ)) :=
          GppDigamma.digamma_add_one hpoles
        _ = GppDigamma.digamma x +
            ∑ k ∈ Finset.range n.succ, 1 / (x + k) := by
              rw [ih, Finset.sum_range_succ]
              ring

/-- An even shift of `g_infinity` is a finite sum of resolvents with spacing `2`. -/
theorem archimedeanG_add_two_nat {q : ℝ} (hq : 0 < q) (n : ℕ) :
    archimedeanG (q + 2 * n) = archimedeanG q + evenShiftSum q n := by
  have hq2 : 0 < q / 2 := by positivity
  have hd := digamma_add_nat hq2 n
  have harg : q / 2 + (n : ℝ) = (q + 2 * (n : ℝ)) / 2 := by ring
  rw [harg] at hd
  unfold archimedeanG evenShiftSum
  rw [hd]
  have hsum :
      (1 / 2 : ℝ) * (∑ k ∈ Finset.range n, 1 / (q / 2 + (k : ℝ))) =
        ∑ k ∈ Finset.range n, 1 / (q + 2 * (k : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hden₁ : q / 2 + (k : ℝ) ≠ 0 := by positivity
    have hden₂ : q + 2 * (k : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [mul_add, hsum]
  ring

/-- **Exact Gamma defect for even shifts.**  The four-term digamma expression collapses
to a finite sum of positive resolvent differences. -/
theorem gammaDefect_even_eq_sum {q : ℝ} (hq : 0 < q) (m n : ℕ) :
    gammaDefect q (2 * (m : ℝ)) (2 * (n : ℝ)) = evenShiftDefectSum q m n := by
  have hqm : 0 < q + 2 * (m : ℝ) := by positivity
  have hm := archimedeanG_add_two_nat hq m
  have hn := archimedeanG_add_two_nat hq n
  have hmn := archimedeanG_add_two_nat hqm n
  unfold gammaDefect
  rw [hm, hn]
  have hlast :
      archimedeanG (q + 2 * (m : ℝ) + 2 * (n : ℝ)) =
        archimedeanG (q + 2 * (m : ℝ)) + evenShiftSum (q + 2 * (m : ℝ)) n := by
    exact hmn
  rw [hlast]
  rw [hm]
  have hshift : evenShiftSum (q + 2 * (m : ℝ)) n =
      ∑ k ∈ Finset.range n, 1 / (q + 2 * (m : ℝ) + 2 * (k : ℝ)) := by
    unfold evenShiftSum
    apply Finset.sum_congr rfl
    intro k _
    congr 2
  rw [hshift]
  unfold evenShiftDefectSum evenShiftSum
  rw [Finset.sum_sub_distrib]
  ring

/-- For even natural shifts, the denominator cancels by a finite geometric sum.  This is
the pointwise bridge from the paper's integral kernel to a finite Laplace sum. -/
theorem defectIntegrand_even_eq_expSum (q : ℝ) (m n : ℕ) {x : ℝ} (hx : 0 < x) :
    defectIntegrand q (2 * (m : ℝ)) (2 * (n : ℝ)) x = evenShiftExpSum q m n x := by
  let z : ℝ := Real.exp (-(2 * x))
  have hzlt : z < 1 := by
    dsimp [z]
    rw [Real.exp_lt_one_iff]
    linarith
  have hz : z ≠ 1 := ne_of_lt hzlt
  have hpow (r : ℕ) :
      Real.exp (-((2 * (r : ℝ)) * x)) = z ^ r := by
    dsimp [z]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hgeom : (1 - z ^ n) / (1 - z) = ∑ k ∈ Finset.range n, z ^ k := by
    have h := geom_sum_eq hz n
    rw [h]
    have hden : z - 1 ≠ 0 := sub_ne_zero.mpr hz
    have hden' : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
    field_simp [hden, hden']
    ring
  have hterm (k : ℕ) :
      Real.exp (-(q * x)) * z ^ k * (1 - z ^ m) =
        Real.exp (-((q + 2 * (k : ℝ)) * x)) -
          Real.exp (-((q + 2 * (m : ℝ) + 2 * (k : ℝ)) * x)) := by
    have hk : z ^ k = Real.exp (-((2 * (k : ℝ)) * x)) := (hpow k).symm
    have hm : z ^ m = Real.exp (-((2 * (m : ℝ)) * x)) := (hpow m).symm
    have hfirst : Real.exp (-(q * x)) * z ^ k =
        Real.exp (-((q + 2 * (k : ℝ)) * x)) := by
      rw [hk, ← Real.exp_add]
      congr 1
      ring
    have hsecond : Real.exp (-(q * x)) * z ^ k * z ^ m =
        Real.exp (-((q + 2 * (m : ℝ) + 2 * (k : ℝ)) * x)) := by
      rw [hk, hm, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [mul_sub, mul_one, hsecond, hfirst]
  unfold defectIntegrand density feature evenShiftExpSum
  rw [hpow m, hpow n]
  change Real.exp (-(q * x)) / (1 - z) * ((1 - z ^ m) * (1 - z ^ n)) = _
  calc
    Real.exp (-(q * x)) / (1 - z) * ((1 - z ^ m) * (1 - z ^ n)) =
        Real.exp (-(q * x)) * (1 - z ^ m) * ((1 - z ^ n) / (1 - z)) := by
          field_simp [sub_ne_zero.mpr (ne_of_gt hzlt)]
          ring
    _ = Real.exp (-(q * x)) * (1 - z ^ m) *
        (∑ k ∈ Finset.range n, z ^ k) := by rw [hgeom]
    _ = ∑ k ∈ Finset.range n, Real.exp (-(q * x)) * z ^ k * (1 - z ^ m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ k ∈ Finset.range n,
        (Real.exp (-((q + 2 * (k : ℝ)) * x)) -
          Real.exp (-((q + 2 * (m : ℝ) + 2 * (k : ℝ)) * x))) := by
      apply Finset.sum_congr rfl
      intro k _
      exact hterm k

/-- The exponential resolvent mode in the parenthesized convention used in this file is
integrable on `(0, infinity)`. -/
theorem exp_resolvent_integrable {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => Real.exp (-(c * x))) (Ioi (0 : ℝ)) := by
  simpa only [neg_mul] using exp_neg_integrableOn_Ioi 0 hc

/-- The finite exponential sum for positive `q` is integrable on `(0, infinity)`. -/
theorem evenShiftExpSum_integrable {q : ℝ} (hq : 0 < q) (m n : ℕ) :
    IntegrableOn (evenShiftExpSum q m n) (Ioi (0 : ℝ)) := by
  unfold evenShiftExpSum
  refine integrable_finset_sum (Finset.range n) ?_
  intro k _
  have h₁ : 0 < q + 2 * (k : ℝ) := by positivity
  have h₂ : 0 < q + 2 * (m : ℝ) + 2 * (k : ℝ) := by positivity
  exact (exp_resolvent_integrable h₁).sub (exp_resolvent_integrable h₂)

/-- Even natural shifts make the full defect integrand integrable; the apparent endpoint
singularity has canceled into a finite sum before integration. -/
theorem defectIntegrand_even_integrable {q : ℝ} (hq : 0 < q) (m n : ℕ) :
    IntegrableOn (defectIntegrand q (2 * (m : ℝ)) (2 * (n : ℝ))) (Ioi (0 : ℝ)) := by
  exact (evenShiftExpSum_integrable hq m n).congr_fun
    (fun x hx => (defectIntegrand_even_eq_expSum q m n hx).symm) measurableSet_Ioi

/-- The full Plancherel integral for even shifts evaluates to the same finite resolvent
difference as the digamma defect. -/
theorem defectKernel_even_eq_sum {q : ℝ} (hq : 0 < q) (m n : ℕ) :
    defectKernel q (2 * (m : ℝ)) (2 * (n : ℝ)) = evenShiftDefectSum q m n := by
  unfold defectKernel
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun x hx => defectIntegrand_even_eq_expSum q m n hx)]
  unfold evenShiftExpSum evenShiftDefectSum
  have htermInt (k : ℕ) : IntegrableOn
      (fun x : ℝ => Real.exp (-((q + 2 * (k : ℝ)) * x)) -
        Real.exp (-((q + 2 * (m : ℝ) + 2 * (k : ℝ)) * x))) (Ioi (0 : ℝ)) := by
    have h₁ : 0 < q + 2 * (k : ℝ) := by positivity
    have h₂ : 0 < q + 2 * (m : ℝ) + 2 * (k : ℝ) := by positivity
    exact (exp_resolvent_integrable h₁).sub (exp_resolvent_integrable h₂)
  rw [integral_finset_sum (Finset.range n) (fun k _ => htermInt k)]
  apply Finset.sum_congr rfl
  intro k _
  have h₁ : 0 < q + 2 * (k : ℝ) := by positivity
  have h₂ : 0 < q + 2 * (m : ℝ) + 2 * (k : ℝ) := by positivity
  rw [integral_sub (exp_resolvent_integrable h₁) (exp_resolvent_integrable h₂)]
  rw [GppHeatTrace.resolvent_laplace h₁, GppHeatTrace.resolvent_laplace h₂]

/-- **Exact even-shift slice of Theorem 62.1.**  For positive `q` and shifts in
`2 * Nat`, the four-term logarithmic derivative of `Gamma` equals the full
Gamma--Plancherel integral, with no analytic side hypothesis. -/
theorem gammaDefect_even_eq_kernel {q : ℝ} (hq : 0 < q) (m n : ℕ) :
    gammaDefect q (2 * (m : ℝ)) (2 * (n : ℝ)) =
      defectKernel q (2 * (m : ℝ)) (2 * (n : ℝ)) := by
  calc
    gammaDefect q (2 * (m : ℝ)) (2 * (n : ℝ)) = evenShiftDefectSum q m n :=
      gammaDefect_even_eq_sum hq m n
    _ = defectKernel q (2 * (m : ℝ)) (2 * (n : ℝ)) :=
      (defectKernel_even_eq_sum hq m n).symm

/-- The finite even-shift resolvent defect is nonnegative. -/
theorem evenShiftDefectSum_nonneg {q : ℝ} (hq : 0 < q) (m n : ℕ) :
    0 ≤ evenShiftDefectSum q m n := by
  unfold evenShiftDefectSum
  apply Finset.sum_nonneg
  intro k _
  have hu : 0 < q + 2 * (k : ℝ) := by positivity
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have huv : q + 2 * (k : ℝ) ≤ q + 2 * (m : ℝ) + 2 * (k : ℝ) := by linarith
  have hrecip := one_div_le_one_div_of_le hu huv
  linarith

/-- The finite even-shift defect is strictly positive when both shifts are nonzero. -/
theorem evenShiftDefectSum_pos {q : ℝ} (hq : 0 < q) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) : 0 < evenShiftDefectSum q m n := by
  unfold evenShiftDefectSum
  apply Finset.sum_pos
  · intro k _
    have hu : 0 < q + 2 * (k : ℝ) := by positivity
    have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    have huv : q + 2 * (k : ℝ) < q + 2 * (m : ℝ) + 2 * (k : ℝ) := by linarith
    have hrecip := one_div_lt_one_div_of_lt hu huv
    linarith
  · exact ⟨0, Finset.mem_range.mpr hn⟩

/-- The Gamma defect is nonnegative on all positive even-natural shifts. -/
theorem gammaDefect_even_nonneg {q : ℝ} (hq : 0 < q) (m n : ℕ) :
    0 ≤ gammaDefect q (2 * (m : ℝ)) (2 * (n : ℝ)) := by
  rw [gammaDefect_even_eq_sum hq m n]
  exact evenShiftDefectSum_nonneg hq m n

/-- The Gamma defect is strictly positive when both even-natural shifts are nonzero. -/
theorem gammaDefect_even_pos {q : ℝ} (hq : 0 < q) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) :
    0 < gammaDefect q (2 * (m : ℝ)) (2 * (n : ℝ)) := by
  rw [gammaDefect_even_eq_sum hq m n]
  exact evenShiftDefectSum_pos hq hm hn

/-- The real-place density is strictly positive away from the endpoint `x = 0`. -/
theorem density_pos (q : ℝ) {x : ℝ} (hx : 0 < x) : 0 < density q x := by
  unfold density
  have hden : Real.exp (-(2 * x)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  exact div_pos (Real.exp_pos _) (sub_pos.mpr hden)

/-- A positive shift gives a strictly positive feature for `x > 0`. -/
theorem feature_pos {a x : ℝ} (ha : 0 < a) (hx : 0 < x) : 0 < feature a x := by
  unfold feature
  have hax : 0 < a * x := mul_pos ha hx
  have hexp : Real.exp (-(a * x)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  linarith

/-- The defect integrand is strictly positive for positive parameters. -/
theorem defectIntegrand_pos {q a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    0 < defectIntegrand q a b x := by
  unfold defectIntegrand
  exact mul_pos (density_pos q hx) (mul_pos (feature_pos ha hx) (feature_pos hb hx))

/-- The elementary denominator identity behind the Plancherel rewriting. -/
theorem one_sub_exp_neg_two_mul (x : ℝ) :
    1 - Real.exp (-(2 * x)) = 2 * Real.exp (-x) * Real.sinh x := by
  rw [Real.sinh_eq]
  have h₁ : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]
    simp
  have h₂ : Real.exp (-x) * Real.exp (-x) = Real.exp (-(2 * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    1 - Real.exp (-(2 * x)) =
        Real.exp (-x) * Real.exp x - Real.exp (-x) * Real.exp (-x) := by
          rw [h₁, h₂]
    _ = 2 * Real.exp (-x) * ((Real.exp x - Real.exp (-x)) / 2) := by ring

/-- **Exact real-place/celestial density identity.**  The density in the paper's
Gamma defect is the existing principal-series weight `P` at `lambda = x / pi`, with the
expected exponential tilt. -/
theorem density_eq_spectralWeight (q : ℝ) {x : ℝ} (hx : 0 < x) :
    density q x =
      Real.exp (-((q - 1) * x)) * P (x / Real.pi) / (2 * x) := by
  have hx0 : x ≠ 0 := hx.ne'
  have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsinh0 : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx0
  have hexp0 : Real.exp (-x) ≠ 0 := Real.exp_ne_zero _
  have hnum : Real.exp (-(q * x)) =
      Real.exp (-((q - 1) * x)) * Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpi : Real.pi * (x / Real.pi) = x := by
    field_simp
  unfold density P
  rw [hnum, one_sub_exp_neg_two_mul, hpi]
  field_simp
  ring

/-- Symmetry in the two shift parameters. -/
theorem defectIntegrand_comm (q a b x : ℝ) :
    defectIntegrand q a b x = defectIntegrand q b a x := by
  unfold defectIntegrand
  ring

/-- The integrand is a positive weight times one real rank-one feature product. -/
theorem pointwise_gram_nonneg {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ)
    (q : ℝ) {x : ℝ} (hx : 0 < x) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      ((starRingEnd ℂ) (c i) * c j).re * defectIntegrand q (a i) (a j) x := by
  have hfactor :
      ∑ i : Fin n, ∑ j : Fin n,
          ((starRingEnd ℂ) (c i) * c j).re * defectIntegrand q (a i) (a j) x =
        density q x *
          ∑ i : Fin n, ∑ j : Fin n,
            ((starRingEnd ℂ) (c i) * c j).re *
              (feature (a i) x * feature (a j) x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    unfold defectIntegrand
    ring
  rw [hfactor]
  exact mul_nonneg (density_pos q hx).le
    (GppHaarPositivityWeil.gram_square_nonneg c (fun i => feature (a i) x))

/-- The defect integrand is continuous on the open half-line. -/
theorem defectIntegrand_continuousOn_Ioi (q a b : ℝ) :
    ContinuousOn (defectIntegrand q a b) (Ioi (0 : ℝ)) := by
  have hnum : Continuous fun x : ℝ => Real.exp (-(q * x)) := by fun_prop
  have hden : Continuous fun x : ℝ => 1 - Real.exp (-(2 * x)) := by fun_prop
  have hdensity : ContinuousOn (density q) (Ioi (0 : ℝ)) := by
    intro x hx
    have hxpos : 0 < x := hx
    unfold density
    exact hnum.continuousAt.continuousWithinAt.div
      hden.continuousAt.continuousWithinAt
      (sub_ne_zero.mpr (ne_of_gt (by
        rw [Real.exp_lt_one_iff]
        linarith)))
  have hfeature (u : ℝ) : Continuous fun x : ℝ => feature u x := by
    unfold feature
    fun_prop
  unfold defectIntegrand
  exact hdensity.mul ((hfeature a).continuousOn.mul (hfeature b).continuousOn)

/-- Compact truncations of every pairwise entry are integrable. -/
theorem truncated_integrable {eps R : ℝ} (heps : 0 < eps) (q a b : ℝ) :
    IntegrableOn (defectIntegrand q a b) (Icc eps R) := by
  have hsub : Icc eps R ⊆ Ioi (0 : ℝ) := by
    intro x hx
    exact lt_of_lt_of_le heps hx.1
  exact (defectIntegrand_continuousOn_Ioi q a b).mono hsub |>.integrableOn_Icc

/-- Integrating the rank-one features preserves finite Gram positivity whenever the
pairwise entries are integrable on the chosen measurable set. -/
theorem integral_gram_nonneg {s : Set ℝ} (hs : MeasurableSet s) {n : ℕ}
    (c : Fin n → ℂ) (a : Fin n → ℝ) (q : ℝ)
    (hInt : ∀ i j : Fin n, IntegrableOn (defectIntegrand q (a i) (a j)) s)
    (hspos : ∀ x ∈ s, 0 < x) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      ((starRingEnd ℂ) (c i) * c j).re *
        (∫ x : ℝ in s, defectIntegrand q (a i) (a j) x) := by
  have hint : ∀ i j : Fin n,
      IntegrableOn
        (fun x => ((starRingEnd ℂ) (c i) * c j).re *
          defectIntegrand q (a i) (a j) x) s :=
    fun i j => (hInt i j).const_mul _
  have hswap :
      ∑ i : Fin n, ∑ j : Fin n,
          ((starRingEnd ℂ) (c i) * c j).re *
            (∫ x : ℝ in s, defectIntegrand q (a i) (a j) x) =
        ∫ x : ℝ in s, ∑ i : Fin n, ∑ j : Fin n,
          ((starRingEnd ℂ) (c i) * c j).re *
            defectIntegrand q (a i) (a j) x := by
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro j _
        rw [integral_const_mul]
      · exact fun j _ => hint i j
    · exact fun i _ => integrable_finset_sum _ fun j _ => hint i j
  rw [hswap]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem hs] with x hx
  exact pointwise_gram_nonneg c a q (hspos x hx)

/-- The full Gamma--Plancherel integral kernel is positive semidefinite under the one
remaining analytic side condition: integrability of each requested pairwise entry. -/
theorem defectKernel_gram_nonneg {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) (q : ℝ)
    (hInt : ∀ i j : Fin n,
      IntegrableOn (defectIntegrand q (a i) (a j)) (Ioi (0 : ℝ))) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      ((starRingEnd ℂ) (c i) * c j).re * defectKernel q (a i) (a j) := by
  unfold defectKernel
  exact integral_gram_nonneg measurableSet_Ioi c a q hInt (fun _ hx => hx)

/-- On the even-natural shift lattice the full integral Gram matrix is unconditionally
positive semidefinite: the geometric cancellation theorem supplies every integrability
hypothesis required by `defectKernel_gram_nonneg`. -/
theorem defectKernel_even_gram_nonneg {N : ℕ} (c : Fin N → ℂ) (m : Fin N → ℕ)
    {q : ℝ} (hq : 0 < q) :
    0 ≤ ∑ i : Fin N, ∑ j : Fin N,
      ((starRingEnd ℂ) (c i) * c j).re *
        defectKernel q (2 * (m i : ℝ)) (2 * (m j : ℝ)) := by
  exact defectKernel_gram_nonneg c (fun i => 2 * (m i : ℝ)) q
    (fun i j => defectIntegrand_even_integrable hq (m i) (m j))

/-- **Finite Gram positivity for the actual Gamma defect on the even-natural lattice.**
This is the positive-definite conclusion of Theorem 62.1 on a nontrivial infinite family
of shifts, now with the digamma and integral sides identified exactly. -/
theorem gammaDefect_even_gram_nonneg {N : ℕ} (c : Fin N → ℂ) (m : Fin N → ℕ)
    {q : ℝ} (hq : 0 < q) :
    0 ≤ ∑ i : Fin N, ∑ j : Fin N,
      ((starRingEnd ℂ) (c i) * c j).re *
        gammaDefect q (2 * (m i : ℝ)) (2 * (m j : ℝ)) := by
  simpa only [gammaDefect_even_eq_kernel hq] using defectKernel_even_gram_nonneg c m hq

/-- Every compact truncation `[eps, R]`, `eps > 0`, is unconditionally positive
semidefinite. -/
theorem truncatedDefectKernel_gram_nonneg {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ)
    (q eps R : ℝ) (heps : 0 < eps) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      ((starRingEnd ℂ) (c i) * c j).re *
        truncatedDefectKernel q eps R (a i) (a j) := by
  unfold truncatedDefectKernel
  apply integral_gram_nonneg measurableSet_Icc c a q
  · intro i j
    exact truncated_integrable heps q (a i) (a j)
  · intro x hx
    exact lt_of_lt_of_le heps hx.1

/-- Positive shifts make each full defect entry nonnegative.  This scalar fact does not
need a separate integrability hypothesis: Mathlib's integral is `0` when nonintegrable,
and otherwise it is the integral of a nonnegative function. -/
theorem defectKernel_nonneg {q a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ defectKernel q a b := by
  unfold defectKernel
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (defectIntegrand_pos ha hb hx).le

end GppGammaPlancherel
