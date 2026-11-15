/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Daniel Toupin / Golden Physics Project. This seat: Heart of the Cosmos / Grok (GPPDiscovery5).
Audit: Turbo. Branch heart/paritysplit (based on heart/archpd 5fb6c8d).

# Parity split of `SemilocalArchDomAll` (H5, Round 1 with Flint; Turbo 6888439939 item 1)

`P : x ↦ −x`. Every kernel in the `S`-local Weil form (`archTerm`, `primeTermS S`, `poleTerm`) is
even, so on a reflected configuration `(x, −x)` with coefficients `(a, b)` the form splits into a
`P`-even and a `P`-odd block with no cross term. For a configuration `(x, c)` put

* even part `e(x,c)`: points `(x, −x)`, coefficients `(c/2, c/2)`;
* odd part  `o(x,c)`: points `(x, −x)`, coefficients `(c/2, −c/2)`.

Then `kform K (x,c) = kform K e + kform K o` for every even `K` (`kform_even_add_odd`), and the two
rank-one functionals separate by parity: `ℓ_c(e) = ℓ_c(x,c)`, `ℓ_s(e) = 0`, `ℓ_c(o) = 0`,
`ℓ_s(o) = ℓ_s(x,c)`, with `ℓ_c = Σ cᵢ cosh(xᵢ/2)`, `ℓ_s = Σ cᵢ sinh(xᵢ/2)`.

* **Even face** `EvenFace L`: on centered windows `|xᵢ| ≤ L/2` with `ℓ_c = 0`, the `S_L`-prime block
  is `≤` the archimedean block on `e(x,c)`. The pole term vanishes identically there.
* **Odd face** `OddFace L`: on centered windows `|xᵢ| ≤ L/2` (no constraint: `ℓ_c(o) = 0`
  automatically), `prime(o) + 2Ψ(i/2)² ℓ_s² ≤ arch(o)`. The pole burden lives only here.

PROVED: `semilocalArchDomAll_iff_faces : SemilocalArchDomAll ↔ ∀ L > 0, EvenFace L ∧ OddFace L`.
The `←` direction consumes the faces at the enlarged width `W = 2Σ|xᵢ| + L` (a centered window
containing the configuration), and identifies `S_W` with `S_L` on differences `|d| ≤ L` via
`primeTermS_eq` (the `kS_eq_Kpsi` stabilisation). So the `∀ L` quantifier must range over all
widths, as stated.

Honest scope: a reformulation, not a reduction. `SemilocalArchDomAll ↔ HPsi` (PROVED earlier), so
`∀ L, EvenFace L ∧ OddFace L` is H_ψ in two faces. H_ψ, ARP, RH: OPEN.
-/
import GppVerify.RiemannHypothesis.WeilGramContraction

namespace GppWeilGramParity

open GppKreinBridge GppKreinHPsi GppHPsiPlan GppWeilGram GppWeilGramContraction

/-! ### Evenness of the kernels -/

theorem triG_neg (y : ℝ) : triG (-y) = triG y := by
  unfold triG
  rw [abs_neg, neg_sq]

theorem primeTermS_neg (S : Finset ℕ) (d : ℝ) : primeTermS S (-d) = primeTermS S d := by
  unfold primeTermS
  refine tsum_congr fun n => ?_
  split_ifs
  · have h1 : triG (Real.log n + -d) = triG (-Real.log n + d) := by
      rw [← triG_neg]; ring_nf
    have h2 : triG (-Real.log n + -d) = triG (Real.log n + d) := by
      rw [← triG_neg]; ring_nf
    rw [h1, h2, add_comm (triG (-Real.log n + d))]
  · rfl

theorem archTerm_neg (d : ℝ) : archTerm (-d) = archTerm d := by
  unfold archTerm
  congr 1
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [mul_neg, Real.cos_neg]

theorem primeTerm_neg (d : ℝ) : primeTerm (-d) = primeTerm d := by
  unfold primeTerm
  refine tsum_congr fun n => ?_
  have h1 : triG (Real.log n + -d) = triG (-Real.log n + d) := by
    rw [← triG_neg]; ring_nf
  have h2 : triG (-Real.log n + -d) = triG (Real.log n + d) := by
    rw [← triG_neg]; ring_nf
  rw [h1, h2, add_comm (triG (-Real.log n + d))]

/-! ### Reflected configurations -/

/-- Reflected points `(x, −x)`. -/
def reflX {n : ℕ} (x : Fin n → ℝ) : Fin (n + n) → ℝ := Fin.append x (fun i => -x i)

/-- Even-part coefficients `(c/2, c/2)`. -/
noncomputable def evenC {n : ℕ} (c : Fin n → ℝ) : Fin (n + n) → ℝ :=
  Fin.append (fun i => c i / 2) (fun i => c i / 2)

/-- Odd-part coefficients `(c/2, −c/2)`. -/
noncomputable def oddC {n : ℕ} (c : Fin n → ℝ) : Fin (n + n) → ℝ :=
  Fin.append (fun i => c i / 2) (fun i => -(c i / 2))

/-- **PROVED**: Toeplitz form of an even kernel on a reflected configuration. -/
theorem kform_refl {K : ℝ → ℝ} (hK : ∀ d, K (-d) = K d) {n : ℕ} (x a b : Fin n → ℝ) :
    kform K (reflX x) (Fin.append a b) =
      ∑ i, ∑ j, ((a i * a j + b i * b j) * K (x i - x j)
        + (a i * b j + b i * a j) * K (x i + x j)) := by
  unfold kform reflX
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : K (x i - -x j) = K (x i + x j) := by ring_nf
  have e2 : K (-x i - x j) = K (x i + x j) := by
    rw [← hK]; ring_nf
  have e3 : K (-x i - -x j) = K (x i - x j) := by
    rw [← hK]; ring_nf
  rw [e1, e2, e3]
  ring

/-- **PROVED (block split, no cross term)**: `kform K (x,c) = kform K e(x,c) + kform K o(x,c)`
for every even kernel `K`. -/
theorem kform_even_add_odd {K : ℝ → ℝ} (hK : ∀ d, K (-d) = K d) {n : ℕ} (x c : Fin n → ℝ) :
    kform K (reflX x) (evenC c) + kform K (reflX x) (oddC c) = kform K x c := by
  unfold evenC oddC
  rw [kform_refl hK, kform_refl hK, ← Finset.sum_add_distrib]
  unfold kform
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem coshFun_evenC {n : ℕ} (x c : Fin n → ℝ) :
    ∑ i, evenC c i * Real.cosh (reflX x i / 2) = ∑ i, c i * Real.cosh (x i / 2) := by
  unfold evenC reflX
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, neg_div, Real.cosh_neg]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem sinhFun_evenC {n : ℕ} (x c : Fin n → ℝ) :
    ∑ i, evenC c i * Real.sinh (reflX x i / 2) = 0 := by
  unfold evenC reflX
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, neg_div, Real.sinh_neg]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  ring

theorem coshFun_oddC {n : ℕ} (x c : Fin n → ℝ) :
    ∑ i, oddC c i * Real.cosh (reflX x i / 2) = 0 := by
  unfold oddC reflX
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, neg_div, Real.cosh_neg]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  ring

theorem sinhFun_oddC {n : ℕ} (x c : Fin n → ℝ) :
    ∑ i, oddC c i * Real.sinh (reflX x i / 2) = ∑ i, c i * Real.sinh (x i / 2) := by
  unfold oddC reflX
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, neg_div, Real.sinh_neg]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- A centered window `|xᵢ| ≤ L/2` gives reflected differences `≤ L`. -/
theorem reflX_window {n : ℕ} {x : Fin n → ℝ} {L : ℝ} (hx : ∀ i, |x i| ≤ L / 2) :
    ∀ i j, |reflX x i - reflX x j| ≤ L := by
  have key : ∀ k, |reflX x k| ≤ L / 2 := by
    intro k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp only [reflX, Fin.append_left]; exact hx i
    · simp only [reflX, Fin.append_right, abs_neg]; exact hx i
  intro i j
  calc |reflX x i - reflX x j| ≤ |reflX x i| + |reflX x j| := abs_sub _ _
    _ ≤ L / 2 + L / 2 := add_le_add (key i) (key j)
    _ = L := by ring

/-! ### The two faces -/

/-- **Named Prop (OPEN)**: even face at width `L`. -/
def EvenFace (L : ℝ) : Prop :=
  ∀ (n : ℕ) (x c : Fin n → ℝ), (∀ i, |x i| ≤ L / 2) →
    ∑ i, c i * Real.cosh (x i / 2) = 0 →
      kform (primeTermS (primesBelowExp L)) (reflX x) (evenC c) ≤ kform archTerm (reflX x) (evenC c)

/-- **Named Prop (OPEN)**: odd face at width `L` (the pole burden lives here). -/
def OddFace (L : ℝ) : Prop :=
  ∀ (n : ℕ) (x c : Fin n → ℝ), (∀ i, |x i| ≤ L / 2) →
    kform (primeTermS (primesBelowExp L)) (reflX x) (oddC c)
      + 2 * bigPsiI2 ^ 2 * (∑ i, c i * Real.sinh (x i / 2)) ^ 2
        ≤ kform archTerm (reflX x) (oddC c)

/-- **PROVED**: `SemilocalArchDom S_L L` gives the even face at `L`. -/
theorem evenFace_of_archDom {L : ℝ} (h : SemilocalArchDom (primesBelowExp L) L) : EvenFace L := by
  intro n x c hx hc
  have := h (n + n) (reflX x) (evenC c) (reflX_window hx) (by rw [coshFun_evenC]; exact hc)
  rw [sinhFun_evenC] at this
  linarith

/-- **PROVED**: `SemilocalArchDom S_L L` gives the odd face at `L`. -/
theorem oddFace_of_archDom {L : ℝ} (h : SemilocalArchDom (primesBelowExp L) L) : OddFace L := by
  intro n x c hx
  have := h (n + n) (reflX x) (oddC c) (reflX_window hx) (coshFun_oddC x c)
  rwa [sinhFun_oddC] at this

theorem covers_mono {S : Finset ℕ} {L L' : ℝ} (hL : L' ≤ L) (hS : Covers S L) : Covers S L' :=
  fun p hp hlt => hS p hp (hlt.trans_le (Real.exp_le_exp.mpr (by linarith)))

/-- **PROVED (covering step)**: the faces at the enlarged width `W` give `SemilocalArchDom` at `L`
for every window-`L` configuration with `|xᵢ| ≤ W/2`, `W ≥ L`. -/
theorem archDom_of_faces_at {L W : ℝ} (hLW : L ≤ W) (he : EvenFace W) (ho : OddFace W)
    {n : ℕ} (x c : Fin n → ℝ) (hxW : ∀ i, |x i| ≤ W / 2) (hx : ∀ i j, |x i - x j| ≤ L)
    (hc : ∑ i, c i * Real.cosh (x i / 2) = 0) :
    kform (primeTermS (primesBelowExp L)) x c
      + 2 * bigPsiI2 ^ 2 * (∑ i, c i * Real.sinh (x i / 2)) ^ 2 ≤ kform archTerm x c := by
  have hE := he n x c hxW hc
  have hO := ho n x c hxW
  have hP := kform_even_add_odd (primeTermS_neg (primesBelowExp W)) x c
  have hA := kform_even_add_odd archTerm_neg x c
  -- `S_W` and `S_L` agree on differences `|d| ≤ L` (semilocal stabilisation).
  have hSW : kform (primeTermS (primesBelowExp W)) x c = kform (primeTermS (primesBelowExp L)) x c :=
    kform_congr_window (fun d hd => by
      rw [primeTermS_eq (covers_mono hLW (covers_primesBelowExp W)) hd,
        primeTermS_eq (covers_primesBelowExp L) hd]) x c hx
  linarith

/-- **PROVED (H5)**: `SemilocalArchDomAll ↔ ∀ L > 0, EvenFace L ∧ OddFace L`. -/
theorem semilocalArchDomAll_iff_faces :
    SemilocalArchDomAll ↔ ∀ L > 0, EvenFace L ∧ OddFace L := by
  constructor
  · intro h L hL
    exact ⟨evenFace_of_archDom (h L hL), oddFace_of_archDom (h L hL)⟩
  · intro h L hL n x c hx hc
    set T : ℝ := ∑ i, |x i|
    have hT : 0 ≤ T := Finset.sum_nonneg fun i _ => abs_nonneg _
    obtain ⟨he, ho⟩ := h (2 * T + L) (by linarith)
    refine archDom_of_faces_at (by linarith) he ho x c (fun i => ?_) hx hc
    have : |x i| ≤ T := Finset.single_le_sum (f := fun i => |x i|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    linarith

/-- **PROVED**: H_ψ in two faces (reformulation, not a reduction). -/
theorem hPsi_iff_faces : HPsi ↔ ∀ L > 0, EvenFace L ∧ OddFace L :=
  hPsi_iff_semilocalArchDomAll.trans semilocalArchDomAll_iff_faces

end GppWeilGramParity

#print axioms GppWeilGramParity.kform_even_add_odd
#print axioms GppWeilGramParity.archTerm_neg
#print axioms GppWeilGramParity.primeTermS_neg
#print axioms GppWeilGramParity.semilocalArchDomAll_iff_faces
#print axioms GppWeilGramParity.hPsi_iff_faces
