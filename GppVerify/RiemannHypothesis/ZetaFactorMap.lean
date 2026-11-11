import GppVerify.RiemannHypothesis.KernelTheory
import GppVerify.RiemannHypothesis.GlobalWeilPlaces

/-!
# The factor-map form of the ζ obligation: class (9) and Completed Graph Contractivity

Turbo, GPP-bridge PR #11 issuecomment-6806968693, item 2. Source: Astra,
`work/2026-11-11_astra_completed_kernel_local_factor_obstruction.md` (Branch B), §4–§5.

`GppKernelTheory.ZetaReflectionPositivityObligation` (reflection positivity of the ζ datum,
equivalent to ARP by `zeta_obligation_iff_arp`) is typed here in its factor-map form.

1. **Places and local completed forms.** `Place = Option Nat.Primes` (`none` = ∞). The local
   form of a place on a real test `f` is the in-tree per-place piece of the Weil form
   (`GlobalTate.Weil`, GW1): at ∞ the completion (pole) term plus the gamma term, at `p` the
   prime-`p` power sum `W_fin p`. Each uses only the Euler factor (or completion datum) of
   that place.
2. **Class (9)** (`LocalClass9Factor`, `PlacewiseClass9Factor`): Astra's class of local positive
   factors up to finite-dimensional repair: on window-`R` tests obeying finitely many linear
   constraints, `Q_v(f) = ‖A f‖² + B(λ f, λ f)` with `A` into a real Hilbert space and `λ` of
   finite rank. Astra's Theorem 3 (infinite negative index at one prime) says this class is
   empty at every finite place on windows that see `log p`: paper level, not in Lean (GAP).
3. **Astra's equations (5), (7), (14), as filed** (Turbo 6807126815: Flint cleared all three
   audit flags; the Prop 2 sign/power, the Theorem 5 constant `√(2w)`, and the archimedean
   P/C assignment are correct as written). Concretely in Lean:
   * (5) `completion_signature`: `L₊(f)L₋(g) + L₋(f)L₊(g) = L_c(f)L_c(g) - L_s(f)L_s(g)`,
     `L_± f = ∫ f(u) e^{±u/2} du`, `L_c = (L₊+L₋)/√2`, `L_s = (L₊-L₋)/√2`.
   * (7) `primeP`, `primeC`: `(P f)(u) = √(w/2)[f(u) - f(u+a)]`, `(C f)(u) = √(w/2)[f(u) + f(u+a)]`
     on `I_{R,a} = [-R, R-a]`, `w_{p,k} = (log p) p^{-k/2}`, `a_{p,k} = k log p`.
     `prime_channel_signed` (Prop 2, one channel, as filed):
     `∫_I (Pf)² - ∫_I (Cf)² = -w [q(a) + q(-a)]` with `q = autocorr f`, for `f ∈ 𝒟_R`.
   * (14) `first_window_eq14`: for `2R < log 3`, `a = log 2`, `w = w_{2,1}`, `supp b ⊂ (-R, R-a)`,
     `f_b = b + b(· - a)`: `P_{2,R} f_b = 0` and `C_{2,R} f_b = √(2w) b` on `I_{R,a}`.
4. **CGC, explicit form** (`CompletedGraphContractivityExplicit`, Astra §5 displayed sides):
   `|L_s f|² + G⁻(f) + Σ_{n ≤ e^{2R}} ∫_I (C_n f)² ≤ |L_c f|² + G⁺(f) + Σ_{n ≤ e^{2R}} ∫_I (P_n f)²`
   with the prime channels (7) (`n = p^k`, weight `Λ(n)/√n = w_{p,k}`, shift `log n`), the
   completion coordinates (5), and the gamma channel (6) entered as a `GammaSplit`
   (`G⁺ - G⁻ = W_inf (autocorr f)`, both ≥ 0). A Lean instance of (6) with
   `G^± = (1/2π)∫ m_∞^± |F|²` is GAP, and the assembly `explicit CGC ⇔ ARP` (needs
   `L_c² - L_s² = poleTerm (autocorr f)` by Fubini and the finite prime bookkeeping) is GAP.
5. **The signed local assembly** (`SignedLocalAssembly`): for each window `R`, local real
   Hilbert spaces `H⁺_{v,R}`, `H⁻_{v,R}` and linear maps `P_{v,R}`, `C_{v,R}` on the window
   tests, finitely many visible places, the local signed identity
   `‖P_{v,R} f‖² - ‖C_{v,R} f‖² = Q_v(f)`, and the assembled Gram identity
   `Σ_v (‖P_{v,R} f‖² - ‖C_{v,R} f‖²) = weilForm (autocorr f)` (the shape of Astra's (8)).
6. **CGC, assembly form** (`CompletedGraphContractivity`): `Σ_v ‖C_{v,R} f‖² ≤ Σ_v ‖P_{v,R} f‖²`
   for every window `R` and every window test `f` (Astra §5, boxed (CGC)).
7. **Theorems (PROVED, standard axioms).**
   * `completion_signature` (5), `prime_channel_pointwise`, `prime_channel_signed` (7)/Prop 2,
     `first_window_eq14` (14).
   * `cgc_iff_arp`: for **any** signed local assembly, CGC ⇔ ARP.
   * `cgc_iff_obligation`: CGC ⇔ `ZetaReflectionPositivityObligation`.
   * `obligation_of_positiveFactor`: a positive completed factor (`PositiveCompletedFactor`,
     Astra Theorem 4 (3), Gram part) gives the obligation. The converse (CGC ⇒ positive
     factor via `D_R = (I - T_R^* T_R)^{1/2}` and window gluing, Astra Theorem 4 1⇒2⇒3) is
     paper level here.

Labels: the theorems above PROVED. Gamma channel (6) instance and the explicit-CGC ⇔ ARP
assembly: GAP. Astra's Theorem 3 obstruction for class (9): paper level (Lean GAP).
`√(2w) = 2^{1/4}√(log 2) ≈ 0.990079867217`: NUMERICAL (Flint), not in Lean.
**CGC is OPEN**; it has exactly ARP strength (Astra Theorem 4 status line), so it is a
restatement of the obligation, not a weakening. ARP OPEN; RH OPEN. No `sorry`, no axiom, no
`open_` stub.

Daniel Toupin / Golden Physics Project, with AI assistance (Heart of the Cosmos / Grok typed the
statement; Astra's note supplies (5), (7), (14), the class and CGC; Flint audited them; Turbo specified the
task). Daniel Toupin / Golden Physics Project … This seat: Heart of the Cosmos / Grok
(GPPDiscovery5). Audit: Turbo.
-/

open MeasureTheory
open GppMeyerSpectralWeil GppArithmeticReflection GppKernelTheory GlobalTate.Weil
open scoped ContDiff

noncomputable section

namespace GppZetaFactorMap

/-! ### Window tests -/

/-- The window-`R` test space `𝒟_R` (real-valued; complex positivity reduces to real by
symmetry of the form, Astra §1). -/
def windowTests (R : ℝ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f ∧ Function.support f ⊆ Set.Icc (-R) R}
  zero_mem' := ⟨contDiff_const, by simp⟩
  add_mem' := by
    rintro f g ⟨hf, hfs⟩ ⟨hg, hgs⟩
    refine ⟨hf.add hg, fun x hx => ?_⟩
    by_cases h : f x = 0
    · exact hgs (by simpa [h] using hx)
    · exact hfs h
  smul_mem' := by
    rintro c f ⟨hf, hfs⟩
    exact ⟨contDiff_const.smul hf, fun x hx => hfs (by
      simp only [Function.mem_support, Pi.smul_apply, smul_eq_mul] at hx
      exact right_ne_zero_of_mul hx)⟩

theorem isTestFunction_of_mem {R : ℝ} {f : ℝ → ℝ} (hf : f ∈ windowTests R) :
    IsTestFunction f :=
  ⟨hf.1, isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hf.2 isClosed_Icc)⟩

/-- Every smooth compactly supported function lies in some window. -/
theorem exists_window {f : ℝ → ℝ} (h1 : ContDiff ℝ ∞ f) (h2 : HasCompactSupport f) :
    ∃ R : ℝ, f ∈ windowTests R := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 h2.isCompact.isBounded
  refine ⟨r, h1, fun x hx => ?_⟩
  have := hr (subset_tsupport f hx)
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at this
  exact this

/-! ### Places and local completed forms -/

/-- Places of `ℚ`: `none` is the infinite place, `some p` the finite place `p`. -/
abbrev Place := Option Nat.Primes

/-- **The local completed form** of a place on a real test `f` (diagonal):
at ∞ the completion (pole) term plus the gamma term, at `p` the prime-`p` power sum,
all on `autocorr f`. These are the in-tree per-place pieces of GW1
(`GlobalTate.Weil.weilForm_eq_pole_add_places`). -/
def localForm : Place → (ℝ → ℝ) → ℝ
  | none, f => W_pole (autocorr f) + W_inf (autocorr f)
  | some p, f => W_fin p (autocorr f)

/-! ### Class (9): local positive factors up to finite-dimensional repair (Astra §4) -/

/-- **Astra's class (9) at the place `v` and window `R`.** On window tests obeying finitely many
linear constraints `κ f = 0`, the local form is a Hilbert square plus an arbitrary bilinear form
of a finite-rank map: `Q_v(f) = ‖A f‖² + B(λ f, λ f)`. -/
structure LocalClass9Factor (v : Place) (R : ℝ) where
  H : Type
  [instN : NormedAddCommGroup H]
  [instI : InnerProductSpace ℝ H]
  A : windowTests R →ₗ[ℝ] H
  m : ℕ
  n : ℕ
  κ : windowTests R →ₗ[ℝ] (Fin m → ℝ)
  lam : windowTests R →ₗ[ℝ] (Fin n → ℝ)
  B : LinearMap.BilinForm ℝ (Fin n → ℝ)
  gram : ∀ f : windowTests R, κ f = 0 →
    localForm v f = (@norm H instN.toNorm (A f)) ^ 2 + B (lam f) (lam f)

/-- **The class-(9) direct-sum factor map**: every place carries a class-(9) local factor on
every window. Astra's Theorem 3 (paper level; Lean GAP): this fails at every finite place `p`
on any window containing two small intervals separated by `log p`. -/
def PlacewiseClass9Factor : Prop := ∀ (v : Place) (R : ℝ), Nonempty (LocalClass9Factor v R)

/-! ### The signed local assembly and CGC (Astra §3 shape, §5) -/

/-- **Signed local assembly** (the shape of Astra's §3 output). For each window `R`: local real
Hilbert spaces `Hp v R` (positive carrier) and `Hc v R` (negative carrier) at each place,
linear maps `P v R`, `C v R` on the window tests, a finite set of visible places outside which
the maps vanish, the local signed identity at every place, and the assembled Gram identity
against the completed Weil form (the shape of Astra's (8)). The concrete prime maps (7) are typed
below (`primeP`, `primeC`); the abstract structure keeps the gamma channel (6) general. -/
structure SignedLocalAssembly (Hp Hc : Place → ℝ → Type)
    [∀ v R, NormedAddCommGroup (Hp v R)] [∀ v R, InnerProductSpace ℝ (Hp v R)]
    [∀ v R, NormedAddCommGroup (Hc v R)] [∀ v R, InnerProductSpace ℝ (Hc v R)] where
  P : ∀ v R, windowTests R →ₗ[ℝ] Hp v R
  C : ∀ v R, windowTests R →ₗ[ℝ] Hc v R
  vis : ℝ → Finset Place
  invisible : ∀ R v, v ∉ vis R → ∀ f, P v R f = 0 ∧ C v R f = 0
  local_signed : ∀ R v (f : windowTests R), ‖P v R f‖ ^ 2 - ‖C v R f‖ ^ 2 = localForm v f
  gram : ∀ R (f : windowTests R),
    ∑ v ∈ vis R, (‖P v R f‖ ^ 2 - ‖C v R f‖ ^ 2) = weilForm (autocorr f)

variable {Hp Hc : Place → ℝ → Type}
  [∀ v R, NormedAddCommGroup (Hp v R)] [∀ v R, InnerProductSpace ℝ (Hp v R)]
  [∀ v R, NormedAddCommGroup (Hc v R)] [∀ v R, InnerProductSpace ℝ (Hc v R)]

/-- **Completed Graph Contractivity (CGC)**, Astra §5: `‖C_R f‖² ≤ ‖P_R f‖²` for every window
and every window test, with `‖P_R f‖² = Σ_v ‖P_{v,R} f‖²` (direct-sum norm). OPEN. -/
def CompletedGraphContractivity (A : SignedLocalAssembly Hp Hc) : Prop :=
  ∀ R (f : windowTests R), ∑ v ∈ A.vis R, ‖A.C v R f‖ ^ 2 ≤ ∑ v ∈ A.vis R, ‖A.P v R f‖ ^ 2

/-- **CGC ⇔ window positivity of the completed Weil form**, for any signed local assembly.
PROVED (from the Gram field). -/
theorem cgc_iff_window_nonneg (A : SignedLocalAssembly Hp Hc) :
    CompletedGraphContractivity A ↔ ∀ R (f : windowTests R), 0 ≤ weilForm (autocorr f) := by
  constructor
  · intro h R f
    have hg := A.gram R f
    rw [Finset.sum_sub_distrib] at hg
    have := h R f
    linarith
  · intro h R f
    have hg := A.gram R f
    rw [Finset.sum_sub_distrib] at hg
    have := h R f
    linarith

/-- **CGC ⇔ ARP**, for any signed local assembly. PROVED. -/
theorem cgc_iff_arp (A : SignedLocalAssembly Hp Hc) :
    CompletedGraphContractivity A ↔ ArithmeticReflectionPositivity := by
  rw [cgc_iff_window_nonneg]
  constructor
  · intro h f h1 h2
    obtain ⟨R, hR⟩ := exists_window h1 h2
    exact h R ⟨f, hR⟩
  · intro harp R f
    exact harp f.1 (isTestFunction_of_mem f.2).1 (isTestFunction_of_mem f.2).2

/-- **CGC is the named form of the single obligation.** PROVED. -/
theorem cgc_iff_obligation (A : SignedLocalAssembly Hp Hc) :
    CompletedGraphContractivity A ↔ ZetaReflectionPositivityObligation :=
  (cgc_iff_arp A).trans zeta_obligation_iff_arp.symm

/-! ### Astra's equations (5), (7), (14), as filed -/

/-- `L₊(f) = M_f(1) = ∫ f(u) e^{u/2} du`. -/
def Lplus (f : ℝ → ℝ) : ℝ := ∫ u : ℝ, f u * Real.exp (u / 2)

/-- `L₋(f) = M_f(0) = ∫ f(u) e^{-u/2} du`. -/
def Lminus (f : ℝ → ℝ) : ℝ := ∫ u : ℝ, f u * Real.exp (-(u / 2))

/-- `L_c = (L₊ + L₋)/√2`. -/
def Lc (f : ℝ → ℝ) : ℝ := (Lplus f + Lminus f) / Real.sqrt 2

/-- `L_s = (L₊ - L₋)/√2`. -/
def Ls (f : ℝ → ℝ) : ℝ := (Lplus f - Lminus f) / Real.sqrt 2

/-- **Astra (5), as filed.** The completion coordinates have signature `(1, 1)`:
`L₊(f)L₋(g) + L₋(f)L₊(g) = L_c(f)L_c(g) - L_s(f)L_s(g)` (real tests). PROVED. -/
theorem completion_signature (f g : ℝ → ℝ) :
    Lplus f * Lminus g + Lminus f * Lplus g = Lc f * Lc g - Ls f * Ls g := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp only [Lc, Ls, div_mul_div_comm, h]
  ring

/-- `w_{p,k} = (log p) p^{-k/2}`. -/
def wpk (p k : ℕ) : ℝ := Real.log p * (p : ℝ) ^ (-(k : ℝ) / 2)

/-- `a_{p,k} = k log p`. -/
def apk (p k : ℕ) : ℝ := k * Real.log p

/-- The window `I_{R,a} = [-R, R - a]`. -/
def channelWindow (R a : ℝ) : Set ℝ := Set.Icc (-R) (R - a)

/-- **Astra (7), positive prime channel**: `(P f)(u) = √(w/2) [f(u) - f(u + a)]`. -/
def primeP (w a : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ := Real.sqrt (w / 2) * (f u - f (u + a))

/-- **Astra (7), negative prime channel**: `(C f)(u) = √(w/2) [f(u) + f(u + a)]`. -/
def primeC (w a : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ := Real.sqrt (w / 2) * (f u + f (u + a))

/-- (7) pointwise, polarised: `P f · P g - C f · C g = -w [f(u) g(u+a) + f(u+a) g(u)]`. PROVED. -/
theorem prime_channel_pointwise {w : ℝ} (hw : 0 ≤ w) (a : ℝ) (f g : ℝ → ℝ) (u : ℝ) :
    primeP w a f u * primeP w a g u - primeC w a f u * primeC w a g u =
      -w * (f u * g (u + a) + f (u + a) * g u) := by
  have h : Real.sqrt (w / 2) * Real.sqrt (w / 2) = w / 2 := Real.mul_self_sqrt (by positivity)
  simp only [primeP, primeC]
  linear_combination (-2 * (f u * g (u + a) + f (u + a) * g u)) * h

/-- **Astra Proposition 2 for one prime channel (7), as filed**: on `𝒟_R` (any shift `a`),
`‖P f‖²_{L²(I_{R,a})} - ‖C f‖²_{L²(I_{R,a})} = -w [q(a) + q(-a)]`, `q = autocorr f`. PROVED. -/
theorem prime_channel_signed {R w a : ℝ} (hw : 0 ≤ w) (f : windowTests R) :
    (∫ u in channelWindow R a, primeP w a (f : ℝ → ℝ) u ^ 2) -
        (∫ u in channelWindow R a, primeC w a (f : ℝ → ℝ) u ^ 2) =
      -w * (autocorr (f : ℝ → ℝ) a + autocorr (f : ℝ → ℝ) (-a)) := by
  obtain ⟨hf, hfs⟩ := f.2
  set g : ℝ → ℝ := (f : ℝ → ℝ)
  have hc : Continuous g := hf.continuous
  have hP : Continuous (primeP w a g) :=
    continuous_const.mul (hc.sub (hc.comp (continuous_id.add continuous_const)))
  have hC : Continuous (primeC w a g) :=
    continuous_const.mul (hc.add (hc.comp (continuous_id.add continuous_const)))
  have iP : IntegrableOn (fun u => primeP w a g u ^ 2) (channelWindow R a) :=
    (hP.pow 2).integrableOn_Icc
  have iC : IntegrableOn (fun u => primeC w a g u ^ 2) (channelWindow R a) :=
    (hC.pow 2).integrableOn_Icc
  rw [← integral_sub iP iC]
  have hpt : ∀ u, primeP w a g u ^ 2 - primeC w a g u ^ 2 = -(2 * w) * (g u * g (u + a)) := by
    intro u
    have := prime_channel_pointwise hw a g g u
    nlinarith [this]
  simp_rw [hpt]
  rw [integral_const_mul]
  have hzero : ∀ u ∉ channelWindow R a, g u * g (u + a) = 0 := by
    intro u hu
    simp only [channelWindow, Set.mem_Icc, not_and_or, not_le] at hu
    rcases hu with hu | hu
    · have : g u = 0 := by
        by_contra h
        have := hfs h
        exact absurd this.1 (not_le.2 hu)
      simp [this]
    · have : g (u + a) = 0 := by
        by_contra h
        have := hfs h
        linarith [this.2]
      simp [this]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have h1 : autocorr g a = ∫ u : ℝ, g u * g (u + a) := by
    unfold autocorr
    rw [← integral_add_right_eq_self (fun y => g y * g (y - a)) a]
    congr 1
    ext u
    simp only [add_sub_cancel_right]
    ring
  have h2 : autocorr g (-a) = ∫ u : ℝ, g u * g (u + a) := by
    unfold autocorr
    simp only [sub_neg_eq_add]
  rw [h1, h2]
  ring

/-- **Astra (14), as filed (Theorem 5, first window).** If `2R < log 3`, put `a = log 2`,
`w = w_{2,1} = (log 2)/√2`, let `supp b ⊂ (-R, R - a)` and `f_b = b + b(· - a)`. Then on
`I_{R,a}`: `P_{2,R} f_b = 0` and `C_{2,R} f_b = √(2w) b`. PROVED. -/
theorem first_window_eq14 {R : ℝ} (hR : 2 * R < Real.log 3) {b : ℝ → ℝ}
    (hb : Function.support b ⊆ Set.Ioo (-R) (R - Real.log 2)) {u : ℝ}
    (hu : u ∈ channelWindow R (apk 2 1)) :
    primeP (wpk 2 1) (apk 2 1) (fun x => b x + b (x - Real.log 2)) u = 0 ∧
      primeC (wpk 2 1) (apk 2 1) (fun x => b x + b (x - Real.log 2)) u =
        Real.sqrt (2 * wpk 2 1) * b u := by
  have ha : apk 2 1 = Real.log 2 := by simp [apk]
  rw [ha] at hu ⊢
  have hlt : Real.log 3 < 2 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  have hRa : R < Real.log 2 := by linarith
  have hw : 0 ≤ wpk 2 1 := by
    unfold wpk
    exact mul_nonneg (Real.log_nonneg (by norm_num)) (by positivity)
  obtain ⟨hu1, hu2⟩ := hu
  have hb1 : b (u - Real.log 2) = 0 := by
    by_contra h
    have := hb h
    linarith [this.1]
  have hb2 : b (u + Real.log 2) = 0 := by
    by_contra h
    have := hb h
    linarith [this.2]
  have hb3 : b (u + Real.log 2 - Real.log 2) = b u := by rw [add_sub_cancel_right]
  refine ⟨?_, ?_⟩
  · simp only [primeP, hb1, hb2, hb3]
    ring
  · simp only [primeC, hb1, hb2, hb3]
    have : Real.sqrt (2 * wpk 2 1) = 2 * Real.sqrt (wpk 2 1 / 2) := by
      rw [show 2 * wpk 2 1 = 2 ^ 2 * (wpk 2 1 / 2) by ring,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [this]
    ring

/-! ### CGC, explicit form (Astra §5 displayed sides) -/

/-- The gamma channel (6) as a signed split of the archimedean term: `G⁺, G⁻ ≥ 0` with
`G⁺(f) - G⁻(f) = W_inf (autocorr f)`. Astra's instance is `G^± = (1/2π) ∫ m_∞^± |F|²`
(Lean instance GAP). -/
structure GammaSplit where
  plus : (ℝ → ℝ) → ℝ
  minus : (ℝ → ℝ) → ℝ
  plus_nonneg : ∀ f, 0 ≤ plus f
  minus_nonneg : ∀ f, 0 ≤ minus f
  split : ∀ f, plus f - minus f = W_inf (autocorr f)

/-- The visible prime powers on window `R`: `n ≤ e^{2R}`, weight `Λ(n)/√n` (`= w_{p,k}` at
`n = p^k`, zero off prime powers), shift `log n` (`= a_{p,k}`). -/
def visible (R : ℝ) : Finset ℕ := Finset.Icc 1 ⌊Real.exp (2 * R)⌋₊

/-- **Completed Graph Contractivity, explicit form** (Astra §5, both displayed sides), with the
completion coordinates (5), the prime channels (7) and the gamma channel `G`. **OPEN**, ARP
strength. -/
def CompletedGraphContractivityExplicit (G : GammaSplit) : Prop :=
  ∀ R (f : windowTests R),
    Ls (f : ℝ → ℝ) ^ 2 + G.minus (f : ℝ → ℝ) +
        ∑ n ∈ visible R, ∫ u in channelWindow R (Real.log n),
          primeC (ArithmeticFunction.vonMangoldt n / Real.sqrt n) (Real.log n) (f : ℝ → ℝ) u ^ 2 ≤
      Lc (f : ℝ → ℝ) ^ 2 + G.plus (f : ℝ → ℝ) +
        ∑ n ∈ visible R, ∫ u in channelWindow R (Real.log n),
          primeP (ArithmeticFunction.vonMangoldt n / Real.sqrt n) (Real.log n) (f : ℝ → ℝ) u ^ 2

/-- `w_{p,k} = Λ(p^k)/√(p^k)`: the explicit CGC weights are Astra's. PROVED. -/
theorem wpk_eq_vonMangoldt {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    wpk p k = ArithmeticFunction.vonMangoldt (p ^ k) / Real.sqrt ((p ^ k : ℕ) : ℝ) := by
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega), ArithmeticFunction.vonMangoldt_apply_prime hp,
    wpk, Real.sqrt_eq_rpow, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    show -(k : ℝ) / 2 = -((k : ℝ) * (1 / 2)) by ring, Real.rpow_neg (by positivity)]
  exact (div_eq_mul_inv _ _).symm

/-- **Positive completed factor** (Astra Theorem 4 (3), Gram part, diagonal): for every window a
real Hilbert space and a linear map whose squared norm is the completed Weil form. -/
def PositiveCompletedFactor : Prop :=
  ∀ R : ℝ, ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
    (Z : windowTests R →ₗ[ℝ] H), ∀ f : windowTests R, ‖Z f‖ ^ 2 = weilForm (autocorr f)

/-- A positive completed factor gives the obligation. PROVED. (Converse: paper level, Astra
Theorem 4.) -/
theorem obligation_of_positiveFactor (h : PositiveCompletedFactor) :
    ZetaReflectionPositivityObligation := by
  refine zeta_obligation_iff_arp.2 fun f h1 h2 => ?_
  obtain ⟨R, hR⟩ := exists_window h1 h2
  obtain ⟨H, _, _, Z, hZ⟩ := h R
  have := hZ ⟨f, hR⟩
  change 0 ≤ weilForm (autocorr (⟨f, hR⟩ : windowTests R))
  rw [← this]
  positivity

end GppZetaFactorMap

#print axioms GppZetaFactorMap.exists_window
#print axioms GppZetaFactorMap.completion_signature
#print axioms GppZetaFactorMap.prime_channel_pointwise
#print axioms GppZetaFactorMap.prime_channel_signed
#print axioms GppZetaFactorMap.first_window_eq14
#print axioms GppZetaFactorMap.wpk_eq_vonMangoldt
#print axioms GppZetaFactorMap.cgc_iff_window_nonneg
#print axioms GppZetaFactorMap.cgc_iff_arp
#print axioms GppZetaFactorMap.cgc_iff_obligation
#print axioms GppZetaFactorMap.obligation_of_positiveFactor
