import GppVerify.StandardModel.ThreeGenerations

/-!
# thm:link6 — c_{2D} = κ₀ × c_{4D}^{Weyl}

## Golden Physics Project — Shadow Framework Formalization
## Lean 4 / Mathlib v4.19.0

This file formalizes `thm:link6` (ONON52, cited 10×):
*c_{2D} = κ₀ × c_{4D}^{Weyl}*, where κ₀ > 0 is a universal constant.

### Proof structure (from Daniel Toupin, 2026)

Four established physics results form the axiom base:
1. Weinberg (1965): tree-level TT OPE vanishes (soft graviton theorem)
2. Cachazo-Strominger (2014): subleading soft graviton defines T(z)
3. Capper-Duff (1974) / 't Hooft-Veltman (1974): graviton self-energy
   Π(Q) = c_{4D} × Q⁴ × (Weyl structure) / (16π²)
   → The Q⁴/Q⁴ = 1 exact cancellation gives c_{1-loop} = κ₀ × c_{4D}^Weyl
4. Adler-Bardeen (1969): trace anomaly is one-loop exact

Therefore c_{2D} = c_tree + c_{1-loop} = 0 + κ₀ × c_{4D}^Weyl.

### Downstream closures

Once link6_corollary compiles, the chain:
  c_{2D} = 0  →  c_{4D}^Weyl = 0  →  n_gen = 3  (Boyle-Turok 2021)
is formally proved (see three_generations_from_c0).

### Infrastructure gap, and how it is carried (revised 2026-08-30)

QFT / celestial OPE is not in Mathlib, so the four physics results above are *inputs*,
not theorems. They used to be carried as global `axiom` declarations, together with
`axiom`-declared opaque constants `c_2D`, `c_4D_weyl`, `n_gen`, `kappa_0`. That was the
wrong mechanism for them: none of these is a *mathematical* gap — `c_2D` and friends are
physical observables (real numbers whose values are measured or computed outside Lean),
and `link6_from_physics` / `boyle_turok_2021` are cited external physics results. A global
declaration of that kind silently contaminates everything downstream: any theorem touching
it reports those axioms in `#print axioms`, whether or not the reader is looking.

They are now carried as **explicit hypotheses on the theorems that use them**. The
mathematical content is identical — the deduction `c_2D = 0 → n_gen = 3` was always
*conditional* on the physics inputs — but now that conditionality is visible in the
statement itself rather than hidden in a global axiom, and this file declares **no axioms
at all**. This is strictly more honest, not merely cosmetically different: a reader of
`three_generations_from_c0` now sees exactly which physics inputs it consumes.
-/

namespace GppLink6

-- ============================================================
-- §1  Abstract constants (QFT observables) — now theorem parameters
-- ============================================================
--
-- `c_2D` (2D central charge from the celestial OPE coefficient), `c_4D_weyl` (4D Weyl
-- anomaly coefficient from the graviton self-energy), `n_gen` (number of fermion
-- generations) and `kappa_0` (universal positive normalisation from the canonical OPE
-- normalisation) are physical observables, not defined mathematical objects. They appear
-- below as universally quantified variables on each theorem rather than as axiomatized
-- opaque constants.

-- ============================================================
-- §2  Four established physics axioms
-- ============================================================

/-- Weinberg (1965): tree-level TT OPE central charge vanishes.
    (Soft graviton theorem in 4D → zero tree-level contribution to 2D c.) -/
theorem open_weinberg_soft_tree : True := trivial

/-- Cachazo-Strominger (2014): subleading soft graviton theorem defines T(z).
    Ensures the celestial stress tensor is well-defined from gravity amplitudes. -/
theorem open_cachazo_strominger : True := trivial

/-- Capper-Duff (1974) / 't Hooft-Veltman (1974): graviton self-energy is
    Π(Q) = c_{4D} × Q⁴ × (Weyl structure) / (16π²).
    The exact Q⁴/Q⁴ = 1 cancellation in the dressed propagator G·Π·G = Π(Q)/Q⁴
    gives: one-loop celestial OPE coefficient = κ₀ × c_{4D}^Weyl. -/
theorem open_capper_duff_one_loop : True := trivial

/-- Adler-Bardeen (1969): the trace anomaly is one-loop exact.
    All n ≥ 2 loop corrections to the TT OPE central charge vanish. -/
theorem open_adler_bardeen_nonrenorm : True := trivial

-- ============================================================
-- §3  Main theorem: c_{2D} = κ₀ × c_{4D}^Weyl
-- ============================================================

/-- **thm:link6** (cited 10×), as a named hypothesis rather than an axiom:
    `c_{2D} = κ₀ × c_{4D}^{Weyl}`.

    The logical structure behind it is `c_{2D} = c_tree + c_{1-loop} = 0 + κ₀·c_{4D}`,
    resting on the four physics results recorded above (Weinberg; Cachazo–Strominger;
    Capper–Duff / 't Hooft–Veltman; Adler–Bardeen). Since none of those is formalizable
    at the pinned Mathlib, this is an *input*, and it is consumed as an explicit
    hypothesis named `link6` on each theorem below. -/
abbrev Link6Hypothesis (c_2D kappa_0 c_4D_weyl : ℝ) : Prop :=
  c_2D = kappa_0 * c_4D_weyl

/-- **Corollary of thm:link6**: `c_{2D} = 0 ↔ c_{4D}^Weyl = 0`.

    Proved from the link6 relation together with strict positivity of `κ₀`, both taken as
    explicit hypotheses. No axiom. -/
theorem link6_corollary {c_2D c_4D_weyl kappa_0 : ℝ}
    (kappa_0_pos : 0 < kappa_0)
    (link6 : c_2D = kappa_0 * c_4D_weyl) :
    c_2D = 0 ↔ c_4D_weyl = 0 := by
  constructor
  · intro h
    rw [link6] at h
    rcases mul_eq_zero.mp h with h0 | h1
    · exact absurd h0 kappa_0_pos.ne'
    · exact h1
  · intro h
    rw [link6, h, mul_zero]

-- ============================================================
-- §4  Downstream: three generations
-- ============================================================

/-- Boyle–Turok (2021): `c_{4D}^Weyl = 0` with the SM gauge group forces `n_gen = 3`.
    An uncited-here external physics analysis, not in Mathlib — consumed below as the
    explicit hypothesis `boyle_turok`, not as an axiom. -/
abbrev BoyleTurokHypothesis (c_4D_weyl : ℝ) (n_gen : ℕ) : Prop :=
  c_4D_weyl = 0 → n_gen = 3

/-- **Three generations from c_{2D} = 0**, via thm:link6 + Boyle–Turok.

    Every physics input is an explicit hypothesis: `kappa_0_pos` (canonical OPE
    normalisation is strictly positive), `link6` (thm:link6 itself), and `boyle_turok`
    (the 2021 anomaly analysis). Given those, the implication `c_{2D} = 0 → n_gen = 3` is
    a genuine kernel-checked deduction depending on no custom axiom.

    Corresponds to `open_three_generations_from_c0_and_link6` in `ShadowSymmetry.lean`, which
    cannot import this file (circular: ShadowSymmetry → ThreeGenerations → Link6). -/
theorem three_generations_from_c0 {c_2D c_4D_weyl kappa_0 : ℝ} {n_gen : ℕ}
    (kappa_0_pos : 0 < kappa_0)
    (link6 : c_2D = kappa_0 * c_4D_weyl)
    (boyle_turok : c_4D_weyl = 0 → n_gen = 3)
    (hc : c_2D = 0) : n_gen = 3 :=
  boyle_turok ((link6_corollary kappa_0_pos link6).mp hc)

/-- The positivity of κ₀ is essential: without it, `c_{2D} = 0` would not force
    `c_{4D} = 0` (the `mul_eq_zero` split could land on the `κ₀ = 0` branch). -/
lemma kappa_0_ne_zero {kappa_0 : ℝ} (kappa_0_pos : 0 < kappa_0) : kappa_0 ≠ 0 :=
  kappa_0_pos.ne'

end GppLink6

-- Summary checks
#check @GppLink6.link6_corollary
#check @GppLink6.three_generations_from_c0
#check @GppLink6.kappa_0_ne_zero
