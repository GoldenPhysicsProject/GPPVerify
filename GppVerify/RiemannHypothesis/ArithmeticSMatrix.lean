/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Heart of the Cosmos / Grok)
-/
import GppVerify.RiemannHypothesis.ArchimedeanScatteringRatio
import GppVerify.RiemannHypothesis.OneDimensionalMellinWeight

/-!
# The arithmetic S-matrix and ARP

Daniel's 2026-11-10 attack: use the arithmetic S-matrix to prove arithmetic
reflection positivity. Candidate: the Lax–Phillips / Pavlov–Faddeev scattering
ratio built from completed-zeta data, `ζ(1−s)/ζ(s)`, whose Euler product would
carry the primes and (one hopes) distinguish `ζ` from `F_θ`. Derive ARP from
its unitarity; write the reflection-positive form; locate exactly where the
zeros or RH enter; run the `ζ` versus `F_θ` test.

## What is already in the tree

`GppArchimedeanScattering` defines the real-place ratio
`S_∞(s) = γ_ℝ(1−s)/γ_ℝ(s)` and proves:

* `|S_∞(1/2 + it)| = 1` (`scattering_unimodular`);
* `ζ(1−s)/ζ(s) = S_∞(s)⁻¹` away from `0`, `1`, Gamma poles and zeros of `ζ`
  (`zeta_ratio`), which is the functional equation rewritten as a cancellation
  between the arithmetic ratio and the archimedean ratio.

So the natural arithmetic S-matrix `S_arith(s) := ζ(1−s)/ζ(s)` is *equal* to
the reciprocal archimedean ratio wherever it is defined. Its unitarity on the
critical line is a theorem, unconditionally, with no Euler-product input and
no zero-location input beyond “do not divide by zero”.

The fully completed ratio `ξ(1−s)/ξ(s)` is identically `1` by the functional
equation (`completed_xi_ratio_eq_one`).

## Reflection-positive form

ARP is already the named statement `ArithmeticReflectionPositivity`:
`0 ≤ W(f ⋆ f̃)` with `W = pole + A_∞ − primeSide` assembled from the pole,
the gamma factor and the primes only
(`GppArithmeticReflection.weilForm`). That *is* the reflection-positive form
attached to the arithmetic side. `|S_arith| = 1` does not appear in `W` and
does not force `W ≥ 0`.

## Where the zeros enter

* Axis unitarity of `S_arith` uses the functional equation and conjugation
  (`SArith_unimodular`). Zeros enter only as points where the ratio is
  undefined (`riemannZeta s ≠ 0`). This is not RH.
* Inner-ness / holomorphy of `S_arith` in `Re s > 1/2` means `ξ` has no zeros
  in that half-plane (`SArithInner`). By the functional equation that is RH
  (`rh_of_SArith_inner`, PROVED). Using it as an input to ARP/RH is circular.
* The Euler product of `ζ` exists for `Re s > 1` (Mathlib
  `riemannZeta_eulerProduct_tprod`) and distinguishes `ζ` from Davenport–Heilbronn,
  but after analytic continuation the identity `S_arith = S_∞⁻¹` cancels the
  primes against the gamma factor. A convergent product `∏_p S_p = S_arith`
  cannot be written in `Re s > 1`, because the product for `ζ(1−s)` does not
  converge there.

## The `ζ` versus `F_θ` test

Axis unitarity of a local ratio `(1 − α p^{-s})/(1 − α p^{-(1−s)})` with real
`α > 0` holds on the critical line (`SLocalTilted_unimodular`). `F_θ`'s local
factors have this shape with `α = p^θ`. So `|S| = 1` on the unitary axis,
globally or locally, does **not** separate `ζ` from `F_θ`. Inner-ness does
separate them (it fails for any off-axis zero,
`spectral_identification_fails_of_off_axis_zero` in
`GppGravitonDeltaId`) because inner-ness *is* the zero-location statement.

Labels: axis unitarity PROVED (standard axioms); inner ⇒ RH PROVED;
ARP, (SIGN), (FLUX-BOUND), RH remain OPEN. No claim that ARP follows from
`|S| = 1`.

Daniel Toupin / Golden Physics Project, with AI assistance (Heart of the
Cosmos / Grok). The archimedean ratio lemmas used here are the existing
in-tree theorems of the Codex / Claude Code thread.
-/

namespace GppArithmeticSMatrix

open Complex GppArchimedeanScattering GppOneDimensionalMellinWeight GppLogDerivZeroFree
open scoped ComplexConjugate

/-! ## The arithmetic scattering ratio -/

/-- The arithmetic S-matrix `S_arith(s) = ζ(1−s)/ζ(s)`.
This is the incomplete ratio; the fully completed ratio is identically 1. -/
noncomputable def SArith (s : ℂ) : ℂ :=
  riemannZeta (1 - s) / riemannZeta s

/-- Away from `0`, `1`, Gamma poles and zeros of `ζ`, the arithmetic ratio
is the reciprocal archimedean scattering ratio. In-tree as `zeta_ratio`. -/
theorem SArith_eq_Sinf_inv (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1)
    (hg : Gammaℝ s ≠ 0) (hg' : Gammaℝ (1 - s) ≠ 0) (hz : riemannZeta s ≠ 0) :
    SArith s = (S s)⁻¹ :=
  zeta_ratio s h0 h1 hg hg' hz

/-- **Axis unitarity of `S_arith`.** On the critical line, off the zeros,
`|S_arith(1/2 + it)| = 1`. This is the functional equation plus
`scattering_unimodular`; it does not use the Euler product and does not
locate the zeros. -/
theorem SArith_unimodular (t : ℝ) (hz : riemannZeta ((1 / 2 : ℂ) + t * I) ≠ 0) :
    ‖SArith ((1 / 2 : ℂ) + t * I)‖ = 1 := by
  set s := (1 / 2 : ℂ) + t * I
  have hsre : s.re = 1 / 2 := by simp [s]
  have h0 : s ≠ 0 := by
    intro h
    have := congrArg re h
    rw [hsre] at this
    norm_num at this
  have h1 : s ≠ 1 := by
    intro h
    have := congrArg re h
    rw [hsre] at this
    norm_num at this
  have hre : 0 < s.re := by rw [hsre]; norm_num
  have hre' : 0 < (1 - s).re := by simp [sub_re, hsre]; norm_num
  have hg := Gammaℝ_ne_zero_of_re_pos hre
  have hg' := Gammaℝ_ne_zero_of_re_pos hre'
  have heq := SArith_eq_Sinf_inv s h0 h1 hg hg' hz
  have hs : ‖S s‖ = 1 := by
    change ‖S (1 / 2 + t * I)‖ = 1
    exact scattering_unimodular t
  rw [heq, norm_inv, hs, inv_one]

/-- The fully completed ratio is identically 1 wherever `ξ(s) ≠ 0`.
This carrier of “unitarity” has no content. -/
theorem completed_xi_ratio_eq_one (s : ℂ) (h : xi s ≠ 0) :
    xi (1 - s) / xi s = 1 := by
  rw [xi_one_sub, div_self h]

/-! ## Local ratios, including an `F_θ`-shaped tilt -/

/-- The local Euler ratio at a prime, `(1 − p^{-s})/(1 − p^{-(1−s)})`. -/
noncomputable def SLocal (p : ℕ) (s : ℂ) : ℂ :=
  (1 - (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-(1 - s)))

/-- A real Satake tilt of the same shape as `F_θ`'s local factor
`(1 − α p^{-s})` with `α = p^θ > 0`. -/
noncomputable def SLocalTilted (alpha : ℝ) (p : ℕ) (s : ℂ) : ℂ :=
  (1 - (alpha : ℂ) * (p : ℂ) ^ (-s)) /
    (1 - (alpha : ℂ) * (p : ℂ) ^ (-(1 - s)))

/-- On the critical line, `1 − s = conj s`. -/
theorem one_sub_eq_conj_on_critical_line (t : ℝ) :
    (1 : ℂ) - ((1 / 2 : ℂ) + t * I) = conj ((1 / 2 : ℂ) + t * I) := by
  apply Complex.ext
  · simp; norm_num
  · simp

/-- **Local axis unitarity, including the `F_θ` tilt.** For real `α` and a
positive real base, the tilted local ratio is unimodular on the critical
line (off the vanishing of the denominator). The untitled zeta factor is
the case `α = 1`. This is the discriminating test: `|S_p| = 1` does not
see the tilt `α = p^θ`. -/
theorem SLocalTilted_unimodular (alpha : ℝ) (p : ℕ) (hp : 0 < (p : ℝ)) (t : ℝ)
    (hne : (1 : ℂ) - (alpha : ℂ) * (p : ℂ) ^ (-((1 : ℂ) - ((1 / 2 : ℂ) + t * I))) ≠ 0) :
    ‖SLocalTilted alpha p ((1 / 2 : ℂ) + t * I)‖ = 1 := by
  set s := (1 / 2 : ℂ) + t * I
  have hline : (1 : ℂ) - s = conj s := one_sub_eq_conj_on_critical_line t
  have hpC : (p : ℂ) = ((p : ℝ) : ℂ) := by norm_cast
  have harg : (p : ℂ).arg ≠ Real.pi := by
    rw [hpC, arg_ofReal_of_nonneg hp.le]
    exact Real.pi_pos.ne
  have hcpow : conj ((p : ℂ) ^ (-s)) = (p : ℂ) ^ (-(1 - s)) := by
    have hconj := cpow_conj (p : ℂ) (-s) harg
    -- cpow_conj: p ^ conj (-s) = conj (conj p ^ (-s))
    have hpconj : conj (p : ℂ) = (p : ℂ) := by rw [hpC, conj_ofReal]
    simp [hpconj] at hconj
    -- hconj: p ^ (-conj s) = conj (p ^ (-s))
    rw [← hconj, ← hline]
  have hw : conj ((alpha : ℂ) * (p : ℂ) ^ (-s)) =
      (alpha : ℂ) * (p : ℂ) ^ (-(1 - s)) := by
    rw [map_mul, conj_ofReal, hcpow]
  unfold SLocalTilted
  have hden : (1 : ℂ) - (alpha : ℂ) * (p : ℂ) ^ (-(1 - s)) =
      conj (1 - (alpha : ℂ) * (p : ℂ) ^ (-s)) := by
    rw [map_sub, map_one, hw]
  rw [hden, norm_div, Complex.norm_conj]
  refine div_self ?_
  refine norm_ne_zero_iff.mpr ?_
  intro h0
  apply hne
  have : (1 : ℂ) - (alpha : ℂ) * (p : ℂ) ^ (-(1 - s)) = 0 := by
    rw [hden, h0, map_zero]
  convert this

/-- Specialization: zeta's own local ratio (`α = 1`) is unimodular on the axis. -/
theorem SLocal_unimodular (p : ℕ) (hp : 0 < (p : ℝ)) (t : ℝ)
    (hne : (1 : ℂ) - (p : ℂ) ^ (-((1 : ℂ) - ((1 / 2 : ℂ) + t * I))) ≠ 0) :
    ‖SLocal p ((1 / 2 : ℂ) + t * I)‖ = 1 := by
  have h := SLocalTilted_unimodular (alpha := 1) p hp t (by
    simpa using hne)
  simpa [SLocal, SLocalTilted] using h

/-! ## Inner-ness is RH (circularity) -/

/-- Inner-ness of the arithmetic ratio in the half-plane `Re s > 1/2`:
`ξ` has no zeros there. (Poles of `S_arith` occur at zeros of `ζ(s)`,
which for the entire completion are the zeros of `ξ`.) -/
def SArithInner : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → xi s ≠ 0

/-- Inner-ness forces every `ξ`-zero onto the one-dimensional principal
axis, by the functional equation `ξ(1−s) = ξ(s)`. -/
theorem all_xi_zeros_principal_of_SArith_inner (h : SArithInner) :
    AllXiZerosPrincipalOne := by
  intro rho hrho
  by_contra hne
  cases' lt_or_gt_of_ne hne with hlt hgt
  · have hre : 1 / 2 < (1 - rho).re := by
      simp [sub_re]
      linarith
    have h0 : xi (1 - rho) = 0 := by
      rw [xi_one_sub]
      exact hrho
    exact h (1 - rho) hre h0
  · exact h rho hgt hrho

/-- **RH from inner-ness of `S_arith`.** This is the circular reading:
asking the arithmetic S-matrix to be inner in `Re s > 1/2` *is* the
zero-location statement. Conditional only; inner-ness is not asserted. -/
theorem rh_of_SArith_inner (h : SArithInner) : RiemannHypothesis :=
  riemannHypothesis_of_all_xi_zeros_kg_normalized
    (all_xi_zeros_kg_normalized_iff_principal.mpr
      (all_xi_zeros_principal_of_SArith_inner h))

/-- OPEN: `SArithInner`. Equivalent in strength to RH via
`rh_of_SArith_inner`. Not implied by axis unitarity (`SArith_unimodular`,
already a theorem). A non-circular proof of ARP cannot take this as input. -/
theorem open_sarith_inner : True := trivial

#print axioms SArith_eq_Sinf_inv
#print axioms SArith_unimodular
#print axioms completed_xi_ratio_eq_one
#print axioms one_sub_eq_conj_on_critical_line
#print axioms SLocalTilted_unimodular
#print axioms SLocal_unimodular
#print axioms all_xi_zeros_principal_of_SArith_inner
#print axioms rh_of_SArith_inner

end GppArithmeticSMatrix
