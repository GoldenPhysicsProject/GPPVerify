import GppVerify.RiemannHypothesis.ConditionalWeightStateLine
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic

/-!
# The Sameness statement is exactly RH

Turbo's "Sameness Theorem" target (bridge note 2026-11-06, occupancy form,
with the half-density character): there is a unitary dilation action `U` on
a complex Hilbert space such that every zero `ρ` of the entire completed xi
is the weight of a nonzero state, `U a ψ = a^(ρ - 1/2) ψ`
(`GppConditionalWeightState.ArithmeticPhysicsCorrespondence`).

This module proves, in both directions,

  `(∃ U, ArithmeticPhysicsCorrespondence U) ↔ (∀ ρ, xi ρ = 0 → Re ρ = 1/2)`.

* `→` is `xi_zeros_on_critical_line_of_correspondence` (unitarity).
* `←` (new here): if every zero is on the line, the diagonal action on
  `ℓ²(zeros of xi)`, multiplying the `ρ` coordinate by the unit-modulus
  character `a^(ρ - 1/2)`, is a linear isometry, and the basis vector at `ρ`
  is a weight state of weight `ρ`.

So the Sameness statement, as a bare existence statement, is equivalent to RH:
neither more nor less. In particular the converse construction uses the zeros
themselves as input, so it does not supply a proof. A proof must construct `U`
from arithmetic data (primes, gamma factor, pole) without using the zero set,
which is what the bridge target T3 asks for. RH is open; nothing here asserts
either side.

Daniel Toupin / Golden Physics Project, with AI assistance from Turbo (target)
and Claude Code (Lean).
-/

namespace GppSameness

open Complex GppScaleMass GppConditionalWeightState

/-- The zero set of the entire completed xi. -/
def XiZeros : Set ℂ := {ρ | GppLogDerivZeroFree.xi ρ = 0}

/-- `ℓ²` over the zero set. -/
noncomputable abbrev ZeroSpace := lp (fun _ : XiZeros => ℂ) 2

/-- Diagonal multiplication by a unit-modulus sequence is a linear isometry of `ℓ²`. -/
noncomputable def diagMul (c : XiZeros → ℂ) (hc : ∀ z, ‖c z‖ = 1) :
    ZeroSpace →ₗᵢ[ℂ] ZeroSpace where
  toFun f := ⟨fun z => c z * f z, by
    have hf := lp.memℓp f
    change Memℓp (fun z => c z * f z) 2
    rw [memℓp_gen_iff (by norm_num)] at hf ⊢
    simpa [norm_mul, hc] using hf⟩
  map_add' f g := by
    apply lp.ext
    funext z
    simp only [lp.coeFn_add, Pi.add_apply]
    change c z * (f z + g z) = c z * f z + c z * g z
    ring
  map_smul' r f := by
    apply lp.ext
    funext z
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    change c z * (r * f z) = r * (c z * f z)
    ring
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 2
    funext z
    change ‖c z * f z‖ ^ _ = _
    rw [norm_mul, hc, one_mul]

theorem diagMul_apply (c : XiZeros → ℂ) (hc : ∀ z, ‖c z‖ = 1) (f : ZeroSpace)
    (z : XiZeros) : diagMul c hc f z = c z * f z := rfl

/-- **Converse direction.** If every zero of the entire xi is on the line, there
is a unitary dilation action realizing every zero as a weight state. -/
theorem correspondence_of_zeros_on_line
    (h : ∀ ρ : ℂ, GppLogDerivZeroFree.xi ρ = 0 → ρ.re = 1 / 2) :
    ∃ U : ℝ → ZeroSpace →ₗᵢ[ℂ] ZeroSpace, ArithmeticPhysicsCorrespondence U := by
  have hunit : ∀ (a : ℝ) (z : XiZeros), ‖dilationCharacter (z : ℂ) a‖ = 1 :=
    fun a z => critical_line_dilation_unitary (h z z.2) a
  refine ⟨fun a => diagMul (fun z => dilationCharacter z a) (hunit a), ?_⟩
  intro ρ hρ
  refine ⟨lp.single 2 (⟨ρ, hρ⟩ : XiZeros) (1 : ℂ), ?_, ?_⟩
  · intro h0
    have := congrArg (fun f : ZeroSpace => f ⟨ρ, hρ⟩) h0
    simp at this
  · intro a _
    apply lp.ext
    funext z
    rw [diagMul_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hz : z = ⟨ρ, hρ⟩
    · subst hz
      rfl
    · rw [lp.single_apply_ne 2 _ _ hz]
      simp

/-- **The Sameness statement is equivalent to RH for the entire xi.** -/
theorem sameness_iff_zeros_on_line :
    (∃ U : ℝ → ZeroSpace →ₗᵢ[ℂ] ZeroSpace, ArithmeticPhysicsCorrespondence U) ↔
      ∀ ρ : ℂ, GppLogDerivZeroFree.xi ρ = 0 → ρ.re = 1 / 2 :=
  ⟨fun ⟨_, hU⟩ => xi_zeros_on_critical_line_of_correspondence hU,
    correspondence_of_zeros_on_line⟩

end GppSameness

#print axioms GppSameness.correspondence_of_zeros_on_line
#print axioms GppSameness.sameness_iff_zeros_on_line
