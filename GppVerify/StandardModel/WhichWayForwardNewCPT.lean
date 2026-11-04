import Mathlib.Tactic
import GppVerify.StandardModel.OrientationCliffordCore

/-!
# *Which Way Is Forward?*: the CPT theorem in arrow form

The paper's discrete-operations analysis, made finite. Labels are triples
`(q, t, h)` of bits (`0 = +`, `1 = -`): the charge orientation `q`, the
time-arrow orientation `t`, and the handedness `h`. The observed charge
sign is the product `χ = qt`, in bits `χ = q + t`.

The three operations that must not be conflated:

* `tgAct`, the particle's own time-arrow flip `T_g`: flips `t`, and with
  it the observed charge, since `χ = qt`;
* `cAct`, charge conjugation `C`: flips `q`;
* Wigner's `T_W`, the antiunitary reversal of a whole history, keeps
  every charge fixed. On labels that requirement forces
  `T_W = C ∘ T_g` (the paper's Eq. (TW)): the diagonal flip, which
  preserves `χ`.

**The new CPT theorem (arrow form).** With `P` the parity flip of `h`,
the standard composite collapses:
`Θ = C ∘ P ∘ T_W = P ∘ T_g`.
The `C` in `CPT` is the correction that turns the arrow flip into
Wigner's operator; once that is seen, it cancels, and the exact
side-to-side symmetry of the theory is parity composed with the
particle's own arrow flip. The theorem is proved here by `decide` over
the eight labels, together with its content: `Θ` fixes `q`, flips `t`
and `h`, and flips `χ` (particle class to antiparticle class).

The sharpener is also here: reading `CPT`'s `T` as the arrow `T_g`
directly, without the correction, gives a different operator,
`C ∘ P ∘ T_g`, which acts on the observables `(χ, h)` exactly as `P`
alone does. Since `P` alone is violated by the weak interaction, that
reading names a false symmetry.

The second half of the module is the same algebra in the Clifford
carrier of `OrientationCliffordCore`: with `Rq`, `Rt` the label-basis
half flips, `Rq * (Rq * Rt) = Rt` is `C ∘ T_W = T_g`, the composite
`Rq * Rt` is the diagonal flip, and conjugation by `Rt` negates the
`χ` grading while the diagonal preserves it.

Scope: this is the finite model of the paper's CPT statement. The
field-theoretic CPT theorem of Lüders and Pauli is the statement being
modelled, not reproved; what is proved is that in the orientation
labels the paper actually uses, the arrow form is an identity.
-/

namespace GppWhichWayForwardNewCPT

/-- A lift label: (charge orientation, time orientation, handedness),
each a bit with `0 = +`, `1 = -`. -/
abbrev Label := Fin 2 × Fin 2 × Fin 2

/-- Charge conjugation `C`: flips the charge orientation. -/
def cAct (l : Label) : Label := (l.1 + 1, l.2.1, l.2.2)

/-- The time-arrow flip `T_g`: flips the time orientation. -/
def tgAct (l : Label) : Label := (l.1, l.2.1 + 1, l.2.2)

/-- Parity `P`: flips the handedness. -/
def pAct (l : Label) : Label := (l.1, l.2.1, l.2.2 + 1)

/-- Wigner's `T_W`, defined by the requirement that charges are kept
fixed: the composite `C ∘ T_g`. -/
def twAct (l : Label) : Label := cAct (tgAct l)

/-- The standard CPT composite `C ∘ P ∘ T_W`. -/
def cptStd (l : Label) : Label := cAct (pAct (twAct l))

/-- The arrow form `Θ = P ∘ T_g`. -/
def thetaNew (l : Label) : Label := pAct (tgAct l)

/-- The observed-charge sign bit `χ = qt`, in bits `q + t`. -/
def chi (l : Label) : Fin 2 := l.1 + l.2.1

/-- The bit-to-sign map: `0 ↦ +1`, `1 ↦ -1`. -/
def sgn (b : Fin 2) : ℤ := if b = 0 then 1 else -1

/-- The observable pair: observed charge sign and handedness. -/
def obs (l : Label) : Fin 2 × Fin 2 := (chi l, l.2.2)

/-- `χ` is the product of the two signs: `sgn χ = sgn q * sgn t`. -/
theorem chi_sgn : ∀ l : Label, sgn (chi l) = sgn l.1 * sgn l.2.1 := by decide

/-- The half flips commute: the two orientations are independent. -/
theorem half_flips_commute : ∀ l : Label, cAct (tgAct l) = tgAct (cAct l) := by
  decide

theorem cAct_involutive : ∀ l : Label, cAct (cAct l) = l := by decide

theorem tgAct_involutive : ∀ l : Label, tgAct (tgAct l) = l := by decide

theorem pAct_involutive : ∀ l : Label, pAct (pAct l) = l := by decide

/-- Wigner's composite is the diagonal flip: it flips both orientations. -/
theorem twAct_apply : ∀ l : Label, twAct l = (l.1 + 1, l.2.1 + 1, l.2.2) := by
  decide

/-- Wigner's `T_W` preserves the observed charge: `χ` is unchanged.
This is the defining property that forces `T_W = C ∘ T_g`. -/
theorem twAct_chi : ∀ l : Label, chi (twAct l) = chi l := by decide

/-- The diagonal flip is invisible to the observables: `(q, t) ~ (-q, -t)`
present the same charge. This is the quotient the paper starts from. -/
theorem diagonal_obs : ∀ l : Label,
    obs (l.1 + 1, l.2.1 + 1, l.2.2) = obs l := by decide

/-- **The CPT theorem, arrow form:** `C ∘ P ∘ T_W = P ∘ T_g`.
The standard composite and the arrow composite are the same map on
every label. -/
theorem cpt_arrow_form : ∀ l : Label, cptStd l = thetaNew l := by decide

/-- What `Θ` does: it fixes the charge orientation and flips the time
orientation and the handedness. -/
theorem theta_action : ∀ l : Label, thetaNew l = (l.1, l.2.1 + 1, l.2.2 + 1) := by
  decide

/-- `Θ` flips the observed charge: it sends the particle class to the
antiparticle class. -/
theorem theta_chi : ∀ l : Label, chi (thetaNew l) = chi l + 1 := by decide

/-- **The sharpener.** Reading `CPT`'s `T` as the arrow flip `T_g`
directly, with no correction, produces an operator that acts on the
observables exactly as parity alone does. It is not the CPT operator,
and parity alone is not a symmetry of the weak interaction. -/
theorem cpt_with_arrow_acts_as_parity : ∀ l : Label,
    obs (cAct (pAct (tgAct l))) = obs (pAct l) := by decide

/-! ## The carrier shadow

The same identities among the label-basis half flips `Rq`, `Rt` of
`OrientationCliffordCore`, checked by `decide` over `ℤ[i]`. -/

open GppOrientationCliffordCore in
/-- The diagonal flip on the label basis is the anti-diagonal exchange. -/
theorem Rq_mul_Rt : Rq * Rt
    = !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by decide

open GppOrientationCliffordCore in
theorem Rq_involutive : Rq * Rq = 1 := by decide

open GppOrientationCliffordCore in
theorem Rt_involutive : Rt * Rt = 1 := by decide

open GppOrientationCliffordCore in
/-- The half flips commute in the carrier. -/
theorem Rq_Rt_commute : Rq * Rt = Rt * Rq := by decide

open GppOrientationCliffordCore in
/-- **The carrier form of the arrow CPT identity:** with `T_W` realized
as the composite `Rq * Rt`, composing with `C = Rq` returns the arrow
flip itself: `C ∘ T_W = T_g`. -/
theorem cpt_carrier : Rq * (Rq * Rt) = Rt := by decide

open GppOrientationCliffordCore in
/-- The diagonal flip preserves the `χ` grading: it commutes with
`χ_L = diag(1, -1, -1, 1)`. -/
theorem diagonal_preserves_chi :
    (Rq * Rt) * !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1]
      = !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1] * (Rq * Rt) := by
  decide

open GppOrientationCliffordCore in
/-- The arrow flip reverses the `χ` grading: conjugation by `Rt` sends
`χ_L` to `-χ_L`, the carrier form of "the time flip changes the
particle class." -/
theorem Rt_conj_chi :
    Rt * !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1] * Rt
      = -!![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1] := by
  decide

end GppWhichWayForwardNewCPT
