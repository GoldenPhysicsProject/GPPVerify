# Operational-information obstruction linking WWIF, the volume constraint and Fisher form (October 22, 2026)

## Inputs and limits

Read from the actual manuscripts, not from an identification of their different notions of time:

- Daniel Toupin, *Which Way Is Forward?* v27 (September 22, 2026): microscopic orientation sign `t = sgn(-u.k)` relative to the record arrow, diagonal `D:(q,t)->(-q,-t)`, relational `chi=q*t`, `D` acting as a real structure relative to `I_q`. **This is NOT Wigner antiunitary T**. Its Section 9.6 already warns that `D`-invariant observables can distinguish coherent states from mixtures.
- Toupin, *The Volume Constraint in Entanglement Equilibrium*: first-order fixed-volume selection conditioned on the matched causal-diamond EH/gravitational and matter modular first laws; independent York-horizontality characterization with explicitly assumed physical reduction.
- Toupin, *The Fisher Form of the Causal Diamond*: reduced-state Kubo–Mori Hessian, radial KL/Fisher factor; do not equate to the full pure-ray Fubini–Study metric.

## New exact mathematics

**A. Anti-symplectic descent obstruction.** If a time-reversal involution `Theta` satisfies `Theta*Omega=-Omega` with `Omega != 0`, then `Omega` CANNOT be the pullback of a two-form from the orbit quotient by `Theta`, since descent implies `Theta*Omega=Omega` and hence `Omega=0`. Its fixed tangent space is isotropic. This is **not** the same construction as the continuous York Hamiltonian symplectic reduction `i_Y Omega = c dV`, with fixed-level-set tangents `ker dV`.

**B. Finite bipartite phase model.** For `|Psi_theta>=(|00>+e^(i theta)|11>)/sqrt(2)`, `rho_A(theta)=I/2` independent of theta. Reduced-state von Neumann entropy, Araki/Umegaki relative entropy between `rho_A(theta)` values and reduced Kubo–Mori Fisher in this direction are zero. Yet full-state FS metric is `g_FS(theta,theta)=1/4`. In a FIXED global measurement convention `<sigma_x otimes sigma_y>=sin(theta)` reveals the phase. Complex conjugation swaps theta->-theta and operator sign, so the COMPLETE observer/apparatus transformation preserves relational probabilities. This is a model of **relative-phase blindness under a subsystem reduction**, not proof of the microscopic q,t interpretation.

**C. Time-odd first law vs Fisher.** If an invariant state `S` has `dS(Tx)=dS(x)` and `TY=-Y`, then `dS(Y)=0`; second variation may be positive. This is already Lean checked in `TimeReversalEntropyGravity`.

**D. York moment-map parity.** If `Theta` is anti-symplectic, `Y` odd, and `i_Y Omega=c dV`, `c!=0`, then `dV` is even. This is Lean checked in `OrientationYorkMomentMap`. It explains why an odd canonical generator can be conjugate to time-even proper volume but does not derive the need to quotient by Y.

Lean module: `GppVerify/QuantumGravity/OrientationObservableObstruction.lean` (targeted CI checked; run against exact head). Declarations: `antisymplectic_invariant_form_zero`, `antisymplectic_fixed_tangents_isotropic`, `antisymplectic_nonzero_obstructs_descent`, `canonical_anti_symplectic_cannot_descend`, `opposite_relative_phase_same_reduced_state`, `opposite_relative_phase_distinguished_globally`, `full_ray_phase_fs_positive`. Proofs use Mathlib, not custom axioms or `sorry`.

## Manuscript edits delivered as current-conversation artifacts (do not silently overwrite originals)

- `Volume_Constraint_orientation_operational_revised.tex` and compiled 16-page PDF.
- `Fisher_Form_reduced_state_scope_revised.tex` and compiled 12-page PDF.
- `Which_Way_Is_Forward_v27_operational_revision.tex` and compiled 113-page PDF, preserves original WWIF structure and use of gppaudit house style (a compatibility copy is bundled for compilation).

Scientific integrity corrections: the Fisher paper's former claim that normalized-state identity freedom *alone proves* the constraint was revised to cite the physical first-law premise; the reduced-state strictness is not promoted to strictness of all purifications. WWIF's claim that gravitational repulsion universally requires negative mass was narrowed, since `Lambda`, pressure and energy conditions matter independently.

## Still open (not certification of all papers)

1. No physical intertwiner from WWIF's `D` real-form carrier and operational observer algebra to generic ADM/covariant phase space or Wigner time reversal.
2. No general theorem forcing York deformations to be gauge/redundant in entanglement equilibrium; the anti-symplectic obstruction shows a discrete orientation quotient cannot simply substitute for this.
3. Full smooth EH/symplectic boundary/corner proof and identification of generic (nonholographic) boundary FS with bulk Omega absent.
4. Original WWIF `Spin(10,2)` interactions, mass-clock/entropy-record locking, nonlinear googly and physical orientation quotient remain hypotheses.
5. Fisher paper's RH-equivalent missing arithmetic channel not constructed; its older numerical certifications were not rerun in this audit.

Sources for context: Jacobson (PRL 116 201101, 2016); Jacobson–Visser (SciPost Phys 7 079, 2019); Belin–Lewkowycz–Sárosi (Phys Lett B 789, 2019, boundary Kähler–bulk Omega in holographic examples); Belin–Lewkowycz–Sárosi (JHEP 03 044, 2019, York volume/complexity); Svesko (PRD 99 086006, 2019).
