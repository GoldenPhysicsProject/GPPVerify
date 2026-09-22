# Charged-CAR / Kähler–Dirac / black-mirror orientation synthesis

Date: 2026-09-09
Branch: `codex/orientation-mass-time-formalization`

## Executive result

The orientation programme has now split into a **standard theorem layer** and a **strong two-sheet extension**.

The standard charged-field theorem is sharper than the original Boolean toy:

\[
q=\operatorname{sgn}b,\qquad J=I\,q,\qquad h=|b|,\qquad b=q h,
\]

where `I` is the original charged phase-space complex structure and `J` is the positive-energy one-particle complex structure. Therefore

\[
\boxed{q=-IJ}.
\]

On `q=+1`, the two complex structures align (`J=I`); on `q=-1`, they anti-align (`J=-I`).  Physical particle/antiparticle charge is therefore literally a relative complex-orientation grading in standard positive-energy charged quantization.

This is prior art / standard mathematics, primarily Dereziński–Gérard, *Positive energy quantization of linear dynamics* (2009), Sec. 7.2.

## The three arrows must remain distinct

1. **Coordinate/proper time:** the real spacetime parameter.
2. **Microscopic quantum phase/causal orientation:** sign of the complex/phase convention or signed first-order frequency generator.
3. **Thermodynamic/record arrow:** an emergent property of a many-body state and its boundary conditions.

The second is not the third.  Opposite microscopic phase orientations can have the same positive physical energy and can be represented at the same increasing coordinate time.

## Standard charged CAR

For a nondegenerate charged fermionic dynamics `r_t = exp(i t b)`:

\[
q=\mathrm{sgn}\,b,\qquad J=I q,\qquad h=|b|.
\]

The charged CAR field is

\[
\psi(y)=a(1_+y)+a^*(1_-y),
\]

so the negative-frequency subspace is quantized by swapping creation and annihilation.  Both particle and antiparticle excitations have positive Hamiltonian `dΓ(h)`.  Thus both microscopic frequency orientations are already present locally in the relativistic field without implying negative physical energy.

### Exact C/T dictionary

At the structural level:

- charge reversal is anti-linear with respect to the original charged complex structure but linear on the positive-energy one-particle space.  Hence it reverses `I`, preserves `J`, and flips `q`;
- time reversal is anti-linear with respect to both complex structures.  Hence it reverses `I` and `J` together and preserves `q`.

Abstractly, for `q=-IJ`, an odd number of orientation flips reverses q while an even number preserves q.  This is formalized representation-independently in `RelativeComplexOrientationSymmetryTheorem.lean`.

## Critical correction to the earlier four-lift toy

The earlier carrier `(++,+-,-+,--)` is a useful finite model but is **not derived from standard charged CAR**.

Because `I` is actual scalar multiplication by `i`, every complex-linear operator commutes with it.  Therefore a complex-linear internal deck operator satisfying

\[
DI=-ID
\]

must be zero.  So simultaneous reversal `(I,J)->(-I,-J)` is not a nontrivial ordinary unitary/internal gauge operation on the same complex Hilbert space.  The natural map is anti-linear conjugation.

Consequently standard QFT does **not** imply that every electron is literally a coherent

\[
(|++\rangle+|--\rangle)/\sqrt2
\]

hidden-state superposition.  The absolute signs of `I` and `J` are structures/presentations, not an extra ordinary particle quantum number.

The global field-theory version is even sharper: by the Shale–Stinespring criterion, Fock representations from exactly opposite polarizations `J` and `-J` are generally not unitarily equivalent in infinite dimension because `J-(-J)=2J` is not Hilbert–Schmidt.  The finite cutoff squared Hilbert–Schmidt norm is `4N`, formalized in `OppositePolarizationShaleObstruction.lean`; the Shale–Stinespring equivalence theorem itself is external analytic input.

## Where literal two-sheet superposition DOES occur

Boyle–Deng, *CPT-Symmetric Kähler–Dirac Fermions* (arXiv:2511.11548), is a major prior-art collision.

They propose:

- a two-sheeted spacetime whose sheets are related by PT, equivalently by `i <-> -i`;
- both sheets have positive-energy, positive-norm states when quantized with their own causal convention;
- to prevent unphysical cross-sheet interactions and remove doubling, impose the KD-Majorana condition
  \[
  \Psi^c=(i\gamma^2)\Psi^*(i\gamma^2)=\Psi;
  \]
- a forward-sheet particle is necessarily paired in an invariant/symmetric combination with its mirror antiparticle on the opposite sheet.

Therefore the literal idea “half one orientation, half its mirror orientation” already has a very close published/preprint realization.  It must be cited as prior art, not claimed as a new GPP prediction.

The minimal anti-linear pairing `Theta(a,b)=(conj b,conj a)` is formalized in `KDMajoranaOrientationBridge.lean`; exact Theta-invariance forces equal sheet norms, and normalization gives one-half Born weight per sheet in that minimal two-amplitude model.  This is a reality-condition consequence, not a new discovery.

## Why two sheets are safer than locally mixing arrows

Donoghue–Menezes (PRL 123, 171601 (2019)) show that the arrow of causality is tied to quantization conventions and that mixing opposite quantization conventions in the same theory can violate microcausality.

This is an important obstruction to a literal picture of two independently interacting causal arrows at each local spacetime point.  The Boyle–Deng two-sheet construction is designed precisely to avoid those cross-sheet interactions, while the KD-Majorana constraint pairs the sheets without creating an independently interacting duplicate sector.

## Fixed coordinate time versus microscopic phase orientation

Boyle–Deng also make the point in the cleanest possible form.  One sheet uses `+i`, the other `-i`.  Thus at the same real coordinate time

\[
\psi_+(t)\sim e^{-iEt},\qquad \psi_-(t)\sim e^{+iEt},
\]

with positive `E` on each sheet in its own convention.

So the correct microscopic “time arrow” is not `t -> -t` on the displayed diagram.  It can be the sign of the quantum complex/phase orientation at fixed coordinate `t`.

Formalized in `FixedCoordinateOppositeQuantumPhase.lean`.

## Black mirrors

Tzanavaris–Boyle–Turok, *Black Mirrors* (arXiv:2412.09558) provide the corresponding horizon geometry.

Schwarzschild black mirror:

\[
r(\sigma)=2m\left[1+(\sigma/4m)^2\right],\qquad r(\sigma)=r(-\sigma).
\]

Thus `sigma` and `-sigma` are two exterior lifts of the same base radius and coalesce at the horizon.

For collapse, the folded picture has the usual upward displayed time on both sheets, and an infalling particle on one sheet meets its CPT mirror antiparticle from the other at the horizon.  Appendix B gives the stationary CPT isometry

\[
(t,\sigma,\theta,\phi)\mapsto(t,-\sigma,\pi-\theta,\phi+\pi).
\]

The coordinate `t` is unchanged by this displayed map, while sheet/angular orientation changes.  The paper also explains that the black mirror has a different global time orientation from the corresponding Kruskal black hole; in the mirror, the relevant time orientation differs by a sign in the second exterior, and the Gauss-law charge assignment changes correspondingly.

Therefore the viable bridge is NOT `sigma flip = coordinate time reversal`.  The target is a bundle intertwiner

\[
\text{black-mirror sheet/PT exchange}\quad\longrightarrow\quad I\leftrightarrow -I
\]

(or the corresponding KD/CAR complex-orientation map) while the folded display time remains ordinary.

`BlackMirrorKDPhaseBridgeCriterion.lean` records exactly this distinction without pretending the missing bundle map has been proved.

## Thermodynamic arrow

The thermodynamic arrow is still not derived from the microscopic complex orientation.  Boyle–Turok's two-sheet cosmology separately proposes boundary/analyticity conditions that make the thermodynamic arrow point away from the bang.  This is compatible with, but logically distinct from, the charged-CAR/KD phase orientation.

A useful global-state model is thermofield-double-like:

\[
|\Psi\rangle=\sum_n c_n |n\rangle_+\otimes|n\rangle_-,\qquad
(H_+-H_-)|\Psi\rangle=0,
\]

while both local Hamiltonians have positive spectra.  `OrientationThermofieldDouble.lean` proves the finite paired-state algebra.  No claim is yet made that the black-mirror quantum state is literally this exact TFD.

## Current best interpretation

The strongest mathematically defensible formulation is:

1. A charged relativistic field has a charged phase complex structure `I` and a positive-energy/dynamical complex structure `J`.
2. Physical particle/antiparticle charge is their relative alignment `q=-IJ`.
3. Opposite microscopic phase orientations are present in the local field expansion, while the physical Hamiltonian remains positive.
4. Reversing a single orientation relative to a fixed standard reverses the relative charge sign.
5. A complete anti-linear reversal can reverse both absolute complex orientations while preserving their relative charge.
6. A literal symmetric two-sheet particle/mirror-antiparticle state requires an additional doubled geometry/reality condition; KD-Majorana theory provides a concrete prior-art implementation.
7. Opposite causal conventions should not be freely mixed locally; a two-sheet/reality-paired construction is the safer consistent architecture.
8. Black-mirror geometry provides a natural branch/gluing locus where the two mirror exterior descriptions meet, with ordinary folded time on both sides.
9. The thermodynamic arrow is a separate many-body/boundary-condition problem.

## Remaining hard bridge

The next genuinely nontrivial theorem is not another sign identity.  It is to derive the action of the black-mirror/KD sheet map on the actual charged Dirac/KD one-particle polarization:

\[
\mathfrak S:\ (Y,I,b,J,q)_{+}\to(Y,-I,?, ?, ?)_{-}
\]

and prove exactly whether

\[
\mathfrak S J = -J\mathfrak S,\qquad
\mathfrak S q = \pm q\mathfrak S,
\]

with the correct anti-linearity, spin action, gauge conjugation, and horizon boundary condition.

Only after that can the GPP orientation language be said to be geometrically identified with the black-mirror/KD sheets rather than merely algebraically compatible with them.
