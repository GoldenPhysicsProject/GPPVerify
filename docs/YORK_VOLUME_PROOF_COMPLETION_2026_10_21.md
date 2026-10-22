# Finishing the volume-constraint explanation: proof obligations (2026-10-21)

**Research objective, unchanged:** explain *why proper spatial volume must be fixed* for the entropy-only version of Jacobson's small causal-diamond entanglement equilibrium, rather than merely note that a volume term happens to occur.

## What is proved / already in GPPVerify main

- Finite-state first-law invariance of the response under scalar shifts of a **fixed** modular Hamiltonian, and a counterexample to identifying it with geometric fixed volume (VolumeConstraintEntanglement, FubiniStudyYorkBridge).
- Einstein/CKV concircularity at the level of explicitly assumed curvature identities and fixed-volume RNC coefficients, with small-ball ensemble-response restrictions.
- Finite-dimensional York/ADM symplectic contraction yielding the volume differential; CP1 local FS Kähler and time-reversal identities; conditional FS–York orthogonality (YorkVolumeSymplectic, FubiniStudyLocalKahler, FubiniStudyYorkBridge).
- The new YorkVolumeReduction module (PR #409) states that if a York flow direction is to become null on admissible tangents for presymplectic quotient descent, then *exactly* the fixed-volume tangents work, given nonzero York moment-map coefficient. It has additional direct corollaries from the existing finite ADM identity. Exact-head CI must be checked.

## Two independent arguments, do not conflate

**A. Necessary constraint for entropy-only equilibrium (physically defensible first paper).**
From the Einstein–Hilbert Iyer–Wald/Jacobson–Visser causal-diamond first law, including all matter matching conditions, fixed Lambda and nonzero boundary mean curvature:
  dS_gen = eta*k*dV.
If dS_gen vanishes on every variation in an admitted linear subspace, then that subspace is contained in ker(dV). If dV has a nonzero direction, unrestricted entropy stationarity fails. This explains why the *entropy-only* variational formulation must fix V, while the equivalent free-conformal-energy formulation can vary it. Concircularity explains why the work functional is **unweighted proper volume**. This is conditional on the EH/dynamical first law, not on quantum normalization alone.

**B. Necessary constraint for York-flow symplectic reduction (new theorem).**
If York flow is to be treated as vertical/redundant, and its symplectic contraction is proportional to dV, then the form descends to the quotient only on constant-volume level sets. Standard moment-map reduction supplies a general model of the mechanism. This algebraic implication is exact and independent of entropy first-law assumptions; the physical assertion that the *entanglement equilibrium state space* must perform this York reduction is NOT proved. Belin–Lewkowycz–Sárosi explicitly distinguish their York deformation from a diffeomorphism; treating it as gauge universally is not justified.

## Mandatory remaining bridges, prioritized

1. **Continuum geometric formalization.** Formalize ADM volume first variation for smooth Riemannian slices with boundaries, canonical momenta from Einstein–Hilbert, linearized Hamiltonian/momentum constraints on a maximal slice, York variation, full covariant symplectic pairing including boundary/corner terms. Show the finite-sum formalization is recovered from this. Establish relevant CKV normal-slope constancy without assuming the Ricci Lie derivative as an undeclared axiom.
2. **Physical ensemble derivation.** Either derive from modular/QFT and boundary conditions why the York-flow direction is vertical in the *specified* quantum gravitational ensemble, or show an alternative independent physical principle that selects the entropy-only ensemble and prevents an additional work term. Without this, the stronger claim "normalization alone makes a geometric constraint mandatory" is unjustified. Attempt an explicit counterexample on off-shell admissible states if the putative identification fails.
3. **Boundary-bulk Fubini–Study identification.** BLS prove a version in controlled holographic source-state settings. Show its hypotheses hold for the Jacobson small causal diamond or state precisely the restricted holographic class. The pure-state FS Kähler metric is NOT automatically the mixed-state Kubo–Mori Fisher metric used in the companion Fisher paper.
4. **Analytic second variation and higher curvature.** Relative-entropy positivity proves a mixed-state information-metric statement; the gravitational geometric Hessian/canonical energy and generalized volume require separate construction, boundary conditions and control.

## Conservative manuscript theorem statement

> In Einstein–Hilbert small-diamond mechanics, with a matched modular response and fixed cosmological constant, the on-shell first law makes generalized entropy stationary on an admissible space only if all its variations preserve proper volume. The Einstein/CKV concircular identity explains why the geometric work one-form is the *unweighted* proper-volume differential. Independently, the ADM York moment-map identity makes the same fixed-volume tangent space necessary for reduction by York flow if such a quotient is part of the physical construction.

Do **not** say that the cosmological multiplier equals the entropy volume multiplier: the latter is -eta*k, nonzero for a finite flat diamond when Lambda=0.

## Relevant primary sources

- T. Jacobson, *Entanglement equilibrium and the Einstein equation* (2016), arXiv:1505.04753.
- T. Jacobson & M. Visser, *Gravitational thermodynamics of causal diamonds in (A)dS* (2019), arXiv:1812.01596.
- A. Belin, A. Lewkowycz & G. Sárosi, *Complexity and the bulk volume, a new York time story* (2019), arXiv:1811.03097.
- A. Svesko, *From entanglement to thermodynamics and to gravity* (2019), Phys. Rev. D 99 086006, arXiv:1810.12236.
- T. Jacobson & M. Visser, *Entropy of causal diamond ensembles* (2023), arXiv:2212.10608.

**Verification convention:** Cite Lean declarations only after an exact-head CI run has completed. Document mathematical assumptions and physical analogies separately. Never use a theorem of the form `True := trivial` as a proof of the research claim.
