import GppVerify.NoGo.FreeJacobiNoEigenvalue
import GppVerify.NoGo.GramDiagonalTautology
import GppVerify.NoGo.EulerDegreeBlind
import GppVerify.NoGo.EulerPoleTruncation
import GppVerify.NoGo.TwoNodePickInsufficient
import GppVerify.NoGo.QuartetThreeNodeUniversal
import GppVerify.NoGo.QuartetSignature
import GppVerify.NoGo.QuartetFourNode
import GppVerify.NoGo.CayleyGap44
import GppVerify.NoGo.LaguerreCutoff
import GppVerify.NoGo.GaussianHeatOS
import GppVerify.NoGo.TwirlNotCollapse
import GppVerify.NoGo.FiniteNoMasking
import GppVerify.NoGo.FiniteLoewnerNoMasking

/-!
# The No-Go ledger

Policy (Daniel, 2026-10-11): a no-go is trusted exactly as much as a go — only when it is a Lean
theorem. Each entry states the **strategy refuted**, the **witness** (an explicit object satisfying
every hypothesis the strategy uses while violating its conclusion, or a proof that the conclusion
carries no information), and the **hint**: which property of `ζ` the witness lacks, i.e. what any
successful argument must use.

| No-go | Status | Lean | Hint (what a proof must use) |
|---|---|---|---|
| Zeros as eigenvalues of the free Jacobi operator | **proved** | `GppNoGo.FreeJacobi.no_l2_eigenvector` | boundary/scattering data or a perturbed operator |
| Cross-prime lower bound from window energy | **proved** (it is Gram positivity) | `GppNoGo.GramDiagonal.offDiag_re_ge_neg_diag` | a signed/upper off-diagonal bound, or the linear Weil term inside the Gram matrix |
| Euler-degree defect `D_p` as zero detector | **proved** | `GppNoGo.EulerDegree.defect_shift_invariant` | splitting witnesses `V_p`, `H_p`, or Archimedean completion |
| Two-node Pick positivity (at every real node pair) implies full Pick | **proved** (Codex's witness + factorisation, Astra's quartet) | `GppNoGo.TwoNodePick.two_node_does_not_imply_three` | sizes ≥ 3 **and** arithmetic input: the quartet has ξ's symmetry and height but no Euler product |
| One off-axis quartet passes 3-node Pick tests somewhere | **proved false**: every distinct real triple gives `det < 0` (Codex's factorisation) | `GppNoGo.QuartetThreeNode.det3K_neg` | each off-axis quartet carries exactly **two** negative squares, on-line pairs none (`GppNoGo.QuartetSignature`); RH ⇔ zero negative squares of the *sum* — exactly Weil positivity, no loophole |
| An off-axis quartet can hide from finite real-node Pick tests | **proved false**: at *every* 4 distinct positive nodes there is a 2-dim negative subspace (Codex's Vandermonde congruence) | `GppNoGo.QuartetFourNode.two_negative_at_four_nodes` | detection needs no clever nodes; only masking by on-line mass in the infinite sum can hide a quartet |
| Finitely many on-line zero pairs can mask an off-axis quartet in the real-node Pick form | **proved false**: one quartet + any finite family of on-line pairs (distinct heights `γ_l ≠ 0`) has a 2-dim negative subspace at some finite set of positive nodes (Codex's additivity, `r = 1` case) | `GppNoGo.FiniteNoMasking.no_masking` | masking needs **infinitely** many on-line constraints — the infinite sum over ξ's zeros, i.e. Weil positivity itself; the general `r`-quartet inertia `(2r+2m, 2r)` still needs cross-quartet independence + Sylvester |
| Finitely many on-line pieces can mask an off-axis quartet's Loewner (shifted-Stieltjes) negativity | **proved false**: `r` quartets + any finite on-line pieces `κ_l/(u+μ_l)` (any real `κ_l`) give, at **every** set of `≥ 2r+m` positive nodes, a Loewner form equal to `−2Σ t_j²` on an `r`-dim family of weights; with `κ_l > 0` also a positive `(r+m)`-dim family, so inertia `(r+m, r)` (Codex's C6 Loewner theorem) | `GppNoGo.FiniteLoewnerNoMasking.no_masking` | Stieltjes-ness of the full `m_*` needs the **infinite** on-line family — Codex's v34 RH-equivalent criterion |
| Finite Euler truncation (pole + any bounded correction) gives PSD Pick matrices | **proved**: `ε²·det → −1/4` at nodes `1+ε, 1+2ε` | `GppNoGo.EulerPole.eps_sq_det_tendsto`, `det_eventually_neg` | renormalise the pole jointly with the infinite prime tail; truncation cannot work |
| Finite (or subexponential) prime cutoff reproduces the Cayley–Laguerre `E_n` | **proved**: any truncation with `N ≤ e^{n/48}` has `(−1)ⁿE_{n,N} < 0`, swamped by the `(−2)ⁿ` pole residue (Codex's observation, explicit bound) | `GppNoGo.LaguerreCutoff.prime_cutoff_sign`, `fixed_cutoff_eventually` | cutoff must grow at least exponentially in `n`; the prime tail and the pole must be renormalised together |
| Positive prime measure transfers OS (Hankel) positivity to the heat kernel through Gaussian subordination | **proved false**: for every length `a = log p` the amplitude `(4πt)^{-1/2}e^{-a²/4t}` has a negative 2×2 OS–Hankel determinant at `t = 3a²/16, 5a²/16` (ratio `4e^{-1/15}/√15 < 1`; Codex) | `GppNoGo.GaussianHeatOS.gaussian_hankel_det_neg` | the Gamma/Archimedean part must actively restore reflected positivity of the *completed* `K(t)`; a mixed amplitude `⟨δ_a, e^{tΔ}δ_0⟩` is not a norm |
| *(book correction)* Gauge invariance of a state yields collapse onto singlets (*On the Nature of Nature*, Ch. 11) | **proved false**: `U_θ = diag(1,e^{iθ})`, `ρ = |e₂⟩⟨e₂|` is twirl-invariant but `PρP = 0`, where `P = (1/2π)∫U_θ dθ = diag(1,0)` (Codex) | `GppNoGo.TwirlNotCollapse.collapse_fails` | Born probabilities come from a positive state's GNS representation `ω(P) = ‖π(P)Ω‖²`, not from Haar averaging |
| Sharp-window energy `E_ℓ(x) = O(1)` | argued (Littlewood Ω±) — **needs Littlewood's theorem, absent from Mathlib** | — | use a smooth cutoff |
| Any argument not using the Euler product (functional equation + growth alone) | classical (Davenport–Heilbronn) — **needs DH zero computation** | — | the Euler product |
| *(criterion)* One-sided Cayley–Laguerre bound (`E_n ≤ C(n+1)^k`, or just `limsup (E_n⁺)^{1/n} ≤ 1`) ⇒ RH (Codex) | analytic step **proved**: Pringsheim `GppPringsheim.pringsheim` and its one-sided corollary `GppOneSidedPringsheim.summable_of_oneSided` (coefficients bounded below by a radius-1 series + analytic continuation along [0,1) ⇒ radius 1); arithmetic bound **open** | `GppVerify/Analysis/Pringsheim.lean`, `OneSidedPringsheim.lean` | a one-sided subexponential bound suffices, but it is Landau-type equivalent to RH |
| First-prime-trace renormalisation | restatement of RH (classical) | — | a ζ-independent regularisation with provable analyticity |
| *(detector, not a no-go)* Cayley 2×2 gap test at `s₀ = 2` misses off-axis quartets | **proved false** for Astra's quartet: passes gaps 1–43, fails at gap 44 | `GppNoGo.CayleyGap44.gap44_noGo` | a different finite projection of the same RH-equivalent positivity; unconditional `sup aₙ ≤ 2a₀` for ξ is RH-strength |

Entries marked *pending* or *needs* are not yet theorems here; they must not be cited as proved.
-/
