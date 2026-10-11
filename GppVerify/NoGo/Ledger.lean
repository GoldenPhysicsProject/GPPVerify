import GppVerify.NoGo.FreeJacobiNoEigenvalue
import GppVerify.NoGo.GramDiagonalTautology
import GppVerify.NoGo.EulerDegreeBlind
import GppVerify.NoGo.EulerPoleTruncation
import GppVerify.NoGo.TwoNodePickInsufficient
import GppVerify.NoGo.QuartetThreeNodeUniversal

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
| One off-axis quartet passes 3-node Pick tests somewhere | **proved false**: every distinct real triple gives `det < 0` (Codex's factorisation) | `GppNoGo.QuartetThreeNode.det3K_neg` | each off-axis quartet is one negative square (Krein–Langer); RH ⇔ zero negative squares of the *sum* — exactly Weil positivity, no loophole |
| Finite Euler truncation (pole + any bounded correction) gives PSD Pick matrices | **proved**: `ε²·det → −1/4` at nodes `1+ε, 1+2ε` | `GppNoGo.EulerPole.eps_sq_det_tendsto`, `det_eventually_neg` | renormalise the pole jointly with the infinite prime tail; truncation cannot work |
| Sharp-window energy `E_ℓ(x) = O(1)` | argued (Littlewood Ω±) — **needs Littlewood's theorem, absent from Mathlib** | — | use a smooth cutoff |
| Any argument not using the Euler product (functional equation + growth alone) | classical (Davenport–Heilbronn) — **needs DH zero computation** | — | the Euler product |
| First-prime-trace renormalisation | restatement of RH (classical) | — | a ζ-independent regularisation with provable analyticity |

Entries marked *pending* or *needs* are not yet theorems here; they must not be cited as proved.
-/
