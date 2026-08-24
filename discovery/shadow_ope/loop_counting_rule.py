"""
loop_counting_rule.py

Investigates Daniel's half-remembered rule ("loops come from double
discontinuities, 2 loops from triple... or points, I can't remember").
This is NOT a vague hunch to chase from scratch -- GppVerify already has an
UNCONDITIONALLY PROVEN Lean theorem about exactly this
(`GppTreeLoopSewing.pairSewing_cycleRank` in
GppVerify/CelestialHolography/TreeLoopSewing.lean), plus a documented
correction of an earlier WRONG version of the same claim. This file
re-derives and independently verifies that rule from scratch in Python (not
just trusting the Lean proof), and checks the specific claim about "double
discontinuities" against the file's own `doubleShadowDisc` structure.

THE PROVEN RULE (TreeLoopSewing.lean, cross-checked independently below):
    Sewing L disjoint pairs of leaves on an open (4+2L)-point cubic tree
    gives a connected 4-point graph of cycle rank EXACTLY L.
i.e. L pair-sewings <-> an L-loop topology. This is pure graph theory
(V - E + 1 for a connected graph), proved for general L in Lean via
`pairSewing_cycleRank`, unconditional -- no physics assumption.

THE "L+1" CORRECTION ALREADY ON RECORD (TreeLoopSewing.lean's own header
comment, lines 37-43): "The paper's early draft language about 'L+1 shadow
closures' is corrected in this version: closing L disjoint pairs of tree
legs is L pair sewings, giving cycle rank L -- not L+1." This is almost
certainly the exact source of the half-remembered rule -- an early WRONG
draft said L+1, later corrected to L. Worth stating precisely rather than
leaving it as "some formula, not sure": the CORRECT, proven statement is
L pairs <-> L loops (not L+1), and this file re-confirms that correction
independently rather than just repeating the Lean comment.

WHERE "DOUBLE" GENUINELY ENTERS (matches "loops come from double
discontinuities" for L=1, precisely, not loosely): each PAIR sewing is
associated with `doubleShadowDisc := disc6 . disc5` (function composition
of exactly 2 leg-wise shadow discontinuities, one per leg of the sewn
pair) -- see TreeLoopSewing.lean lines 78-90 and the paper's Definition 2.1
this file cites. So for L=1 (one pair sewn, one loop), the paper's own
mechanism is literally A SINGLE DOUBLE discontinuity (2 leg-wise ops). For
general L: L pair-sewings = L applications of doubleShadowDisc = 2L total
leg-wise shadow-discontinuity operations, structured as L pairs -- NOT a
single "(L+1)-fold" or "triple" discontinuity for L=2. The "triple
discontinuity for 2 loops" half of the half-remembered rule does not match
this specific project's proven construction; the "double discontinuity"
half (for the ONE-LOOP case specifically) matches exactly.

CONFIRMS THE SPECIFIC BOX TOPOLOGY, NOT JUST GENERIC CYCLE RANK: cycle rank
alone doesn't distinguish a box from (say) a bubble-with-a-tadpole -- both
have cycle rank 1. Checked explicitly below (independent of Lean) that
sewing the comb's TWO FAR ENDS (leg 5 at vertex A, leg 6 at vertex D, in
celestial_kinematics.py's "A:{1,5} B:{2} C:{3} D:{4,6}" convention) gives a
literal 4-cycle A-B-C-D-A -- the box specifically -- matching
`closedBoxDenominator = Q(l) * D1 * D2 * D3`'s four factors exactly. Sewing
adjacent legs instead (both extra legs at the same vertex) would ALSO give
cycle rank 1 but a topologically different (tadpole) graph -- confirming
WHICH pairing matters for getting the box specifically, even though the
LOOP COUNT (cycle rank) doesn't care which pairing is chosen.

HONEST SCOPE: `pairSewing_cycleRank` and this file's independent
re-verification are pure graph theory / combinatorics -- completely proven,
zero physics content. The genuinely open, physics-laden claim is
`ShadowPairSewing.sewing_identity` (TreeLoopSewing.lean lines 215-220): that
the ANALYTIC double-shadow-discontinuity operation on an actual celestial
correlator equals the momentum-space pair closure. The graph theory says
"L pair-sewings gives an L-loop TOPOLOGY"; it does not say "L pair-sewings
of shadow discontinuities gives the L-loop AMPLITUDE VALUE" -- that
translation from topology to analytic value is exactly the open problem
this entire session's K1/box-reconstruction work has been attacking, and
remains unproved.
"""


def build_cubic_tree(n_leaves):
    assert n_leaves >= 3
    n_internal = n_leaves - 2
    edges = []
    for i in range(n_internal - 1):
        edges.append((f"I{i}", f"I{i+1}"))
    edges.append(("L1", "I0"))
    edges.append(("L2", "I0"))
    leaf_idx = 3
    for i in range(1, n_internal):
        edges.append((f"L{leaf_idx}", f"I{i}"))
        leaf_idx += 1
    edges.append((f"L{n_leaves}", f"I{n_internal - 1}"))
    vertices = set()
    for a, b in edges:
        vertices.add(a)
        vertices.add(b)
    return vertices, edges


def cycle_rank(vertices, edges):
    return len(edges) - len(vertices) + 1


def sew_pairs(vertices, edges, leaf_pairs):
    return vertices, list(edges) + list(leaf_pairs)


def find_cycle(vertices, edges):
    adj = {v: [] for v in vertices}
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    visited, parent = {}, {}

    def dfs(u, par):
        visited[u] = True
        parent[u] = par
        for v in adj[u]:
            if v == par:
                continue
            if v in visited:
                cyc = [v, u]
                cur = u
                while parent.get(cur) is not None and parent[cur] != v:
                    cur = parent[cur]
                    cyc.append(cur)
                return cyc
            r = dfs(v, u)
            if r:
                return r
        return None

    return dfs(next(iter(vertices)), None)


def main():
    print("=" * 78)
    print("PART 1: independent re-verification of pairSewing_cycleRank, L=0..6")
    print("(pure graph theory, matches the Lean-proven general-L statement)")
    print("=" * 78)
    for L in range(0, 7):
        n = 4 + 2 * L
        V, E = build_cubic_tree(n)
        assert cycle_rank(V, E) == 0
        leaf_pairs = [(f"L{5+2*i}", f"L{6+2*i}") for i in range(L)]
        V2, E2 = sew_pairs(V, E, leaf_pairs)
        cr = cycle_rank(V2, E2)
        status = "OK" if cr == L else "MISMATCH"
        print(f"  L={L}: {n}-point tree, {L} pair-sewings -> cycle rank {cr} (expect {L})  {status}")

    print()
    print("=" * 78)
    print("PART 2: does sewing the comb's far ends give the BOX specifically,")
    print("not just some generic cycle-rank-1 graph?")
    print("=" * 78)
    vertices = {"A", "B", "C", "D"}
    edges = [("A", "B"), ("B", "C"), ("C", "D")]
    print(f"  Open comb (D1,D2,D3): cycle rank = {cycle_rank(vertices, edges)} (tree)")
    edges_sewn = edges + [("A", "D")]
    cr = cycle_rank(vertices, edges_sewn)
    cyc = find_cycle(vertices, edges_sewn)
    print(f"  Sew far ends (leg 5@A, leg 6@D): cycle rank = {cr}, cycle = {cyc}")
    print(f"  -> {'literal 4-cycle (box)' if cyc and len(cyc) == 4 else 'NOT a 4-cycle'}, "
          f"matching closedBoxDenominator = Q(l)*D1*D2*D3's four factors")
    edges_tadpole = edges + [("A", "A")]
    print(f"  Contrast, sew adjacent legs (both at A): cycle rank = "
          f"{cycle_rank(vertices, edges_tadpole)} (same count, different topology -- a tadpole, not a box)")

    print()
    print("=" * 78)
    print("PART 3: the 'double discontinuity' terminology, precisely")
    print("=" * 78)
    print("  doubleShadowDisc := disc6 . disc5  (2 leg-wise ops per pair sewing)")
    for L in range(1, 5):
        print(f"  L={L}: {L} pair-sewing(s) = {L} application(s) of doubleShadowDisc "
              f"= {2*L} total leg-wise shadow discontinuities")
    print()
    print("  So: L=1 (one loop) <-> exactly ONE double discontinuity. Matches")
    print("  'loops come from double discontinuities' precisely for the one-loop case.")
    print("  L=2 (two loops) <-> TWO double discontinuities (4 leg-wise ops total),")
    print("  not a single 'triple' discontinuity -- the 'triple for 2 loops' half of")
    print("  the half-remembered rule does not match this project's proven construction.")


if __name__ == "__main__":
    main()
