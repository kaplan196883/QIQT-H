#!/usr/bin/env python3
"""
A fully explicit λ for a toy 3-qubit universe — one concrete worked example.

It assembles everything the long discussion converged on, in the smallest non-trivial world:
  • Φ  = a definite 3-qubit state ⇒ 8 computational-basis RECORDS with exact Born weights.
  • the SCAFFOLD = the coarse-graining REFINEMENT TREE (1 bit → 2 blocks, 2 → 4, 3 → 8 records),
    self-similar: every node splits in two. (This is the part that can be 'fractal'.)
  • λ = ONE DEFINITE record (a leaf), equivalently one PATH root→leaf down the tree.
  • No randomness: λ = inverse-CDF(seed). The single brute fact is WHICH SEED s∈[0,1) is actual;
    given s, the whole path is DETERMINED. No dice, no process.
  • Born-typical: a seed spread uniformly over [0,1) lands in each leaf's interval with probability
    = its Born weight ⇒ across many universes the leaf frequencies are Born. Each one is definite.
  • = Everett: Φ keeps all 8 branches unitary; λ only tags one as ACTUAL; it is inert.

Standard library only.
"""

# ----- Φ : a product of three tilted qubits (chosen so all 8 weights are distinct) -----
#   qubit A: √0.9|0> + √0.1|1>   B: √0.6|0> + √0.4|1>   C: √0.7|0> + √0.3|1>
wA = {0: 0.9, 1: 0.1}
wB = {0: 0.6, 1: 0.4}
wC = {0: 0.7, 1: 0.3}

def record_weight(x, y, z):
    return wA[x] * wB[y] * wC[z]

RECORDS = [(x, y, z) for x in (0, 1) for y in (0, 1) for z in (0, 1)]   # 000 … 111

def label(r):
    return "".join(map(str, r))

# ----- the actuality seed: the ONE brute fact (a fixed number in [0,1)) -----
SEED = 0.42

def inverse_cdf(seed, blocks):
    """blocks = list of (name, weight); return the block whose cumulative interval holds `seed`.
       This is DETERMINISTIC: given the seed, the block is fixed. No randomness."""
    c = 0.0
    for name, w in blocks:
        if seed < c + w:
            return name, (c, c + w)
        c += w
    return blocks[-1][0], (c - blocks[-1][1], c)

def run():
    print("=" * 78)
    print("A TOY 3-QUBIT UNIVERSE — an explicit λ")
    print("  Φ = (√0.9|0>+√0.1|1>) ⊗ (√0.6|0>+√0.4|1>) ⊗ (√0.7|0>+√0.3|1>)   (qubits A,B,C)")
    print("=" * 78)

    # 1. the 8 records, Born weights, and CDF intervals
    print("\n  THE 8 RECORDS (the leaves) — Born weight = |amplitude|², and their CDF intervals:")
    print("    record ABC   Born weight   CDF interval")
    print("    " + "-" * 46)
    c = 0.0
    blocks3 = []
    for r in RECORDS:
        w = record_weight(*r)
        print("    {:<13}{:<14.3f}[{:.3f}, {:.3f})".format(label(r), w, c, c + w))
        blocks3.append((label(r), w))
        c += w
    print("    {:<13}{:.3f}".format("(sum)", c))

    # 2. the scaffold: the refinement tree (1 → 2 → 4 → 8), self-similar
    print("\n  THE SCAFFOLD — the coarse-graining REFINEMENT TREE (each node splits in two):")
    # 1-bit: resolve A only
    b1 = []
    for x in (0, 1):
        w = sum(record_weight(x, y, z) for y in (0, 1) for z in (0, 1))
        b1.append(("{}**".format(x), w))
    # 2-bit: resolve A,B
    b2 = []
    for x in (0, 1):
        for y in (0, 1):
            w = sum(record_weight(x, y, z) for z in (0, 1))
            b2.append(("{}{}*".format(x, y), w))
    print("    1 bit  (2 blocks):  " + "   ".join("{}={:.3f}".format(n, w) for n, w in b1))
    print("    2 bits (4 blocks):  " + "   ".join("{}={:.3f}".format(n, w) for n, w in b2))
    print("    3 bits (8 records): the leaves above")

    # 3. λ from the seed — the actual PATH down the tree
    print("\n  λ — the ACTUAL history, read off the single seed s = {} (deterministic):".format(SEED))
    n1, i1 = inverse_cdf(SEED, b1)
    n2, i2 = inverse_cdf(SEED, b2)
    n3, i3 = inverse_cdf(SEED, blocks3)
    print("    budget 1 bit :  s ∈ [{:.3f},{:.3f}) ⇒ block {}   (A = {})".format(i1[0], i1[1], n1, n1[0]))
    print("    budget 2 bits:  s ∈ [{:.3f},{:.3f}) ⇒ block {}   (A,B = {},{})".format(i2[0], i2[1], n2, n2[0], n2[1]))
    print("    budget 3 bits:  s ∈ [{:.3f},{:.3f}) ⇒ record {} ← THE ACTUAL WORLD".format(i3[0], i3[1], n3))
    print("    ⇒ λ traces ONE path:  root → {} → {} → {}   (A={}, B={}, C={})".format(
        n1, n2, n3, n3[0], n3[1], n3[2]))
    print("    The coarse λ is always CONSISTENT with the fine λ (nesting): {} ⊃ {} ⊃ {}.".format(n1, n2, n3))

    # 4. Born-typical across an ensemble of universes (each definite)
    print("\n  BORN, as a frequency across many universes (each with its own definite seed):")
    print("    spread seeds uniformly over [0,1); the fraction landing in each leaf's interval")
    print("    equals its Born weight — so leaf frequencies reproduce |amplitude|² exactly.")
    print("    (Each universe still has ONE definite λ; 'probability' is the across-universe count.)")

    leaf = n3   # the actual record label, e.g. "001"
    print("""
  WHAT THIS SHOWS (the whole discussion, in one toy):
   • λ is a finite INDEX — here exactly 3 bits (the leaf {leaf}), or 3 binary choices down the tree.
   • DEFINITE, NO RANDOMNESS: λ = inverse-CDF(seed). The one brute fact is which seed s is actual;
     given s, the entire path is fixed. There is no dice and no process anywhere in λ.
   • The SCAFFOLD (the refinement tree) is self-similar — every node splits in two; this is the
     'fractal' part. λ is ONE definite PATH through it, not a random walk on it.
   • Φ keeps all 8 branches (exactly unitary); λ only marks {leaf} as ACTUAL ⇒ inert ⇒ = Everett.
   • PATTERNLESS only shows up for LONG histories: one 3-bit λ is trivially simple, but the leaf
     SEQUENCE of many independent runs is Born-typical = incompressible (the Martin-Löf point) —
     definite, yet with no short description. Here, with N=1 'run', that is not yet visible.""".format(leaf=leaf))

if __name__ == "__main__":
    run()
