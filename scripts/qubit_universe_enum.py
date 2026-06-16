#!/usr/bin/env python3
"""
Qubit-universe enumeration (the finite-λ ladder, made concrete).

For a q-qubit world (records = the 2^q computational basis states) and a b-bit
actuality budget, λ resolves a coarse-graining of the records into 2^b blocks and
names one block. This script enumerates the coarse-grainings ("questions") and, for
a set of canonical states Φ, prints the coarse Born law (block weights) and its
Shannon entropy in bits.

  - FULL mode (small cases, total set-partitions S(2^q,2^b) <= FULL_THRESHOLD):
    every set partition of the records into exactly 2^b blocks.
  - LINEAR mode (all cases, up to 5 qubits): every b-bit *linear* question — a
    b-dimensional subspace of the GF(2) dual (read b independent parities of the
    bits). These are the "structured" questions; their count is the Gaussian
    binomial [q,b]_2. The local "read b of the q qubits" reads are a labelled subset.

Honest frame: single fixed (computational) basis — in the real theory the basis is
fixed by einselection; Born is exact; λ is inert ⇒ operationally Everett.
"""
import sys, math, itertools
from fractions import Fraction

FULL_THRESHOLD = 200          # enumerate ALL set partitions only when count <= this
MAXQ = int(sys.argv[1]) if len(sys.argv) > 1 else 5

# ---------- records & bits ----------
def recs(q): return list(range(2 ** q))
def bitstr(r, q): return format(r, '0{}b'.format(q))
def parity(x): return bin(x).count('1') & 1

# ---------- canonical states: record -> Born weight |amp|^2 (Fractions, sum=1) ----------
def st_uniform(q):                       # |+>^q  (product, flat)
    return {r: Fraction(1, 2 ** q) for r in recs(q)}
def st_tilted(q, p=Fraction(4, 5)):      # product, each qubit |0> wt p, |1> wt 1-p
    w = {}
    for r in recs(q):
        wr = Fraction(1)
        for i in range(q):
            wr *= p if ((r >> (q - 1 - i)) & 1) == 0 else (1 - p)
        w[r] = wr
    return w
def st_ghz(q):                           # (|0..0>+|1..1>)/sqrt2
    w = {r: Fraction(0) for r in recs(q)}
    w[0] = Fraction(1, 2); w[2 ** q - 1] = Fraction(1, 2); return w
def st_w(q):                             # equal single-excitation superposition
    w = {r: Fraction(0) for r in recs(q)}
    for i in range(q): w[2 ** (q - 1 - i)] = Fraction(1, q)
    return w
def st_bisep(q):                         # |0> (x) GHZ_{q-1}   (one qubit product, rest GHZ)
    w = {r: Fraction(0) for r in recs(q)}
    w[0] = Fraction(1, 2); w[2 ** (q - 1) - 1] = Fraction(1, 2); return w

def states(q):
    s = [("uniform-product |+>^q", st_uniform(q)),
         ("tilted-product (.8/.2)", st_tilted(q))]
    if q >= 2:
        s += [("GHZ |0..0>+|1..1>", st_ghz(q)), ("W (single-excitation)", st_w(q))]
    if q >= 3:
        s += [("biseparable |0>(x)GHZ", st_bisep(q))]
    return s

# ---------- entropy ----------
def entropy_bits(weights):
    h = 0.0
    for w in weights:
        x = float(w)
        if x > 0: h -= x * math.log2(x)
    return h

# ---------- coarse-graining -> coarse Born law ----------
def coarse_law(part, w):
    """part: list of blocks (each a list of records). Returns list of block weights."""
    return [sum((w[r] for r in blk), Fraction(0)) for blk in part]

# ---------- FULL: all set partitions of `elems` into exactly k non-empty blocks ----------
def set_partitions_k(elems, k):
    n = len(elems)
    if k == 1:
        yield [list(elems)]; return
    if k == n:
        yield [[e] for e in elems]; return
    if k <= 0 or k > n:
        return
    first, rest = elems[0], elems[1:]
    for smaller in set_partitions_k(rest, k - 1):
        yield [[first]] + smaller
    for bigger in set_partitions_k(rest, k):
        for i in range(len(bigger)):
            yield bigger[:i] + [[first] + bigger[i]] + bigger[i + 1:]

# ---------- LINEAR: all b-dim subspaces of GF(2)^q (the dual = parity functionals) ----------
def subspace_key(vecs):
    """Canonical RREF key (frozenset of basis ints) for span; None if rank != len(vecs)."""
    basis = {}
    for v in vecs:
        cur = v
        while cur:
            hb = cur.bit_length() - 1
            if hb in basis:
                cur ^= basis[hb]
            else:
                basis[hb] = cur
                break
        else:
            return None
    if len(basis) != len(vecs):
        return None
    piv = sorted(basis.keys(), reverse=True)
    for p in piv:
        for o in piv:
            if o != p and (basis[o] >> p) & 1:
                basis[o] ^= basis[p]
    return frozenset(basis.values())

def linear_questions(q, b):
    """Yield (label, functionals) for every distinct b-bit linear question."""
    seen = {}
    for combo in itertools.combinations(range(1, 2 ** q), b):
        key = subspace_key(combo)
        if key is None or key in seen:
            continue
        seen[key] = sorted(key, reverse=True)
    out = []
    for key, fns in seen.items():
        out.append(fns)
    return out

def linear_partition(q, fns):
    """Partition records by the tuple of parities (r & f) over the basis functionals."""
    groups = {}
    for r in recs(q):
        lab = tuple(parity(r & f) for f in fns)
        groups.setdefault(lab, []).append(r)
    # order blocks by label
    return [groups[k] for k in sorted(groups.keys())]

def is_coordinate_read(q, fns):
    """If the subspace is spanned by single-bit (coordinate) functionals, name the qubits."""
    qubits = []
    for f in fns:
        if bin(f).count('1') == 1:
            qubits.append(q - 1 - (f.bit_length() - 1))   # qubit index (A=0)
        else:
            return None
    # only a coordinate read if every basis functional is a single coordinate
    return sorted(qubits) if len(qubits) == len(fns) else None

def fns_label(q, fns):
    cr = is_coordinate_read(q, fns)
    names = "ABCDEFGH"
    if cr is not None:
        return "read {" + ",".join(names[i] for i in cr) + "}"
    # otherwise describe as parities
    parts = []
    for f in fns:
        bits = [names[q - 1 - i] for i in range(q) if (f >> (q - 1 - i)) & 1]
        parts.append("⊕".join(bits))
    return "parities [" + " ; ".join(parts) + "]"

# ---------- stirling / gaussian-binomial counts ----------
def stirling2(n, k):
    # number of partitions of n elements into k non-empty unlabeled blocks
    row = [0] * (k + 1); row[0] = 1
    for _ in range(n):
        row = [0] + [j * row[j] + row[j - 1] for j in range(1, k + 1)]
    return row[k] if k <= n else 0
def gauss_binom(n, k, q=2):
    if k < 0 or k > n: return 0
    num = 1; den = 1
    for i in range(k):
        num *= (q ** (n - i) - 1)
        den *= (q ** (i + 1) - 1)
    return num // den

def fmt_law(law):
    return "(" + ", ".join(str(x) for x in law) + ")"

# ---------- driver ----------
def run():
    print("=" * 96)
    print("QUBIT-UNIVERSE ENUMERATION — q = 1..{}  (coarse-grainings × canonical states)".format(MAXQ))
    print("records = 2^q basis states · b-bit budget → 2^b blocks · weights = exact Born |amp|²")
    print("=" * 96)
    for q in range(1, MAXQ + 1):
        for b in range(1, q + 1):
            R, B = 2 ** q, 2 ** b
            S = stirling2(R, B)
            L = gauss_binom(q, b)
            C = math.comb(q, b)
            print("\n" + "#" * 96)
            print("q = {} qubits  ·  b = {} bit(s)  →  {} records, {} blocks".format(q, b, R, B))
            print("  total coarse-grainings  S({},{}) = {:,}".format(R, B, S))
            print("  linear (structured) questions  [{}, {}]_2 = {:,}   (coordinate reads: C({},{}) = {})"
                  .format(q, b, L, q, b, C))
            sts = states(q)
            print("  states: " + " | ".join(name for name, _ in sts))

            full = S <= FULL_THRESHOLD
            if full:
                print("  --- FULL enumeration: all {} set partitions ---".format(S))
                parts = list(set_partitions_k(recs(q), B))
            else:
                print("  --- LINEAR enumeration: all {} structured questions (full space too large) ---".format(L))
                parts = [linear_partition(q, fns) for fns in linear_questions(q, b)]
                qlabels = [fns_label(q, fns) for fns in linear_questions(q, b)]

            # per-state entropy summary
            summ = {name: [] for name, _ in sts}
            for idx, part in enumerate(parts):
                if full:
                    desc = "{" + " | ".join(",".join(bitstr(r, q) for r in blk) for blk in part) + "}"
                else:
                    desc = qlabels[idx]
                line = "  [{:>4}] {:<34}".format(idx, desc[:34])
                cols = []
                for name, w in sts:
                    law = coarse_law(part, w)
                    H = entropy_bits(law)
                    summ[name].append(H)
                    cols.append("{}={:.3f}b".format(name.split()[0][:4], H))
                # print law only in FULL mode (compact); in LINEAR mode print entropies
                if full:
                    laws = " ; ".join("{}:{}".format(name.split()[0][:4], fmt_law(coarse_law(part, w)))
                                      for name, w in sts)
                    print(line + " " + laws)
                else:
                    print(line + " " + "  ".join(cols))

            print("  --- summary (Shannon entropy of the coarse Born law, bits) ---")
            for name, _ in sts:
                hs = summ[name]
                ndef = sum(1 for h in hs if h < 1e-9)
                print("    {:<26} H ∈ [{:.3f}, {:.3f}]   definite(H=0): {}/{}"
                      .format(name, min(hs), max(hs), ndef, len(hs)))

if __name__ == "__main__":
    run()
