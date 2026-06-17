#!/usr/bin/env python3
"""
The permutation quotient — 'the limit on combinations is permutations', made concrete.

The idea (the user's refinement of the bit-limit): every individual configuration is possible,
but indistinguishable constituents make combinations related by a PERMUTATION the SAME physical
configuration. So the distinguishable-combination count is the configuration space quotiented by
the permutation group S_N:

        distinguishable configurations  =  configuration space / permutations

That quotient is basis-independent, it IS quantum statistics, and it is where three threads of
QIQT-H meet: the finiteness (a quotient count), the record structure (relabelings collapse to one
record), and the Born rule (typicality over permutation orbits).

HONEST FRAME (consistent with the whole ladder): the permutation quotient produces REAL, OBSERVED
physics — Bose/Fermi statistics, Pauli exclusion, the Gibbs N!. But that is the standard
symmetrization postulate on Φ, not a new λ effect: λ merely indexes the permutation-quotiented
records. The added clarity is structural — the finiteness is combinatorial/permutational and
basis-independent — and the Born link below still rests on the |amplitude|² typicality premise
(permutation symmetry supplies the orbit structure, not the premise). λ inert ⇒ still = Everett.

Refs in the Lean development: RedundancyCompressible (permuting copies ⇒ one record),
GoldsteinStruyveStep1.step1c_collapse_of_perm_symmetric (Born from permutation symmetry).
Needs only the standard library + numpy (for the concentration plot).
"""
import math
import numpy as np

def comb(n, k):
    return math.comb(n, k) if 0 <= k <= n else 0

# ======================================================================
#  PART 1 — the permutation quotient: distinguishable vs Bose vs Fermi
# ======================================================================
def run_quotient():
    print("=" * 78)
    print("PART 1 — distinguishable configurations = configuration space / permutations")
    print("  N constituents in M single-particle states (modes).")
    print("    distinguishable : M^N            (full tensor product — no quotient)")
    print("    bosons          : C(N+M-1, N)    (symmetric: combinations WITH repetition)")
    print("    fermions        : C(M, N)        (antisymmetric: combinations WITHOUT repetition)")
    print("=" * 78)
    print("  {:<14}{:<16}{:<16}{:<16}{}".format("(N, M)", "distinguishable", "bosons", "fermions", "dist/bosons"))
    print("  " + "-" * 74)
    for N, M in [(2, 4), (3, 6), (5, 10), (10, 20), (10, 1000), (20, 50)]:
        dist = M**N
        bose = comb(N+M-1, N)
        fermi = comb(M, N)
        ratio = dist / bose
        print("  {:<14}{:<16.3e}{:<16.3e}{:<16.3e}{:.3e}".format(
            "({},{})".format(N, M), float(dist), float(bose), float(fermi), ratio))
    print("""
  The quotient is enormous and basis-independent: relabelling identical constituents does not make
  a new configuration. In the dilute limit M ≫ N (few particles, many modes) the reduction
  approaches exactly N!  (each of the N! orderings collapses to one combination) — the Gibbs factor.
  This is the real 'limit on combinations': not which configs exist, but how many are DISTINCT.""")

# ======================================================================
#  PART 2 — Pauli exclusion: the HARD combinatorial limit
# ======================================================================
def run_pauli():
    print("\n" + "=" * 78)
    print("PART 2 — Pauli exclusion: antisymmetry makes the combination limit HARD")
    print("  Fermions: C(M, N) = 0 once N > M — you cannot place two in the same state.")
    print("=" * 78)
    M = 6
    print("  M = {} fermionic states; put N fermions in:".format(M))
    print("  N      C(M,N) distinct combinations")
    print("  " + "-" * 40)
    for N in range(0, M+3):
        c = comb(M, N)
        tag = "" if N <= M else "   ← N>M: IMPOSSIBLE (Pauli)"
        print("  {:<7}{}{}".format(N, c, tag))
    print("""
  This is a genuine, OBSERVED limit on combinations, straight from permutation antisymmetry: at
  most M fermions in M states. It builds the periodic table (shell filling), holds up white dwarfs
  and neutron stars (degeneracy pressure), and forbids two electrons in one quantum state. The
  'combinatorial bit-limit' is not exotic — for fermions it is Pauli, and we see it everywhere.
  (Standard QM, a property of Φ's antisymmetry — not λ.)""")

# ======================================================================
#  PART 3 — Gibbs: the permutation quotient in the ENTROPY
# ======================================================================
def run_gibbs():
    print("\n" + "=" * 78)
    print("PART 3 — the permutation quotient in the entropy: the Gibbs N! (no paradox)")
    print("=" * 78)
    print("  log2(counts) in bits, and the indistinguishability saving log2(N!):")
    print("  {:<12}{:<16}{:<16}{}".format("(N, M)", "dist (bits)", "bose (bits)", "log2(N!) saving"))
    print("  " + "-" * 64)
    for N, M in [(5, 1000), (10, 1000), (20, 5000), (50, 100000)]:
        dist_bits = N * math.log2(M)
        bose_bits = math.log2(comb(N+M-1, N))
        nfact = math.log2(math.factorial(N))
        print("  {:<12}{:<16.2f}{:<16.2f}{:.2f}".format(
            "({},{})".format(N, M), dist_bits, bose_bits, nfact))
    print("""
  Counting distinguishable arrangements (M^N) overcounts the entropy by ~log2(N!); modding out
  permutations removes exactly that excess and resolves the Gibbs paradox (entropy stays extensive
  on mixing identical gases). The holographic record count is the DISTINGUISHABLE one — already the
  permutation quotient — so 'redundant relabelings' never spend budget. (This is the entropy face
  of RedundancyCompressible: R copies of a fact carry H(X), not R·H(X).)""")

# ======================================================================
#  PART 4 — permutation ORBITS → Born (typicality over the quotient)
# ======================================================================
def run_orbits_to_born():
    print("\n" + "=" * 78)
    print("PART 4 — permutation orbits ⇒ Born: typicality over the quotient")
    print("  Qubit |ψ> = √p|0> + √q|1>, q=1−p.  N iid copies.  Permutation symmetry sorts the 2^N")
    print("  bit-string configs into ORBITS labelled by the frequency f = w/N (w = # of 1s).")
    print("=" * 78)
    p, q = 0.7, 0.3
    print("  p=|a|²={}, q=|b|²={}.  Orbit of weight w has C(N,w) configs (the permutation count);".format(p, q))
    print("  its Born weight (|amplitude|² in |ψ>^⊗N) is C(N,w) p^(N−w) q^w — a binomial in w.")
    print("\n  N        typical freq ⟨w/N⟩   std(w/N)        peak orbit at f =   → Born |b|²?")
    print("  " + "-" * 70)
    for N in [10, 100, 1000, 10000]:
        mean_f = q                              # binomial mean / N
        std_f = math.sqrt(q*(1-q)/N)            # binomial std / N → 0
        # locate the peak orbit numerically
        ws = np.arange(N+1)
        logw = (np.array([math.lgamma(N+1)-math.lgamma(k+1)-math.lgamma(N-k+1) for k in ws])
                + ws*math.log(q) + (N-ws)*math.log(p))
        peak = ws[np.argmax(logw)] / N
        print("  {:<9}{:<20.4f}{:<16.4f}{:<20.4f}{}".format(
            N, mean_f, std_f, peak, "✓ → 0.300" if abs(peak-q) < 0.05 else ""))
    print("""
  As N grows the frequency concentrates: std(w/N) = √(q(1−q)/N) → 0, and the typical orbit sits at
  f = q = |b|² — the Born frequency. So the TYPICAL actual record (the typical permutation orbit)
  shows Born statistics. Permutation symmetry supplies the structure — the orbits ARE the frequency
  records, the quotient makes 'how many ways' = C(N,w) — and the |amplitude|² measure makes the
  Born-frequency orbit typical.

  HONEST CAVEAT (unchanged): the |amplitude|² weighting of the orbits is the irreducible TYPICALITY
  PREMISE — permutation symmetry organises the configurations into frequency classes but does not,
  by itself, hand you the p^(N−w)q^w measure. So this ILLUSTRATES how the permutation quotient +
  the typicality premise ⇒ Born; it does not derive the premise (Born stays 'reduced, not derived').""")

# ======================================================================
#  PART 5 — honest verdict
# ======================================================================
def run_verdict():
    print("\n" + "=" * 78)
    print("PART 5 — honest verdict")
    print("=" * 78)
    print("""  'The limit on combinations is permutations' — correct, and it is the cleanest, most
  basis-independent form of the finiteness:

   • distinguishable configurations = configuration space / S_N — a huge, basis-independent
     quotient (Part 1), with the Gibbs N! as its entropy face (Part 3);
   • for fermions the quotient is a HARD, OBSERVED limit — Pauli exclusion, the periodic table,
     degeneracy pressure (Part 2);
   • and it is where the finiteness meets the Born rule: permutation orbits are the frequency
     records, and the typicality premise on them yields Born (Part 4).

  But the placement is the same as everywhere on the ladder. Bose/Fermi statistics and Pauli are
  REAL, observed physics — and they are the standard symmetrization postulate on Φ, a property of
  the wavefunction, NOT a new effect of λ. λ inert ⇒ it merely indexes the permutation-quotiented
  records; the statistics would be identical with or without it ⇒ operationally = Everett.

  What permutations DO add is structural clarity: the QIQT-H finiteness is combinatorial — a
  quotient by relabelings — which is basis-independent, ties directly to the machine-checked core
  (RedundancyCompressible, GoldsteinStruyve), and explains why the holographic record count is the
  DISTINGUISHABLE count. That is the honest gain: not a new empirical effect, but the right
  mathematical shape for the finiteness — permutations — and the node where it meets Born.""")

def main():
    run_quotient()
    run_pauli()
    run_gibbs()
    run_orbits_to_born()
    run_verdict()

if __name__ == "__main__":
    main()
