#!/usr/bin/env python3
"""
The permutation quotient — 'the limit on combinations is permutations', made concrete.

The idea (the user's refinement of the bit-limit): every individual configuration is possible,
but indistinguishable constituents make configurations related by a particle-label PERMUTATION the
SAME physical configuration. So the count of PHYSICALLY DISTINCT configurations is the LABELLED
space (M^N) reduced by the particle-permutation redundancy S_N — the physical sectors being
Sym^N(ℂ^M) for bosons and ∧^N(ℂ^M) for fermions:

        physical (indistinguishable-particle) configs  ≈  labelled space (M^N) / S_N

CAVEATS (9th GPT-5.5-pro consult, verified):
  • Terminology: M^N is the LABELLED/distinguishable count; the QUOTIENT is the INDISTINGUISHABLE
    count (do not call the quotient 'distinguishable').
  • This is the particle-LABEL gauge redundancy. It is basis-independent only narrowly: it is NOT
    invariance under one-particle basis rotations U(M), the sectors admit para-statistics/anyons,
    and it is not a literal Hilbert-space quotient (Sym^N / ∧^N are the standard sectors).
  • It IS quantum statistics — and that is STANDARD QM (symmetrization postulate), a property of Φ,
    not a λ effect and not thesis-specific. The Born link in Part 4 uses a DIFFERENT permutation
    (of trial SLOTS = optional frequency coarse-graining), NOT this particle-indistinguishability
    S_N; the two must not be conflated.

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
    print("PART 1 — physical (indistinguishable-particle) configs ≈ labelled space (M^N) / S_N")
    print("  N constituents in M single-particle states (modes).")
    print("    labelled        : M^N            (distinguishable particles — full tensor product)")
    print("    bosons          : C(N+M-1, N)    (symmetric: combinations WITH repetition)")
    print("    fermions        : C(M, N)        (antisymmetric: combinations WITHOUT repetition)")
    print("=" * 78)
    print("  {:<14}{:<16}{:<16}{:<16}{}".format("(N, M)", "labelled M^N", "bosons", "fermions", "labelled/bose"))
    print("  " + "-" * 74)
    for N, M in [(2, 4), (3, 6), (5, 10), (10, 20), (10, 1000), (20, 50)]:
        dist = M**N
        bose = comb(N+M-1, N)
        fermi = comb(M, N)
        ratio = dist / bose
        print("  {:<14}{:<16.3e}{:<16.3e}{:<16.3e}{:.3e}".format(
            "({},{})".format(N, M), float(dist), float(bose), float(fermi), ratio))
    print("""
  The reduction is large: relabelling identical constituents does not make a new configuration. In
  the dilute limit M ≫ N (few particles, many modes, rare double occupancy) it approaches N! (each
  of the N! orderings collapses to one combination) — the Gibbs factor — but it is N! only in that
  limit (when modes are shared an orbit has size N!/∏ nᵢ!, not N!). This is the real 'limit on
  combinations': not which configs exist, but how many are DISTINCT.""")

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
  Counting labelled arrangements (M^N) overcounts the entropy by ~log2(N!); modding out the
  particle-label permutations removes that excess (exactly log2(N!) in the dilute/no-coincidence
  limit) and resolves the Gibbs paradox (entropy stays extensive on mixing identical gases). The
  physical record count is the gauge-invariant one — so 'redundant relabelings' never spend budget.
  (Loosely the entropy face of RedundancyCompressible — though note that is correlated-copy
  redundancy, H(X) not R·H(X); particle-label gauge redundancy is a related but distinct quotient.)""")

# ======================================================================
#  PART 4 — permutation ORBITS → Born (typicality over the quotient)
# ======================================================================
def run_orbits_to_born():
    print("\n" + "=" * 78)
    print("PART 4 — frequency orbits ⇒ Born: law of large numbers on the Born measure")
    print("  Qubit |ψ> = √p|0> + √q|1>, q=1−p.  N iid copies.  NOTE the permutation here acts on")
    print("  TRIAL SLOTS (copies), NOT identical particles — '01' and '10' are distinct ordered")
    print("  records; grouping by frequency f = w/N (w = # of 1s) is OPTIONAL COARSE-GRAINING, a")
    print("  DIFFERENT S_N from the particle-indistinguishability quotient of Parts 1–3.")
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
  As N grows the frequency concentrates: std(w/N) = √(q(1−q)/N) → 0, on f = q = |b|² — the Born
  frequency. (Any SINGLE orbit near the peak has weight ~1/√N → 0; what becomes typical is an
  ε-BAND of frequencies around q, not one exact orbit.) So the typical N-trial record shows Born
  statistics.

  HONEST CAVEATS (9th pro consult):
   • This is just the LAW OF LARGE NUMBERS for the Born measure — NOT 'permutations imply Born'.
     The |amplitude|² weighting p^(N−w)q^w is the irreducible TYPICALITY PREMISE; without it the
     orbit-count alone peaks at f = 1/2, not q. Frequency-coarse-graining organises the records;
     it does not hand you the measure. Born stays 'reduced, not derived'.
   • The S_N here permutes TRIAL SLOTS (an optional coarse-graining of ordered histories), which is
     NOT the particle-indistinguishability gauge S_N of Parts 1–3. Calling permutations 'the node
     where finiteness meets Born' conflated those two; it is withdrawn.""")

# ======================================================================
#  PART 5 — honest verdict
# ======================================================================
def run_verdict():
    print("\n" + "=" * 78)
    print("PART 5 — honest verdict")
    print("=" * 78)
    print("""  'The limit on combinations is permutations' — partly right, but with the overclaims cut
  (9th GPT-5.5-pro consult, verified):

   • Particle-label indistinguishability DOES reduce the physical config count: M^N / S_N, sectors
     Sym^N (bosons) and ∧^N (fermions), with the Gibbs N! as its dilute-limit entropy face
     (Parts 1, 3). For fermions it is a HARD, OBSERVED limit — Pauli, the periodic table,
     degeneracy pressure (Part 2).
   • This is STANDARD QM — the symmetrization postulate, quantum statistics — a property of Φ, NOT
     a λ effect and NOT thesis-specific. λ inert ⇒ it merely indexes the gauge-invariant records;
     the statistics are identical with or without it ⇒ operationally = Everett.

  Two overclaims are WITHDRAWN: (a) the Born story (Part 4) uses a DIFFERENT permutation (trial-slot
  coarse-graining), so 'permutations is the node where finiteness meets Born' conflated two S_N's —
  it is just the law of large numbers on the Born measure, and Born stays reduced-not-derived;
  (b) 'basis-independent' holds only as particle-label gauge redundancy, not as invariance under
  one-particle basis rotations U(M) (and para-statistics/anyons show it is not a literal
  Hilbert-space quotient).

  THE LEGITIMATE GAIN (pro's safe sentence): the permutation framing usefully reminds QIQT-H to
  count only genuinely distinguishable, gauge-invariant decohered records; in ordinary QM this
  reproduces standard Bose/Fermi/Gibbs counting, but it does NOT derive Born, impose a holographic
  cutoff on Φ, or give λ any empirical role.""")

def main():
    run_quotient()
    run_pauli()
    run_gibbs()
    run_orbits_to_born()
    run_verdict()

if __name__ == "__main__":
    main()
