#!/usr/bin/env python3
"""
Finite information, infinite complexity — the algorithmic-information shape of λ.

The idea (the user's): λ is information-finite (≤ Q_R bits) yet can DESIGNATE an unboundedly,
self-similarly ('infinitely') complex actuality structure — because the Q_R bound is on the
ALGORITHMIC (Kolmogorov) description (the generating RULE), not on the unfolded structure. A
fractal is the proof of concept: infinite detail, finite rule.

Five demonstrations:
  1. A finite rule (one byte: a cellular-automaton rule) generates an UNBOUNDED self-similar
     structure — the unfolded size grows without limit while the rule stays constant.
  2. Algorithmic complexity (compressed size) vs raw size: for the fractal the compressed/rule
     size stays ~constant while the raw size grows; for a random structure they coincide.
  3. The CONSTRAINT: under a finite Q_R budget on the COMPRESSED description, only COMPRESSIBLE
     (algorithmically simple) histories are admissible; random/incompressible ones cannot fit.
  4. Compressibility ↔ CLASSICALITY: a redundant (Quantum-Darwinism) classical record compresses
     to ~H(X), NOT R·H(X) — admissible; a generic random state is incompressible — not. So
     'actuality is compressible' ≈ 'actuality is classical/decohered' (einselection). This is the
     numerical face of the machine-checked RedundancyCompressible (R copies carry H(X), not R·H(X)).
  5. Depth vs budget: a fractal of unbounded DEPTH has ~constant generating size ≤ Q_R.

HONEST FRAME: zlib is a PRACTICAL proxy (an upper bound) for Kolmogorov complexity K; the true
minimal description is the generating PROGRAM (constant for a fractal — that is the real bound,
zlib over-estimates it). As a DESCRIPTION of already-decohered records this is inert (= Everett:
the records are already compressible, λ just indexes one). As a CONSTRAINT ('only histories
compressible to ≤ Q_R can be actual') it is NEW content — potentially the basis-independent
constraint — with the standing cost (must show Born + no-signaling survive) and the suggestive
payoff (compressible = classical, tying the finiteness to einselection). Needs numpy + zlib (stdlib).
"""
import zlib
import math
import numpy as np

def kbits(b: bytes) -> int:
    """Compressed size in BITS — a practical upper bound on Kolmogorov complexity K."""
    return len(zlib.compress(b, 9)) * 8

# ======================================================================
#  PART 1 — a finite RULE generates an UNBOUNDED self-similar structure
# ======================================================================
def rule90(depth):
    """Elementary cellular automaton Rule 90 (new = left XOR right) from a single seed cell.
       Rule 90 is a 1-BYTE rule; it generates the Sierpiński triangle — a fractal."""
    width = 2*depth + 1
    rows = np.zeros((depth, width), dtype=np.uint8)
    rows[0, depth] = 1                         # single seed in the middle
    for t in range(1, depth):
        left = np.roll(rows[t-1], 1)
        right = np.roll(rows[t-1], -1)
        rows[t] = left ^ right
    return rows

def run_finite_rule():
    print("=" * 80)
    print("PART 1 — a finite RULE (1 byte) generates an UNBOUNDED self-similar structure")
    print("  Rule 90 (new = left XOR right) from one seed cell ⇒ the Sierpiński triangle.")
    print("  The RULE is constant (1 byte); the unfolded pattern grows without limit.")
    print("=" * 80)
    print("  depth D    unfolded cells (~2D²)    rule size (bits, constant)")
    print("  " + "-" * 60)
    for D in [8, 32, 128, 512]:
        cells = D * (2*D + 1)
        print("  {:<11}{:<24,}{}".format(D, cells, "≈ 8 (rule) + ~log2(D) (depth) + 1 (seed)"))
    print("""
  The whole infinitely-detailed fractal is regenerated, to ANY depth, from the SAME ~12 bits:
  'Rule 90, single seed, run D steps'. Unbounded structure, finite generating information. This is
  the existence proof for 'infinitely complex structure that fits in a finite λ': the information
  is in the RULE, not in the unfolded structure.""")

# ======================================================================
#  PART 2 — algorithmic complexity (compressed) vs raw size
# ======================================================================
def run_complexity_vs_size():
    print("\n" + "=" * 80)
    print("PART 2 — compressed (≈ algorithmic) size vs raw size: fractal vs random")
    print("  zlib-compressed bits = practical upper bound on Kolmogorov K. Fractal: K ≪ raw and")
    print("  grows slowly; random: K ≈ raw (incompressible).")
    print("=" * 80)
    rng = np.random.default_rng(0)
    print("  depth D   raw bits     fractal K (bits)   random K (bits)   fractal/raw")
    print("  " + "-" * 66)
    for D in [16, 32, 64, 128, 256]:
        frac = rule90(D)
        raw = frac.size
        frac_bytes = np.packbits(frac.ravel()).tobytes()
        rand = rng.integers(0, 2, size=raw, dtype=np.uint8)
        rand_bytes = np.packbits(rand).tobytes()
        kf, kr = kbits(frac_bytes), kbits(rand_bytes)
        print("  {:<10}{:<13,}{:<19,}{:<18,}{:.3f}".format(D, raw, kf, kr, kf/raw))
    print("""
  The fractal's compressed size is a small FRACTION of its raw size and that fraction SHRINKS as the
  structure grows (self-similarity = redundancy = compressibility). The random structure does not
  compress at all (K ≈ raw). The true algorithmic bound for the fractal is even smaller — the ~12-bit
  generating program of Part 1 — which zlib only approaches. So: structured ⇒ finite information;
  random ⇒ information = size.""")

# ======================================================================
#  PART 3 — the CONSTRAINT: a finite Q_R admits only compressible histories
# ======================================================================
def run_constraint():
    print("\n" + "=" * 80)
    print("PART 3 — the CONSTRAINT: under a finite Q_R (on the COMPRESSED description),")
    print("  only COMPRESSIBLE histories are admissible as actual")
    print("=" * 80)
    rng = np.random.default_rng(1)
    QR = 4096       # holographic budget, in COMPRESSED bits
    print("  Q_R = {} bits (budget on the compressed/algorithmic description).".format(QR))
    print("  history (unfolded)         raw bits     compressed K     fits in Q_R?")
    print("  " + "-" * 68)
    for D in [64, 128, 256, 512]:
        frac = rule90(D)
        kf = kbits(np.packbits(frac.ravel()).tobytes())
        admit = "YES — admissible" if kf <= QR else "no — too complex"
        print("  {:<27}{:<13,}{:<17,}{}".format("fractal depth {}".format(D), frac.size, kf, admit))
    for nbits in [2048, 8192, 32768]:
        rb = np.packbits(rng.integers(0, 2, size=nbits, dtype=np.uint8)).tobytes()
        kr = kbits(rb)
        admit = "YES" if kr <= QR else "no — INCOMPRESSIBLE, exceeds Q_R"
        print("  {:<27}{:<13,}{:<17,}{}".format("random {} bits".format(nbits), nbits, kr, admit))
    print("""
  So a finite Q_R on the COMPRESSED description does NOT cap the unfolded complexity (deep fractals
  pass) — it caps the ALGORITHMIC complexity. The admissible actual histories are exactly the
  algorithmically SIMPLE (compressible) ones; random/incompressible histories are excluded once they
  exceed Q_R. THIS is the substantive constraint: 'actuality is low-complexity', basis-independent,
  not a weight-truncation and not a literal Hilbert cut.""")

# ======================================================================
#  PART 4 — compressibility ↔ CLASSICALITY (Quantum Darwinism redundancy)
# ======================================================================
def run_classicality():
    print("\n" + "=" * 80)
    print("PART 4 — compressibility ↔ CLASSICALITY: redundant records compress, random don't")
    print("  Classical record = one value X imprinted R times (Quantum Darwinism). Generic state =")
    print("  R independent random values. Compressed size: H(X) vs R·H(X).")
    print("=" * 80)
    rng = np.random.default_rng(2)
    kX = 64                       # bytes in the fact X
    R = 2000                      # redundancy (environment fragments)
    X = rng.integers(0, 256, size=kX, dtype=np.uint8).tobytes()
    classical = X * R                                   # R identical imprints of the one fact
    generic = rng.integers(0, 256, size=kX*R, dtype=np.uint8).tobytes()   # R independent values
    raw_bits = kX * R * 8
    kc, kg = kbits(classical), kbits(generic)
    HX = kX * 8                                          # H(X) for a uniform kX-byte value
    print("  one fact X = {} bytes (H(X) = {} bits);  R = {} redundant imprints".format(kX, HX, R))
    print("  {:<26}{:<14}{:<16}{}".format("record type", "raw bits", "compressed K", "≈"))
    print("  " + "-" * 64)
    print("  {:<26}{:<14,}{:<16,}{}".format("classical (R copies of X)", raw_bits, kc,
          "H(X)-scale: ≪ R·H(X)={:,}; true K~{} (+zlib overhead)".format(HX*R, HX+11)))
    print("  {:<26}{:<14,}{:<16,}{}".format("generic (R random values)", raw_bits, kg,
          "≈ R·H(X) — incompressible"))
    print("  compression ratio:  classical {:.0f}× vs generic {:.2f}×".format(raw_bits/kc, raw_bits/kg))
    print("""
  The redundant CLASSICAL record collapses to ~H(X) under compression — exactly the machine-checked
  RedundancyCompressible fact (R copies carry H(X), not R·H(X)) — so the REDUNDANCY is admissible
  under a finite Q_R; the generic state's redundancy is not.

  CORRECTION (11th GPT-5.5-pro consult): 'compressible ⇒ classical actuality' is TOO STRONG. Only the
  REDUNDANCY of a classical record compresses (the same fact copied R times). The underlying outcome
  itself — which fact X, and across many measurement events the full sequence of distinct outcomes —
  still carries ~H(X) (resp. ~N·H₂(q)) of IRREDUCIBLE, incompressible information. So a classical
  measurement RECORD is NOT algorithmically simple; it is Born-random (incompressible). 'Information-
  finiteness = classicality' conflated 'redundant copies compress' with 'the outcome is compressible'
  — they are different. See scripts/martin_lof_typicality.py: actuality is incompressible-relative-to-
  Born (maximally typical), NOT compressible.""")

# ======================================================================
#  PART 5 — unbounded DEPTH at constant generating size ≤ Q_R
# ======================================================================
def run_depth():
    print("\n" + "=" * 80)
    print("PART 5 — unbounded DEPTH, constant generating information (the fractal-λ picture)")
    print("=" * 80)
    print("  The generating program 'Rule 90, seed, D steps' has size ~ 8 + log2(D) + 1 bits:")
    print("  depth D            generating size (bits)   unfolded cells")
    print("  " + "-" * 60)
    for e in [10, 20, 40, 80]:
        gen = 8 + e + 1
        print("  2^{:<16}{:<25}~ 2·D² (astronomically large)".format(e, gen))
    print("""
  Depth (apparent complexity) grows without limit; the generating size grows like log2(D) — so for
  any realistic Q_R the rule fits with room to spare while the designated structure is unbounded.
  That is exactly 'λ is information-finite, yet designates an infinitely complex (fractal) actuality':
  λ ≈ the finite RULE; the actuality ≈ its unbounded unfolding.""")

# ======================================================================
#  PART 6 — honest verdict
# ======================================================================
def run_verdict():
    print("\n" + "=" * 80)
    print("PART 6 — honest verdict")
    print("=" * 80)
    print("""  'Finite information, infinitely complex structure in λ' — coherent and correct, via
  ALGORITHMIC information: the Q_R bound is on the generating RULE (compressed description), not on
  the unfolded structure. A fractal proves it (Parts 1, 5). The bound caps complexity in the sense
  of Kolmogorov K, not raw size (Part 2).

  The idea was to make this a CONSTRAINT (Part 3): under a finite Q_R on K, only algorithmically
  SIMPLE (compressible) histories can be actual. THAT LAW IS NOW KILLED — see
  scripts/compressibility_born.py (make-or-break test) and the 11th GPT-5.5-pro consult:

  ** NO-GO (verified by standard algorithmic-information theory — Levin–Schnorr / Martin-Löf):
     a Born-TYPICAL measurement record is algorithmically RANDOM / INCOMPRESSIBLE (K ≈ N·H₂(q),
     grows with N) — the OPPOSITE of a compressible fractal. So conditioning Born on low K excludes
     exactly the typical records: any law ν(h) ∝ Born(h)·F(K(h)) preserves Born only if F is constant
     (does nothing). Hard cutoff ⇒ Born distorted when it bites; soft penalty 2^{-βK} ⇒ Born distorted
     for ANY β>0. 'Compressible actuality' contradicts 'Born actuality'. **

  HONEST STATUS:
   • The 'finite RULE ⇒ unbounded fractal' point (Parts 1, 5) stands — finite algorithmic info can
     DESIGNATE an unboundedly complex structure. That part is fine and was never the problem.
   • The CONSTRAINT 'actuality is compressible' is FALSE: actual histories are Born-random, i.e.
     incompressible-relative-to-Born (maximally typical), not simple. The correct algorithmic
     characterization is the INVERSE — Martin-Löf typicality — built in martin_lof_typicality.py.
   • zlib/LZ are only PROXIES (and not in bits); K is uncomputable. The conclusions rest on the AIT
     theorems, not the proxy. Don't conflate unfolded complexity with information.""")

def main():
    run_finite_rule()
    run_complexity_vs_size()
    run_constraint()
    run_classicality()
    run_depth()
    run_verdict()

if __name__ == "__main__":
    main()
