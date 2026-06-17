#!/usr/bin/env python3
"""
Rule 110 — the universal fractal machine — and why even universality can't beat the wall.

Rule 110 is special among the 8-bit cellular automata: it is TURING COMPLETE (Cook 2004) and it is
Wolfram CLASS 4 — the 'edge of chaos', where localized complex structures ('gliders') persist and
interact, neither boring order (fractal) nor boring chaos (random). So as a 'few-bit fractal machine'
it is the STRONGEST possible: 8 bits that can compute ANYTHING computable, given the right input.

So does Rule 110 let a few-bit FACT generate a Born-random λ? The honest answer, demonstrated here:

  • Universality means: Rule 110 + the RIGHT INITIAL CONDITION can produce any computable output. But
    the information then lives in the INITIAL CONDITION (the program/input), NOT in the 8-bit rule.
  • From a SIMPLE seed, Rule 110 makes COMPLEX-but-compressible structure (Class 4: regular background
    + gliders) — apparent complexity, low Kolmogorov K, NOT Born-random.
  • The apparent RANDOMNESS of the output comes from the RANDOMNESS of the INPUT: feed a random IC and
    the output looks random; feed a simple IC and it's structured. The rule propagates the IC's
    information; it does not create it.
  • So to get a TRULY Born-random (incompressible) world you need a TRULY-random (incompressible) IC —
    universality does not compress it. A few-bit IC gives only PSEUDO-random output (the generator
    fork: looks random to bounded observers, low-K, untestable at the Poincaré scale).

Conclusion: Rule 110 is the strongest few-bit machine, and it CLOSES the line — the machine (code/laws)
can be minimal and universal, but the actual history's information is in the INITIAL CONDITION, and a
Born-random world needs an incompressible one. The residue is a real complexity-science observation:
the actual world's TEXTURE (structure + apparent randomness) is Class-4 / edge-of-chaos, not pure
fractal nor pure chaos. Standard library only.
"""
import zlib, random

W = 401
T = 220
RULE = 110

def step(row, rule):
    n = len(row); nxt = [0]*n
    for i in range(n):
        l = row[i-1] if i > 0 else 0
        c = row[i]
        r = row[i+1] if i < n-1 else 0
        nxt[i] = (rule >> ((l<<2)|(c<<1)|r)) & 1
    return nxt

def evolve(ic, rule=RULE, steps=T):
    row = list(ic); out = list(row)
    for _ in range(steps-1):
        row = step(row, rule); out.extend(row)
    return out

def comp_ratio(bits):
    packed = bytes(int("".join(map(str, bits[i:i+8])).ljust(8,"0"),2) for i in range(0,len(bits),8))
    return len(zlib.compress(packed,9))/max(1,len(packed))

# ======================================================================
#  PART 1 — Rule 110 from a simple seed: complex (Class 4), but compressible
# ======================================================================
def run_character():
    print("=" * 80)
    print("PART 1 — Rule 110: Turing-complete, Class 4 (edge of chaos). From a SINGLE seed:")
    print("=" * 80)
    ic = [0]*W; ic[W//2] = 1
    bits = evolve(ic)
    print("  width {}, {} steps from one seed cell.".format(W, T))
    print("  frequency = {:.3f} ;  zlib compress-ratio = {:.3f}  ⇒  structured (low-K), NOT random."
          .format(sum(bits)/len(bits), comp_ratio(bits)))
    # show a small slice of the pattern (gliders / structure visible)
    print("\n  a 60×24 window of the evolution (· = 0, █ = 1) — note the regular background + structures:")
    rows = [bits[t*W:(t+1)*W] for t in range(T)]
    for t in range(0, 48, 2):
        seg = rows[t][W//2-30:W//2+30]
        print("    " + "".join("█" if c else "·" for c in seg))
    print("""
  Rule 110 makes genuine COMPLEXITY from one seed — a regular striped background with persistent
  diagonal 'gliders' that collide and interact (this is what makes it Turing-complete). But the
  pattern is still COMPRESSIBLE (low Kolmogorov K): structured, not Born-random.""")

# ======================================================================
#  PART 2 — where the randomness comes from: the INPUT, not the rule
# ======================================================================
def run_source_of_randomness():
    print("\n" + "=" * 80)
    print("PART 2 — the apparent randomness comes from the INITIAL CONDITION, not the 8-bit rule")
    print("=" * 80)
    rng = random.Random(7)
    simple = [0]*W; simple[W//2] = 1
    randic = [rng.randint(0,1) for _ in range(W)]
    print("  initial condition         output frequency   output zlib-ratio   apparent character")
    print("  " + "-" * 76)
    for name, ic in [("single seed (≈0 bits)", simple), ("random IC (W random bits)", randic)]:
        bits = evolve(ic)
        ratio = comp_ratio(bits)
        char = "structured / low-K" if ratio < 0.3 else "looks RANDOM (to a bounded observer)"
        print("  {:<26}{:<19.3f}{:<20.3f}{}".format(name, sum(bits)/len(bits), ratio, char))
    print("""
  Same 8-bit rule. A simple IC gives structured output; a RANDOM IC gives output that LOOKS random.
  So the rule does not CREATE randomness — it PROPAGATES the input's. (True Kolmogorov K of the
  random-IC run is still only ~W bits — the IC — but zlib, a bounded observer, cannot reverse the CA
  and so sees it as incompressible: the pseudo-random regime.) To make the output truly incompressible
  to EVERY observer, the IC itself must be truly incompressible.""")

# ======================================================================
#  PART 3 — honest verdict
# ======================================================================
def run_verdict():
    print("\n" + "=" * 80)
    print("PART 3 — verdict: universality is the strongest few-bit machine, and it CLOSES the line")
    print("=" * 80)
    print("""  Rule 110 is the strongest possible 'fractal machine from few bits' — 8 bits, Turing-complete,
  able to compute ANY computable output. And precisely because it is universal, it settles the idea:

   • The MACHINE (the 8-bit rule ≈ simple universal laws) can be minimal. But what it computes lives
     in the INITIAL CONDITION (the program/input) — universality moves the information to the IC, it
     does not compress it. K(output) ≤ K(rule) + K(IC), and for an incompressible output K(IC) must be
     ~K(output). So a Born-random (incompressible) world needs an incompressible IC; the few-bit rule
     buys nothing there.

   • A few-bit IC + a universal rule gives PSEUDO-random output — looks random to bounded observers
     (us), low-K, the generator fork (Bell ⇒ superdeterminism; period ⇒ Poincaré recurrence ⇒
     untestable). Exactly the status we mapped; Rule 110 makes it sharpest.

  THE CONSTRUCTIVE RESIDUE (a real idea, not a generator). Rule 110 is CLASS 4 — the edge of chaos,
  where complex structures emerge and compute. The actual world's TEXTURE is like this: persistent
  structure (atoms, galaxies, life, records) in a quasi-random background (quantum outcomes) — neither
  a boring fractal nor structureless chaos. That 'edge of chaos' character is the genuinely suggestive
  thing the fractal-machine idea points at — but it is an observation about the TEXTURE of actuality,
  not a few-bit GENERATOR of the incompressible Born content. The laws can be Rule-110-simple and
  universal; the actual history's information is in the initial condition; and the true-random Born
  part is, as ever, the brute incompressible λ of the paper — the Martin–Löf wall, seen from the top.""")

def main():
    run_character()
    run_source_of_randomness()
    run_verdict()

if __name__ == "__main__":
    main()
