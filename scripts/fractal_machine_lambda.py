#!/usr/bin/env python3
"""
The fractal machine as a λ-construction: a few-bit 'fact' → a whole structure.

The user's idea: a fractal machine that runs on FEW BITS, whose few-bit seed (the 'fact') unfolds
into a whole structure = λ. The cleanest concrete fractal machine is the ELEMENTARY CELLULAR
AUTOMATON: the rule is exactly 8 bits (a number 0–255), and from a single seed cell it generates,
deterministically, an unbounded 2D pattern. So the 'space of all fractals from a few-bit machine'
is literally the 256 elementary CA rules — each an 8-bit FACT mapping to a full unfolded λ.

What this maps, honestly:
  • The 8-bit rule space spans the whole spectrum — from SIMPLE/periodic (Rule 0, 255), to genuine
    FRACTALS (Rule 90 = Sierpiński, Rule 18, 22…), to CHAOS that LOOKS random (Rule 30 — actually
    used as a pseudo-random generator). All from 8 bits + a seed.
  • This is exactly the GENERATOR picture made concrete: λ = M(fact), M a fixed few-bit machine,
    'fact' the few-bit seed. It inherits the generator fork's status (deterministic; for Born it is
    pseudo-random at best; superdeterministic for Bell; untestable at the Poincaré scale).
  • The KEY split (consistent with everything prior): a fractal rule produces COMPRESSIBLE structure
    (low Kolmogorov complexity, recognisable) — ideal for the SCAFFOLD of λ (the self-similar record
    geometry), but NOT the Born CONTENT, which is incompressible (Martin–Löf). A chaotic rule fakes
    randomness but is still low-K (reproducible from 8 bits) — pseudo-Born, not true Born.

So the fractal machine is a beautiful, tangible realisation of 'λ from few bits' — it shows precisely
which part of λ a few-bit machine can supply (the structure/scaffold, and pseudo-random frequencies)
and which it cannot (the true-random, incompressible Born content). Needs only the standard library.
"""
import zlib

W = 401            # lattice width (odd, single seed in the middle)
T = 200            # time steps

def run_rule(rule, width=W, steps=T):
    """Elementary CA, 8-bit `rule`, single seed cell; return the steps×width 0/1 pattern (flat)."""
    row = [0]*width
    row[width//2] = 1
    out = list(row)
    for _ in range(steps-1):
        nxt = [0]*width
        for i in range(width):
            l = row[i-1] if i > 0 else 0
            c = row[i]
            r = row[i+1] if i < width-1 else 0
            idx = (l << 2) | (c << 1) | r           # 0..7
            nxt[i] = (rule >> idx) & 1
        row = nxt
        out.extend(row)
    return out

def compress_ratio(bits):
    packed = bytes(int("".join(map(str, bits[i:i+8])).ljust(8, "0"), 2) for i in range(0, len(bits), 8))
    return len(zlib.compress(packed, 9)) / max(1, len(packed))

def frequency(bits):
    return sum(bits) / len(bits)

# ======================================================================
#  PART 1 — the space of few-bit fractal machines (256 CA rules = 8-bit facts)
# ======================================================================
def run_space():
    print("=" * 80)
    print("PART 1 — the 8-bit 'fact' space: 256 elementary CA rules, each a fractal machine")
    print("=" * 80)
    rows = []
    for rule in range(256):
        bits = run_rule(rule)
        rows.append((rule, frequency(bits), compress_ratio(bits)))
    # classify by compressibility of the unfolded pattern
    simple   = [r for r in rows if r[2] < 0.06]
    fractal  = [r for r in rows if 0.06 <= r[2] < 0.45]
    chaotic  = [r for r in rows if r[2] >= 0.45]
    print("  Of 256 rules (8-bit facts), the unfolded patterns sort by compressibility (zlib ratio):")
    print("    SIMPLE  (ratio<0.06, near-trivial/periodic):  {} rules".format(len(simple)))
    print("    FRACTAL (0.06–0.45, self-similar, low-K):      {} rules".format(len(fractal)))
    print("    CHAOTIC (>=0.45, random-LOOKING):              {} rules".format(len(chaotic)))
    print("\n  Notable rules (rule : frequency : compress-ratio : character):")
    for rule, lbl in [(0,"all-0 (trivial)"), (90,"Sierpiński triangle (FRACTAL)"),
                      (18,"fractal"), (22,"fractal"), (110,"universal / complex"),
                      (30,"CHAOTIC — used as a PRNG"), (45,"chaotic"), (255,"all-1 (trivial)")]:
        f = next(x for x in rows if x[0]==rule)
        print("    {:>3} : f={:.3f} : ratio={:.3f} : {}".format(rule, f[1], f[2], lbl))
    print("""
  The same 8-bit machine spans the whole spectrum: most rules give COMPRESSIBLE structure (simple or
  fractal, low Kolmogorov complexity), and a few (Rule 30, 45…) give CHAOTIC, random-LOOKING output
  that zlib cannot compress. So 'λ = a fractal from few bits' is a real, finite construction — the
  fact is 8 bits, the unfolding is unbounded.""")
    return rows

# ======================================================================
#  PART 2 — fractal (structure) vs chaotic (pseudo-random): the two roles
# ======================================================================
def run_two_roles():
    print("\n" + "=" * 80)
    print("PART 2 — what a few-bit fractal machine can and cannot supply for λ")
    print("=" * 80)
    # Rule 90 (fractal/scaffold) vs Rule 30 (chaotic/pseudo-random) — compare to true random
    import random
    rng = random.Random(12345)
    n = T*W
    cases = [
        ("Rule 90 (Sierpiński, fractal)", run_rule(90)),
        ("Rule 30 (chaotic, PRNG-like)",  run_rule(30)),
        ("true random (reference)",       [rng.randint(0,1) for _ in range(n)]),
    ]
    print("  source                          frequency   compress-ratio   reproducible from 8 bits?")
    print("  " + "-" * 76)
    for name, bits in cases:
        repro = "YES (low K)" if "Rule" in name else "no (incompressible)"
        print("  {:<32}{:<12.3f}{:<17.3f}{}".format(name, frequency(bits), compress_ratio(bits), repro))
    print("""
  Rule 90 is a FRACTAL: highly compressible, visibly structured — it does NOT look random (it fails
  Born-frequency/randomness tests immediately). It is the OPPOSITE of random. Rule 30 is CHAOTIC: it
  LOOKS random (zlib barely compresses it) and is even used as a PRNG — but it is still generated from
  8 bits, so its true Kolmogorov complexity is tiny and it is exactly reproducible. Only the true-random
  reference is genuinely incompressible.

  So a few-bit fractal machine gives you TWO things, neither of which is the Born content:
   • FRACTAL rules → COMPRESSIBLE STRUCTURE = the SCAFFOLD of λ (the self-similar record/holographic
     geometry). Real and useful — but structure, not outcomes.
   • CHAOTIC rules → PSEUDO-RANDOM frequencies = fakes Born up to ~2^(8 bits) before its determinism
     shows. This is the generator fork (Rule 30 ≈ a tiny 't Hooft machine).""")

# ======================================================================
#  PART 3 — honest verdict
# ======================================================================
def run_verdict():
    print("\n" + "=" * 80)
    print("PART 3 — honest verdict: where the fractal-machine λ fits")
    print("=" * 80)
    print("""  'λ = a fractal from a few-bit fact' is a genuine, concrete construction — the 8-bit CA rule IS
  the fact, the unfolded pattern IS λ. It makes 'few bits → λ' tangible. But it lands exactly where
  the whole generator thread did, and the fractal framing actually sharpens WHY:

   1. A fractal is the COMPRESSIBLE / structured extreme (low Kolmogorov complexity). A Born-typical
      actual record is INCOMPRESSIBLE (Martin–Löf random). So a fractal-generated outcome sequence is
      detectably NON-Born — it fails randomness tests immediately. A fractal cannot BE the Born content.

   2. What a few-bit machine CAN supply: (a) the SCAFFOLD — the self-similar record/holographic
      geometry of λ (fractal rules); (b) PSEUDO-random frequencies — chaotic rules (Rule 30) fake Born
      up to ~2^(seed) before repeating. Both are low-K (the generator fork), with its costs: Bell ⇒
      superdeterminism, and the period buried at the Poincaré recurrence ⇒ untestable.

   3. The 'space of all few-bit fractals' is a FINITE actuality-structure space (256 here; 2^B in
      general). That is the genuine 'Quantized Information' content — a finite menu of possible λ
      STRUCTURES. But the actual high-entropy world cannot be a low-K fractal: its incompressible Born
      content must be filled in on top of whatever scaffold the machine provides.

  NET: the fractal machine beautifully realises 'few bits → λ' for the STRUCTURE of actuality (the
  scaffold, and pseudo-random frequencies), but the true-random, incompressible Born CONTENT is not
  something a few-bit fractal machine can generate — that is the Martin–Löf wall, seen one more way.
  It is the same honest fork: structure/pseudo-Born from few bits (inert or untestable), vs the brute
  true-random λ of the paper.""")

def main():
    run_space()
    run_two_roles()
    run_verdict()

if __name__ == "__main__":
    main()
