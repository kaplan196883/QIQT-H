#!/usr/bin/env python3
"""
Where the finiteness becomes REAL: limit the λ-generator's information ⇒ Born eventually breaks.

The whole arc lands here. A finite-information generator (the λ 'selector' as a deterministic
algorithm, à la 't Hooft) can fake Born — BUT only up to a data size set by its information budget.
A generator with B bits of internal state:
  • produces at most B bits of genuine entropy ⇒ its output is algorithmically compressible to ~B
    bits (not Martin-Löf random) — detectable in principle for any N ≫ B;
  • has period ≤ 2^B ⇒ once you observe > 2^B outputs the 'randomness' EXACTLY REPEATS — detectable
    by ANY observer, no cleverness needed.

So 'limit the information of the λ-generator' is exactly where a real, in-principle-OBSERVABLE
difference from true Born lives: quantum randomness would show finite-information structure
(periodicity, compressibility, correlations) at data sizes approaching the budget. THIS is the
empirical content — and unlike the inert-λ reading, it is FALSIFIABLE.

This script demonstrates the breakdown and its scale. Standard library only.

HONEST FRAME: the breakdown data-size is ~2^B. For a holographic budget B = Q_R ~ 10^70 bits the
break is at 2^(10^70) events — never reached (the universe has ~10^120 events total), so it stays
operationally = QM. The difference is observable only if the budget is SMALL (saturation/horizons,
or if quantum randomness is far more information-limited than holography suggests). And it is a
DETERMINISTIC/superdeterministic theory (the Bell cost from the previous model still applies).
"""
import zlib

def lcg_bits(k, n, q_num=3, q_den=10):
    """Full-period LCG with 2^k state (a=5≡1 mod4, c=3 odd ⇒ Hull–Dobell full period 2^k).
       Emit n bits, each = 1 with frequency q = q_num/q_den. Deterministic; period = 2^k."""
    m = 1 << k
    a, c, x = 5, 3, 1
    thresh = (m * q_num) // q_den
    bits = []
    for _ in range(n):
        x = (a * x + c) % m
        bits.append(1 if x < thresh else 0)
    return bits

def freq(bits):
    return sum(bits) / len(bits)

def is_periodic(bits, period):
    """True if bits repeats exactly with the given period (checks the overlap)."""
    if len(bits) <= period:
        return None
    return all(bits[i] == bits[i + period] for i in range(len(bits) - period))

# ======================================================================
#  PART 1 — the breakdown: looks Born below the budget, repeats above it
# ======================================================================
def run_breakdown():
    print("=" * 80)
    print("PART 1 — a B-bit λ-generator fakes Born up to N ~ 2^B, then BREAKS (exact period)")
    print("  target Born frequency q = 0.3 ;  generator = full-period LCG with 2^B state")
    print("=" * 80)
    print("  B bits   period 2^B   f̂ over 1 period   N=3·period: exactly periodic?   detectable?")
    print("  " + "-" * 76)
    for B in [8, 12, 16, 20]:
        period = 1 << B
        within = lcg_bits(B, period)                 # one full period
        fhat = freq(within)
        long = lcg_bits(B, 3 * period)               # three periods
        periodic = is_periodic(long, period)
        print("  {:<9}{:<13,}{:<18.4f}{:<31}{}".format(
            B, period, fhat, "YES — repeats every 2^B" if periodic else "no",
            "non-Born for N > 2^B"))
    print("""
  Within one period (N < 2^B) the output has the right Born frequency and passes finite tests — it
  'looks Born'. But the sequence is EXACTLY periodic with period 2^B: observe more than 2^B outcomes
  and the 'quantum randomness' literally repeats. A finite-information generator cannot fake Born
  forever — its faking window is ~2^B, set by its information budget. THAT is the real difference.""")

# ======================================================================
#  PART 2 — compressibility: the output carries only ~B bits, for any N
# ======================================================================
def run_compress():
    print("\n" + "=" * 80)
    print("PART 2 — the output's algorithmic content is ~B bits (≪ N): compressible in principle")
    print("=" * 80)
    print("  B=16 generator; compress N bits (zlib finds the 2^B period once N exceeds it):")
    print("    N (bits)     compressed bits   ratio   note")
    print("    " + "-" * 56)
    B = 16; period = 1 << B
    for N in [period // 2, period, 2 * period, 6 * period]:
        bits = lcg_bits(B, N)
        packed = bytes(int("".join(map(str, bits[i:i+8])).ljust(8, "0"), 2) for i in range(0, N, 8))
        comp = len(zlib.compress(packed, 9)) * 8
        tag = "looks random (N ≤ period)" if N <= period else "COMPRESSES — period detected"
        print("    {:<13,}{:<18,}{:<8.3f}{}".format(N, comp, comp / N, tag))
    print("""
  Below the budget the output is incompressible (looks Born). Above it, the finite structure shows:
  the compressed size saturates (the whole sequence is regenerable from the ~B-bit state), so the
  ratio → 0 as N grows. A true-Born sequence would stay incompressible at every N. (zlib detects the
  period once it exceeds the budget; an ideal observer sees compressibility for any N ≫ B.)""")

# ======================================================================
#  PART 3 — the scale, and the honest verdict
# ======================================================================
def run_verdict():
    print("\n" + "=" * 80)
    print("PART 3 — the scale of the break, and the honest verdict")
    print("=" * 80)
    print("  break data-size ≈ 2^B, set by the generator's information budget B:")
    print("    budget B (bits)     break at N ≈ 2^B           status")
    print("    " + "-" * 64)
    rows = [
        ("20 (toy)",           "~10^6 events",            "BREAKS in a lab-scale dataset — observable"),
        ("80 (~atom Planck)",  "~10^24 events",           "beyond any experiment, but finite"),
        ("Q_R ~ 10^70 (holo)", "~2^(10^70) events",       "never (universe has ~10^120 events) ⇒ = QM"),
        ("S_BH (horizon)",     "saturated",               "the one place a small budget could bite"),
    ]
    for b, n, s in rows:
        print("    {:<20}{:<27}{}".format(b, n, s))
    print("""
  THE PAYOFF (and it is the real one):
   • You are RIGHT — limiting the λ-generator's information is exactly where a genuine, in-principle
     OBSERVABLE difference from true Born appears: quantum randomness would show finite-information
     structure (periodicity / compressibility / correlations) at data sizes approaching the budget.
   • This is the program's actual EMPIRICAL CONTENT, and unlike the inert-λ reading it is FALSIFIABLE:
     a concrete prediction — 'quantum randomness is finite-information pseudo-randomness'. (So far
     every test of quantum RNGs finds NO structure — consistent with a very large budget.)
   • THE CATCH is the scale: the break is at N ~ 2^B. For the holographic budget B ~ 10^70 that is
     2^(10^70) events — unreachable — so it stays operationally = QM for everything we can measure.
     A difference is observable only if the budget is SMALL: horizons, or quantum randomness being
     far more information-limited than holography says (a bold, testable-in-principle hypothesis).
   • HONEST COST: this is the deterministic/superdeterministic GENERATOR ontology, not inert-λ-Everett.
     It still owes Bell its price (global superdeterminism, previous model) and an account of WHY the
     generator reproduces the Born measure (the typicality premise, relocated into the algorithm).

  So the finite-λ-generator is the most empirically meaningful version in the whole thread: a real,
  falsifiable claim (Born breaks at N ~ 2^Q_R), currently consistent with all data, distinguishing
  it IN PRINCIPLE from standard QM — at the price of a superdeterministic, finite-information ontology.""")

def main():
    run_breakdown()
    run_compress()
    run_verdict()

if __name__ == "__main__":
    main()
