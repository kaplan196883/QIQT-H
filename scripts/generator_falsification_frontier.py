#!/usr/bin/env python3
"""
The ONE visible effect of the limited-information idea: the generator (Rule 110) falsification frontier.

The main QIQT-H thesis (inert λ) makes NO observable prediction (= Everett). But the *exploratory*
generator fork — λ as a finite-information deterministic machine (a B-bit seed + a rule, in the spirit
of 't Hooft / cellular automata) — DOES make a visible, falsifiable prediction: a B-bit generator can
fake true randomness only up to its period ~2^B, after which it REPEATS / shows structure. That is a
real effect, and it has ALREADY been tested two ways:

  (1) BELL / CHSH. A finite *local* generator is capped at CHSH = 2 (Tsirelson for local models is 2).
      Loophole-free Bell experiments (Hensen 2015, Giustina 2015, Shalm 2015) measure ≈ 2√2 ≈ 2.83.
      ⇒ finite LOCAL generators are EXCLUDED at *every* B. The survivor must be nonlocal/superdeterministic.

  (2) QRNG PERIODICITY. A finite generator predicts structure in quantum-random data at ~2^B outcomes.
      Quantum RNG statistical testing (NIST STS, dieharder, device-independent QRNG) finds NONE out to
      ~10^15 bits ⇒ generators with B ≲ 50 bits are EXCLUDED.

So the limited-information effect is genuine and falsifiable — and the data already push the generator
into the corner where its only deviation (the period repeat) sits beyond any reachable dataset:
  • testable window grows as 2^B (you must collect ~the period to see the repeat),
  • Lloyd's bound caps the observable universe at ~10^120 operations ⇒ B ≲ 400 bits is the absolute
    ceiling of conceivable testability,
  • the universe's actual realized-entropy state is M ~ 10^104 bits, so a generic (thermalizing)
    generator's period is the Poincaré recurrence ~2^(10^104) — ~10^103 ORDERS past the Lloyd ceiling.

This script (Part 1) demonstrates the effect concretely with real Rule 110 (a finite-width run is
deterministic and PERIODIC — it literally repeats), and (Part 2) draws the falsification-frontier chart:
generator size B vs the dataset needed to falsify it, with the QRNG-excluded, in-principle-testable, and
forever-untestable regimes marked. Needs numpy + matplotlib.
"""
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Patch

LN2_LOG10 = np.log10(2.0)   # log10(2) ≈ 0.301 : bits → orders of magnitude

# ======================================================================
#  PART 1 — Rule 110 is deterministic and PERIODIC: the effect, concretely
# ======================================================================
def rule110_step(row):
    n = len(row); nxt = np.zeros(n, dtype=np.uint8)
    for i in range(n):
        l = row[(i-1) % n]; c = row[i]; r = row[(i+1) % n]
        nxt[i] = (110 >> ((l << 2) | (c << 1) | r)) & 1
    return nxt

def find_period(W, cap=200000):
    """Run width-W Rule 110 (periodic boundary) from a fixed seed; return its exact cycle period."""
    rng = np.random.default_rng(12345 + W)
    row = rng.integers(0, 2, size=W, dtype=np.uint8)
    seen = {}
    history = []
    for t in range(cap):
        key = row.tobytes()
        if key in seen:
            return t - seen[key], seen[key]      # (period, transient)
        seen[key] = t
        history.append(row[0])                   # the "measurement" bit = cell 0
        row = rule110_step(row)
    return None, None

def run_period_demo():
    print("=" * 84)
    print("PART 1 — the effect is REAL: finite Rule 110 is deterministic and PERIODIC (it repeats)")
    print("  A width-W run has a state in {0,1}^W, so it MUST cycle within 2^W steps. The extracted")
    print("  'measurement' bitstream (cell 0) inherits that period — i.e. it fakes randomness, then repeats.")
    print("=" * 84)
    print("  {:<8}{:<14}{:<16}{:<18}{}".format("W (bits)", "state space 2^W", "measured period",
                                               "transient", "fakes random for..."))
    print("  " + "-" * 80)
    for W in (6, 8, 10, 12, 14, 16):
        period, transient = find_period(W)
        ss = 2**W
        if period is None:
            print("  {:<8}{:<14}{:<16}{:<18}{}".format(W, f"{ss:,}", ">200000", "-", ">200000 bits"))
        else:
            print("  {:<8}{:<14}{:<16}{:<18}{}".format(W, f"{ss:,}", f"{period:,}",
                                                       f"{transient:,}", f"~{period:,} bits then repeats"))
    print("""
  The period grows with the seed size W: a small generator betrays itself in a SHORT dataset, a large one
  in a long one. That IS the visible effect — structure (a repeat) at ~the period. The only question is
  whether the universe's generator is small enough for the period to fall inside a reachable dataset.""")

# ======================================================================
#  PART 2 — the falsification-frontier chart
# ======================================================================
def run_chart():
    print("\n" + "=" * 84)
    print("PART 2 — the falsification frontier: generator size B vs dataset needed to falsify it")
    print("=" * 84)

    QRNG_ORDERS  = 15     # log10(largest QRNG dataset statistically tested) ~10^15 bits
    LLOYD_ORDERS = 120    # log10(max operations of the observable universe, Lloyd 2002)
    M_UNIVERSE   = 1e104  # realized-entropy state of the universe (bits) = the actual generator size
    B_QRNG  = QRNG_ORDERS  / LN2_LOG10     # ~50 bits  : below this, already excluded by QRNG
    B_LLOYD = LLOYD_ORDERS / LN2_LOG10     # ~399 bits : absolute ceiling of conceivable testability

    print(f"  QRNG frontier      : B ≈ {B_QRNG:5.0f} bits  (period 2^B ≈ 10^{QRNG_ORDERS}; tested, null ⇒ smaller B EXCLUDED)")
    print(f"  Lloyd cosmic ceiling: B ≈ {B_LLOYD:5.0f} bits  (period 2^B ≈ 10^{LLOYD_ORDERS}; max ops in the universe)")
    print(f"  Actual universe gen : B ≈ 10^104 bits  (period = Poincaré recurrence 2^(10^104) ≈ 10^(3x10^103) orders)")
    print(f"  Bell/CHSH          : finite LOCAL generator ≤ 2 ; observed 2√2 ≈ 2.83 ⇒ local EXCLUDED at every B")

    # ZOOMED to the testable window (0..440 bits) so the regimes are actually visible;
    # the real universe (B~10^104) is off the right edge by ~10^101 and is drawn as an arrow.
    B = np.linspace(1, 440, 800)                  # generator size, bits (testable-scale zoom)
    N = 2.0 ** B                                   # dataset to falsify ≈ 2^B outcomes (fits float to ~10^132)

    fig, ax = plt.subplots(figsize=(10.5, 6.6))
    ax.set_yscale("log")

    # regime shading (now WIDE and visible because x is zoomed to the testable scale)
    ax.axvspan(0, B_QRNG, color="#d62728", alpha=0.16)
    ax.axvspan(B_QRNG, B_LLOYD, color="#2ca02c", alpha=0.16)
    ax.axvspan(B_LLOYD, 440, color="#7f7f7f", alpha=0.16)

    # the falsification curve, coloured by regime
    seg_excl = B <= B_QRNG
    seg_test = (B > B_QRNG) & (B <= B_LLOYD)
    seg_untest = B > B_LLOYD
    ax.plot(B[seg_excl],   N[seg_excl],   color="#d62728", lw=3.4, zorder=5, solid_capstyle="round")
    ax.plot(B[seg_test],   N[seg_test],   color="#2ca02c", lw=3.4, zorder=5, solid_capstyle="round")
    ax.plot(B[seg_untest], N[seg_untest], color="#7f7f7f", lw=3.0, zorder=5)

    # horizontal experimental reference lines (now well separated on the zoomed y)
    ax.axhline(2.0**B_QRNG,  color="#d62728", ls=":", lw=1.2)
    ax.axhline(2.0**B_LLOYD, color="#7f7f7f", ls=":", lw=1.2)

    # milestone markers
    ax.scatter([B_QRNG],  [2.0**B_QRNG],  color="#d62728", s=70, zorder=7, ec="white", lw=1)
    ax.scatter([B_LLOYD], [2.0**B_LLOYD], color="#444",    s=70, zorder=7, ec="white", lw=1)

    ax.annotate("QRNG frontier — already tested to ~$10^{15}$ outcomes (NULL)\n"
                "⇒ every generator with $B\\lesssim50$ bits is EXCLUDED",
                xy=(B_QRNG, 2.0**B_QRNG), xytext=(70, 1e6),
                fontsize=9, ha="left", color="#b01d1d",
                arrowprops=dict(arrowstyle="->", color="#d62728", lw=1.2))
    ax.annotate("Lloyd ceiling — $10^{120}$ ops, the MOST any experiment\n"
                "in the whole observable universe could ever collect ($B\\approx400$ bits)",
                xy=(B_LLOYD, 2.0**B_LLOYD), xytext=(40, 1e95),
                fontsize=9, ha="left", color="#333",
                arrowprops=dict(arrowstyle="->", color="#555", lw=1.2))

    # the real universe: OFF THE RIGHT EDGE
    ax.annotate("the universe's ACTUAL generator:\n$B\\sim10^{104}$ bits  →  OFF THIS CHART\n"
                "($10^{101}\\times$ past the right edge);\nperiod $2^{10^{104}}$ — untestable forever",
                xy=(439, 2.0**435), xytext=(250, 1e40),
                fontsize=9.2, ha="center", color="black", fontweight="bold",
                arrowprops=dict(arrowstyle="-|>", color="black", lw=1.6))

    # Bell note (orthogonal exclusion)
    ax.text(8, 1e125,
            "Bell / CHSH (a 2nd, orthogonal test): a finite LOCAL generator is capped at\n"
            "$2$; experiment measures $2\\sqrt{2}\\approx2.83$  ⇒  LOCAL generators EXCLUDED at every $B$.",
            fontsize=8.6, ha="left", va="top",
            bbox=dict(boxstyle="round,pad=0.45", fc="#fff6cc", ec="#caa700", lw=1.1))

    ax.set_xlabel("generator information  $B$  (bits of seed + state)   —   zoomed to the testable scale", fontsize=10.5)
    ax.set_ylabel("dataset needed to falsify,  $N \\approx 2^{B}$  (outcomes)", fontsize=11)
    ax.set_title("Where the limited-information effect can — and cannot — be tested (generator fork)",
                 fontsize=12.5, pad=12)
    ax.set_xlim(0, 440); ax.set_ylim(1, 1e140)

    legend_handles = [
        Patch(facecolor="#d62728", alpha=0.35, label="already EXCLUDED by QRNG data ($B\\lesssim50$ bits)"),
        Patch(facecolor="#2ca02c", alpha=0.35, label="testable in principle ($50\\lesssim B\\lesssim400$ bits)"),
        Patch(facecolor="#7f7f7f", alpha=0.35, label="untestable ($B\\gtrsim400$) — where the real universe sits, far off-chart"),
    ]
    ax.legend(handles=legend_handles, fontsize=8.8, loc="lower right", framealpha=0.96)

    fig.text(0.5, 0.004,
             "Main QIQT-H thesis (inert λ): no effect, = Everett. This is the EXPLORATORY generator fork only — "
             "a different (deterministic / superdeterministic) ontology.",
             ha="center", fontsize=7.9, style="italic", color="#555")

    fig.tight_layout(rect=(0, 0.03, 1, 1))
    out = "build/generator_falsification.png"
    fig.savefig(out, dpi=140)
    print(f"\n  chart written: {out}")

# ======================================================================
#  PART 3 — honest verdict
# ======================================================================
def run_verdict():
    print("\n" + "=" * 84)
    print("PART 3 — honest verdict: yes there is a visible effect — and it has already been tested")
    print("=" * 84)
    print("""  THE EFFECT IS REAL AND FALSIFIABLE (generator fork only). A finite-information generator (Rule 110
  or any B-bit machine) cannot fake randomness past its period ~2^B; it then repeats / shows structure.
  Two existing experiments already test this:
   • Bell/CHSH excludes finite LOCAL generators outright (observed 2√2 > local cap 2).
   • QRNG statistical testing (~10^15 bits, null) excludes generators with B ≲ 50 bits.

  WHAT THE DATA SAY. The small and local versions are GONE — that is a genuine empirical result, not a
  dodge. What survives is only a generator that is (a) nonlocal/superdeterministic (to evade Bell) and
  (b) large, B above the ~400-bit Lloyd ceiling — and the real universe's state is B ~ 10^104, whose
  period is the Poincaré recurrence ~2^(10^104), ~10^103 orders beyond anything observable.

  SO: the limited-information idea DOES predict a visible effect; experiment has pushed it into the only
  surviving corner, where the effect (the period repeat) sits past the recurrence wall — observationally
  indistinguishable from true randomness, i.e. = Everett. The honest 'effect chart' is therefore a
  FALSIFICATION-FRONTIER chart (this one), not a deviation curve: it shows the effect is real, where it
  has been ruled out, and where the surviving version hides. This is the exploratory generator fork (a
  different ontology), NOT the main inert-λ thesis — which remains effect-free by construction.""")

def main():
    run_period_demo()
    run_chart()
    run_verdict()

if __name__ == "__main__":
    main()
