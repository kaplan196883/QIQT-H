#!/usr/bin/env python3
"""
Can the λ-generator's used information be forced far below the holographic capacity? — the push.

The hope: if the generator is algorithmically SIMPLE (a small seed/program), its faking window 2^B is
small ⇒ testable. The Bekenstein/holographic flow even MOTIVATES a small seed (the world is the
hologram of an area-scaling boundary). So: can anything force the used information down to the
testable ~50-bit level?

THE RESOLUTION — a distinction we had been blurring:
  • CODE complexity K_code = the size of the generating program (the Lagrangian + the initial
    condition). This CAN be tiny — the laws of physics fit on a page, and a simple initial state
    (a specific low-complexity vacuum) is low-K. The universe is plausibly algorithmically SIMPLE.
  • STATE complexity M = the size of the evolving microstate (the entropy of the actual realized
    state). This is HUGE — the universe's realized entropy is ~10^104 bits (black-hole + CMB
    dominated), up toward the holographic capacity ~10^122.

A deterministic generator's PERIOD (its faking window — when the trajectory repeats / structure
appears) is bounded by the STATE space it explores, 2^M — NOT by the code size 2^{K_code}. A tiny
program evolving a huge state has a huge period. For ergodic dynamics (generic QM / ETH) the
trajectory explores the full microcanonical state space, so:

        faking window  ≈  2^M  =  2^(realized entropy)  ≈  the POINCARÉ RECURRENCE TIME.

So the simplicity of the code does NOT shorten the period; the period is set by the (physically
large) entropy. The universe can be a SIMPLE deterministic generator AND have observably perfect
quantum randomness — because its recurrence time is 2^(10^104), astronomically beyond its age.

CONCLUSION: you CANNOT force the used (state) information small. K_code small is real and motivated
(by holography/the flow), but B for the faking window is M = the realized entropy, and no principle
makes the universe's entropy small — it is a physical fact that the universe has high entropy. The
generator is viable and motivated, but untestable, and the obstruction is the STATE entropy (period
= Poincaré recurrence), not the code. Standard library only.
"""
import math

HBAR = 1.054571817e-34
C    = 2.99792458e8
G    = 6.674e-11
LP   = math.sqrt(HBAR * G / C**3)
T_P  = LP / C                                  # Planck time
AGE  = 4.35e17                                 # age of universe (s)

# ======================================================================
#  PART 1 — CODE complexity (small) vs STATE complexity (huge)
# ======================================================================
def run_code_vs_state():
    print("=" * 84)
    print("PART 1 — CODE complexity (the program) vs STATE complexity (the entropy)")
    print("=" * 84)
    print("  {:<34}{:<18}{}".format("quantity", "size (bits)", "what it is"))
    print("  " + "-" * 78)
    rows = [
        ("Standard Model + GR Lagrangian", "~10^3", "the laws — 'fits on a T-shirt'"),
        ("a simple initial state (vacuum)", "~10^2–10^4", "low-complexity IC (if it is simple)"),
        ("  ⇒ K_code (program)",            "~10^3–10^4", "SMALL — the universe may be algorithmically simple"),
        ("", "", ""),
        ("realized entropy of the universe", "~10^104", "the microstate's information (BH + CMB dominated)"),
        ("holographic capacity (dS horizon)","~10^122", "the maximum (saturated only at the horizon)"),
        ("  ⇒ M (evolving state)",           "~10^104", "HUGE — the entropy the trajectory carries"),
    ]
    for q, s, w in rows:
        print("  {:<34}{:<18}{}".format(q, s, w))
    print("""
  The CODE (laws + simple IC) is small — the universe is plausibly algorithmically simple, and the
  holographic flow MOTIVATES that (the world is the hologram of a small area-scaling boundary). But
  the STATE the code evolves carries the realized entropy ~10^104 bits — astronomically larger.""")

# ======================================================================
#  PART 2 — the faking window is set by the STATE, not the code
# ======================================================================
def run_period():
    print("\n" + "=" * 84)
    print("PART 2 — the period (faking window) is 2^M (state), NOT 2^K_code (program)")
    print("=" * 84)
    print("""  A deterministic program with K_code bits of CODE but M bits of evolving STATE repeats only when
  the STATE recurs ⇒ period ≤ 2^M. The code size is irrelevant to the period. For generic (ergodic /
  eigenstate-thermalizing) dynamics the trajectory explores the full microcanonical state space, so

        faking window ≈ 2^M = 2^(realized entropy) ≈ the Poincaré recurrence time.

  So a SMALL program evolving a LARGE state has a LARGE period. Algorithmic simplicity of the laws
  does not shorten it.""")
    # Poincaré recurrence vs age of the universe
    S = 1e104                                   # realized entropy (bits), order of magnitude
    age_in_planck = AGE / T_P
    print("\n  age of the universe         ≈ {:.0e} s ≈ 2^{:.0f} Planck times".format(AGE, math.log2(age_in_planck)))
    print("  faking window ≈ 2^M, M ≈ realized entropy ≈ 10^104 bits")
    print("                              ≈ 2^(10^104) ≈ 10^(3×10^103) Planck times")
    print("  gap (window / age)          ≈ 10^(3×10^103) / 10^61  ≈ 10^(3×10^103)  — utterly beyond reach")
    print("""
  The recurrence/faking time exceeds the age of the universe not by 60 orders but by ~10^103 ORDERS
  of magnitude. (This is just the standard Poincaré-recurrence estimate for the universe, ~10^(10^104+).)""")

# ======================================================================
#  PART 3 — so can the USED information be forced small? No.
# ======================================================================
def run_verdict():
    print("\n" + "=" * 84)
    print("PART 3 — the push, resolved: you cannot force the used (state) information small")
    print("=" * 84)
    print("""  The question was: can any principle force the generator's used information far below the
  holographic capacity, down to the testable ~50-bit level? The answer separates cleanly:

   • K_code (the PROGRAM) CAN be small — and the holographic flow MOTIVATES it (world = hologram of a
     small boundary; the laws are simple). So 'the universe is a simple deterministic generator' is a
     viable, even attractive, picture. That much the push WINS.

   • But the faking window is 2^M, M = the realized ENTROPY of the evolving state (~10^104), not
     2^K_code. And no principle can make M small: it is a PHYSICAL FACT that the universe has high
     entropy (black holes, the CMB). Generic dynamics is ergodic (ETH), so the trajectory explores
     the full ~10^104-bit state space, and the period is the Poincaré recurrence ~2^(10^104).

   • The only escape would be NON-ERGODIC dynamics confining the actual trajectory to a ~50-bit
     subspace — flatly contradicted by the observed high entropy and thermalization. There is no such
     principle, and the data (a high-entropy, thermalizing universe) directly excludes it.

  NET — the honest end of the line. The λ-generator can be algorithmically SIMPLE (small code,
  motivated by the holographic flow), and that is a genuine, attractive picture: a simple
  deterministic program whose apparent randomness is the ergodic unfolding of a low-complexity seed.
  But it is OBSERVABLY indistinguishable from true randomness — not because the seed is large, but
  because the PERIOD is 2^(realized entropy) ≈ the Poincaré recurrence time, set by the universe's
  (physically large) entropy, not by its (small) code. So:

     'the universe is a simple generator'      — viable, motivated, possibly true;
     'quantum randomness will reveal structure' — only at the Poincaré time 2^(10^104) ⇒ never.

  The used (state) information CANNOT be forced small. The simplicity lives in the code; the
  untestability lives in the entropy; and nothing physical bridges them. That is the real wall —
  cleaner than 'Bekenstein budget': the obstruction is the universe's entropy, via its recurrence
  time, and it is a fact, not a free parameter.""")

def main():
    run_code_vs_state()
    run_period()
    run_verdict()

if __name__ == "__main__":
    main()
