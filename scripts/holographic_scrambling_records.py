#!/usr/bin/env python3
"""
How the edge-of-chaos / records picture fits the Bekenstein flow — they meet at the black hole.

Two threads, one boundary:
  • BEKENSTEIN FLOW (holographic): information capacity scales with AREA (∝R²); BLACK HOLES SATURATE it
    (S = A/4ℓ_P²) — the collapse envelope. Ordinary matter realizes ∝R³ ≪ capacity (huge slack).
  • EDGE OF CHAOS (records): objective records (Quantum Darwinism redundancy) exist only when the
    dynamics is SUB-SCRAMBLING; a fast scrambler destroys them. The ceiling is the Maldacena–Shenker–
    Stanford chaos bound λ_L ≤ 2πk_BT/ℏ, and BLACK HOLES SATURATE it (Sekino–Susskind fast scramblers).

THE UNIFICATION: the black hole saturates BOTH bounds — it is simultaneously the information-capacity
maximum (Bekenstein) and the scrambling maximum (MSS). So the holographic ENVELOPE of the Bekenstein
flow IS the scrambling CEILING of the records picture — the boundary beyond which records cease to
exist. λ's records therefore live in the SUB-SATURATION BULK (the realized-entropy slack, far below
the envelope, where the dynamics is sub-scrambling); at the horizon the information is maximal (A/4)
but MAXIMALLY SCRAMBLED — present yet not classical/redundant. The realized-entropy track of the
Bekenstein-flow plot is exactly the record-supporting region; the envelope is record-free.

This script computes the black-hole numbers (Hawking T, the MSS Lyapunov bound, the fast-scrambling
time) to show the double saturation, and reads off the honest fit. Needs only the standard library.
"""
import math

HBAR = 1.054571817e-34
C    = 2.99792458e8
G    = 6.674e-11
KB   = 1.380649e-23
LP2  = HBAR*G/C**3
LN2  = math.log(2)
MSUN = 1.989e30

def bh(M):
    Rs = 2*G*M/C**2
    S_bits = math.pi*Rs*Rs/(LP2*LN2)                 # Bekenstein–Hawking entropy (bits)
    S_nats = S_bits*LN2
    T_H = HBAR*C**3/(8*math.pi*G*M*KB)               # Hawking temperature
    lam = 2*math.pi*KB*T_H/HBAR                      # MSS Lyapunov bound (saturated): = c/(2Rs)
    t_star = (1.0/lam)*math.log(S_nats)              # fast-scrambling time ≈ (β/2π) ln S
    return Rs, S_bits, T_H, lam, t_star

# ======================================================================
#  PART 1 — black holes saturate BOTH bounds (capacity AND chaos)
# ======================================================================
def run_double_saturation():
    print("=" * 84)
    print("PART 1 — black holes saturate BOTH the holographic bound AND the MSS chaos bound")
    print("  λ_L(MSS bound) = 2πk_BT/ℏ ; for a Schwarzschild BH λ_L = c/(2R_s) (saturated).")
    print("=" * 84)
    print("  {:<16}{:<12}{:<13}{:<13}{:<14}{}".format(
        "black hole", "R_s (m)", "S (bits)", "T_H (K)", "λ_L (1/s)", "scramble t* (s)"))
    print("  " + "-" * 82)
    for M, lbl in [(2.18e-8,"Planck-mass"), (MSUN,"solar"), (1e6*MSUN,"10^6 M_sun"),
                   (1e9*MSUN,"10^9 M_sun SMBH")]:
        Rs, S, T, lam, ts = bh(M)
        lam_check = C/(2*Rs)
        print("  {:<16}{:<12.2e}{:<13.2e}{:<13.2e}{:<14.2e}{:.2e}".format(lbl, Rs, S, T, lam, ts))
    print("""
  The BH entropy S = A/4ℓ_P² is the holographic MAXIMUM (Bekenstein), and its Lyapunov rate equals the
  MSS chaos bound 2πk_BT/ℏ = c/(2R_s) EXACTLY — the maximal scrambler (Sekino–Susskind: t* ≈ (β/2π)lnS,
  the fastest possible). Same object, both bounds saturated. (Solar BH: scrambles in ~milliseconds.)""")

# ======================================================================
#  PART 2 — records live in the slack; the envelope is record-free
# ======================================================================
def run_where_records():
    print("\n" + "=" * 84)
    print("PART 2 — where records live: the sub-saturation slack (sub-scrambling), not the envelope")
    print("=" * 84)
    print("""  Putting the two threads on the SAME plot (the Bekenstein flow):

    holographic ENVELOPE  (∝R², black, BH-saturated)  =  the CHAOS CEILING (MSS bound, BH-saturated)
                                                       =  the boundary where RECORDS CEASE to exist.

    realized-entropy TRACK (∝R³, purple, ≪ envelope)  =  the SUB-SCRAMBLING bulk
                                                       =  exactly where OBJECTIVE RECORDS live.

  • Ordinary matter sits deep in the slack (universe ~10⁻¹⁸ of capacity) AND far below the chaos bound
    (decoherence imprints redundant records far faster than any scrambling erases them) ⇒ the regime
    of stable, broadcast, classical records — the edge of chaos, where λ's records exist.
  • A black hole / horizon saturates BOTH: its information is maximal (A/4) but MAXIMALLY SCRAMBLED —
    present, yet not redundant, not classical, not a record. This is *why* black holes carry no
    classical records, and why the one place a finite budget 'bites' (the horizon, in every earlier
    model) is exactly the place λ has nothing to index.""")

# ======================================================================
#  PART 3 — honest verdict: the fit
# ======================================================================
def run_verdict():
    print("\n" + "=" * 84)
    print("PART 3 — honest verdict: how the edge of chaos fits the Bekenstein flow")
    print("=" * 84)
    print("""  THE FIT (real, and rather elegant). The Bekenstein flow's holographic ENVELOPE and the records
  picture's SCRAMBLING CEILING are the SAME boundary — both saturated by the black hole, which is at
  once the information-capacity maximum (Bekenstein) and the scrambling maximum (MSS). So:

   • λ's records (the scaffold it indexes) inhabit the SUB-SATURATION BULK — the realized-entropy track
     far below the holographic envelope — because that is the sub-scrambling, edge-of-chaos regime
     where decoherence + einselection + Quantum Darwinism produce stable, redundant, classical records.
   • The horizon (BH, cosmological) saturates both bounds: maximal information, maximal scrambling, NO
     records. It is the record-free boundary. This dovetails with every earlier result that the finite
     budget only 'bites' at horizons — and now we can say *why* λ has nothing to index there: the
     information is maximally scrambled.

  WHAT IT BUYS, HONESTLY. It unifies two strands of the program — the holographic finiteness (the
  record STAGE / Q_R) and the metaselector (which records / einselection) — under one boundary: the
  black hole, saturating capacity and chaos together. It gives a physical reason WHY the realized
  (record-bearing) world sits far below the holographic envelope: records require sub-scrambling. This
  is a genuine, quantitatively-anchored sharpening of the SCAFFOLD (the record stage + the metaselector,
  Gaps 1 and 3).

  WHAT IT DOES NOT BUY. It still does not touch the Born CONTENT (which record is actual = λ's brute
  fact), gives no generator, no testability, no deviation from QM. The synthesis is about WHERE and
  WHETHER records exist (capacity + criticality), not WHICH outcome is selected. The honest status is
  unchanged: a clarified, unified scaffold; λ inert; = Everett.""")

def main():
    run_double_saturation()
    run_where_records()
    run_verdict()

if __name__ == "__main__":
    main()
