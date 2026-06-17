#!/usr/bin/env python3
"""
How the edge-of-chaos / records picture fits the Bekenstein flow — they meet at the black hole.

Two threads, one boundary:
  • BEKENSTEIN FLOW (holographic): information capacity scales with AREA (∝R²); BLACK HOLES SATURATE it
    (S = A/4ℓ_P²) — the collapse envelope. Ordinary matter realizes ∝R³ ≪ capacity (huge slack).
  • EDGE OF CHAOS (records): objective records (Quantum Darwinism redundancy) exist only when the
    dynamics is SUB-SCRAMBLING; a fast scrambler destroys them. The ceiling is the Maldacena–Shenker–
    Stanford chaos bound λ_L ≤ 2πk_BT/ℏ, and BLACK HOLES SATURATE it (Sekino–Susskind fast scramblers).

THE JUXTAPOSITION (de-hyped per GPT-5.5-pro referee, 2026-06-17): the black hole saturates BOTH bounds
— it is at once the information-capacity maximum (Bekenstein) and, in semiclassical Einstein gravity,
the chaos maximum (MSS). These are TWO DISTINCT bounds (an entropy vs. a Lyapunov RATE — different
dimensions, no general map between "fraction of capacity used" and "fraction of chaos bound used";
indeed bigger holes have MORE capacity but SLOWER λ_L = c/2R_s), both tied to horizon thermodynamics —
NOT a single identity, and NOT "the envelope IS the scrambling ceiling." What is defensible is a
QUALITATIVE CONTRAST: at the maximally-scrambling horizon the FINE-GRAINED microstate information is
delocalised (Page/Hayden–Preskill: unitarily preserved, decodable only from large radiation subsystems
with nontrivial decoding) — NOT redundantly broadcast as Quantum-Darwinism pointer records. (Black holes
DO still carry macroscopic records: M, Q, J, location, accretion history — large entropy ≠ many objective
records.) So stable redundant classical records are EXPECTED in ordinary sub-holographic, non-maximally-
scrambling open-system environments — a qualitative physical expectation, NOT a theorem linking
S/S_holo<1 to λ_L/(2πT/ℏ)<1 to QD redundancy.

This script computes the black-hole numbers (Hawking T, the MSS Lyapunov bound, the fast-scrambling
time) to show the double saturation, and reads off the honest (de-hyped) fit. Needs only the std library.
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
    print("""  Putting the two threads on the SAME plot (the Bekenstein flow) — as a CONTRAST, not an identity:

    holographic ENVELOPE  (∝R², black, BH-saturated)   ~  the regime of MAXIMAL SCRAMBLING (horizons)
                                                          where fine-grained info is delocalised,
                                                          NOT redundantly broadcast as QD records.

    realized-entropy TRACK (∝R³, purple, ≪ envelope)   ~  the sub-holographic, non-maximally-scrambling
                                                          bulk where stable REDUNDANT records are expected.

  • Ordinary matter sits deep in the slack (universe ~10⁻¹⁸ of capacity) and is a weak/slow scrambler
    (decoherence imprints redundant records far faster than its dynamics could delocalise them) ⇒ the
    regime of stable, broadcast, classical records where λ's records live.
  • A black hole / horizon saturates BOTH bounds: its fine-grained information is maximal (A/4) but
    maximally SCRAMBLED — delocalised, decodable only nonlocally (Page/Hayden–Preskill), NOT a redundant
    Quantum-Darwinism record. (It still carries macroscopic M, Q, J records.) This is a qualitative
    reason the horizon — the one place a finite budget 'bites' in every earlier model — is record-POOR
    in the redundant-broadcast sense, NOT a theorem that it is record-free.""")

# ======================================================================
#  PART 3 — honest verdict: the fit
# ======================================================================
def run_verdict():
    print("\n" + "=" * 84)
    print("PART 3 — honest verdict: how the edge of chaos fits the Bekenstein flow")
    print("=" * 84)
    print("""  THE FIT (a qualitative contrast, signed off by the referee — NOT a unification). The black hole
  jointly saturates two SHARP but DISTINCT limits: its Bekenstein–Hawking entropy A/4ℓ_P² saturates the
  capacity bound, and (in semiclassical Einstein gravity) its chaotic dynamics saturate the MSS bound
  (λ_L = 2πk_BT_H/ℏ = c/2R_s, t_* ~ λ_L⁻¹ ln S). These are different quantities tied to the same horizon
  thermodynamics — a juxtaposition, not an identity (there is no general map between fraction-of-capacity
  and fraction-of-chaos-bound; larger holes have more capacity yet slower λ_L). So:

   • At the maximally-scrambling horizon the fine-grained microstate information is delocalised — present
     and (Page/Hayden–Preskill) decodable only from large radiation subsystems by nontrivial decoding —
     NOT redundantly broadcast as Quantum-Darwinism pointer records. (Macroscopic M, Q, J records remain.)
   • Therefore stable redundant classical records — what λ indexes — are EXPECTED in ordinary
     sub-holographic, non-maximally-scrambling open-system environments (the realized-entropy bulk), where
     decoherence + einselection + Quantum Darwinism operate, NOT at the horizon limit.

  WHAT IT BUYS, HONESTLY. A physically-grounded ORGANIZING CONTRAST linking two strands of the program —
  the holographic record STAGE (Q_R) and the metaselector (which records / einselection): both the
  capacity limit and the record-destroying scrambling limit are realised at the black-hole horizon, so
  ordinary record-bearing matter sits doubly far from that limit. It constrains WHERE stable objective
  records are expected to arise.

  WHAT IT DOES NOT BUY (the referee's cut). It is NOT a theorem: there is no proven link from S/S_holo<1
  to λ_L/(2πT/ℏ)<1 to QD redundancy, and 'realized-entropy ∝R³ = the record-supporting region' is glib
  (record formation depends on dynamics/locality/decoherence, not volume entropy; and BH entropy already
  dominates the cosmic budget). It does not touch the Born CONTENT (which record is actual = λ's brute
  fact), gives no generator, no testability, no deviation from QM, and does NOT select which Everett
  branch is actual. Honest status: a qualitative physical contrast organizing the SCAFFOLD; λ inert;
  = Everett.""")

def main():
    run_double_saturation()
    run_where_records()
    run_verdict()

if __name__ == "__main__":
    main()
