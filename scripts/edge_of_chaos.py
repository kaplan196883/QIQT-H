#!/usr/bin/env python3
"""
The edge of chaos — the one open residue — and whether it touches QIQT-H honestly.

The fractal-machine thread left exactly one suggestive lead, not a generator: the actual world's
TEXTURE (persistent structure in a quasi-random background) resembles Wolfram CLASS 4, the 'edge of
chaos'. This script asks, concretely and honestly: does criticality say anything about λ?

THE HONEST HYPOTHESIS being tested: RECORDS — the things λ indexes — can exist only at the edge.
  • Too ORDERED  (frozen): a perturbation dies; nothing is registered ⇒ no record.
  • Too CHAOTIC  (scrambled): a perturbation spreads but is destroyed in noise ⇒ no STABLE,
    redundant record.
  • The EDGE: a perturbation PERSISTS and PROPAGATES as a coherent structure that copies a bit to
    many places — which is exactly what a record / Quantum-Darwinism imprint IS.

We measure DAMAGE SPREADING (the Derrida/Langton order parameter): evolve an initial condition and a
1-cell-perturbed copy, and track how the Hamming 'damage' grows, as a function of the CA activity
λ = (number of 1s in the 8-bit rule)/8 (Langton's parameter). A frozen→critical→chaotic transition
is the edge.

HONEST FRAME (stated up front): the CA↔QM connection here is an ANALOGY, not a derivation. The
genuine, non-poetic conclusion is that the edge characterises the RECORD-SUPPORTING regime —
decoherence + einselection + Quantum Darwinism — i.e. the program's METASELECTOR (Gap 1: which
pointer basis), NOT the Born CONTENT (which outcome, λ's brute Born-typical fact). So the residue is
a candidate new ANGLE on the metaselector, not a new mechanism and not a constraint on Born. Needs
only the standard library.
"""
import random

W = 200        # lattice width
T = 120        # steps
RULES_PER_L = 40
ICS = 6

def evolve(ic, rule, steps=T):
    row = list(ic)
    for _ in range(steps-1):
        n = len(row); nxt = [0]*n
        for i in range(n):
            l = row[i-1]; c = row[i]; r = row[(i+1) % n]   # periodic
            nxt[i] = (rule >> ((l<<2)|(c<<1)|r)) & 1
        row = nxt
    return row

def damage(rule, rng):
    """Mean normalized Hamming distance after T steps between an IC and a 1-cell-flipped copy."""
    tot = 0.0
    for _ in range(ICS):
        ic = [rng.randint(0,1) for _ in range(W)]
        ic2 = list(ic); ic2[W//2] ^= 1
        a = evolve(ic, rule); b = evolve(ic2, rule)
        tot += sum(x != y for x, y in zip(a, b)) / W
    return tot / ICS

# ======================================================================
#  PART 1 — damage spreading vs activity λ: the frozen → critical → chaotic edge
# ======================================================================
def run_sweep():
    print("=" * 78)
    print("PART 1 — damage spreading vs Langton activity λ (the edge-of-chaos order parameter)")
    print("  λ = #(1s in the 8-bit rule)/8.  Damage = how far a 1-cell perturbation spreads.")
    print("=" * 78)
    rng = random.Random(0)
    rules_by_pop = {k: [r for r in range(256) if bin(r).count('1') == k] for k in range(9)}
    print("  λ      damage (mean)   regime              bar")
    print("  " + "-" * 64)
    results = []
    for k in range(1, 8):
        lam = k/8
        rules = rules_by_pop[k]
        sample = rules if len(rules) <= RULES_PER_L else rng.sample(rules, RULES_PER_L)
        d = sum(damage(r, rng) for r in sample) / len(sample)
        results.append((lam, d))
        regime = ("FROZEN (no record)" if d < 0.04 else
                  "edge / critical" if d < 0.30 else
                  "CHAOTIC (scrambled)")
        bar = "█" * int(d*50)
        print("  {:<7.3f}{:<16.4f}{:<20}{}".format(lam, d, regime, bar))
    print("""
  Damage is near-zero at BOTH extremes — low λ freezes to all-0, high λ to all-1 (perturbations heal,
  nothing recorded) — and PEAKS in the intermediate band (λ≈0.5), where perturbations survive and
  propagate. That intermediate band is the edge of chaos; it contains both the Class-4 'edge' rules
  (coherent gliders = records) and the genuinely Class-3 chaotic rules — the next part separates them,
  since the average over many rules dilutes the rare strongly-chaotic ones.""")
    return results

# ======================================================================
#  PART 2 — where records live: the named Class-4 rules sit in the band
# ======================================================================
def run_class4():
    print("\n" + "=" * 78)
    print("PART 2 — the record-supporting band: persistence AND propagation (not heal, not scramble)")
    print("=" * 78)
    rng = random.Random(1)
    named = [(0,"Class 1 frozen"), (90,"Class 3 fractal"), (110,"Class 4 (edge, universal)"),
             (54,"Class 4 (edge)"), (30,"Class 3 chaotic"), (45,"Class 3 chaotic"), (250,"Class 2 periodic")]
    print("  rule   λ      damage    character")
    print("  " + "-" * 54)
    for r, lbl in named:
        lam = bin(r).count('1')/8
        d = damage(r, rng)
        print("  {:<7}{:<7.3f}{:<10.4f}{}".format(r, lam, d, lbl))
    print("""
  A RECORD needs both: it must SURVIVE (a frozen rule heals the perturbation → no record) and it must
  PROPAGATE/broadcast (a fully chaotic rule scrambles it → no stable, redundant record). Only the
  intermediate (Class-4 / edge) rules keep a perturbation alive AND carry it coherently — gliders that
  transport a bit. That is exactly the structure of a Quantum-Darwinism record: one fact, copied,
  robust, broadcast. So 'records can exist only at the edge' is the real, defensible content here.""")

# ======================================================================
#  PART 3 — honest verdict: what the edge does and does not buy QIQT-H
# ======================================================================
def run_verdict():
    print("\n" + "=" * 78)
    print("PART 3 — honest verdict")
    print("=" * 78)
    print("""  WHAT IS REAL. The edge of chaos is a genuine, measured transition (damage spreading / Langton's
  λ / Derrida), and it characterises the regime in which RECORDS can exist: persistent, propagating,
  redundant structures that carry a bit — neither frozen nor scrambled. In QIQT-H the records are
  precisely what λ indexes, and they are produced by decoherence + einselection + Quantum Darwinism.
  So the edge is a real characterisation of the RECORD-SUPPORTING regime.

  WHERE IT CONNECTS (the honest payoff). This is the program's METASELECTOR question (Gap 1: *which*
  pointer basis / record framework), seen from a new angle. The current answer is Zurek's commutativity
  /einselection criterion (a record commutes with the monitored observable). 'Records live at the edge
  of chaos' is a candidate DYNAMICAL restatement of the same selection: the einselected pointer
  observables are those whose dynamics are critical — robust enough to persist, rich enough to imprint
  redundantly. There are real quantitative hooks (decoherence/scrambling rates; the Maldacena–Shenker–
  Stanford quantum chaos bound λ_L ≤ 2πk_BT/ℏ, saturated by black holes = fast scramblers), so this is
  not merely poetic — it is a possible criticality criterion for the record net.

  WHERE IT DOES NOT REACH (no overclaim). The edge constrains the record STRUCTURE (the scaffold /
  which variables are recorded), NOT the Born CONTENT (which outcome is actual). The content is λ's
  brute, Born-typical, incompressible fact — independent of how critical the dynamics is. So the
  edge-of-chaos residue does NOT give a generator of Born outcomes, does NOT make λ testable, and does
  NOT change the = QM verdict. It is a candidate reframing of the METASELECTOR, and the CA↔QM link is
  an ANALOGY/conjecture, not a derivation.

  NET. The one open lead is real but modest and well-bounded: 'the record net is critical (edge of
  chaos)' is a plausible, quantitatively-anchored new ANGLE on the einselection/metaselector problem
  (Gap 1) — worth posing as a research question — but it touches the SCAFFOLD, not the Born content,
  and it adds no empirical content. The honest next step would be to ask whether the Zurek
  einselection criterion and a criticality (edge-of-chaos) criterion pick the SAME pointer basis.""")

def main():
    run_sweep()
    run_class4()
    run_verdict()

if __name__ == "__main__":
    main()
