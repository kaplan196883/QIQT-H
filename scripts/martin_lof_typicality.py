#!/usr/bin/env python3
"""
The durable takeaway: actuality is Born-MARTIN-LÖF-RANDOM (incompressible), not compressible.

This is the one thing the algorithmic-information thread produced that survives. The 'compressible
actuality' law is dead (scripts/compressibility_born.py + 11th GPT-5.5-pro consult: a low-K
constraint either does nothing or breaks Born). Its INVERSE is the correct, Born-preserving
characterization of which history λ designates — and it is a rigorous form of the TYPICALITY PREMISE
the program already leans on (Born 'reduced to typicality, not derived').

Three facts, then the takeaway (all large-N rate formulas; standard library only):
  1. A Born-TYPICAL measurement record is algorithmically RANDOM / INCOMPRESSIBLE — complexity rate
     → H₂(q) per symbol — the OPPOSITE of a compressible fractal. (Levin–Schnorr / Brudno.)
  2. THE NO-GO: any law ν(h) ∝ Born(h)·F(K(h)) preserves Born only if F is constant. Hard cutoff
     1[K≤Q] and soft penalty 2^{-βK} are both non-constant ⇒ both break Born (shift the frequency
     off q toward the high-amplitude outcome).
  3. THE CONSISTENT CHARACTERIZATION: randomness deficiency δ(x) = −log₂μ(x) − K(x) ≈ N·D(f‖q) is
     ZERO exactly at the Born frequency. 'λ designates a BOUNDED-DEFICIENCY (Martin-Löf-random)
     history' ⟺ Born frequencies ⟺ Born preserved BY CONSTRUCTION — and the history is incompressible.

TAKEAWAY: the algorithmic shape of λ is INCOMPRESSIBILITY-relative-to-Born = maximal typicality =
Martin-Löf randomness — the rigorous form of 'λ picks a typical history'. It preserves Born by
construction and λ stays inert ⇒ = Everett. (Convention: log₂; q = |b|² = the smaller amplitude.)
"""
import math

def H2(r):
    if r <= 0 or r >= 1:
        return 0.0
    return -(r*math.log2(r) + (1-r)*math.log2(1-r))

def KL(r, q):                                   # D(r‖q) in bits
    def term(a, b):
        return 0.0 if a <= 0 else a*math.log2(a/b)
    return term(r, q) + term(1-r, 1-q)

def H2_inv_low(alpha):
    """Inverse binary entropy on [0, 1/2]: the r ≤ 1/2 with H₂(r) = alpha (bisection)."""
    lo, hi = 0.0, 0.5
    for _ in range(60):
        mid = (lo+hi)/2
        if H2(mid) < alpha:
            lo = mid
        else:
            hi = mid
    return (lo+hi)/2

def soft_r(beta, q):
    """Dominant frequency under ν ∝ Born·2^{-βK}: r/(1-r) = (q/(1-q))^{1/(1-β)}."""
    ratio = (q/(1-q)) ** (1.0/(1.0-beta))
    return ratio/(1+ratio)

# ======================================================================
#  FACT 1 — Born-typical histories are INCOMPRESSIBLE (the inversion)
# ======================================================================
def fact1(q):
    print("=" * 80)
    print("FACT 1 — a Born-typical record is algorithmically RANDOM (incompressible)")
    print("  Qubit, q=|b|²={}.  N iid copies. A frequency-r record needs −log₂μ/N = H₂(r)+D(r‖q)".format(q))
    print("  bits/symbol to specify; a TYPICAL one of that frequency has complexity rate K/N ≈ H₂(r).")
    print("  Born weight concentrates at r=q (D=0); there the complexity rate is H₂(q) — HIGH.")
    print("=" * 80)
    print("  frequency r   complexity rate K/N≈H₂(r)   Born exponent D(r‖q)   note")
    print("  " + "-" * 72)
    for r in [0.0, 0.05, q, 0.5, 1.0]:
        note = ("compressible BUT Born-negligible" if r in (0.0, 1.0) else
                "← BORN-TYPICAL: incompressible" if abs(r-q) < 1e-9 else
                "atypical" if abs(r-0.5) > 1e-9 else "max-complexity, atypical")
        print("  {:<14}{:<27.3f}{:<23.3f}{}".format(
            "{:.2f}".format(r), H2(r), KL(r, q), note))
    print("""
  The compressible records (r=0 all-0s, r=1 all-1s, complexity rate 0) carry essentially NO Born
  weight (D large). The Born-typical record (r=q) has complexity rate H₂(q) ≈ {:.3f} — it is
  algorithmically RANDOM. 'Short rule → intricate fractal' is LOW complexity; a real outcome
  sequence is HIGH complexity. They are opposites. That is why 'compressible actuality' fails.""".format(H2(q)))

# ======================================================================
#  FACT 2 — the NO-GO: complexity-weighting breaks Born (hard AND soft)
# ======================================================================
def fact2(q):
    print("\n" + "=" * 80)
    print("FACT 2 — NO-GO: ν(h) ∝ Born(h)·F(K(h)) preserves Born only if F is constant")
    print("=" * 80)
    print("  HARD cutoff F=1[K/N ≤ α]: dominant allowed frequency r_α = H₂⁻¹(α) (the KL-nearest")
    print("  admissible freq). Below α=H₂(q)={:.3f} it leaves q; → 0 as α→0.".format(H2(q)))
    print("    budget α (bits/sym)   dominant r_α    Born?")
    for alpha in [H2(q)+0.05, H2(q), 0.6, 0.4, 0.2]:
        ra = q if alpha >= H2(q) else H2_inv_low(alpha)
        print("    {:<22.3f}{:<16.4f}{}".format(alpha, ra,
              "yes (=q, slack/inert)" if abs(ra-q) < 1e-3 else "NO — distorted toward 0"))
    print("\n  SOFT penalty F=2^{-βK}: dominant r_β solves r/(1-r) = (q/(1-q))^{1/(1-β)}.")
    print("    temperature β        dominant r_β    Born?")
    for beta in [0.0, 0.1, 0.5, 0.9]:
        rb = soft_r(beta, q)
        print("    {:<21.2f}{:<16.4f}{}".format(beta, rb,
              "yes (=q)" if abs(rb-q) < 1e-3 else "NO — distorted toward 0"))
    print("""
  Both are non-constant in K, so both move the typical frequency off q: the hard cutoff abruptly
  once it bites (α < H₂(q)), the soft penalty CONTINUOUSLY for any β>0. There is no complexity-
  weighted law that both DOES something and keeps Born. (Levin–Schnorr is the reason: weighting by
  K is weighting AGAINST randomness, and Born-typical = random.)""")

# ======================================================================
#  FACT 3 — the CONSISTENT characterization: randomness deficiency
# ======================================================================
def fact3(q):
    print("\n" + "=" * 80)
    print("FACT 3 — the consistent characterization: bounded RANDOMNESS DEFICIENCY")
    print("  δ(x) = −log₂μ(x) − K(x) ≈ N·D(f‖q):  how far x is from Born-random. δ=0 ⟺ Born freq.")
    print("=" * 80)
    print("  frequency r   deficiency rate δ/N = D(r‖q)   Martin-Löf-typical?")
    print("  " + "-" * 64)
    for r in [0.0, 0.1, 0.2, q, 0.4, 0.5]:
        d = KL(r, q)
        tag = "← δ=0: BORN-TYPICAL (admissible)" if abs(r-q) < 1e-9 else (
              "δ small: near-typical" if d < 0.05 else "δ large: ATYPICAL (excluded)")
        print("  {:<14}{:<30.4f}{}".format("{:.2f}".format(r), d, tag))
    print("""
  Deficiency is minimized (=0) EXACTLY at the Born frequency r=q, and grows with |r−q|. So the rule
  'λ designates a history of bounded randomness deficiency (Martin-Löf-random w.r.t. Born)' selects
  precisely the Born-typical histories — it PRESERVES Born by construction (it is not a reweighting
  of Born; it is the support of Born's typical set). And those histories are INCOMPRESSIBLE
  (K ≈ −log₂μ), not simple. This is the correct algorithmic form of the typicality premise.""")

# ======================================================================
#  TAKEAWAY
# ======================================================================
def takeaway(q):
    print("\n" + "=" * 80)
    print("TAKEAWAY — the durable result of the algorithmic-λ thread")
    print("=" * 80)
    print("""  The chain bit-limit → combinations → permutations → algorithmic information ends here, and
  it leaves exactly ONE thing standing:

    λ designates a history that is MARTIN-LÖF RANDOM with respect to the Born measure —
    i.e. of bounded randomness deficiency, hence algorithmically INCOMPRESSIBLE (maximally typical).

  • This is the rigorous form of the program's standing premise 'λ picks a TYPICAL history' — it
    gives 'typical' a precise, measure-theoretic-free definition (passes all Born randomness tests).
  • It PRESERVES Born by construction (the bounded-deficiency set IS Born's typical set), so it adds
    no deviation: λ stays inert ⇒ operationally = Everett. It is a sharper statement of the SAME
    theory, not new physics.
  • It is the INVERSE of the seductive but false 'compressible actuality': a real, Born-distributed
    record is incompressible. The finite RULE can still generate unbounded structure (that part was
    always fine), but the ACTUAL history is random, not simple.
  • It does NOT derive Born (the Born measure is still the input that defines 'typical'); it sharpens
    the premise, consistent with the established 'Born reduced to typicality, not derived'.

  HONEST STATUS: a conceptual sharpening, machine-illustrated here with large-N rate formulas (the
  underlying facts are the Levin–Schnorr theorem and Shannon–McMillan–Breiman, cited not proved).
  The 'finite information, infinite complexity' intuition was RIGHT about the rule and WRONG about
  the record: λ ≈ a finite specification of a TYPICAL (random) history, not a compressible one.""")

def main():
    q = 0.3
    fact1(q); fact2(q); fact3(q); takeaway(q)

if __name__ == "__main__":
    main()
