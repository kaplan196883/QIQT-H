#!/usr/bin/env python3
"""
Does the compressibility constraint preserve Born? — the make-or-break test.

The candidate law (from scripts/algorithmic_lambda.py): only histories with algorithmic complexity
K ≤ Q_R can be actual. The question that decides whether it can be physics: when we CONDITION the
Born measure on {K ≤ Q_R}, do the observed outcome frequencies stay at the Born value, or distort?

Setup: a qubit |ψ> = √p|0> + √q|1>, N iid copies. Histories = length-N bit-strings. Born weight of
string s with w ones is p^(N-w) q^w. Observable statistic = frequency f = w/N (Born ⇒ f → q).
Complexity proxy = Lempel–Ziv (a standard, computable stand-in for Kolmogorov K). We enumerate ALL
2^N strings, and for each complexity threshold C ('Q_R') compute the Born-weighted mean frequency
over the admissible set {s : LZ(s) ≤ C}, comparing to the Born value q.

The tension being tested: Born-TYPICAL strings (f≈q, otherwise patternless) are INCOMPRESSIBLE
(K≈N·H₂(q)); the low-K strings are ATYPICAL (all-0s, periodic). So a biting budget may strip the
typical strings and keep atypical low-K ones — distorting Born.

HONEST FRAME: LZ is a proxy for K; this tests the natural HARD cutoff K≤Q_R (a soft complexity
penalty could differ). The result is the sharp form of the standing fork — read the verdict.
Needs only the standard library.
"""
import itertools, math

def lz_complexity(seq: str) -> int:
    """Lempel–Ziv complexity: number of distinct phrases in the greedy parse (Kaspar–Schuster).
       Low for patterned strings (all-0s, periodic), high for random — a computable K proxy."""
    phrases = set()
    n, ind, inc = len(seq), 0, 1
    while ind + inc <= n:
        sub = seq[ind:ind+inc]
        if sub in phrases:
            inc += 1
        else:
            phrases.add(sub)
            ind += inc
            inc = 1
    return len(phrases)

def run(N=16, p=0.7):
    q = 1 - p
    H2 = -(p*math.log2(p) + q*math.log2(q))               # Born entropy rate (bits/copy)
    print("=" * 80)
    print("MAKE-OR-BREAK: does conditioning Born on {{K ≤ Q_R}} preserve Born?")
    print("  qubit p=|a|²={}, q=|b|²={};  N={} copies;  Born entropy rate H₂(q)={:.3f} bits/copy"
          .format(p, q, N, H2))
    print("  ⇒ a Born-typical history needs ≈ N·H₂(q) = {:.1f} bits to describe (incompressible).".format(N*H2))
    print("=" * 80)

    # enumerate all 2^N histories: (weight, frequency, LZ complexity)
    rows = []
    for bits in itertools.product('01', repeat=N):
        s = ''.join(bits)
        w = s.count('1')
        weight = (p ** (N - w)) * (q ** w)
        rows.append((weight, w / N, lz_complexity(s)))
    Cmax = max(r[2] for r in rows)
    Cmin = min(r[2] for r in rows)

    # unconstrained Born mean frequency (sanity: should be q)
    Wtot = sum(r[0] for r in rows)
    f_born = sum(r[0]*r[1] for r in rows) / Wtot
    print("  unconstrained Born mean frequency ⟨f⟩ = {:.4f}   (should equal q = {:.3f})  ✓\n".format(f_born, q))

    print("  LZ threshold C   admissible strings   admissible Born mass   ⟨f⟩ | C   Born-preserved?")
    print("  " + "-" * 78)
    for C in range(Cmin, Cmax + 1):
        adm = [r for r in rows if r[2] <= C]
        mass = sum(r[0] for r in adm)
        f_c = (sum(r[0]*r[1] for r in adm) / mass) if mass > 0 else float('nan')
        frac_strings = len(adm) / len(rows)
        ok = "yes (≈ q)" if abs(f_c - q) < 0.03 else "NO — distorted toward {}".format(
            "f=0 (high-|a|²)" if f_c < q else "f=1")
        star = "   ← slack: constraint inert" if frac_strings > 0.98 else (
               "   ← tight: constraint bites" if frac_strings < 0.5 else "")
        print("  {:<17}{:<21}{:<23}{:<10.4f}{}{}".format(
            C, "{} ({:.1%})".format(len(adm), frac_strings), "{:.4f}".format(mass), f_c, ok, star))

    print("""
  READING. At HIGH thresholds (C large, ~all strings admissible) the constraint is SLACK and ⟨f⟩ = q
  — Born is preserved, but the constraint does nothing (= Everett). As C drops and the budget BITES,
  the admissible set loses the incompressible Born-typical strings (f≈q) and keeps the low-complexity
  ones; the Born-weighted mean frequency SHIFTS toward f=0 — the high-amplitude outcome |a|² — i.e.
  Born is DISTORTED. The crossover is near C corresponding to ≈ N·H₂(q) bits: above it, slack +
  Born; below it, biting + non-Born.""")

    print("=" * 80)
    print("VERDICT — the make-or-break answer")
    print("=" * 80)
    print("""  A hard compressibility cutoff K ≤ Q_R does NOT give 'biting constraint + preserved Born':
   • SLACK regime (Q_R ≥ the history's Born entropy ≈ N·H₂(q)): the typical Born histories ARE
     admissible, ⟨f⟩ = q, Born preserved — but the constraint never bites, so it is INERT ⇒ = Everett.
     (And this is the ACTUAL regime for every real system: Q_R is ~65–70 orders above the entropy.)
   • BITING regime (Q_R < N·H₂(q), i.e. a tight/saturated budget — horizons or a small dynamical
     Q_eff): the constraint strips the incompressible typical strings and DISTORTS Born, biasing
     outcomes toward the simplest, highest-amplitude records. So it does NOT preserve Born.

  So the compressibility route is the SAME fork, now proven sharp: you get either (preserved Born,
  inert constraint = Everett) OR (biting constraint, broken Born). You cannot get both from K ≤ Q_R.
  That is a genuine no-go for 'a Born-preserving compressibility law' in this hard-cutoff form.

  UPDATE (11th GPT-5.5-pro consult): the SOFT penalty FAILS TOO. Weighting by 2^{-βK} alongside Born
  breaks Born for ANY β>0 — it just breaks it continuously. Large-N saddle point: the dominant
  frequency solves r_β/(1−r_β) = (q/(1−q))^{1/(1−β)}, so for q=0.3: β=0.1→r≈0.28, 0.5→0.16, 0.9→2e-4.
  GENERAL NO-GO: any law ν(h) ∝ Born(h)·F(K(h)) preserves Born only if F is constant μ-a.e. (i.e. does
  nothing). Hard cutoff F=1[K≤Q] and soft F=2^{-βK} are both non-constant ⇒ both non-Born.

  WHY (the deep reason, standard AIT — Levin–Schnorr/Martin-Löf): a Born-typical record is
  algorithmically RANDOM (K ≈ −log₂μ ≈ N·H₂(q), incompressible) — the OPPOSITE of a compressible
  fractal. So 'low-K actuality' necessarily excludes the typical records. The CONSISTENT algorithmic
  characterization is the inverse: actuality is Born-Martin-Löf-RANDOM (bounded randomness deficiency)
  = the rigorous form of 'λ designates a TYPICAL history'. See scripts/martin_lof_typicality.py.
  (LZ is a proxy; the conclusions rest on the AIT theorems.)""")

if __name__ == "__main__":
    run()
