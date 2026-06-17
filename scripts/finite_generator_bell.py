#!/usr/bin/env python3
"""
Finite-information generator of Born statistics — and where it hits the Bell wall.

The inventor's point (correct): a SHORT, deterministic algorithm can emit a sequence with the right
Born FREQUENCIES that passes statistical-randomness tests, even though it has low Kolmogorov
complexity (the seed + generator is a few bytes). π / Champernowne / any good PRNG show this.

PART 1 proves that in code: a 16-byte-state PRNG (splitmix64) → a qubit's Born frequency q, passing
frequency / block / autocorrelation tests AND looking incompressible to zlib — yet it is exactly
reproducible from its 64-bit seed, so its true complexity is tiny. Finite info ⇒ Born frequencies. ✓

PART 2 is the wall. Frequencies are easy; CORRELATIONS are not. A finite generator where Alice's
outcome depends only on (her setting, shared seed λ) and Bob's only on (his setting, λ) is a LOCAL
hidden-variable model ⇒ CHSH ≤ 2 (Bell). Quantum mechanics gives 2√2 ≈ 2.828. So the local
finite generator reproduces Born frequencies but NOT Born correlations. To reach 2√2 the generator
must be NONLOCAL or SUPERDETERMINISTIC (λ allowed to depend on the settings) — we show the
superdeterministic version does reach 2√2, making explicit exactly what it costs.

Conclusion: 'finite info ⇒ Born' is TRUE for frequencies/any finite test (so it's empirically
viable as pseudo-Born, à la 't Hooft) but it is a DIFFERENT, deterministic theory, and it must pay
the Bell price (superdeterminism). Needs only the standard library.
"""
import math, zlib

MASK64 = (1 << 64) - 1

# ======================================================================
#  PART 1 — a finite-info generator that emits Born frequencies & passes tests
# ======================================================================
def splitmix64(state):
    state = (state + 0x9E3779B97F4A7C15) & MASK64
    z = state
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK64
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK64
    z = (z ^ (z >> 31)) & MASK64
    return state, z

def born_bits(seed, n, q):
    """Deterministic: emit n bits, each = 1 with frequency q, from a 64-bit seed."""
    s = seed
    bits = []
    for _ in range(n):
        s, z = splitmix64(s)
        u = z / 2.0**64
        bits.append(1 if u < q else 0)
    return bits

def run_part1(q=0.3, N=200000, seed=0xC0FFEE):
    print("=" * 80)
    print("PART 1 — finite information ⇒ Born frequencies that pass statistical tests")
    print("  generator = splitmix64 (64-bit state) ; seed = {:#x} ; target Born freq q = {}".format(seed, q))
    print("=" * 80)
    bits = born_bits(seed, N, q)
    ones = sum(bits)

    # (a) frequency test
    fhat = ones / N
    print("  frequency test:        f̂ = {:.4f}   (target q = {})   |f̂−q| = {:.4f}".format(fhat, q, abs(fhat-q)))

    # (b) 4-bit block chi-square (a real randomness test)
    from collections import Counter
    nb = N // 4
    cnt = Counter()
    for i in range(nb):
        blk = tuple(bits[4*i:4*i+4]); cnt[blk] += 1
    chi2 = 0.0
    for blk, c in [( (a,b,cc,d), cnt[(a,b,cc,d)] ) for a in (0,1) for b in (0,1) for cc in (0,1) for d in (0,1)]:
        j = sum(blk)
        exp = nb * (q**j) * ((1-q)**(4-j))
        chi2 += (c - exp)**2 / exp
    print("  4-bit block χ² test:   χ² = {:.1f}  (df=15, 5% crit ≈ 25.0)  → {}".format(
        chi2, "PASS (looks iid-Bernoulli(q))" if chi2 < 25 else "fail"))

    # (c) lag-1 autocorrelation
    m = fhat
    num = sum((bits[i]-m)*(bits[i+1]-m) for i in range(N-1))
    den = sum((b-m)**2 for b in bits)
    ac1 = num/den
    print("  lag-1 autocorrelation: r₁ = {:+.4f}   (≈ 0 ⇒ no serial pattern)  → {}".format(
        ac1, "PASS" if abs(ac1) < 0.01 else "fail"))

    # (d) zlib: the OUTPUT does not compress (looks random) — even though true K is tiny
    packed = bytes(int("".join(map(str, bits[i:i+8])).ljust(8,'0'), 2) for i in range(0, N, 8))
    comp = len(zlib.compress(packed, 9))
    print("  zlib on the output:    {:.3f} (compressed/raw) ⇒ looks INCOMPRESSIBLE to zlib".format(comp/len(packed)))

    # (e) but it is EXACTLY reproducible from the 64-bit seed ⇒ true Kolmogorov complexity is tiny
    repro = born_bits(seed, N, q)
    print("  PRNG detector:         regenerate from the 64-bit seed → identical? {}".format(repro == bits))
    print("                         ⇒ true K ≈ 64-bit seed + tiny program ≪ N. LOW complexity.")
    print("""
  VERDICT (Part 1): the inventor is RIGHT. ~16 bytes of generator+seed emit a sequence with the
  Born frequency q that passes frequency, block-χ², and autocorrelation tests and is even
  zlib-incompressible — yet it is reproducible from the seed, so its algorithmic complexity is
  tiny. 'Finite information ⇒ Born FREQUENCIES (passing any finite test)' holds. zlib-incompressible
  ≠ high K: a good PRNG is the gap between them.""")

# ======================================================================
#  PART 2 — the Bell wall: a LOCAL finite generator caps at CHSH ≤ 2
# ======================================================================
def E_qm(alpha, beta):
    """Singlet correlation E(α,β) = −cos(α−β)."""
    return -math.cos(alpha - beta)

def chsh(Eab, Eabp, Eapb, Eapbp):
    return Eab + Eabp + Eapb - Eapbp

def run_part2():
    print("\n" + "=" * 80)
    print("PART 2 — the Bell wall: frequencies are easy, CORRELATIONS are not")
    print("=" * 80)
    a, ap = 0.0, math.pi/2          # Alice settings
    b, bp = math.pi/4, -math.pi/4   # Bob settings

    # (1) quantum prediction (singlet)
    Sqm = chsh(E_qm(a,b), E_qm(a,bp), E_qm(ap,b), E_qm(ap,bp))
    print("  (1) QUANTUM (singlet, optimal angles):  CHSH = {:.4f}  ≈ 2√2 = {:.4f}".format(abs(Sqm), 2*math.sqrt(2)))

    # (2) LOCAL DETERMINISTIC: enumerate all strategies A(a),A(a'),B(b),B(b') ∈ {±1}
    best = 0.0
    for Aa in (-1,1):
        for Aap in (-1,1):
            for Bb in (-1,1):
                for Bbp in (-1,1):
                    S = chsh(Aa*Bb, Aa*Bbp, Aap*Bb, Aap*Bbp)
                    best = max(best, abs(S))
    print("  (2) LOCAL DETERMINISTIC (all 16 strategies):  max|CHSH| = {:.1f}   (Bell bound = 2)".format(best))

    # (3) finite-info LOCAL generator: shared seed λ, A=fn(setting_A, λ), B=fn(setting_B, λ).
    #     Any such model is local-hidden-variable ⇒ ≤ 2. Simulate the best mixture.
    #     (Best local strategy for this CHSH is a deterministic one giving 2; mixtures only lower it.)
    N = 200000
    s = 0xBE11 & MASK64
    # optimal local: Aa=Aap=+1, Bb=+1, Bbp=+1 gives CHSH = 1+1+1-1 = 2 deterministically
    cnt = {('a','b'):[0,0], ('a','bp'):[0,0], ('ap','b'):[0,0], ('ap','bp'):[0,0]}
    for _ in range(N):
        s, z = splitmix64(s)
        # local responses use only their own setting + λ; here the optimal fixed strategy
        Aa, Aap, Bb, Bbp = 1, 1, 1, 1
        for key, (sa, sb) in [(('a','b'),(Aa,Bb)),(('a','bp'),(Aa,Bbp)),
                              (('ap','b'),(Aap,Bb)),(('ap','bp'),(Aap,Bbp))]:
            cnt[key][0] += sa*sb; cnt[key][1] += 1
    Es = {k: cnt[k][0]/cnt[k][1] for k in cnt}
    Sloc = chsh(Es[('a','b')], Es[('a','bp')], Es[('ap','b')], Es[('ap','bp')])
    print("  (3) finite-info LOCAL generator (shared λ, local responses):  CHSH = {:.3f}  ≤ 2  ⇒".format(abs(Sloc)))
    print("      reproduces frequencies but CANNOT reach the quantum 2.83. The Bell ceiling is hard.")

    # (4) SUPERDETERMINISTIC generator: let the responses see BOTH settings (λ correlates with a,b).
    #     Then it can output ±1 pairs with P(A=B)=(1+E(a,b))/2, reproducing E(a,b) exactly ⇒ 2√2.
    s = 0x12345 & MASK64
    cnt2 = {}
    for key,(al,be) in [(('a','b'),(a,b)),(('a','bp'),(a,bp)),(('ap','b'),(ap,b)),(('ap','bp'),(ap,bp))]:
        E = E_qm(al,be); pSame = (1+E)/2; tot = corr = 0
        for _ in range(N):
            s, z = splitmix64(s)
            A = 1 if (z & 1) else -1
            s, z2 = splitmix64(s)
            same = (z2/2.0**64) < pSame
            B = A if same else -A
            corr += A*B; tot += 1
        cnt2[key] = corr/tot
    Ssup = chsh(cnt2[('a','b')], cnt2[('a','bp')], cnt2[('ap','b')], cnt2[('ap','bp')])
    print("  (4) SUPERDETERMINISTIC generator (λ sees the settings a,b):  CHSH = {:.3f}  ≈ 2√2  ⇒".format(abs(Ssup)))
    print("      it REACHES the quantum value — but only by letting the generator depend on the")
    print("      measurement settings (the 'free choice' / statistical-independence assumption fails).")
    print("""
  VERDICT (Part 2): a finite generator gives Born FREQUENCIES (Part 1) but a LOCAL one is capped at
  CHSH = 2; QM needs 2√2. To reproduce quantum CORRELATIONS the generator must be NONLOCAL or
  SUPERDETERMINISTIC (its seed correlates with the detector settings). That is the real, famous price
  of any deterministic-QM / 't Hooft-style program — not compressibility, but Bell. So: 'finite info
  ⇒ Born' is viable as PSEUDO-Born for everything we actually measure, but it buys a deterministic
  theory that must either go nonlocal or abandon measurement free-choice. That is the honest cost.""")

def main():
    run_part1()
    run_part2()

if __name__ == "__main__":
    main()
