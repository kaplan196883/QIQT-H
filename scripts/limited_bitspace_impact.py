#!/usr/bin/env python3
"""
What impact does VERY LIMITED bit space actually have? — the concrete effects.

The honest fork first (do not blur it):
  • QIQT-H's λ is NON-DYNAMICAL and Born-transparent ⇒ it produces NO impact. The holographic
    budget Q_R is also astronomically large (~2^233 for a 1 m region), so even a dynamical
    finiteness would be ~10^-140 at lab scales. That is the "= Everett" verdict, unchanged.
  • BUT if the bit space were GENUINELY small — a real finite Hilbert dimension / a real minimum
    length, i.e. a dynamical cutoff Q_eff — the impacts are concrete and computable. THAT is what
    this script shows. They are the standard finite-dimensional-QM / minimum-length (GUP) effects;
    they are what a theory with dynamical finiteness predicts, NOT what inert λ predicts.

So: "what would we see in very limited bit space?" — four real, rigorous impacts, large at small
B and scaling away as 2^(-2B), saturating to O(1) only where B is small/saturated = horizons.

Units: ℏ = m = ω = 1 (so the exact CCR is [x,p] = i). Needs numpy.
"""
import numpy as np

def ladder(N):
    """Truncated annihilation a (N×N): a|n> = √n |n-1>, with |N> cut off."""
    a = np.zeros((N, N), complex)
    for n in range(1, N):
        a[n-1, n] = np.sqrt(n)
    return a

def xp(N):
    a = ladder(N)
    ad = a.conj().T
    x = (a + ad) / np.sqrt(2)
    p = (a - ad) / (1j*np.sqrt(2))
    return x, p

# ======================================================================
#  IMPACT 1 — the CANONICAL COMMUTATOR CANNOT HOLD in finite bit space
# ======================================================================
def impact_commutator():
    print("=" * 78)
    print("IMPACT 1 — [x,p] = iℏ is IMPOSSIBLE in finite bit space (the fundamental one)")
    print("  Trace theorem: Tr[x,p] = 0 always, but Tr(iℏ·𝟙) = iℏN ≠ 0. So a finite Hilbert")
    print("  space CANNOT represent the Heisenberg algebra: the CCR must break somewhere.")
    print("=" * 78)
    print("  B bits  N=2^B   ‖[x,p] − i𝟙‖   Tr[x,p]   where it breaks")
    print("  " + "-" * 66)
    for B in [1, 2, 3, 4, 6, 8]:
        N = 2**B
        x, p = xp(N)
        comm = x @ p - p @ x
        defect = comm - 1j*np.eye(N)
        nrm = np.linalg.norm(defect, 2)          # spectral norm
        tr = np.trace(comm)
        print("  {:<8}{:<8}{:<15.3f}{:<10}{}".format(
            B, N, nrm, "{:.1e}".format(abs(tr)),
            "all of it on the top level |N−1⟩"))
    print("""
  [x,p] = i𝟙 − iN|N−1⟩⟨N−1|: the commutator is exactly correct in the BULK (value +i) but the
  entire deficit −iN piles onto the single top state (so the trace can stay 0), giving
  ‖[x,p] − i𝟙‖ = N. This is not an approximation artefact — it is forced. Any genuinely finite-bit
  quantum system has a DEFORMED Heisenberg algebra. That deformation IS the impact; the rest follows.""")

# ======================================================================
#  IMPACT 2 — position & momentum become DISCRETE and BOUNDED
# ======================================================================
def impact_discreteness():
    print("\n" + "=" * 78)
    print("IMPACT 2 — no continuum: position spectrum becomes a DISCRETE, finite grid")
    print("  Finite bits ⇒ x has N eigenvalues (Gauss–Hermite nodes), p likewise bounded.")
    print("  The continuous line is replaced by 2^B points; there is a largest representable x.")
    print("=" * 78)
    for B in [2, 3, 4]:
        N = 2**B
        x, _ = xp(N)
        ev = np.sort(np.linalg.eigvalsh(x))
        gaps = np.diff(ev)
        print("  B={} (N={:>2}):  x ∈ [{:+.2f}, {:+.2f}],  {} levels,  min gap Δx = {:.3f}"
              .format(B, N, ev[0], ev[-1], N, gaps.min()))
        print("            eigen-positions: " + " ".join("{:+.2f}".format(v) for v in ev))
    print("""
  A bit-limited particle lives on a finite lattice of allowed positions with a hard outer edge
  and a minimum spacing Δx_min — exactly the 'records are discrete cells' picture, now forced by
  the dimension. Momentum is dually bounded (a Brillouin-zone-like cutoff). No true continuum,
  no arbitrarily sharp localisation, a built-in UV cutoff.""")

# ======================================================================
#  IMPACT 3 — minimum length ⇒ Generalized Uncertainty Principle + level shifts
# ======================================================================
def impact_gup():
    print("\n" + "=" * 78)
    print("IMPACT 3 — a minimum length ⇒ GENERALIZED UNCERTAINTY PRINCIPLE and level shifts")
    print("  A floor Δx_min deforms Δx·Δp ≥ (ℏ/2)(1 + β Δp²). Every bound spectrum shifts by a")
    print("  fractional ~ (Δx_min/L_sys)². The size of the impact is ONE honest ratio: floor/system.")
    print("=" * 78)
    a0 = 5.29177e-11      # Bohr radius (m)
    lP = 1.616255e-35     # Planck length (m)
    lC = 3.86159e-13      # reduced Compton wavelength of the electron (m)
    alpha = 7.297e-3      # fine-structure constant (= λ_C/a0)
    print("  TOY — region L resolved by only B bits, Δx_min = L/2^B:")
    print("    B bits     Δx_min/L      impact (Δx_min/L)²")
    for B in [2, 4, 8, 16]:
        r = 1.0 / 2**B
        print("    {:<10}{:<14.3e}{:.3e}".format(B, r, r**2))
    print("  PHYSICAL minimum lengths, on an ATOM (L = a₀ = 5.3e-11 m):")
    print("    {:<24}{:<14}{}".format("floor Δx_min", "Δx_min/a₀", "impact (Δx_min/a₀)²"))
    print("    {:<24}{:<14.3e}{:.3e}   ← = α² : OBSERVED as fine structure (but standard Dirac QM)"
          .format("Compton  λ_C=ℏ/mc", lC/a0, (lC/a0)**2))
    print("    {:<24}{:<14.3e}{:.3e}   ← genuine QG minimum-length shift — far below detection"
          .format("Planck   ℓ_P", lP/a0, (lP/a0)**2))
    print("""
  The whole impact is the ratio (floor/system)². For a TOY with only a few resolution bits it is
  ORDER ONE — spectrum, hydrogen levels and density of states all visibly modified. For the real
  physical floors: the Compton length on an atom gives exactly α² ≈ 5e-5 — which we DO see, as
  relativistic fine structure, but that is standard Dirac QM, not λ; the Planck length gives
  ~10^-49 — the genuine quantum-gravity minimum-length signature, ~45 orders below measurement.""")

# ======================================================================
#  IMPACT 4 — the scaling law, and the one place it saturates
# ======================================================================
def impact_scaling():
    print("\n" + "=" * 78)
    print("IMPACT 4 — where the impact is O(1): comparable scales, or a SATURATED horizon")
    print("  Impact = (Δx_min/L)². It is O(1) only when the floor is comparable to the system.")
    print("=" * 78)
    print("  {:<28}{:<22}{}".format("regime", "Δx_min / L", "impact & status"))
    print("  " + "-" * 74)
    rows = [
        ("few-bit toy universe",      "~1/2 … 1/8",   "O(1) — deformed CCR, discrete x, recurrences"),
        ("atom, Compton floor",       "α ≈ 7e-3",     "α² ≈ 5e-5 — SEEN = fine structure (Dirac, not λ)"),
        ("atom, Planck floor",        "ℓ_P/a₀ ≈ 3e-25", "~1e-49 — unobserved (QG minimum length)"),
        ("1 m region, Planck floor",  "ℓ_P/L ≈ 2e-35", "~3e-70 — unobserved"),
        ("black-hole horizon",        "~1 (saturated)", "O(1) — IS Bekenstein–Hawking holography"),
    ]
    for name, r, eff in rows:
        print("  {:<28}{:<22}{}".format(name, r, eff))
    print("""
  The impact of limited bit space is REAL and computable — a deformed Heisenberg algebra, a
  discrete bounded spectrum, a minimum-length GUP with shifted levels and a UV cutoff. Its size is
  (floor/system)², so it is O(1) only when the two are comparable: a genuinely tiny-budget toy, or
  a horizon where the holographic bound is SATURATED — and there it is standard Bekenstein–Hawking
  holography (area law, Hawking spectrum, the information puzzle). For ordinary matter the only
  'floor' visible at all is the Compton length, and its impact (α², fine structure) is plain
  relativistic QM. Everything genuinely bit-limit / Planckian is ≥45 orders below measurement.""")

def verdict():
    print("\n" + "=" * 78)
    print("THE HONEST ANSWER")
    print("=" * 78)
    print("""  'In very limited bit space we should see the impact' — yes, and here it is, concretely:
    (1) the canonical commutator [x,p]=iℏ becomes impossible — the Heisenberg algebra is forced
        to deform (a theorem, not an approximation);
    (2) position/momentum become discrete and bounded — a finite lattice with a minimum cell and
        a hard edge, i.e. a built-in UV cutoff (no true continuum, no arbitrarily sharp records);
    (3) a minimum length ⇒ a Generalized Uncertainty Principle: every bound spectrum shifts,
        the density of states is modified — standard minimum-length / quantum-gravity signatures;
    (4) the size of every one of these is (Δx_min/L_system)², so it is O(1) only when the floor is
        comparable to the system — a tiny-budget toy, or a SATURATED horizon. For an atom the only
        real floor, the Compton length, gives α² (fine structure — seen, but plain Dirac QM);
        anything Planckian/bit-limit is ≥45 orders below measurement.

  TWO honest caveats that keep this consistent with everything prior:
    • These are the impacts of DYNAMICAL finiteness — a real cutoff Q_eff. QIQT-H's λ is INERT
      and produces NONE of them; to predict any of (1)–(3) you must ADD a dynamical-finiteness
      postulate (a small Q_eff), which is at present a free parameter, not a consequence of the
      holographic bound. With only inert λ + the huge holographic Q_R, the framework stays
      operationally = Everett (no impact), as established.
    • Where the impact is genuinely O(1) — the horizon — it is standard quantum-gravity
      holography, not λ. So 'very limited bit space' has real, dramatic physics; it just lives at
      horizons (and in hypothetical tiny-Q_eff toys), not in the inert-λ reading of ordinary
      laboratory systems.""")

def main():
    impact_commutator()
    impact_discreteness()
    impact_gup()
    impact_scaling()
    verdict()

if __name__ == "__main__":
    main()
