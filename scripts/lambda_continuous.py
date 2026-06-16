#!/usr/bin/env python3
"""
λ's bit-limit in continuous systems — particle in a box & harmonic oscillator.

A finite-bit λ indexes at most 2^B distinguishable records. For a continuum the
records are decohered cells, so the bit budget B caps the resolution. This script
computes, for representative states Φ, the *record entropy* H_B (the bits λ must
hold to name the actual cell) as a function of the budget B, and shows the two
qualitatively different behaviours:

  • BOX (position records): no natural floor — you can localise position arbitrarily
    (paying in momentum), so H_B ≈ B + h_diff(Φ) grows with the budget. The bit limit
    just caps the position resolution Δx ≳ L/2^B.
  • OSCILLATOR (phase-space records): the uncertainty principle gives a minimum cell
    of area 2πℏ, so H_B SATURATES at the ℏ-cell entropy — extra bits buy nothing once
    you resolve to ℏ. A coherent state IS one cell (needs ~0 bits); a Fock |n> spreads
    over a ring of ~√n cells.

Honest frame: standard decoherence/phase-space counting in (Φ,λ) language; the
holographic Q_R cap is astronomically slack for everyday systems (decoherence sets
the real resolution); λ is inert ⇒ operationally Everett. No new physics.

Units: ℏ = m = ω = L = 1.   Pure Python (no numpy).
"""
import math, cmath

def entropy_bits(weights):
    h = 0.0
    for w in weights:
        if w > 1e-15:
            h -= w * math.log2(w)
    return h

# ======================================================================
#  PARTICLE IN A BOX  — position records
# ======================================================================
NX = 8192
xs = [(i + 0.5) / NX for i in range(NX)]            # midpoints of a fine grid on [0,1]
dx = 1.0 / NX

def box_density(name):
    if name.startswith("ground"):                    # n=1 eigenstate (one broad bump)
        rho = [2 * math.sin(math.pi * x) ** 2 for x in xs]
    elif name.startswith("excited"):                 # n=4 eigenstate (four bumps)
        rho = [2 * math.sin(4 * math.pi * x) ** 2 for x in xs]
    elif name.startswith("localized"):               # narrow Gaussian wavepacket
        x0, s = 0.35, 0.03
        rho = [math.exp(-((x - x0) ** 2) / (2 * s * s)) for x in xs]
    elif name.startswith("two-bump"):                # (psi_1 + psi_2)/sqrt2 superposition
        rho = []
        for x in xs:
            psi = (math.sqrt(2) * math.sin(math.pi * x) + math.sqrt(2) * math.sin(2 * math.pi * x))
            rho.append((psi / math.sqrt(2)) ** 2)
    Z = sum(rho) * dx
    return [r / Z for r in rho]

def box_coarse_entropy(rho, B):
    ncells = 2 ** B
    per = NX // ncells
    w = []
    for c in range(ncells):
        s = sum(rho[c * per:(c + 1) * per]) * dx
        w.append(s)
    return entropy_bits(w)

def run_box():
    print("=" * 78)
    print("PARTICLE IN A BOX — position records.  H_B = bits λ must hold at budget B.")
    print("(Expect H_B to GROW with B: position has no minimum cell.)")
    print("=" * 78)
    states = ["ground n=1", "excited n=4", "localized σ=.03", "two-bump (ψ1+ψ2)"]
    Bs = list(range(1, 12))
    print("  state              " + "".join("B={:<5}".format(b) for b in Bs))
    for name in states:
        rho = box_density(name)
        hs = [box_coarse_entropy(rho, b) for b in Bs]
        print("  {:<18}".format(name) + "".join("{:<6.2f}".format(h) for h in hs))
    print("  note: H_B ≈ B + h_diff(Φ).  'localized' sits LOWEST (small differential")
    print("        entropy ⇒ fewer effective bits); all keep growing — no ℏ floor in x alone.")

# ======================================================================
#  HARMONIC OSCILLATOR — phase-space (coherent-state) records, Husimi Q
# ======================================================================
R = 4.0                  # phase-space half-width in β = (x+ip)/√2
NB = 240                 # grid points per axis
db = 2 * R / NB
HBAR_CELL_AREA_BETA = math.pi   # 2πℏ in (x,p) = π in the β-plane (d²β = dx dp /2)

def husimi(name):
    """Return Q(u,v) on the β=u+iv grid (already /π, ∫Q d²β = 1)."""
    grid = [[0.0] * NB for _ in range(NB)]
    if name.startswith("coherent"):
        a = 1.6 + 0j
        for i in range(NB):
            for j in range(NB):
                b = complex(-R + (i + .5) * db, -R + (j + .5) * db)
                grid[i][j] = math.exp(-abs(b - a) ** 2) / math.pi
    elif name.startswith("Fock"):
        n = 5
        for i in range(NB):
            for j in range(NB):
                b = complex(-R + (i + .5) * db, -R + (j + .5) * db)
                r2 = abs(b) ** 2
                grid[i][j] = math.exp(-r2) * r2 ** n / (math.pi * math.factorial(n))
    elif name.startswith("cat"):
        a = 2.0 + 0j
        norm = 2 * (1 + math.exp(-2 * abs(a) ** 2))
        for i in range(NB):
            for j in range(NB):
                b = complex(-R + (i + .5) * db, -R + (j + .5) * db)
                ov = (cmath.exp(-abs(b) ** 2 / 2 - abs(a) ** 2 / 2 + b.conjugate() * a)
                      + cmath.exp(-abs(b) ** 2 / 2 - abs(a) ** 2 / 2 - b.conjugate() * a))
                grid[i][j] = abs(ov / math.sqrt(norm)) ** 2 / math.pi
    elif name.startswith("squeezed"):
        # squeezed vacuum, real squeeze r: Husimi is an area-PRESERVING ellipse
        #   Q ∝ sech(r) exp[ -u²(1-tanh r) - v²(1+tanh r) ]   (u=x-quad anti-squeezed, v=p-quad squeezed)
        r = 1.1; t = math.tanh(r)
        for i in range(NB):
            for j in range(NB):
                u = -R + (i + .5) * db; v = -R + (j + .5) * db
                grid[i][j] = (1.0 / math.cosh(r)) * math.exp(-u * u * (1 - t) - v * v * (1 + t)) / math.pi
    elif name.startswith("thermal"):
        # thermal (mixed) state, mean photon number nbar: Q = exp(-|β|²/(1+nbar)) / (π(1+nbar))
        nbar = 2.0
        for i in range(NB):
            for j in range(NB):
                b = complex(-R + (i + .5) * db, -R + (j + .5) * db)
                grid[i][j] = math.exp(-abs(b) ** 2 / (1 + nbar)) / (math.pi * (1 + nbar))
    # renormalize on the (finite) grid
    Z = sum(sum(row) for row in grid) * db * db
    return [[v / Z for v in row] for row in grid]

def ho_coarse_entropy(Q, cells_per_axis):
    """Coarse-grain the β-plane into cells_per_axis^2 square cells; entropy of the law."""
    per = NB // cells_per_axis
    w = []
    for ci in range(cells_per_axis):
        for cj in range(cells_per_axis):
            s = 0.0
            for i in range(ci * per, (ci + 1) * per):
                for j in range(cj * per, (cj + 1) * per):
                    s += Q[i][j]
            w.append(s * db * db)
    return entropy_bits(w)

def ho_cell_area_beta(cells_per_axis):
    return (2 * R / cells_per_axis) ** 2          # area of one cell in β-plane

def heatmap(Q, label):
    chars = " .:-=+*#%@"
    step = NB // 24
    mx = max(max(row) for row in Q)
    print("  Husimi Q — " + label + "  (x→, p↑; one ℏ-cell ≈ {}×{} chars)"
          .format(max(1, round(math.sqrt(HBAR_CELL_AREA_BETA) / db / step)),
                  max(1, round(math.sqrt(HBAR_CELL_AREA_BETA) / db / step))))
    for j in range(NB - 1, -1, -step):
        line = "    "
        for i in range(0, NB, step):
            line += chars[min(len(chars) - 1, int(Q[i][j] / mx * (len(chars) - 1)))]
        print(line)

def run_ho():
    print("\n" + "=" * 78)
    print("HARMONIC OSCILLATOR — phase-space (coherent-state) records, Husimi Q.")
    print("(Expect H_B to SATURATE at the ℏ-cell: uncertainty gives a minimum cell 2πℏ.)")
    print("=" * 78)
    states = ["coherent α=1.6", "squeezed r=1.1", "thermal n̄=2", "Fock |5>", "cat |2>+|-2>"]
    # cells_per_axis values; the ℏ floor is where cell area ≈ 2πℏ (=π in β)
    cpa_list = [1, 2, 4, 8, 16, 32]
    # bits B = log2(total cells) = log2(cpa^2)
    print("  cells/axis        " + "".join("{:<8}".format("{}^2".format(c)) for c in cpa_list))
    print("  bits B=log2(#)    " + "".join("{:<8.1f}".format(math.log2(c * c)) for c in cpa_list))
    print("  cell area / 2πℏ   " + "".join("{:<8.2f}".format(ho_cell_area_beta(c) / HBAR_CELL_AREA_BETA)
                                           for c in cpa_list))
    print("  " + "-" * 70)
    for name in states:
        Q = husimi(name)
        hs = [ho_coarse_entropy(Q, c) for c in cpa_list]
        print("  {:<16}".format(name) + "".join("{:<8.2f}".format(h) for h in hs))
    print("  note: cells with area/2πℏ < 1 are SUB-ℏ — not distinguishable records (states")
    print("        there overlap), so that growth is unphysical over-counting. Read AT the ℏ")
    print("        floor (area ≈ 2πℏ, the '1.27' column):")
    print("          coherent ≈ 2.0 b — one compact ℏ-cell (the floor case)")
    print("          squeezed ≈ 2.7 b — AREA-PRESERVING ellipse: squeezing REDISTRIBUTES bits")
    print("                             between quadratures (narrow p ⇒ fewer p-bits, wide x ⇒")
    print("                             more x-bits); same intrinsic area — reshapes, doesn't add")
    print("          thermal  ≈ 3.0 b — MIXED: footprint GROWS with T, area ≈ (1+n̄) cells, so")
    print("                             H ≈ coherent + log2(1+n̄) — heating genuinely ADDS records")
    print("          Fock|5>  ≈ 3.7 b — a √n ring of cells;   cat ≈ 3.0 b — two blobs")
    print("        The bit budget caps the # of ℏ-cells = accessible phase-space area = the")
    print("        energy range — the uncertainty floor on λ. Squeezing reshapes the records;")
    print("        temperature adds them; the holographic Q_R is the (slack) outer cap.")
    print()
    for name in ["coherent α=1.6", "squeezed r=1.1", "thermal n̄=2", "Fock |5>", "cat |2>+|-2>"]:
        heatmap(husimi(name), name)
        print()

# ======================================================================
#  HOLOGRAPHIC REALITY CHECK
# ======================================================================
def run_reality():
    print("=" * 78)
    print("REALITY CHECK — where λ's holographic bit limit actually sits.")
    print("=" * 78)
    # Q_R ~ A/4 l_P^2 ;  l_P ~ 1.6e-35 m
    lP2 = (1.6e-35) ** 2
    for label, A in [("1 cm² boundary", 1e-4), ("1 m² boundary", 1.0),
                     ("Earth (4πR²)", 5.1e14), ("cosmological horizon", 6e52)]:
        QR = A / (4 * lP2)
        print("  {:<22} Q_R ≈ {:.1e} bits   →  up to 2^Q_R distinguishable records"
              .format(label, QR / math.log(2)))
    print("  --- vs physical resolution ---")
    print("  A decohered pointer cell (thermal de Broglie / scattering) is ~10s of orders")
    print("  of magnitude COARSER than the holographic ℏ-cap, yet finite. So in practice")
    print("  λ indexes DECOHERENCE-defined cells (far fewer than 2^Q_R); the holographic")
    print("  bit-limit is a slack in-principle ceiling — it bites only near horizons /")
    print("  the Planck scale. The universe runs at ~10^-18 of its holographic capacity.")

if __name__ == "__main__":
    run_box()
    run_ho()
    run_reality()
