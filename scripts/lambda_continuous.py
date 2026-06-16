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
#  TRUNCATION — thermal records pushed against a SMALL budget
# ======================================================================
def run_truncation():
    print("\n" + "=" * 78)
    print("TRUNCATION — a thermal oscillator vs a deliberately SMALL bit budget B.")
    print("Records = energy levels |n>, thermal weights p_n = n̄^n / (1+n̄)^(n+1).")
    print("Budget B ⇒ only N = 2^B levels exist; the high-energy tail is CUT and renormalised.")
    print("=" * 78)
    nbar = 5.0
    S_full = ((1 + nbar) * math.log(1 + nbar) - nbar * math.log(nbar)) / math.log(2)
    print("  thermal n̄ = {:.0f}:  untruncated ⟨n⟩ = {:.2f},  entropy S = {:.2f} bits"
          .format(nbar, nbar, S_full))
    print("  → it 'wants' ~2^S = {:.0f} records. Truncation bites once the budget B drops below S."
          .format(2 ** S_full))
    print("  " + "-" * 74)
    print("  {:<4}{:<8}{:<10}{:<12}{:<12}{}".format(
        "B", "N=2^B", "⟨n⟩_N", "S_N (bits)", "⟨E⟩/ℏω", "effect"))

    def thermal_p(n):
        return nbar ** n / (1 + nbar) ** (n + 1)

    for B in range(1, 9):
        N = 2 ** B
        ps = [thermal_p(n) for n in range(N)]
        Z = sum(ps)
        ps = [p / Z for p in ps]
        mean_n = sum(n * p for n, p in enumerate(ps))
        S_N = entropy_bits(ps)
        E = mean_n + 0.5
        if abs(mean_n - nbar) / nbar < 0.01 and abs(S_N - S_full) < 0.05:
            eff = "slack — no effect"
        elif S_N >= B - 0.05:
            eff = "SATURATED: S capped at B"
        else:
            eff = "truncated: ⟨n⟩,S suppressed"
        print("  {:<4}{:<8}{:<10.3f}{:<12.3f}{:<12.3f}{}".format(B, N, mean_n, S_N, E, eff))
    print("  → S_N → min(S_full, B): the budget CAPS the entropy (this is the Bekenstein–Hawking")
    print("    statement S ≤ A/4). For B ≫ S (lab thermal systems) it is slack — ⟨n⟩,S unchanged;")
    print("    it only bites at saturation B ≲ S (horizons), and there it is QG, not λ.")

    # show the distribution: slack budget vs truncating budget
    def bars(B, tag):
        N = 2 ** B
        ps = [thermal_p(n) for n in range(N)]
        Z = sum(ps); ps = [p / Z for p in ps]
        print("    {} (B={}, N={}):".format(tag, B, N))
        for n in range(min(N, 22)):
            print("      |{:>2}>  {}{:.3f}".format(n, "#" * int(round(ps[n] * 80)), ps[n]))
    print("  --- record distribution p_n ---")
    bars(7, "slack budget")        # B=7, N=128 ≫ S: full thermal tail
    bars(2, "truncating budget")   # B=2, N=4 < S: tail cut, mass piles at the cutoff

# ======================================================================
#  (B, n̄) PHASE DIAGRAM — where the budget bites a thermal oscillator
# ======================================================================
def _Sfull(nbar):
    if nbar <= 0: return 0.0
    return (1 + nbar) * math.log2(1 + nbar) - nbar * math.log2(nbar)

def _trunc(B, nbar):
    """Closed-form ⟨n⟩_N and S_N (bits) for a thermal level distribution truncated to N=2^B."""
    r = nbar / (1 + nbar)
    N = 2 ** B
    rN = r ** N
    if rN >= 1.0 - 1e-15:        # r→1, N small: nearly uniform over N levels
        meanN = (N - 1) / 2.0
        S_N = math.log2(N)
        return meanN, S_N
    meanN = r * (1 - N * r ** (N - 1) + (N - 1) * rN) / ((1 - r) * (1 - rN))
    S_N = -math.log2(1 - r) + math.log2(1 - rN) - meanN * math.log2(r)
    return meanN, S_N

def _classify(B, nbar):
    meanN, S_N = _trunc(B, nbar)
    S_full = _Sfull(nbar)
    dE = (nbar - meanN) / nbar if nbar > 0 else 0.0
    if dE < 0.01 and abs(S_N - S_full) < 0.05:
        return "."      # slack: no effect
    if S_N >= B - 0.15:
        return "#"      # saturated: entropy capped at the budget (S → B)
    return "T"          # truncated: ⟨n⟩ and S suppressed

def run_phase_diagram():
    print("\n" + "=" * 78)
    print("(B, n̄) PHASE DIAGRAM — where the bit budget BITES a thermal oscillator.")
    print("  '.' slack (B ≫ S: no effect)   'T' truncated (⟨n⟩,S suppressed)   '#' saturated (S → B)")
    print("=" * 78)
    ks = list(range(0, 17))          # n̄ = 2^k  (1 … 65536)
    print("  log2(n̄):       " + "".join("{:<3}".format(k) for k in ks))
    for B in range(16, 0, -1):
        row = "".join(" {} ".format(_classify(B, 2.0 ** k)) for k in ks)
        print("  B={:<2}          {}".format(B, row))
    print("  S_full(n̄)≈:    " + "".join("{:<3.0f}".format(_Sfull(2.0 ** k)) for k in ks))
    print("  → boundary: B ≈ S_full(n̄) ≈ log₂(n̄)+1.4 (the diagonal). Above it the budget is")
    print("    slack (no effect); on/below it the thermal state is truncated, S capped at B.")
    print("  → REAL thermal systems sit at astronomically LARGE B (Q_R ≈ 1e65…1e122 bits) —")
    print("    far off the TOP of this chart, deep in the '.' slack region. The '#'/'T' bite-")
    print("    zone is reached only by (i) an artificially tiny budget, or (ii) n̄ pushed up to")
    print("    the holographic entropy (black-hole / horizon saturation) — where it IS")
    print("    Bekenstein–Hawking finiteness, NOT λ. λ inert ⇒ no observable effect either way.")

# ======================================================================
#  ADDING G — the bit budget IS gravitational (Q_R = A/4ℓ_P² ∝ 1/G)
# ======================================================================
def run_gravity():
    hbar, c, G, kB = 1.0546e-34, 2.998e8, 6.674e-11, 1.381e-23
    lP2 = hbar * G / c ** 3
    mP = math.sqrt(hbar * c / G)
    print("\n" + "=" * 78)
    print("ADDING G — the bit budget is GRAVITATIONAL: Q_R = A/(4ℓ_P²),  ℓ_P² = ℏG/c³ ∝ G.")
    print("=" * 78)
    print("  So Q_R = A c³/(4ℏG)  ∝  1/G.  Gravity is WHAT makes the budget finite:")
    print("    G → 0  ⇒  ℓ_P → 0  ⇒  Q_R → ∞  ⇒  infinite records, no truncation — pure QM")
    print("    continuum, and the whole finite-λ thesis has no anchor. The bound is gravity's.")
    print("  ℓ_P = {:.3e} m,   Planck mass m_P = {:.3e} kg".format(math.sqrt(lP2), mP))
    # Q_R ∝ 1/G demonstration on a 1 m² patch
    A1 = 1.0
    print("  Q_R for a 1 m² patch:  with G → {:.2e} bits;   with 2G → {:.2e} bits  (halves ∝ 1/G)"
          .format(A1 / (4 * lP2) / math.log(2), A1 / (4 * hbar * 2 * G / c ** 3) / math.log(2)))
    print("  " + "-" * 74)
    print("  A BLACK HOLE is the thermal system whose entropy EQUALS its budget — it sits")
    print("  exactly ON the saturation boundary (B = S), and G sets where that is:")
    print("  {:<18}{:<13}{:<14}{:<14}{}".format("object", "R_s (m)", "S_BH (bits)", "T_Hawking (K)", "phase"))
    for label, M in [("Planck-mass BH", mP), ("1 kg BH", 1.0),
                     ("solar-mass BH", 1.989e30), ("10⁹ M_sun SMBH", 1.989e39)]:
        Rs = 2 * G * M / c ** 2
        A = 4 * math.pi * Rs ** 2
        S_bits = A / (4 * lP2) / math.log(2)
        TH = hbar * c ** 3 / (8 * math.pi * G * M * kB)
        print("  {:<18}{:<13.2e}{:<14.2e}{:<14.2e}{}".format(label, Rs, S_bits, TH, "SATURATED (S = A/4)"))
    print("  → S_BH = A/(4ℓ_P²) = Q_R(horizon): the black hole is exactly at saturation, set by G;")
    print("    its Hawking radiation is the truncated thermal spectrum. This is Bekenstein–Hawking")
    print("    (standard quantum gravity). G anchors the bit-limit to spacetime — it does NOT make")
    print("    λ observable: λ stays inert ⇒ still = Everett. (A genuine λ-effect would need λ to")
    print("    couple dynamically — abandoning inert-λ — which is the speculative, non-Born route.)")

# ======================================================================
#  REAL SYSTEMS overlaid on the (entropy-demand vs budget) plane
# ======================================================================
def run_overlay():
    hbar, c, G = 1.0546e-34, 2.998e8, 6.674e-11
    lP2 = hbar * G / c ** 3
    ln2 = math.log(2)
    def Smax_bits(R):                       # holographic budget for a region of radius R (bits)
        return math.pi * R * R / (lP2 * ln2)
    print("\n" + "=" * 78)
    print("REAL SYSTEMS on the (S_demand vs B=budget) plane — the (B,n̄) diagram, generalised.")
    print("  x = log₁₀(S the system WANTS, bits)   y = log₁₀(B = holographic budget for its size)")
    print("  boundary B = S (the bite line): ONLY black holes & horizons sit there (saturated).")
    print("=" * 78)
    # (marker, name, radius_m, S_sys_bits  [None ⇒ saturating: S = B])
    systems = [
        ("a", "trapped-ion qubit",      1e-4,   1.0),
        ("b", "1 cm³ gas (300 K)",      1e-2,   7e20),
        ("c", "the Earth",              6.37e6, 1e44),
        ("d", "the Sun",                6.96e8, 1e58),
        ("e", "CMB photons (obs.univ)", 1.3e26, 3e88),
        ("f", "obs-universe matter",    1.3e26, 1e104),
        ("g", "solar-mass black hole",  2953.0, None),
        ("h", "10⁹ M_sun SMBH",         2.95e12, None),
        ("i", "de Sitter horizon",      1.3e26, None),
    ]
    rows = []
    print("  {:<3}{:<22}{:<11}{:<13}{:<13}{}".format("", "system", "R (m)", "log10 S_sys", "log10 B", "phase"))
    for mk, name, R, Ssys in systems:
        B = Smax_bits(R)
        if Ssys is None:
            Ssys = B
        slack = math.log10(B / Ssys) if Ssys > 0 else 0
        phase = "SATURATED — on the bite line" if slack < 0.3 else "slack: {:>2.0f} orders → no effect".format(slack)
        rows.append((mk, math.log10(Ssys), math.log10(B)))
        print("  {:<3}{:<22}{:<11.1e}{:<13.1f}{:<13.1f}{}".format(mk, name, R, math.log10(Ssys), math.log10(B), phase))
    # ASCII scatter: y=log10 B (budget) up, x=log10 S (demand) right; diagonal = bite line
    print("  " + "-" * 74)
    print("  log10 B")
    HI, STEP = 130, 10
    nrow = HI // STEP + 1
    for ri in range(nrow - 1, -1, -1):
        yv = ri * STEP
        line = "  {:>4} |".format(yv)
        for ci in range(nrow):
            xv = ci * STEP
            ch = " "
            if abs(yv - xv) <= STEP / 2:
                ch = "\\"                      # the B = S bite line
            for mk, xs, ys in rows:
                if round(xs / STEP) == ci and round(ys / STEP) == ri:
                    ch = mk
            line += ch
        print(line)
    print("       +" + "-" * nrow)
    print("        " + "".join(str((ci * STEP) // 10 % 10) for ci in range(nrow)) + "  (log10 S_sys, ×10)")
    print("  legend: " + " ".join("{}={}".format(mk, nm) for mk, nm, _, _ in systems))
    print("  → '\\' is the bite line B = S. Every system sits ON it (g,h,i = black holes /")
    print("    horizon — SATURATED, Bekenstein–Hawking) or far ABOVE it (a…f — slack by 18–62")
    print("    orders, NO effect). Even the SMBH-dominated universe (f) is ~18 orders slack")
    print("    (~10⁻¹⁸ of capacity). The bite line is reached only by gravity, set by G; the")
    print("    effect there is standard QG, not λ. λ inert ⇒ = Everett everywhere on this chart.")

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
    run_truncation()
    run_phase_diagram()
    run_gravity()
    run_overlay()
    run_reality()
