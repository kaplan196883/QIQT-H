#!/usr/bin/env python3
"""
The Bekenstein flow, modelled and plotted — why the AREA law is the envelope.

Grow a ball of matter at fixed density ρ and watch its information capacity flow:

  • BEKENSTEIN (energy) bound:  B_Bek = 2πRE/(ℏc·ln2),  E = (4/3)πR³ρc²  ⇒  B_Bek ∝ ρ R⁴.
  • HOLOGRAPHIC (area) bound:   B_holo = A/(4ℓ_P²·ln2) = πR²/(ℓ_P²·ln2)  ⇒  B_holo ∝ R².

The energy bound grows FASTER (R⁴) than the area bound (R²), so as the ball grows the two MUST cross.
They cross exactly at the Schwarzschild radius R*(ρ) = √(3c²/8πGρ) — i.e. the ball becomes a BLACK
HOLE precisely when its Bekenstein information would exceed the holographic ceiling. So the actual
capacity is

        B(R) = min(B_Bek, B_holo):   ∝ R⁴ (energy-limited) until BH collapse, then ∝ R² (area-limited).

This is the standard spherical-entropy argument (Bekenstein/Susskind): the most entropy a region can hold
is that of the black hole that fits inside it, so black holes/horizons are the area-scaling upper ENVELOPE.

CAVEATS (14th GPT-5.5-pro consult, verified): B_Bek is an UPPER BOUND (not realized info); the weak-gravity
form 2πRE/ℏc pushed to R_s is a FORMAL extrapolation (a Schwarzschild BH happens to saturate the same
expression); static matter destabilizes BEFORE R_s (Buchdahl R>9R_s/8), so 'collapse exactly at R_s' is
heuristic; and ordinary weakly-gravitating matter does NOT saturate the area law — it maxes at ~A^{3/4}, not
A (only horizons saturate). So the framing is: horizons are the upper envelope; ordinary matter sits far
below; pushing energy toward the envelope triggers collapse. The R⁴ lines are truncated at R_s (formal beyond).

This script tabulates the flow, overlays real objects, makes a log–log plot (build/bekenstein_flow.png),
and reads off the impact on the λ-generator. Needs numpy + matplotlib.
"""
import math
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HBAR = 1.054571817e-34
C    = 2.99792458e8
G    = 6.674e-11
M_P  = 1.67262192e-27          # proton mass (kg)
LP2  = HBAR * G / C**3
LN2  = math.log(2)

def B_bek(R, rho):
    E = (4.0/3.0) * math.pi * R**3 * rho * C**2
    return 2 * math.pi * R * E / (HBAR * C * LN2)

def B_holo(R):
    return math.pi * R * R / (LP2 * LN2)

def S_realized(R, rho):
    """Realized (thermodynamic) entropy of ordinary matter ≈ particle number N = mass/m_p, ∝ ρR³
       (VOLUME). Order of magnitude — true entropy is a few × N. Black holes are the exception: they
       saturate B_holo, far above their progenitor matter's N (the entropy jump of collapse)."""
    return (4.0/3.0) * math.pi * R**3 * rho / M_P

def R_schwarzschild_density(rho):
    """Radius at which a ball of density ρ is its own Schwarzschild radius (BH collapse = the crossover)."""
    return math.sqrt(3 * C**2 / (8 * math.pi * G * rho))

# ======================================================================
#  PART 1 — the flow for fixed-density balls: R⁴ rise, R² ceiling, BH crossover
# ======================================================================
def run_flow_table():
    print("=" * 84)
    print("PART 1 — the Bekenstein flow: B_Bek ∝ ρR⁴ rises until it hits B_holo ∝ R² (BH collapse)")
    print("=" * 84)
    print("  {:<24}{:<14}{:<16}{}".format("density ρ (kg/m³)", "R* (m)", "B at R* (bits)", "what R* is"))
    print("  " + "-" * 74)
    for rho, name in [(1.2, "air"), (1.0e3, "water"), (5.5e3, "Earth-avg"),
                      (1.6e5, "Sun-core"), (4.0e17, "neutron-star"), (5.2e96, "Planck")]:
        Rs = R_schwarzschild_density(rho)
        print("  {:<24}{:<14.3e}{:<16.3e}{}".format(
            "{:.1e} ({})".format(rho, name), Rs, B_holo(Rs), "Schwarzschild radius ⇒ BH"))
    print("""
  Denser matter collapses at a SMALLER radius: a water-density ball would become a black hole at
  R* ~ 4×10¹¹ m (a few AU), neutron-star matter at ~20 km. At R* the energy (R⁴) and area (R²) bounds
  meet — the ball saturates the holographic bound and is a black hole. Below R* it is energy-limited
  (R⁴); it can never exceed the area bound without collapsing. The area law is the collapse envelope.""")

# ======================================================================
#  PART 2 — real objects on the flow
# ======================================================================
#  (name, radius m, mass kg, is_black_hole)
OBJECTS = [
    ("H atom",        5.3e-11, 1.67e-27,        False),
    ("human",         0.5,     70.0,            False),
    ("Earth",         6.37e6,  5.97e24,         False),
    ("Sun",           6.96e8,  1.989e30,        False),
    ("white dwarf",   7.0e6,   1.4*1.989e30,    False),
    ("neutron star",  1.2e4,   1.4*1.989e30,    False),
    ("solar BH",      2.95e3,  1.989e30,        True),
    ("Sgr A* (SMBH)", 1.2e10,  4.3e6*1.989e30,  True),
    ("Milky Way",     5e20,    1.5e42,          False),
]

def run_objects():
    print("\n" + "=" * 84)
    print("PART 2 — capacity (holographic) vs max info (Bekenstein) vs REALIZED entropy")
    print("=" * 84)
    print("  {:<15}{:<13}{:<13}{:<14}{:<14}{}".format(
        "object", "B_holo", "B_Bek", "S_realized", "realized/holo", "note"))
    print("  " + "-" * 80)
    for name, R, M, is_bh in OBJECTS:
        bh = B_holo(R)
        bb = 2 * math.pi * R * (M*C**2) / (HBAR * C * LN2)
        sr = bh if is_bh else M / M_P                  # BHs saturate; matter realizes ~N particles
        note = "BLACK HOLE — saturated" if is_bh else ""
        print("  {:<15}{:<13.1e}{:<13.1e}{:<14.1e}{:<14.1e}{}".format(name, bh, bb, sr, sr/bh, note))
    print("""
  Three very different quantities. CAPACITY (holographic, ∝R²) is the absolute ceiling; MAX INFO
  (Bekenstein, ∝R⁴) is what the energy could in principle encode; REALIZED entropy (∝R³ ≈ particle
  number N) is what is ACTUALLY there. For ordinary matter realized ≪ Bekenstein ≪ holographic — the
  Sun realizes ~10⁵⁷ of its ~10⁸⁸-bit capacity, i.e. ~10⁻³¹ of it. Black holes are the exception:
  realized = capacity (they saturate), which is why collapse JUMPS the entropy up by ~20 orders
  (a stellar core's ~10⁵⁷ → its black hole's ~10⁷⁷).""")

# ======================================================================
#  PART 3 — the plot
# ======================================================================
def make_plot(path="build/bekenstein_flow.png"):
    R = np.logspace(-15, 27, 600)
    fig, ax = plt.subplots(figsize=(9, 6.5))

    # holographic envelope (slope 2) — the black-hole / collapse line
    ax.plot(R, [B_holo(r) for r in R], "k-", lw=2.4, label="holographic bound $\\propto R^2$ (black holes)")

    # Bekenstein R^4 lines for a few densities, truncated at BH collapse R*
    for rho, name, col in [(1.0e3, "water", "tab:blue"),
                           (4.0e17, "neutron-star", "tab:red"),
                           (1.2, "air", "tab:green")]:
        Rstar = R_schwarzschild_density(rho)
        Rline = R[R <= Rstar]
        ax.plot(Rline, [B_bek(r, rho) for r in Rline], "--", color=col, lw=1.8,
                label="Bekenstein $\\propto \\rho R^4$ ({})".format(name))
        ax.plot(Rstar, B_holo(Rstar), "o", color=col, ms=7)

    # REALIZED-entropy reference line: S ≈ ρR³/m_p (VOLUME) for water density
    rho_w = 1.0e3
    Rstar_w = R_schwarzschild_density(rho_w)
    Rreal = R[R <= Rstar_w]
    ax.plot(Rreal, [S_realized(r, rho_w) for r in Rreal], ":", color="tab:purple", lw=1.8,
            label="realized entropy $\\propto \\rho R^3$ (matter, water)")

    # real objects: bound (B_Bek) as a square, realized entropy as a triangle; BHs sit on the envelope
    for name, r, M, is_bh in OBJECTS:
        bb = 2 * math.pi * r * (M*C**2) / (HBAR * C * LN2)
        sr = B_holo(r) if is_bh else M / M_P
        ax.plot(r, bb, "ks", ms=5)
        if is_bh:
            ax.annotate(name, (r, bb), textcoords="offset points", xytext=(5, 4), fontsize=7)
        else:
            ax.plot(r, sr, "v", color="tab:purple", ms=6)
            ax.annotate(name, (r, sr), textcoords="offset points", xytext=(5, -9), fontsize=7)

    # the entropy JUMP at collapse: neutron star (realized) → solar BH (saturated)
    ns = next(o for o in OBJECTS if o[0] == "neutron star")
    bhp = next(o for o in OBJECTS if o[0] == "solar BH")
    ax.annotate("", xy=(bhp[1], B_holo(bhp[1])), xytext=(ns[1], ns[2]/M_P),
                arrowprops=dict(arrowstyle="->", color="darkorange", lw=1.6))
    ax.annotate("collapse:\nentropy jumps\n~20 orders", (ns[1]*3, ns[2]/M_P*1e8),
                fontsize=7, color="darkorange")

    # COSMOLOGICAL HORIZON: like a black-hole horizon, it SATURATES the holographic bound
    # (de Sitter / Hubble entropy ~10^122); the universe's REALIZED entropy ~10^104 sits 10^-18 below.
    R_H = 1.32e26                     # Hubble radius c/H0
    S_univ = 1.0e104                  # realized entropy of the observable universe (Egan–Lineweaver)
    ax.plot(R_H, B_holo(R_H), "*", color="black", ms=15, zorder=5)
    ax.annotate("cosmological horizon\n(saturated, $\\sim 10^{122}$)", (R_H, B_holo(R_H)),
                textcoords="offset points", xytext=(-118, -30), fontsize=7)
    ax.plot(R_H, S_univ, "v", color="tab:purple", ms=9, zorder=5)
    ax.annotate("universe realized\n$\\sim 10^{104}$  ($10^{-18}$ of capacity)", (R_H, S_univ),
                textcoords="offset points", xytext=(-60, -22), fontsize=7, color="tab:purple")
    ax.annotate("", xy=(R_H, B_holo(R_H)), xytext=(R_H, S_univ),
                arrowprops=dict(arrowstyle="<->", color="gray", lw=1.1, ls=":"))

    ax.set_xscale("log"); ax.set_yscale("log")
    ax.set_xlabel("region radius  R  (m)")
    ax.set_ylabel("information  (bits)")
    ax.set_title("Bekenstein flow: capacity ($R^2$) vs max info ($R^4$) vs REALIZED entropy ($R^3$)")
    ax.set_xlim(1e-15, 1e27); ax.set_ylim(1, 1e125)
    ax.plot([], [], "ks", ms=5, label="object's Bekenstein bound")
    ax.plot([], [], "v", color="tab:purple", ms=6, label="object's realized entropy ($\\approx N$)")
    ax.plot([], [], "*", color="black", ms=12, label="horizon (saturates: BH / cosmological)")
    ax.legend(loc="upper left", fontsize=7.5, framealpha=0.9)
    ax.grid(True, which="major", ls=":", alpha=0.4)
    fig.tight_layout()
    fig.savefig(path, dpi=130)
    plt.close(fig)
    return path

# ======================================================================
#  PART 4 — impact on the λ-generator
# ======================================================================
def run_impact(path):
    print("\n" + "=" * 84)
    print("PART 4 — plot saved + impact on the λ-generator")
    print("=" * 84)
    print("  plot → {}".format(path))
    print("""
  The flow is the answer to 'why area, not volume'. A generator that tried to source the world's
  randomness from VOLUME-much information (∝R⁴, energy-limited) would drive the region to its
  Schwarzschild radius and COLLAPSE — the holographic (∝R²) line is the collapse envelope it cannot
  cross. So the λ-generator's budget is forced onto the AREA: the boundary is the seed, the bulk its
  hologram (consistent with bekenstein_flow_generator.py). The black-hole points where the R⁴ lines
  meet the R² envelope are exactly the saturated regime — the one place a finite budget genuinely
  bites — and there it is standard Bekenstein–Hawking, not λ. Everywhere below the envelope the budget
  is slack, the faking window 2^B is astronomically large, and the generator is observably = QM.""")

def main():
    run_flow_table()
    run_objects()
    p = make_plot()
    run_impact(p)

if __name__ == "__main__":
    main()
