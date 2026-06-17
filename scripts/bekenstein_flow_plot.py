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

That is WHY information scales with area, not volume: matter that tries to pack volume-much information
collapses to a black hole, whose entropy is the area. The holographic bound is the collapse ENVELOPE.

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
LP2  = HBAR * G / C**3
LN2  = math.log(2)

def B_bek(R, rho):
    E = (4.0/3.0) * math.pi * R**3 * rho * C**2
    return 2 * math.pi * R * E / (HBAR * C * LN2)

def B_holo(R):
    return math.pi * R * R / (LP2 * LN2)

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
OBJECTS = [
    ("H atom",        5.3e-11, 1.67e-27),
    ("human",         0.5,     70.0),
    ("Earth",         6.37e6,  5.97e24),
    ("Sun",           6.96e8,  1.989e30),
    ("white dwarf",   7.0e6,   1.4*1.989e30),
    ("neutron star",  1.2e4,   1.4*1.989e30),
    ("solar BH",      2.95e3,  1.989e30),
    ("Sgr A* (SMBH)", 1.2e10,  4.3e6*1.989e30),
    ("Milky Way",     5e20,    1.5e42),
]

def run_objects():
    print("\n" + "=" * 84)
    print("PART 2 — real objects: Bekenstein bound vs holographic bound (BHs saturate)")
    print("=" * 84)
    print("  {:<16}{:<12}{:<15}{:<15}{}".format("object", "R (m)", "B_Bek (bits)", "B_holo (bits)", "B_Bek/B_holo"))
    print("  " + "-" * 76)
    for name, R, M in OBJECTS:
        E = M * C**2
        bb = 2 * math.pi * R * E / (HBAR * C * LN2)
        bh = B_holo(R)
        print("  {:<16}{:<12.2e}{:<15.2e}{:<15.2e}{:.2e}".format(name, R, bb, bh, bb/bh))
    print("""
  Every ordinary object sits BELOW the holographic line (B_Bek/B_holo < 1); black holes sit ON it
  (ratio = 1, saturated). The ratio B_Bek/B_holo = R_s/R is the object's 'closeness to collapse'.""")

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

    # real objects
    for name, r, M in OBJECTS:
        bb = 2 * math.pi * r * (M*C**2) / (HBAR * C * LN2)
        ax.plot(r, bb, "ks", ms=5)
        ax.annotate(name, (r, bb), textcoords="offset points", xytext=(5, 4), fontsize=7)

    ax.set_xscale("log"); ax.set_yscale("log")
    ax.set_xlabel("region radius  R  (m)")
    ax.set_ylabel("information capacity  B  (bits)")
    ax.set_title("The Bekenstein flow: energy bound ($R^4$) rises into the area envelope ($R^2$) at BH collapse")
    ax.set_xlim(1e-15, 1e27); ax.set_ylim(1, 1e125)
    ax.legend(loc="upper left", fontsize=8, framealpha=0.9)
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
