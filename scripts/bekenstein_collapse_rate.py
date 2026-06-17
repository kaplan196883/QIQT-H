#!/usr/bin/env python3
"""
Moving the power-law scaling factor to the BEKENSTEIN side: the gravitational (Diósi–Penrose) collapse
rate, and the 'working' limit that fits observed data.

The CSL factor (previous script) is phenomenological — λ_CSL and r_C are free. The natural question:
does the BEKENSTEIN / holographic side DERIVE a rate by itself, the way it derives the capacity power
laws (∝R², ∝R³)? It does — through gravity (Diósi–Penrose), and it is PARAMETER-FREE (set by G alone).

THE BEKENSTEIN-SIDE READING (an exact identity). For a spatial superposition of a mass M of size R
(separation ≳ R), the gravitational self-energy difference is E_G ~ GM²/R. Its Bekenstein information
(bound S ≤ 2πRE/ℏc) is
        ΔS_Bek = 2πR·E_G/(ℏc) = 2πGM²/(ℏc)      [dimensionless — the gravitational self-info],
and the Diósi–Penrose collapse rate is exactly that information processed at the holographic (light-
crossing) rate c/2πR:
        Γ_grav = E_G/ℏ = GM²/(ℏR) = ΔS_Bek · c/(2πR).
So the 'Bekenstein-side' collapse rate = (gravitational self-information) × (holographic processing rate).

THE POWER LAW. With fixed density (M ∝ R³), Γ_grav ∝ R⁵ — a clean power law over length scale, sitting
right next to the Bekenstein flow's R² (capacity) and R³ (realized). UNLIKE the finite-information
factor (exponential 2^(-R²) ≈ 0), this gravitational rate is non-trivial and lands in the right ballpark.

THE 'WORKING' LIMIT. The parameter-free version (mass localized at nuclei) is EXCLUDED by spontaneous
X-ray emission (Donadi et al., Nature Physics 2021); it survives only with a regularization length
R_0 ≳ 10^-10 m (atomic scale). So the working Bekenstein/gravitational limit that fits the data is
Γ_grav = GM²/(ℏR) regulated at R_0 ~ 1 Å — one residual free length. Whether QIQT-H's finite-information
Q_R derives that R_0 is the open question (not yet; but the gravitational rate at least isn't zero).

Needs numpy + matplotlib.
"""
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Patch

G    = 6.674e-11
HBAR = 1.054571817e-34
C    = 2.99792458e8
LN2  = np.log(2.0)
RHO  = 1000.0
M_NUC = 1.66e-27
PERCEPT = 0.1
AGE_UNIVERSE = 4.35e17
R0_WORKING = 1e-10           # the surviving DP regularization length (~atomic scale; Donadi 2021)

def mass(R):                 # compact object, condensed-matter density
    return (4.0/3.0)*np.pi*R**3*RHO

def gamma_grav(R):           # Diósi–Penrose / gravitational collapse rate, separation >~ R
    M = mass(R)
    return G*M*M/(HBAR*R)

def dS_bek_bits(R):          # gravitational self-information (Bekenstein bound), in bits
    M = mass(R)
    return 2*np.pi*G*M*M/(HBAR*C)/LN2

# ======================================================================
#  PART 1 — the Bekenstein-side rate, the identity, and the R^5 power law
# ======================================================================
def run_table():
    print("=" * 90)
    print("PART 1 — the Bekenstein-side (gravitational / Diósi–Penrose) collapse rate, parameter-free")
    print("  Γ_grav = GM²/(ℏR) = ΔS_Bek · c/(2πR)   (gravitational self-information × holographic rate)")
    print("  fixed density ⇒ Γ_grav ∝ R⁵.   Compare the Bekenstein flow's capacity ∝R², realized ∝R³.")
    print("=" * 90)
    print("  {:<16}{:<13}{:<22}{:<16}{}".format("object", "R (m)", "ΔS_Bek (bits, grav)", "Γ_grav (s^-1)", "τ = 1/Γ"))
    print("  " + "-" * 86)
    for lbl, R in [("atom (1 Å)", 1e-10), ("C60", 7e-10), ("100 nm cluster", 1e-7),
                   ("1 µm grain", 1e-6), ("10 µm", 1e-5), ("sand (0.5 mm)", 5e-4), ("cat (0.3 m)", 0.3)]:
        g = gamma_grav(R); tau = 1.0/g
        tdesc = (f"{tau:.1e} s (>age univ.)" if tau > AGE_UNIVERSE
                 else f"{tau:.1e} s (instant)" if tau < PERCEPT else f"{tau:.1e} s")
        print("  {:<16}{:<13.1e}{:<22.2e}{:<16.2e}{}".format(lbl, R, dS_bek_bits(R), g, tdesc))
    # micro/macro boundary
    Rb = (PERCEPT*1.11e31)  # placeholder, computed properly below
    Rgrid = np.logspace(-10, 0, 20000)
    Gg = gamma_grav(Rgrid)
    Rb = Rgrid[np.argmin(np.abs(Gg - 1.0/PERCEPT))]
    print(f"""
  The gravitational rate is a clean R⁵ power law. Its micro/macro boundary (Γ = 1/0.1 s) sits at
  R ≈ {Rb:.1e} m (~a µm grain): atoms/molecules stay coherent (Γ≈0), µm-and-larger objects become
  definite — in the right ballpark, WITHOUT any fitted parameter (set by G alone). Contrast the
  finite-information DERIVED factor, which is exponential 2^(-R²) ≈ 0 at every R.""")

# ======================================================================
#  PART 2 — the chart: the Bekenstein-side R^5 rate, the working limit, and the data
# ======================================================================
def run_chart():
    print("\n" + "=" * 90)
    print("PART 2 — chart: the Bekenstein-side collapse rate Γ_grav(R) ∝ R⁵ and the working limit")
    print("=" * 90)
    R = np.logspace(-10, 0, 700)
    Gg = gamma_grav(R)
    Gpercept = 1.0/PERCEPT
    Gnever   = 1.0/AGE_UNIVERSE

    fig, ax = plt.subplots(figsize=(10.6, 6.7))
    ax.set_xscale("log"); ax.set_yscale("log")
    ax.axhspan(1e-30, Gnever, color="#1f77b4", alpha=0.08)
    ax.axhspan(Gpercept, 1e34, color="#d62728", alpha=0.08)

    # the gravitational (Bekenstein-side) rate, R^5
    ax.plot(R, Gg, color="#8c564b", lw=3.0, zorder=6,
            label=r"Bekenstein/gravitational rate  $\Gamma_{\rm grav}=GM^2/\hbar R\propto R^{5}$ (parameter-free)")

    # CSL phenomenological for comparison (R^6 below r_C, R^3 above) at GRW value
    R_C = 1e-7; lam = 1e-16
    N_C = (4/3)*np.pi*R_C**3*RHO/M_NUC; Grc = lam*N_C**2
    Gcsl = np.where(R <= R_C, Grc*(R/R_C)**6, Grc*(R/R_C)**3)
    ax.plot(R, Gcsl, color="#2ca02c", lw=1.8, ls="--", alpha=0.8,
            label=r"CSL phenomenological ($R^6\!\to\!R^3$, free $\lambda,r_C$) — for comparison")

    # thresholds
    ax.axhline(Gpercept, color="#d62728", ls=":", lw=1.3)
    ax.text(1.3e-10, Gpercept*1.7, "above: definite within ~0.1 s", fontsize=8.2, color="#b01d1d")
    ax.axhline(Gnever, color="#1f77b4", ls=":", lw=1.3)
    ax.text(1.3e-10, Gnever*1.7, "below: coherent > age of universe", fontsize=8.2, color="#1f5fa0")

    # micro/macro boundary marker on the gravitational curve
    Rb = R[np.argmin(np.abs(Gg - Gpercept))]
    ax.scatter([Rb], [Gpercept], color="#8c564b", s=70, zorder=7, ec="white", lw=1)
    ax.annotate(f"micro/macro boundary\n≈ {Rb*1e6:.1f} µm — set by G ALONE\n(no fitted parameter)",
                xy=(Rb, Gpercept), xytext=(2e-5, 1e-6),
                fontsize=8.7, ha="left", color="#5c352b",
                arrowprops=dict(arrowstyle="->", color="#8c564b", lw=1.2))

    # object markers
    for lbl, r in [("atom", 1e-10), ("C$_{60}$", 7e-10), ("100 nm", 1e-7),
                   ("µm grain", 1e-6), ("sand", 5e-4), ("cat", 0.3)]:
        ax.scatter([r], [gamma_grav(r)], color="#444", s=24, zorder=6)
        ax.annotate(lbl, xy=(r, gamma_grav(r)), xytext=(0, 6), textcoords="offset points",
                    fontsize=7.3, ha="center", color="#333")

    # the WORKING limit / observational status box
    ax.text(1.3e-10, 5e30,
            "THE 'WORKING' BEKENSTEIN LIMIT (what fits the data):\n"
            "$\\Gamma_{\\rm grav}=GM^2/\\hbar R$  regulated at  $R_0\\gtrsim10^{-10}$ m (atomic).\n"
            "• Parameter-free (mass at nuclei) — EXCLUDED by spontaneous X-ray\n"
            "   emission (Donadi et al., Nature Phys. 2021).\n"
            "• Survives with $R_0\\sim1$ Å — ONE residual free length.\n"
            "Open Q: does finite-info $Q_R$ derive $R_0$? (not yet — but $\\Gamma\\neq0$, unlike $2^{-Q_R}$).",
            fontsize=8.0, ha="left", va="top",
            bbox=dict(boxstyle="round,pad=0.45", fc="#f3ead8", ec="#8c564b", lw=1.0))

    # finite-info contrast
    ax.annotate("finite-info DERIVED factor: exponential $2^{-R^2/\\ell_P^2}\\approx0$ (off bottom)",
                xy=(1e-4, 3e-29), xytext=(3e-9, 1e-26), fontsize=8.4, ha="left", color="black",
                arrowprops=dict(arrowstyle="-|>", color="black", lw=1.2))

    ax.set_xlabel("object size  $R$  (m)", fontsize=11)
    ax.set_ylabel("collapse rate  $\\Gamma$  (s$^{-1}$)", fontsize=11)
    ax.set_title("Moving the scaling factor to the Bekenstein side:  the gravitational rate $\\Gamma_{\\rm grav}\\propto R^5$",
                 fontsize=11.8, pad=12)
    ax.set_xlim(1e-10, 1); ax.set_ylim(1e-30, 1e34)
    handles, _ = ax.get_legend_handles_labels()
    handles += [Patch(facecolor="#1f77b4", alpha=0.2, label="quantum-coherent regime"),
                Patch(facecolor="#d62728", alpha=0.2, label="definite / classical regime")]
    ax.legend(handles=handles, fontsize=8.2, loc="lower right", framealpha=0.96)

    fig.text(0.5, 0.004,
             "Gravitational (Diósi–Penrose) rate from G alone — the Bekenstein-side analogue of the capacity power laws. "
             "Dynamical λ, breaks unitarity; a different ontology from inert-λ QIQT-H.",
             ha="center", fontsize=7.4, style="italic", color="#555")
    fig.tight_layout(rect=(0, 0.03, 1, 1))
    out = "build/bekenstein_collapse_rate.png"
    fig.savefig(out, dpi=140)
    print(f"  chart written: {out}")

# ======================================================================
#  PART 3 — verdict
# ======================================================================
def run_verdict():
    print("\n" + "=" * 90)
    print("PART 3 — verdict: the 'working' Bekenstein limit that fits QIQT-H to the data")
    print("=" * 90)
    print("""  MOVING THE POWER LAW TO THE BEKENSTEIN SIDE gives the GRAVITATIONAL (Diósi–Penrose) collapse rate
  Γ_grav = GM²/(ℏR) = ΔS_Bek·c/(2πR) ∝ R⁵ — gravitational self-information processed at the holographic
  rate. This is the Bekenstein-side analogue of the capacity power laws (R², R³), and crucially it is
  PARAMETER-FREE (set by G), and NON-ZERO — landing its micro/macro boundary at ~1 µm, the right ballpark.
  (The finite-information DERIVED factor, by contrast, is the exponential 2^(-R²) ≈ 0.)

  THE WORKING LIMIT. The fully parameter-free version is EXCLUDED by spontaneous X-ray data (Donadi 2021);
  it survives only regulated at a length R_0 ≳ 10^-10 m (atomic). So:

     working Bekenstein/gravitational limit  =  Γ_grav = GM²/(ℏR),  regulated at  R_0 ~ 1 Å.

  This IS a concrete, observationally-viable rate — but three honest flags:
   (1) It is the Diósi–Penrose GRAVITATIONAL collapse model; in this fork QIQT-H INHERITS it rather than
       predicting something new — and it makes λ dynamical, breaking Φ's exact unitarity (different ontology).
   (2) R_0 is a residual free length; it becomes a QIQT-H PREDICTION only if finite-info Q_R derives R_0 —
       which is NOT done (the open lead). Until then it is a fit, not a derivation.
   (3) Even the regulated rate is being squeezed by the same experiments; the surviving window is narrow.

  SO: the 'working' Bekenstein limit is gravitational (DP) collapse with an atomic R_0. It is the only
  place finite-size physics gives a non-zero, in-the-ballpark, testable rate — but it is borrowed DP
  phenomenology with one free length, not a finite-information prediction, and it costs exact unitarity.""")

def main():
    run_table()
    run_chart()
    run_verdict()

if __name__ == "__main__":
    main()
