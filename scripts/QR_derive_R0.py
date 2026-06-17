#!/usr/bin/env python3
"""
Does the holographic budget Q_R derive the working Diósi–Penrose regularization length R_0 ~ 1 Å?

The working Bekenstein/gravitational collapse rate Γ_grav = GM²/ℏR survives the data only when the mass
density is smeared over a length R_0 ≳ 10^-10 m ~ 1 Å (Donadi et al., Nature Physics 2021, exclude the
nuclear-scale value). For this to become a QIQT-H PREDICTION rather than a fitted knob, finite
information (Q_R) would have to DERIVE R_0 ~ 1 Å. This script tests that directly: it computes every
candidate length the finite-information / holographic side can produce, and every candidate the rest of
physics offers, and asks which one lands at ~1 Å.

Q_R = A/4ℓ_P² is DIMENSIONLESS (a bit count); the only lengths it natively contains are ℓ_P (its own
quantum) and R (the region size). So any intrinsic length it yields is Planck-scale — or, via
information-resolution, exponentially small. The atomic scale 1 Å, by contrast, is the Bohr radius
a_0 = λ_C(e)/α — set by the electron mass and the fine-structure constant (electromagnetism), not by
holography. The computation makes the ~25-order mismatch explicit. Needs numpy + matplotlib.
"""
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HBAR  = 1.054571817e-34
C     = 2.99792458e8
G     = 6.674e-11
ME    = 9.1093837e-31
MP    = 1.67262192e-27
ALPHA = 7.2973525693e-3            # fine-structure constant (~1/137)
LP    = np.sqrt(HBAR*G/C**3)       # Planck length
A0    = 5.29177210903e-11          # Bohr radius (CODATA)

R0_TARGET_LO = 0.5e-10             # Donadi 2021 lower bound on R_0 (~0.5 Å)
R0_TARGET_HI = 3e-10               # generous upper edge of the "atomic" band

# ======================================================================
#  candidate lengths
# ======================================================================
def candidates():
    lam_e = HBAR/(ME*C)            # reduced Compton wavelength, electron
    lam_p = HBAR/(MP*C)            # reduced Compton wavelength, nucleon
    holo_res = LP/np.sqrt(np.pi)   # holographic boundary resolution R/sqrt(Q_R) = ℓ_P/√π (R-independent)
    a0_from = lam_e/ALPHA          # Bohr radius rebuilt as λ_C(e)/α  (check: = a_0)
    return [
        # (label, length, category)  category: 'holo' finite-info/holographic, 'compton', 'atomic', 'target'
        ("Planck length ℓ_P  (Q_R's own quantum)",            LP,        "holo"),
        ("holographic resolution  R/√Q_R = ℓ_P/√π",           holo_res,  "holo"),
        ("info-position resolution  R·2^(−Q_R)",              1e-300,    "holo"),   # underflow ⇒ effectively 0
        ("nucleon Compton  ℏ/m_p c  (naive DP R_0 — EXCLUDED)", lam_p,   "compton"),
        ("electron Compton  ℏ/m_e c",                         lam_e,     "compton"),
        ("Bohr radius  a_0 = λ_C(e)/α  (atomic/EM)",          a0_from,   "atomic"),
        ("working R_0  (Donadi-allowed, ~1 Å)",               1e-10,     "target"),
    ]

def run_table():
    print("=" * 92)
    print("Candidate lengths vs the working R_0 ~ 1 Å = 1e-10 m")
    print("=" * 92)
    print("  {:<48}{:<16}{}".format("candidate", "length (m)", "ratio to 1 Å"))
    print("  " + "-" * 86)
    for lbl, L, cat in candidates():
        ratio = L/1e-10
        rtxt = ("≈ 0 (underflow)" if L < 1e-200 else
                f"{ratio:.1e}  ({'MATCH' if 0.3 < ratio < 3 else 'off by '+f'{abs(np.log10(ratio)):.0f} orders'})")
        print("  {:<48}{:<16.3e}{}".format(lbl, L, rtxt))
    print(f"""
  Bohr radius check:  a_0 = λ_C(e)/α = {HBAR/(ME*C)/ALPHA:.3e} m  vs CODATA {A0:.3e} m  ✓
  The ONLY candidate at ~1 Å is the Bohr radius — and it is built from m_e and α (electromagnetism),
  NOT from Q_R. Every finite-information / holographic length is Planck-scale (ℓ_P ~ {LP:.1e} m, ~25
  orders too small) or exponentially small (info-position resolution ~ 0).""")

# ======================================================================
#  chart — a length number line
# ======================================================================
def run_chart():
    cand = candidates()
    colors = {"holo": "#d62728", "compton": "#ff7f0e", "atomic": "#2ca02c", "target": "#1f77b4"}
    fig, ax = plt.subplots(figsize=(11.0, 5.3))
    ax.set_xscale("log")

    # target band ~1 Å
    ax.axvspan(R0_TARGET_LO, R0_TARGET_HI, color="#1f77b4", alpha=0.13)
    ax.text(np.sqrt(R0_TARGET_LO*R0_TARGET_HI), 1.07, "working $R_0\\sim1$ Å\n(Donadi 2021)",
            ha="center", va="bottom", fontsize=8.6, color="#1f4e9c")

    ys = [0.62, 0.36, 0.14, 0.66, 0.40, 0.18, 0.85]   # staggered label heights
    for (lbl, L, cat), y in zip(cand, ys):
        Lp = max(L, 1e-37)                              # clamp the underflow one to the axis edge for drawing
        ax.scatter([Lp], [0], s=80, color=colors[cat], zorder=6, ec="white", lw=1)
        ax.plot([Lp, Lp], [0, y], color=colors[cat], lw=1.0, alpha=0.6, zorder=3)
        ax.annotate(("→ 0  " if L < 1e-200 else "") + lbl, xy=(Lp, y), xytext=(0, 2),
                    textcoords="offset points", fontsize=8.0, ha="center", color=colors[cat])

    # the 25-order gap annotation
    ax.annotate("", xy=(LP, -0.18), xytext=(1e-10, -0.18),
                arrowprops=dict(arrowstyle="<->", color="#555", lw=1.3))
    ax.text(np.sqrt(LP*1e-10), -0.30, "~25 orders of magnitude — the holographic length is nowhere near 1 Å",
            ha="center", fontsize=8.4, color="#555")

    ax.set_yticks([]); ax.set_ylim(-0.42, 1.18)
    ax.set_xlim(1e-37, 1e-8)
    ax.set_xlabel("length scale (m)", fontsize=11)
    ax.set_title("Does $Q_R$ derive $R_0\\sim1$ Å?  —  candidate lengths on a number line",
                 fontsize=12.5, pad=10)
    # legend
    from matplotlib.lines import Line2D
    leg = [Line2D([], [], marker='o', color='w', markerfacecolor=colors[c], markersize=9, label=l)
           for c, l in [("holo", "finite-info / holographic  (→ Planck or 0)"),
                        ("compton", "particle Compton wavelengths"),
                        ("atomic", "atomic / EM  (Bohr radius) ← the match"),
                        ("target", "working $R_0$ target (~1 Å)")]]
    ax.legend(handles=leg, fontsize=8.4, loc="lower right", framealpha=0.96)
    fig.tight_layout()
    out = "build/QR_derive_R0.png"
    fig.savefig(out, dpi=140)
    print(f"\n  chart written: {out}")

# ======================================================================
#  verdict
# ======================================================================
def run_verdict():
    print("\n" + "=" * 92)
    print("VERDICT — does Q_R derive R_0 ~ 1 Å?")
    print("=" * 92)
    print(f"""  NO.  The working regularization length R_0 ~ 1 Å is the ATOMIC scale — the Bohr radius
  a_0 = λ_C(e)/α ≈ {A0:.2e} m — set by the electron mass and the fine-structure constant
  (electromagnetism). It is the length over which real matter's mass density is actually smeared
  (nuclei held in atomic-scale electron clouds). It has NOTHING to do with the holographic budget.

  Every finite-information / holographic length misses by ~25 orders:
   • ℓ_P (Q_R's own quantum) ≈ {LP:.1e} m  — 25 orders too small;
   • holographic boundary resolution R/√Q_R = ℓ_P/√π — also Planck-scale (R-independent);
   • information-position resolution R·2^(−Q_R) — exponentially small, ≈ 0  (the exponential again).
  Q_R is dimensionless; the only lengths it natively carries are ℓ_P and R, so it cannot manufacture an
  intrinsic 1 Å without injecting m_e and α — i.e. without ADMITTING the scale is atomic/EM, not holographic.

  CONSEQUENCE FOR THE PROGRAM. In the gravitational-collapse fork, R_0 is fixed by ATOMIC PHYSICS, not by
  finite information. So the working Bekenstein/gravitational rate is exactly Diósi–Penrose with an
  atomic R_0 — inherited, already-constrained collapse phenomenology — and finite information contributes
  NOTHING to its one free length. The hoped-for QIQT-H prediction does not materialise here: Q_R does not
  pick out R_0. This is the null the prior anticipated, now demonstrated rather than asserted.

  (The honest residue: 'R_0 = atomic scale' is itself well-motivated physics — matter IS atomic — so the
  regulated DP rate stands on its own as a testable collapse model. It is just not a finite-information
  result, and adopting it still costs Φ's exact unitarity. The inert-λ thesis remains = Everett.)""")

def main():
    run_table()
    run_chart()
    run_verdict()

if __name__ == "__main__":
    main()
