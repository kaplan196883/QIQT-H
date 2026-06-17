#!/usr/bin/env python3
"""
Compute "the scaling factor" — the two readings, side by side, against experiment.

The idea "maybe λ's effect is just a scaling factor we add" splits into two cases (see the previous
analysis). This script COMPUTES both, concretely:

  CASE A — scaling factor DERIVED from finite information (Q_R).
    If amplitudes are physically resolved to ~Q_R bits, the smallest physical amplitude is ε ~ 2^(-Q_R),
    so Born probabilities can deviate by at most ~ε. Q_R = A/4ℓ_P² is astronomically large even for a
    lab, so ε is ~10^(-10^70): a real scaling factor, but its VALUE is pinned by physics to be
    unobservably small. Not a free knob. (This is the same off-chart verdict, now as a number.)

  CASE B — scaling factor ADDED as a free dynamical rate = a COLLAPSE MODEL (GRW / CSL).
    Standard QM + a single-nucleon collapse rate λ_CSL, AMPLIFIED by system size: the collapse rate of a
    spatial superposition of N nucleons (rigid, separation > r_C) is Γ ≈ λ_CSL · N². That N² is the
    scaling factor that makes micro-superpositions survive and macro ones collapse. It IS testable — and
    is being actively constrained. But it makes λ DYNAMICAL and breaks Φ's exact unitarity: a different
    ontology from inert-λ QIQT-H, and the parameter is bounded by experiment, not derived from Q_R.

Output: the computed numbers (Parts 1–2) and a chart Γ(N) (Part 3) showing the CSL benchmark lines, the
"stay quantum" / "be definite" thresholds, the experimental status, and where the finite-information
derived rate sits (off the bottom). Needs numpy + matplotlib.
"""
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Patch

HBAR = 1.054571817e-34
C    = 2.99792458e8
G    = 6.674e-11
LP   = 1.616255e-35           # Planck length (m)
LP2  = LP*LP
LN2  = np.log(2.0)
AGE_UNIVERSE = 4.35e17        # s
PERCEPT = 0.1                 # s  (a "definite macroscopic outcome" timescale)

# ======================================================================
#  CASE A — the scaling factor DERIVED from finite information
# ======================================================================
def run_caseA():
    print("=" * 86)
    print("CASE A — scaling factor DERIVED from finite information:  ε ~ 2^(-Q_R),  Q_R = A/4ℓ_P²")
    print("=" * 86)
    print("  {:<22}{:<16}{:<20}{}".format("region", "radius R (m)", "Q_R (bits)", "ε = 2^(-Q_R)  (amplitude floor)"))
    print("  " + "-" * 82)
    for R, lbl in [(1e-9, "atom-scale (1 nm)"), (1.0, "lab (1 m)"),
                   (6.4e6, "Earth"), (8.8e26, "observable universe")]:
        A = 4*np.pi*R*R
        QR_nats = A/(4*LP2)
        QR_bits = QR_nats/LN2
        log10_eps = -QR_bits*np.log10(2.0)      # log10(ε)
        print("  {:<22}{:<16.2e}{:<20.2e}{}".format(lbl, R, QR_bits, f"10^({log10_eps:.1e})"))
    print("""
  The derived scaling factor exists but is pinned to ~10^(-5x10^69) already at 1 metre — it can never
  reach a real amplitude. So 'finite-information' as a scaling factor gives EXACTLY zero observable
  effect on any accessible scale: this is the off-chart verdict, now as a computed number. = Everett.""")

# ======================================================================
#  CASE B — the scaling factor ADDED: CSL collapse rate Γ ≈ λ_CSL · N²
# ======================================================================
LAMBDA_GRW   = 1e-16          # s^-1, original GRW/CSL single-nucleon rate
LAMBDA_ADLER = 1e-8           # s^-1, Adler's enhanced value (perception-scale)

def gamma(N, lam):            # rigid-body CSL amplification (separation > r_C)
    return lam * N**2

def run_caseB():
    print("\n" + "=" * 86)
    print("CASE B — scaling factor ADDED (collapse model):  Γ ≈ λ_CSL · N²   (N = nucleons in the superposition)")
    print("  Benchmarks: GRW λ=1e-16 s^-1 ; Adler (enhanced) λ=1e-8 s^-1.  Collapse time τ = 1/Γ.")
    print("=" * 86)
    print("  {:<26}{:<14}{:<20}{}".format("system", "N (nucleons)", "Γ_GRW (s^-1)", "τ_GRW = 1/Γ"))
    print("  " + "-" * 80)
    systems = [("single nucleon", 1), ("fullerene C60", 720), ("interferometry macromol.", 1e6),
               ("large virus", 1e10), ("dust grain (~ng)", 1e15), ("housefly (~10 mg)", 6e21),
               ("cat (~1 kg)", 6e26)]
    for lbl, N in systems:
        g = gamma(N, LAMBDA_GRW)
        tau = 1.0/g
        if tau > AGE_UNIVERSE:
            tdesc = f"{tau:.1e} s  (> age of universe — never)"
        elif tau > PERCEPT:
            tdesc = f"{tau:.1e} s"
        else:
            tdesc = f"{tau:.1e} s  (instant — definite)"
        print("  {:<26}{:<14}{:<20}{}".format(lbl, f"{N:.0e}".replace('e+0','e'), f"{g:.1e}", tdesc))
    # the macro-definite boundary at the GRW value
    N_def = np.sqrt(1.0/(PERCEPT*LAMBDA_GRW))          # Γ = 1/percept = 10 s^-1
    tau_nucleon = 1.0/gamma(1, LAMBDA_GRW)
    print(f"""
  At the GRW scaling factor a single nucleon localizes only once per ~{tau_nucleon:.0e} s (~{tau_nucleon/3.15e7:.0e} yr)
  — negligible for any experiment, so micro-superpositions stay coherent in practice; but objects with
  N > ~{N_def:.0e} nucleons collapse within ~0.1 s (a definite outcome). The N² amplification IS the
  scaling factor that bridges the two regimes — ~17 orders of N from micro-survival to macro-collapse.""")
    return systems

# ======================================================================
#  CASE B chart — Γ(N) with thresholds, benchmarks, bounds, and the finite-info rate off the bottom
# ======================================================================
def run_chart(systems):
    print("\n" + "=" * 86)
    print("CHART — the scaling factor in action:  collapse rate Γ vs system size N")
    print("=" * 86)
    N = np.logspace(0, 27, 600)
    G_grw = gamma(N, LAMBDA_GRW)
    G_adl = gamma(N, LAMBDA_ADLER)
    Gamma_never   = 1.0/AGE_UNIVERSE     # below: never collapses in cosmic time
    Gamma_percept = 1.0/PERCEPT          # above: definite within perception

    fig, ax = plt.subplots(figsize=(10.6, 6.7))
    ax.set_xscale("log"); ax.set_yscale("log")

    # regime shading
    ax.axhspan(1e-45, Gamma_never, color="#1f77b4", alpha=0.08)     # quantum-coherent
    ax.axhspan(Gamma_percept, 1e45, color="#d62728", alpha=0.08)    # definite/classical

    # CSL benchmark lines
    ax.plot(N, G_grw, color="#2ca02c", lw=2.6, label="CSL collapse rate  $\\Gamma=\\lambda_{\\rm CSL}N^2$  (GRW: $\\lambda=10^{-16}$)")
    ax.plot(N, G_adl, color="#9467bd", lw=2.0, ls="--", label="CSL with Adler's enhanced $\\lambda=10^{-8}$  (now EXCLUDED by exp.)")

    # threshold lines
    ax.axhline(Gamma_never, color="#1f77b4", ls=":", lw=1.4)
    ax.axhline(Gamma_percept, color="#d62728", ls=":", lw=1.4)
    ax.text(1.4, Gamma_never*1.5, "below: stays quantum-coherent for the age of the universe",
            fontsize=8.2, color="#1f5fa0")
    ax.text(1.4, Gamma_percept*1.6, "above: collapses to a definite outcome within ~0.1 s",
            fontsize=8.2, color="#b01d1d")

    # a few system markers on the GRW line
    for lbl, n in [("nucleon", 1), ("C60", 720), ("virus", 1e10), ("dust", 1e15), ("cat", 6e26)]:
        ax.scatter([n], [gamma(n, LAMBDA_GRW)], color="#2ca02c", s=34, zorder=6, ec="white", lw=0.6)
        ax.annotate(lbl, xy=(n, gamma(n, LAMBDA_GRW)), xytext=(0, 6),
                    textcoords="offset points", fontsize=7.6, ha="center", color="#2c7a2c")

    # the finite-information DERIVED rate: off the bottom
    ax.annotate("finite-information DERIVED scaling factor:\n"
                "$\\varepsilon\\sim2^{-Q_R}\\sim10^{-5\\times10^{69}}$  ⇒  $\\Gamma\\approx0$\n"
                "→ NO collapse at any N  =  Everett (inert λ)",
                xy=(1e13, 1e-40), xytext=(2e2, 1e-37),
                fontsize=9, ha="left", color="black", fontweight="bold",
                arrowprops=dict(arrowstyle="-|>", color="black", lw=1.4))
    ax.annotate("", xy=(1e13, 3e-44), xytext=(1e13, 1e-40),
                arrowprops=dict(arrowstyle="->", color="black", lw=1.2))

    # experimental-status box
    ax.text(1.3e1, 3e30,
            "Experimental status of the ADDED factor $\\lambda_{\\rm CSL}$:\n"
            "• Adler's $10^{-8}$ value — EXCLUDED (X-ray emission, Donadi 2021;\n"
            "   mechanical resonators; matter-wave interferometry).\n"
            "• GRW $10^{-16}$ — still allowed, being squeezed from above.\n"
            "The factor is BOUNDED BY EXPERIMENT, not derived from $Q_R$.",
            fontsize=8.0, ha="left", va="top",
            bbox=dict(boxstyle="round,pad=0.45", fc="#fff6cc", ec="#caa700", lw=1.0))

    ax.set_xlabel("system size  $N$  (nucleons in the spatial superposition)", fontsize=11)
    ax.set_ylabel("collapse rate  $\\Gamma$  (s$^{-1}$)", fontsize=11)
    ax.set_title("Computing 'the scaling factor': CSL amplification $\\Gamma=\\lambda_{\\rm CSL}N^2$ vs the finite-information rate",
                 fontsize=11.8, pad=12)
    ax.set_xlim(1, 1e27); ax.set_ylim(1e-44, 1e44)
    handles, labels = ax.get_legend_handles_labels()
    handles += [Patch(facecolor="#1f77b4", alpha=0.2, label="quantum-coherent regime"),
                Patch(facecolor="#d62728", alpha=0.2, label="definite / classical regime")]
    ax.legend(handles=handles, fontsize=8.3, loc="lower right", framealpha=0.96)

    fig.text(0.5, 0.004,
             "Case A (derived from finite info): Γ≈0, = Everett.   Case B (added by hand): a CSL collapse model — "
             "testable, but dynamical λ, breaks unitarity, already constrained.",
             ha="center", fontsize=7.8, style="italic", color="#555")
    fig.tight_layout(rect=(0, 0.03, 1, 1))
    out = "build/collapse_scaling_factor.png"
    fig.savefig(out, dpi=140)
    print(f"  chart written: {out}")

# ======================================================================
#  VERDICT
# ======================================================================
def run_verdict():
    print("\n" + "=" * 86)
    print("VERDICT — what 'the scaling factor' actually is")
    print("=" * 86)
    print("""  Computed, both readings:

   • DERIVED from finite information: ε ~ 2^(-Q_R) ~ 10^(-5x10^69) already at 1 metre ⇒ Γ ≈ 0, no
     collapse at any size. The scaling factor is REAL but its value is PINNED by Q_R to be unobservable.
     This is the inert-λ thesis: = Everett. No free knob, no prediction.

   • ADDED by hand (a collapse model): Γ = λ_CSL·N². The N² amplification IS exactly 'the scaling
     factor' that makes micro-superpositions survive and macro ones collapse — and it WORKS as physics
     (it is the GRW/CSL mechanism). But: (i) λ_CSL is a FREE parameter, not derived from Q_R; (ii) it
     makes λ DYNAMICAL and breaks Φ's exact unitarity (a different ontology); (iii) it is already
     BOUNDED BY EXPERIMENT — Adler's 10^-8 is excluded, the GRW 10^-16 window is shrinking.

  SO: you can compute a scaling factor that gives predictive power — but only the ADDED CSL one does,
  and it is no longer QIQT-H's inert λ; it is a dynamical collapse theory with an experimentally
  constrained parameter. The factor finite information actually DERIVES is ~10^(-10^70): a rigorous zero.
  There is no scaling factor that is both derived-from-finiteness AND large enough to see.""")

def main():
    run_caseA()
    systems = run_caseB()
    run_chart(systems)
    run_verdict()

if __name__ == "__main__":
    main()
