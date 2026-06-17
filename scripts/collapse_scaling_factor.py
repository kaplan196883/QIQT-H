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
#  CHART (R) — the scaling factor as a power law over LENGTH SCALE, with the r_C crossover
# ======================================================================
RHO = 1000.0                  # kg/m^3 (condensed-matter density)
M_NUC = 1.66e-27              # kg
R_C = 1e-7                    # m, CSL correlation length

def run_chart_R():
    print("\n" + "=" * 86)
    print("CHART (R) — the scaling factor as a POWER LAW over length scale R, with the r_C crossover")
    print("  R < r_C : object is one coherent patch  ⇒  Γ ∝ N² ∝ R^6   (steep)")
    print("  R > r_C : many incoherent patches        ⇒  Γ ∝ N  ∝ R^3   (mass-proportional, gentler)")
    print("=" * 86)
    N_C = (4.0/3.0)*np.pi*R_C**3*RHO/M_NUC          # nucleons in one correlation volume
    G_rc = LAMBDA_GRW*N_C**2                          # rate at R = r_C (continuous match point)
    print(f"  density ρ={RHO:.0f} kg/m³, r_C={R_C:.0e} m, λ_CSL={LAMBDA_GRW:.0e} s^-1  ⇒  N_C≈{N_C:.1e} nucleons, Γ(r_C)≈{G_rc:.1e} s^-1")

    def gamma_R(R):
        R = np.asarray(R, float)
        return np.where(R <= R_C, G_rc*(R/R_C)**6, G_rc*(R/R_C)**3)

    R = np.logspace(-10, 0, 700)                      # 1 Å .. 1 m
    G = gamma_R(R)
    Gamma_never   = 1.0/AGE_UNIVERSE
    Gamma_percept = 1.0/PERCEPT

    fig, ax = plt.subplots(figsize=(10.6, 6.7))
    ax.set_xscale("log"); ax.set_yscale("log")

    # regime shading by collapse outcome
    ax.axhspan(1e-30, Gamma_never, color="#1f77b4", alpha=0.08)
    ax.axhspan(Gamma_percept, 1e34, color="#d62728", alpha=0.08)

    # the two-slope power law, coloured by regime
    lo = R <= R_C; hi = R >= R_C
    ax.plot(R[lo], G[lo], color="#1f77b4", lw=2.8, zorder=5, label=r"$\Gamma\propto R^{6}$  ($R<r_C$: coherent, $N^2$)")
    ax.plot(R[hi], G[hi], color="#2ca02c", lw=2.8, zorder=5, label=r"$\Gamma\propto R^{3}$  ($R>r_C$: mass-proportional, $N$)")

    # the r_C crossover
    ax.axvline(R_C, color="#caa700", ls="--", lw=1.5)
    ax.scatter([R_C], [G_rc], color="#caa700", s=70, zorder=7, ec="white", lw=1)
    ax.annotate("correlation length  $r_C\\approx10^{-7}$ m\n— the SLOPE CHANGES here (6 → 3):\nthe scaling factor is NOT scale-free",
                xy=(R_C, G_rc), xytext=(3e-7, 1e-9),
                fontsize=8.8, ha="left", color="#8a7400",
                arrowprops=dict(arrowstyle="->", color="#caa700", lw=1.2))

    # slope guide-triangles annotations
    ax.text(2e-9, gamma_R(2e-9)*15, "slope 6", fontsize=8.5, color="#1f5fa0", rotation=0)
    ax.text(3e-3, gamma_R(3e-3)/40, "slope 3", fontsize=8.5, color="#2c7a2c", rotation=0)

    # threshold lines
    ax.axhline(Gamma_percept, color="#d62728", ls=":", lw=1.3)
    ax.text(1.3e-10, Gamma_percept*1.7, "above: definite outcome within ~0.1 s", fontsize=8.2, color="#b01d1d")
    ax.axhline(Gamma_never, color="#1f77b4", ls=":", lw=1.3)
    ax.text(1.3e-10, Gamma_never*1.7, "below: coherent longer than the age of the universe", fontsize=8.2, color="#1f5fa0")

    # object size markers
    for lbl, r in [("atom\n(1 Å)", 1e-10), ("C$_{60}$", 7e-10), ("virus", 1e-7),
                   ("µm dust", 1e-6), ("sand grain", 5e-4), ("cat (~0.3 m)", 0.3)]:
        gr = float(gamma_R(r))
        ax.scatter([r], [gr], color="#444", s=26, zorder=6)
        ax.annotate(lbl, xy=(r, gr), xytext=(0, 7), textcoords="offset points",
                    fontsize=7.4, ha="center", color="#333")

    # finite-information derived factor: exponential, NOT a power law — off the bottom
    ax.annotate("finite-information DERIVED factor is EXPONENTIAL, not a power law:\n"
                "$\\varepsilon\\sim2^{-Q_R}\\sim2^{-R^2/\\ell_P^2}$  →  $\\Gamma\\approx0$ at every $R$  (off the bottom)",
                xy=(1e-3, 3e-29), xytext=(2e-9, 1e-26),
                fontsize=8.6, ha="left", color="black", fontweight="bold",
                arrowprops=dict(arrowstyle="-|>", color="black", lw=1.3))

    ax.set_xlabel("object size  $R$  (m)", fontsize=11)
    ax.set_ylabel("collapse rate  $\\Gamma$  (s$^{-1}$)", fontsize=11)
    ax.set_title("The scaling factor as a power law over length scale:  CSL  $\\Gamma(R)$  with the $r_C$ crossover",
                 fontsize=11.8, pad=12)
    ax.set_xlim(1e-10, 1); ax.set_ylim(1e-30, 1e34)
    handles, _ = ax.get_legend_handles_labels()
    handles += [Patch(facecolor="#1f77b4", alpha=0.2, label="quantum-coherent regime"),
                Patch(facecolor="#d62728", alpha=0.2, label="definite / classical regime")]
    ax.legend(handles=handles, fontsize=8.4, loc="lower right", framealpha=0.96)

    fig.text(0.5, 0.004,
             "CSL center-of-mass rate, condensed-matter density, superposition separation > r_C. The power law (R^6→R^3) is the "
             "ADDED collapse factor; finite-info DERIVES an exponential (≈0), not this.",
             ha="center", fontsize=7.4, style="italic", color="#555")
    fig.tight_layout(rect=(0, 0.03, 1, 1))
    out = "build/collapse_scaling_factor_vs_R.png"
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
    run_chart_R()
    run_verdict()

if __name__ == "__main__":
    main()
