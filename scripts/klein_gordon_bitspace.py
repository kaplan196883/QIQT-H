#!/usr/bin/env python3
"""
The Klein–Gordon equation in limited bit space — the MINIMAL relativistic rung.

Ladder so far:
  Box (Schrödinger): position records, NO floor — H_B grows without limit.
  Oscillator:        phase-space records, an ℏ-floor (the 2πℏ cell).
  Dirac:             position floor λ_C=ℏ/mc (mass-set) + a 2-qubit internal (spin⊗sign) record.
  Klein–Gordon (here): NO spin, and a genuinely different obstruction.

What is DIFFERENT about KG (and worth the honesty):
  • The conserved KG density ρ = (ℏ/2mc²)·i(φ*∂_tφ − φ∂_tφ*) is INDEFINITE — it equals
    (E/mc²)|φ|² per mode, so a negative-energy mode carries NEGATIVE density. Hence |φ|² is
    NOT a record law: single-particle KG has no clean position-record reading at all. (Dirac's
    j⁰=ψ†ψ≥0 is positive; KG's is not — this is why KG was abandoned as a 1-particle equation.)
  • Stripping spin, the only internal structure is the charge/SIGN (particle/antiparticle), a
    single qubit via the Feshbach–Villars 2-component form — and ZERO for a neutral real scalar.
    The simplest relativistic record there is.
  • The resolution is the FIELD: KG = a tower of independent oscillators (one per mode,
    ω_k = c√(k²+(mc/ℏ)²)); the well-defined records are the Fock OCCUPATION numbers, and each
    mode is exactly the oscillator rung. So KG ties the relativistic ladder back to the oscillator.

HONEST FRAME (consistent with box/oscillator/Dirac, GPT-5.5-pro-checked): every line is standard
relativistic QM / free scalar QFT in (Φ,λ) language. The Compton floor is particle creation
(mass-set), not λ and not holography (budget ~70 orders slack); the indefinite density and the
Fock turn are textbook; λ is inert ⇒ operationally Everett. The KG rung is the MINIMAL case and
exposes a real obstruction, but like the others it is THESIS-EMPTY — no λ-specific effect anywhere.

Units: ℏ=c=m=1 (so mc²=1, λ_C=1, energies in units of mc²) unless SI constants are shown. Needs numpy.
"""
import numpy as np

# ---- SI constants (a charged scalar of electron mass, for the dimensional numbers) ----
HBAR = 1.054571817e-34
C    = 2.99792458e8
M    = 9.1093837015e-31          # take m = electron mass for concrete numbers
G    = 6.674e-11
LP2  = HBAR * G / C**3
LN2  = np.log(2)
LAMBDA_C = HBAR / (M * C)        # reduced Compton wavelength
MC2  = M * C**2

def entropy_bits(weights):
    w = np.asarray(weights, float)
    w = w[w > 1e-15]
    if w.size == 0:
        return 0.0
    w = w / w.sum()
    return max(0.0, float(-np.sum(w * np.log2(w))))

# ======================================================================
#  PART 1 — the INDEFINITE density:  |φ|² is NOT a record law
# ======================================================================
def run_indefinite_density():
    print("=" * 78)
    print("PART 1 — the conserved KG density is INDEFINITE:  |φ|² is NOT a record law")
    print("  ρ = (ℏ/2mc²) i(φ*∂_tφ − φ∂_tφ*).  Per mode of energy E:  ρ = (E/mc²)|φ|².")
    print("  ⇒ a NEGATIVE-energy mode carries NEGATIVE 'probability'. (Dirac's ψ†ψ≥0 does not.)")
    print("=" * 78)
    # units ℏ=c=m=1. Superpose a +E mode (k1) and a -E mode (k2): show ρ(x) goes negative.
    k1, k2 = 0.6, 1.3
    E1, E2 = np.sqrt(k1**2 + 1), np.sqrt(k2**2 + 1)     # in units of mc²
    a, b = 1.0, 0.8                                     # amplitudes (+E and -E)
    x = np.linspace(0, 4*np.pi, 4000)
    # φ(x,0) and ∂_tφ(x,0):  +E mode ~ e^{i(k1 x - E1 t)},  -E mode ~ e^{i(k2 x + E2 t)}
    phi = a*np.exp(1j*k1*x) + b*np.exp(1j*k2*x)
    dphi_dt = a*(-1j*E1)*np.exp(1j*k1*x) + b*(1j*E2)*np.exp(1j*k2*x)
    rho = -np.imag(np.conj(phi) * dphi_dt)             # = (ℏ/mc²)·... with ℏ=mc²=1
    print("  mode energies (units mc²):  +E1 = {:.3f}   -E2 = {:.3f}".format(E1, -E2))
    print("  ρ(x) over the sample:  min = {:+.3f}   max = {:+.3f}   (mean {:+.3f})"
          .format(rho.min(), rho.max(), rho.mean()))
    frac_neg = float(np.mean(rho < 0))
    print("  fraction of space with ρ < 0:  {:.1%}".format(frac_neg))
    print("""
  ρ goes negative over a finite fraction of space — so it cannot be normalised to a record
  law. The single-particle KG 'position record' is ILL-DEFINED: there is no positive density
  to read |φ|² as 'which cell is actual'. This is the genuine KG obstruction (absent in Dirac).
  The fix is not a better single-particle reading — it is the field (Part 4).""")

# ======================================================================
#  PART 2 — Feshbach–Villars: the MINIMAL internal record (≤1 sign-qubit)
# ======================================================================
def fv_components(E):
    """Feshbach–Villars particle/antiparticle amplitudes for a mode of energy E (units mc²):
       η = ½(1 + E/mc²),  χ = ½(1 − E/mc²)  (up to the common φ). E in units of mc²."""
    eta = 0.5 * (1 + E)
    chi = 0.5 * (1 - E)
    return eta, chi

def run_feshbach_villars():
    print("\n" + "=" * 78)
    print("PART 2 — Feshbach–Villars: the MINIMAL internal record (charge/sign, ≤ 1 qubit)")
    print("  No spin: the only internal structure is particle vs antiparticle (η, χ).")
    print("  record law = (|η|², |χ|²) normalised;  H ≤ 1 bit  (Dirac had ≤ 2; neutral scalar: 0).")
    print("=" * 78)
    print("  {:<26}{:<10}{}".format("state Φ (mode energy)", "H (bits)", "record (|η|², |χ|²)"))
    print("  " + "-" * 64)
    for pbar, lbl in [(0.0, "rest        p=0"), (0.1, "slow        p=0.1mc"),
                      (1.0, "fast        p=mc"), (5.0, "ultra       p=5mc")]:
        E = np.sqrt(1 + pbar**2)
        eta, chi = fv_components(E)
        w = np.array([eta**2, chi**2]); w = w / w.sum()
        print("  {:<26}{:<10.3f}({:.3f}, {:.3f})".format(lbl, entropy_bits(w), w[0], w[1]))
    print("""
  A rest scalar is a definite record (pure particle, 0 bits). Boosting mixes in the
  antiparticle component, but H stays ≤ 1 bit — half the Dirac internal record (no spin
  qubit). For a NEUTRAL real scalar even the charge qubit is absent: 0 internal bits, the
  minimal record in the whole ladder.""")

# ======================================================================
#  PART 3 — the COMPTON floor (same mass-set grain as Dirac)
# ======================================================================
def run_compton_floor():
    print("\n" + "=" * 78)
    print("PART 3 — the COMPTON floor λ_C = ℏ/mc  (same mass-set grain as Dirac)")
    print("=" * 78)
    L = 1e-2
    print("  λ_C = {:.3e} m ;  region L = 1 cm ⇒ position-bit ceiling log2(L/λ_C) = {:.2f} bits"
          .format(LAMBDA_C, np.log2(L/LAMBDA_C)))
    print("  Localising below λ_C costs ΔE > 2mc² ⇒ particle creation ⇒ the single-quantum record")
    print("  dissolves — identical to Dirac. H_pos = min(B, log2(L/λ_C)). The floor is the mass,")
    print("  not the spin: KG (spin 0) and Dirac (spin ½) share the SAME Compton position grain.")

# ======================================================================
#  PART 4 — the field turn: KG = a tower of oscillators (Fock records)
# ======================================================================
def run_field_turn():
    print("\n" + "=" * 78)
    print("PART 4 — the resolution: KG = a TOWER OF OSCILLATORS; records = Fock occupations")
    print("  ω_k = c√(k² + (mc/ℏ)²).  Each mode is an oscillator; the well-defined records are")
    print("  the occupation numbers n_k — and each mode is exactly the OSCILLATOR rung.")
    print("=" * 78)
    kc = M*C/HBAR                                      # 1/λ_C, the mass scale in k
    print("  lowest mode  ω_0 = mc²/ℏ = {:.3e} rad/s  (the rest-mass / Compton frequency)"
          .format(MC2/HBAR))
    print("  mode k (units mc/ℏ)   ω_k/ω_0 = √(1+(k/kc)²)")
    print("  " + "-" * 46)
    for kr in [0.0, 0.5, 1.0, 2.0, 5.0]:
        print("  {:<22}{:.3f}".format(kr, np.sqrt(1 + kr**2)))
    print("""
  The free KG field is a product of independent oscillators, one per mode; the vacuum is the
  product of their ground states and a 'particle' is one quantum of excitation. So the genuine
  record structure is occupation numbers {n_k}, and the per-mode bit content is the oscillator's
  phase-space floor (the 2πℏ cell) — KG adds no new floor beyond mass (Part 3) and oscillator.
  This is also where the indefinite density of Part 1 is cured: positive Fock norms replace the
  indefinite single-particle ρ.""")

# ======================================================================
#  PART 5 — holographic slack + the honest verdict
# ======================================================================
def run_verdict():
    print("\n" + "=" * 78)
    print("PART 5 — holographic slack and the honest verdict")
    print("=" * 78)
    for L, lbl in [(1e-2, "1 cm"), (1.0, "1 m")]:
        QR = (4*np.pi*L**2) / (4*LP2) / LN2
        demand = np.log2(L/LAMBDA_C) + 1               # position grain + ≤1 sign bit
        slack = np.log10(QR) - np.log10(demand)
        print("  region {:<5}  Q_R ≈ {:.2e} bits   single-quantum record ≈ {:.0f} bits   slack ≈ {:.0f} orders"
              .format(lbl, QR, demand, slack))
    print("""
  VERDICT (consistent with box/oscillator/Dirac, pro-checked):
  • KG is the MINIMAL relativistic rung — no spin, the smallest internal record (≤1 sign-qubit;
    0 for a neutral scalar) — and the one that EXPOSES a real obstruction: its conserved density
    is indefinite, so single-particle position records are ill-defined. The honest fix is the
    field: KG = a tower of oscillators, records = Fock occupations (back to the oscillator rung).
  • Yet every effect is STANDARD relativistic QM / free scalar QFT: the position floor is the
    mass-set Compton grain (particle creation), shared with Dirac; the indefinite density and
    Fock turn are textbook; the holographic budget is ~70 orders slack. None of it is λ.
  • λ non-dynamical and Born-transparent ⇒ no resolution cap, no deviation. The obstruction and
    its field cure are there with or without λ. So, like the whole ladder: thesis-empty,
    operationally = Everett. The minimal rung teaches the most physics and adds the least λ.""")

def main():
    run_indefinite_density()
    run_feshbach_villars()
    run_compton_floor()
    run_field_turn()
    run_verdict()

if __name__ == "__main__":
    main()
