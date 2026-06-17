#!/usr/bin/env python3
"""
The Dirac equation in limited bit space — the relativistic rung of the λ bit-limit ladder.

  Box (Schrödinger):  position records have NO floor — H_B grows with the budget without limit.
  Oscillator:         phase-space records have an ℏ-floor (the 2πℏ Husimi cell).
  Dirac (this file):  position records have a PHYSICAL floor set by the MASS — the (reduced)
                      Compton wavelength λ_C = ℏ/mc. Localise a single particle below it and
                      Δp > mc ⇒ ΔE > mc² ⇒ pair production: the single-particle position RECORD
                      dissolves. And the 4-spinor is a clean 2-qubit internal (spin ⊗ sign)
                      record — the qubit ladder realised in a real relativistic equation.

So Dirac is the richest rung: it finally gives a position-space bit floor (box had none), and
it ties the continuous floor to the discrete 2-qubit ladder.

HONEST FRAME (consistent with the box/oscillator verdict — see scripts/lambda_continuous.py and
the 7th GPT-5.5-pro consult): every line here is standard Dirac theory / relativistic QFT in
(Φ,λ) language. The Compton floor is PAIR PRODUCTION (mass-set), NOT λ and NOT holography; the
internal record entropy is ordinary single-basis spinor bookkeeping; the holographic budget Q_R
stays ~70 orders slack for any laboratory region. λ is inert ⇒ operationally Everett. Like the
box and the oscillator, the Dirac case is pedagogically rich but THESIS-EMPTY: there is no
λ-specific effect anywhere — only standard relativistic QM with a mass-set resolution floor.

Units: bit counts are dimensionless; lengths/energies use SI constants (electron). Needs numpy.
"""
import numpy as np

# ---- physical constants (SI, electron) ----
HBAR = 1.054571817e-34
C    = 2.99792458e8
ME   = 9.1093837015e-31
G    = 6.674e-11
LP2  = HBAR * G / C**3                 # Planck length squared
LN2  = np.log(2)
LAMBDA_C = HBAR / (ME * C)             # reduced Compton wavelength λ_C = ℏ/mc ≈ 3.86e-13 m
MC2  = ME * C**2                       # rest energy mc² ≈ 8.19e-14 J ≈ 0.511 MeV
EV   = 1.602176634e-19

def entropy_bits(weights):
    w = np.asarray(weights, dtype=float)
    w = w[w > 1e-15]
    if w.size == 0:
        return 0.0
    w = w / w.sum()
    return max(0.0, float(-np.sum(w * np.log2(w))))   # clamp -0.0 → 0.0

# ======================================================================
#  PART 1 — the 4-spinor as a 2-qubit INTERNAL record (spin ⊗ sign)
# ======================================================================
sx = np.array([[0, 1], [1, 0]], complex)
sy = np.array([[0, -1j], [1j, 0]], complex)
sz = np.array([[1, 0], [0, -1]], complex)

def u_spinor(pbar, s):
    """Positive-energy plane-wave spinor u(p,s); pbar = p/(mc) (3-vector); s=0 (↑) or 1 (↓)."""
    pbar = np.asarray(pbar, float)
    E = np.sqrt(1.0 + pbar @ pbar)                 # E/mc²
    chi = np.array([1, 0], complex) if s == 0 else np.array([0, 1], complex)
    sigma_p = pbar[0]*sx + pbar[1]*sy + pbar[2]*sz
    lower = (sigma_p @ chi) / (E + 1.0)            # small-component coupling σ·p/(E+1)
    psi = np.concatenate([chi, lower])
    return psi / np.sqrt(np.abs(psi.conj() @ psi))

def v_spinor(pbar, s):
    """Negative-energy plane-wave spinor v(p,s) (the antiparticle / lower-sign partner)."""
    pbar = np.asarray(pbar, float)
    E = np.sqrt(1.0 + pbar @ pbar)
    chi = np.array([1, 0], complex) if s == 0 else np.array([0, 1], complex)
    sigma_p = pbar[0]*sx + pbar[1]*sy + pbar[2]*sz
    upper = (sigma_p @ chi) / (E + 1.0)
    psi = np.concatenate([upper, chi])
    return psi / np.sqrt(np.abs(psi.conj() @ psi))

def record_law(psi):
    """Single (computational) basis record law: |component|² over the 4 spinor slots
       {↑upper, ↓upper, ↑lower, ↓lower} = {spin}⊗{sign}. Normalised (u,v at the same p
       are non-orthogonal, so a raw u+v superposition needs renormalising)."""
    w = np.abs(psi) ** 2
    return w / w.sum()

def run_spinor():
    print("=" * 78)
    print("PART 1 — the Dirac 4-spinor as a 2-qubit INTERNAL record (spin ⊗ sign)")
    print("  basis = {↑upper, ↓upper, ↑lower, ↓lower};  record law = |component|²;  H ≤ 2 bits")
    print("=" * 78)
    rt = 1/np.sqrt(2)
    states = [
        ("rest electron  u(0,↑)",        u_spinor([0, 0, 0], 0)),
        ("slow  e⁻  u(0.1ẑ,↑)",          u_spinor([0, 0, 0.1], 0)),
        ("fast  e⁻  u(1.0ẑ,↑)  (p=mc)",  u_spinor([0, 0, 1.0], 0)),
        ("ultra e⁻  u(5.0ẑ,↑)",          u_spinor([0, 0, 5.0], 0)),
        ("spin x-superpos (↑+↓)/√2",     rt*(u_spinor([0,0,0],0) + u_spinor([0,0,0],1))),
        ("zitterbewegung (u+v)/√2 @p=ẑ", rt*(u_spinor([0,0,1.0],0) + v_spinor([0,0,1.0],0))),
    ]
    print("  {:<32}{:<10}{}".format("state Φ", "H (bits)", "record law |ψ_i|²  (↑u,↓u,↑l,↓l)"))
    print("  " + "-" * 74)
    for name, psi in states:
        law = record_law(psi)
        H = entropy_bits(law)
        print("  {:<32}{:<10.3f}({})".format(name, H,
              ", ".join("{:.3f}".format(x) for x in law)))
    print("""
  Reading: a rest electron is a DEFINITE internal record (0 bits — pure ↑upper). Boosting
  populates the lower components (σ·p/(E+1)) → the spin and sign records mix, but H stays ≤ 2
  bits: the internal record space is finite and exactly 2 qubits, no matter the momentum. The
  ±energy (u+v) superposition spreads across upper+lower — this interference is zitterbewegung
  (Part 3). All exact, all single-basis — the 2-qubit rung of the ladder in a real equation.""")

# ======================================================================
#  PART 2 — POSITION records: the Compton floor (box had none)
# ======================================================================
def run_position_floor():
    print("\n" + "=" * 78)
    print("PART 2 — POSITION records and the COMPTON FLOOR  λ_C = ℏ/mc")
    print("  Box: H_pos ≈ B grows forever. Dirac: localising below λ_C makes pairs ⇒ the single-")
    print("  particle position record SATURATES at resolution Δx_min ≈ λ_C. Floor set by MASS.")
    print("=" * 78)
    print("  λ_C(e⁻) = {:.3e} m   (the position-record grain)".format(LAMBDA_C))
    L = 1e-2  # a 1 cm region
    print("  region L = {:.0e} m → max distinguishable position records = L/λ_C = {:.3e}"
          .format(L, L/LAMBDA_C))
    print("  → position-bit CEILING  log2(L/λ_C) = {:.2f} bits  (finite — unlike the box)\n"
          .format(np.log2(L/LAMBDA_C)))
    print("  budget B   Δx=L/2^B (m)   Δx/λ_C       behaviour")
    print("  " + "-" * 66)
    Bceil = np.log2(L/LAMBDA_C)
    for B in [10, 20, 30, 34, 35, 40, 45]:
        dx = L / 2**B
        ratio = dx / LAMBDA_C
        if ratio > 3:
            tag = "Schrödinger-like: record tracks the budget"
        elif ratio > 1:
            tag = "approaching the Compton grain"
        else:
            tag = "SUB-λ_C: pairs created ⇒ record dissolves (capped)"
        Heff = min(B, Bceil)
        print("  {:<11}{:<15.3e}{:<13.3e}{}".format(B, dx, ratio, tag))
    print("""
  So H_pos(Dirac) = min(B, log2(L/λ_C)): it tracks the budget like the box until Δx hits λ_C,
  then SATURATES — exactly the role the 2πℏ cell played for the oscillator, now in POSITION and
  fixed by the mass. The grain is pair production, i.e. standard relativistic QFT, not λ.""")

# ======================================================================
#  PART 3 — ZITTERBEWEGUNG: the internal Compton clock (time-domain bits)
# ======================================================================
def run_zitterbewegung():
    print("\n" + "=" * 78)
    print("PART 3 — ZITTERBEWEGUNG: the internal Compton clock (time-domain record bits)")
    print("=" * 78)
    omega_zb = 2 * MC2 / HBAR              # ω_zb = 2mc²/ℏ (±energy interference frequency)
    T_zb = 2 * np.pi / omega_zb
    print("  ω_zb = 2mc²/ℏ = {:.3e} rad/s ;  period T_zb = {:.3e} s ;  amplitude ≈ λ_C/2 = {:.3e} m"
          .format(omega_zb, T_zb, LAMBDA_C/2))
    print("  The (u+v) interference (Part 1) oscillates ⟨x⟩ at ω_zb — an internal 'clock'.")
    print("\n  proper time τ      # cycles ω_zb·τ/2π     clock bits log2(#)")
    print("  " + "-" * 60)
    for tau, lbl in [(1e-21, "~T_zb"), (1e-18, "1 as"), (1e-15, "1 fs"),
                     (1e-12, "1 ps"), (1e-9, "1 ns")]:
        cycles = omega_zb * tau / (2*np.pi)
        bits = np.log2(cycles) if cycles > 1 else 0.0
        print("  {:<19}{:<22.3e}{:.2f}".format(lbl, cycles, bits))
    print("""
  The Compton clock is a real, fast (1.6e21 rad/s) internal oscillation; its resolvable phase
  is a time-domain record count log2(ω_zb·τ/2π). It is standard Dirac interference between ±E
  components — never observed as free-particle motion (it averages out; only the mass-set scale
  λ_C survives). No λ here either: it is the time-domain face of the same Compton grain.""")

# ======================================================================
#  PART 4 — energy cost of localisation: the pair-production line
# ======================================================================
def run_pair_line():
    print("\n" + "=" * 78)
    print("PART 4 — energy cost of localising a Dirac particle: the pair-production line")
    print("  E(Δx) ≈ √[(ℏc/Δx)² + (mc²)²].  Δx = λ_C ⇒ E = √2·mc².  E > 2mc² ⇒ a pair is cheaper.")
    print("=" * 78)
    print("  Δx/λ_C      E/mc²        verdict")
    print("  " + "-" * 50)
    for ratio in [100, 10, 3, 1.0, 0.5, 0.2, 0.1]:
        dx = ratio * LAMBDA_C
        E = np.sqrt((HBAR*C/dx)**2 + MC2**2) / MC2
        if E < 2:
            v = "single particle OK"
        else:
            v = "ΔE > 2mc² ⇒ PAIR PRODUCTION (record dissolves)"
        print("  {:<12}{:<13.3f}{}".format(ratio, E, v))
    print("""
  Below Δx ≈ λ_C the localisation energy exceeds the 2mc² pair threshold: you can no longer
  hold one electron at a sharper position — the vacuum makes e⁺e⁻ pairs and the single-particle
  position record loses meaning. THIS is the physical mechanism behind the Part-2 floor.""")

# ======================================================================
#  PART 5 — holographic slack + the honest verdict
# ======================================================================
def run_verdict():
    print("\n" + "=" * 78)
    print("PART 5 — holographic slack and the honest verdict")
    print("=" * 78)
    for L, lbl in [(1e-2, "1 cm"), (1.0, "1 m")]:
        A = 4*np.pi*L**2
        QR = A / (4*LP2) / LN2                       # holographic budget (bits)
        pos_bits = np.log2(L/LAMBDA_C)
        demand = pos_bits + 2                        # position grain + 2 internal spinor bits
        slack = np.log10(QR) - np.log10(demand if demand>0 else 1)
        print("  region {:<5}  Q_R ≈ {:.2e} bits   single-e⁻ record ≈ {:.0f} bits   slack ≈ {:.0f} orders"
              .format(lbl, QR, demand, slack))
    print("""
  VERDICT (consistent with box/oscillator, GPT-5.5-pro-checked):
  • The Dirac equation gives, for the FIRST time in this ladder, a PHYSICAL position-space bit
    floor — the Compton wavelength λ_C = ℏ/mc — completing box (no floor) → oscillator
    (phase-space ℏ-floor) → Dirac (position floor, mass-set). Plus a clean 2-qubit internal
    (spin ⊗ sign) record. Richest rung pedagogically.
  • But every effect is STANDARD relativistic QM/QFT: the floor is pair production (set by the
    mass m, via ΔE > 2mc²), NOT λ and NOT the holographic Q_R; the internal bits are ordinary
    single-basis spinor bookkeeping; zitterbewegung is ±E interference. The holographic budget
    is ~70 orders slack for any lab region, so finiteness never bites.
  • λ is non-dynamical and Born-transparent ⇒ it produces no resolution cap, no deviation.
    The Compton floor would be there with or without λ. So, exactly as before: thesis-empty,
    operationally = Everett. The mass-set grain is real physics; the λ part adds nothing.""")

def main():
    run_spinor()
    run_position_floor()
    run_zitterbewegung()
    run_pair_line()
    run_verdict()

if __name__ == "__main__":
    main()
