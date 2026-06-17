#!/usr/bin/env python3
"""
The Bekenstein bound as the λ-generator's budget — the first place the idea touches DATA.

Earlier we used the HOLOGRAPHIC budget Q_R = A/4ℓ_P² (area) ~ 10^70 bits ⇒ Born would break only at
2^(10^70) events ⇒ untestable. The BEKENSTEIN bound is different and tighter:

        I ≤ 2πRE/(ℏc·ln2)   bits        (energy × size, not area)

It limits how much information a system of size R and energy E can hold. Crucially, for a SINGLE
QUANTUM it is TINY — and the λ-generator's state capacity (hence its faking window 2^B, the data
size before its pseudo-randomness repeats / becomes compressible) is bounded by the Bekenstein bound
of whatever physical system encodes that state. So if the generator's hidden state lives in the
quantum SOURCE itself (an electron, a photon), B is only ~10–60 bits ⇒ Born would break after only
~2^B outcomes ⇒ TESTABLE, and for the smallest sources ALREADY EXCLUDED by quantum-RNG data.

Clean facts (derived below): an electron at its Compton scale ⇒ 2π/ln2 ≈ 9 bits; a single photon ⇒
4π²/ln2 ≈ 57 bits, INDEPENDENT of wavelength (R·E = ℏc is fixed). These are the smallest budgets.

HONEST FRAME: this is still the speculative deterministic/superdeterministic GENERATOR fork (not the
inert-λ thesis), and it inherits the Bell cost. But Bekenstein is what turns its prediction from
'untestable (2^10^70)' into 'already in tension for single-quantum sources' — the first contact with
data in the whole thread. Needs only the standard library.
"""
import math

HBAR = 1.054571817e-34
C    = 2.99792458e8
G    = 6.674e-11
ME   = 9.1093837015e-31
H    = 2 * math.pi * HBAR
LN2  = math.log(2)
LP2  = HBAR * G / C**3
EV   = 1.602176634e-19
LAMBDA_C = HBAR / (ME * C)

def bekenstein_bits(R, E):
    """I ≤ 2πRE/(ℏc ln2) bits."""
    return 2 * math.pi * R * E / (HBAR * C * LN2)

def holographic_bits(R):
    """Q_R = A/(4 ℓ_P² ln2) = π R²/(ℓ_P² ln2) bits (sphere of radius R)."""
    return math.pi * R * R / (LP2 * LN2)

# ======================================================================
#  PART 1 — the Bekenstein budget is TINY for single quanta
# ======================================================================
def run_systems():
    print("=" * 86)
    print("PART 1 — Bekenstein budget I = 2πRE/(ℏc·ln2) for real systems (energy × size)")
    print("=" * 86)
    print("  {:<26}{:<13}{:<13}{:<19}{}".format("system", "R (m)", "E (J)", "Bekenstein (bits)", "note"))
    print("  " + "-" * 84)
    systems = [
        ("electron @ Compton λ_C", LAMBDA_C, ME*C**2, "= 2π/ln2 ≈ 9"),
        ("single optical photon",  500e-9,   H*C/500e-9, "= 4π²/ln2 ≈ 57"),
        ("single radio photon 1m", 1.0,      H*C/1.0,  "same 57 (R·E=ℏc fixed)"),
        ("electron in an atom",    5.29e-11, ME*C**2,  "rest energy, atomic size"),
        ("Na atom (rest energy)",  1.9e-10,  23*1.66e-27*C**2, ""),
        ("1 µm trapped-ion qubit", 1e-6,     2.0*EV,   "optical transition energy"),
        ("dust grain (1 µg)",      1e-5,     1e-9*C**2, ""),
    ]
    for name, R, E, note in systems:
        print("  {:<26}{:<13.2e}{:<13.2e}{:<15.3e}{}".format(name, R, E, bekenstein_bits(R, E), note))
    print("""
  Single elementary quanta carry an astonishingly SMALL Bekenstein budget: ~9 bits (electron),
  ~57 bits (any single photon — wavelength-independent, since R·E = ℏc is fixed). Energy×size, not
  area, makes it tiny. THIS is the budget that would limit a generator whose hidden state lives in
  the quantum source.""")

# ======================================================================
#  PART 2 — Bekenstein ≪ holographic for everything but black holes
# ======================================================================
def run_vs_holographic():
    print("\n" + "=" * 86)
    print("PART 2 — Bekenstein (energy) vs Holographic (area): Bekenstein is far tighter")
    print("=" * 86)
    print("  {:<22}{:<18}{:<18}{}".format("system (size, energy)", "Bekenstein (bits)", "Holographic (bits)", "ratio Bek/Holo"))
    print("  " + "-" * 80)
    rows = [
        ("photon, R=λ=500nm", 500e-9, H*C/500e-9),
        ("electron, R=λ_C",   LAMBDA_C, ME*C**2),
        ("atom, R=a0",        5.29e-11, ME*C**2),
        ("1 cm cube, ~1 J",   1e-2, 1.0),
        ("solar-mass BH",     2*G*1.989e30/C**2, 1.989e30*C**2),
    ]
    for name, R, E in rows:
        bek, hol = bekenstein_bits(R, E), holographic_bits(R)
        print("  {:<22}{:<18.3e}{:<18.3e}{:.2e}".format(name, bek, hol, bek/hol))
    print("""
  For ordinary matter the Bekenstein (energy) budget is many orders BELOW the holographic (area)
  budget; they coincide only at a black hole, where E = Mc² and R = R_s make 2πRE/ℏc = A/4ℓ_P²
  (the bound is saturated). So Bekenstein is the operative, much smaller budget for a finite-energy
  generator — and it is what could make the prediction observable.""")

# ======================================================================
#  PART 3 — the break data-size 2^B vs what quantum RNGs have produced
# ======================================================================
def run_test():
    print("\n" + "=" * 86)
    print("PART 3 — the finite-generator prediction meets data: Born breaks at ~2^B")
    print("=" * 86)
    # rough scales of generated/tested quantum-random bits
    tested = 1e15     # bits tested for structure (terabytes-scale analyses), order of magnitude
    print("  A generator whose state has Bekenstein budget B bits fakes Born only up to ~2^B outcomes.")
    print("  Quantum-RNG data tested for structure ≈ 10^15 bits (≈ 2^{:.0f}); none found.\n".format(math.log2(tested)))
    print("  {:<26}{:<14}{:<22}{}".format("source (if it holds λ-state)", "B (bits)", "break at 2^B", "vs ~10^15 tested?"))
    print("  " + "-" * 84)
    cases = [
        ("single electron",     bekenstein_bits(LAMBDA_C, ME*C**2)),
        ("single photon",       bekenstein_bits(500e-9, H*C/500e-9)),
        ("1 µm ion qubit",      bekenstein_bits(1e-6, 2.0*EV)),
        ("electron in atom",    bekenstein_bits(5.29e-11, ME*C**2)),
        ("dust grain (1 µg)",   bekenstein_bits(1e-5, 1e-9*C**2)),
    ]
    for name, B in cases:
        break_at = 2.0**min(B, 1023)   # cap to avoid overflow in display
        if B < math.log2(tested):
            verdict = "ALREADY EXCLUDED (break ≪ tested)"
        elif B < math.log2(tested) + 10:
            verdict = "AT THE FRONTIER (break ≈ tested)"
        else:
            verdict = "safe (break ≫ tested)"
        bstr = "{:.2e}".format(break_at) if B < 1023 else "> 10^300"
        print("  {:<26}{:<14.4g}{:<22}{}".format(name, B, bstr, verdict))
    print("""
  The punchline: the bare single-ELECTRON budget (~9 bits ⇒ break at ~500 outcomes) is WILDLY
  excluded — electron-based randomness has produced far more than 2^9 bits with no structure. The
  single-PHOTON budget (~57 bits ⇒ break at ~10^17) sits right at the frontier of what has been
  tested. So a finite generator whose hidden state lives in the bare quantum SOURCE is already
  disfavoured (electron) or about to be tested (photon).""")

# ======================================================================
#  PART 4 — honest verdict
# ======================================================================
def run_verdict():
    print("\n" + "=" * 86)
    print("PART 4 — honest verdict")
    print("=" * 86)
    print("""  Bekenstein is the first thing in this whole thread to make the finite-λ-generator idea TOUCH
  DATA. Where the holographic budget gave an untestable 2^(10^70), the Bekenstein (energy×size)
  budget of a single quantum is only ~9–57 bits, so:

   • If the generator's hidden state lives in the quantum SOURCE itself, its faking window is just
     ~2^9 … 2^57 outcomes. The electron case (~500) is ALREADY EXCLUDED by quantum-RNG data; the
     photon case (~10^17) is at the current experimental frontier. So this version is testable —
     and the smallest budgets are already ruled out.

   • That forces a fork. EITHER the λ-generator's state is NOT the bare quantum but a much larger
     system (the apparatus, the environment, the causal diamond) whose Bekenstein/holographic budget
     is large again ⇒ back to untestable, but with a clear physical question ('what holds the
     state?'). OR one takes the small-source budget seriously, in which case single-quantum
     randomness ALREADY disfavours a Bekenstein-limited finite generator — i.e. the data favours
     true Born / inert-λ over a finite generator for those degrees of freedom.

   • Either way this is genuine progress: a concrete, energy-based, system-specific budget; a real
     (already partly excluded) prediction; and a sharp open question — WHERE does the generator's
     state live, and therefore what is its energy and Bekenstein budget?

  CAVEATS (unchanged): still the speculative deterministic/superdeterministic GENERATOR fork (owes
  Bell its price); 'how much has been tested for structure' is an order-of-magnitude estimate; and
  the choice of E for a system (transition energy vs total rest energy) shifts B and is part of the
  open question above.""")

def main():
    run_systems()
    run_vs_holographic()
    run_test()
    run_verdict()

if __name__ == "__main__":
    main()
