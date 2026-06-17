#!/usr/bin/env python3
"""
The Bekenstein bound as the λ-generator's budget — the first place the idea touches DATA.

Earlier we used the HOLOGRAPHIC budget Q_R = A/4ℓ_P² (area) ~ 10^70 bits ⇒ Born would break only at
2^(10^70) events ⇒ untestable. The BEKENSTEIN bound is different and tighter:

        I ≤ 2πRE/(ℏc·ln2)   bits        (energy × size, not area)

It limits how much information a system of size R and energy E can hold. For a minimally-localized
single quantum it is small (O(10–100) bits), and IF (a strong 'if') the λ-generator's persistent
state were confined to that bare quantum, its faking window 2^B would be tiny ⇒ testable.

CORRECTIONS (13th GPT-5.5-pro consult — the strong version was OVERCLAIMED; verified):
  • The 'electron = 9 bits / photon = 57 bits, wavelength-independent' split is a 2π CONVENTION
    artifact: I used the REDUCED Compton wavelength for the electron and the FULL wavelength for the
    photon. With one convention they coincide. A minimally-localized elementary quantum is O(10–100)
    bits DEPENDING ON the radius convention; a photon spread over many wavelengths is much larger.
  • The KEY move 'the generator state lives in the bare quantum ⇒ B ≤ 9–57 bits' is NOT a theorem of
    Bekenstein physics. Bekenstein bounds the COMPLETE physical system, not a chosen subsystem; the
    outcome depends on source+apparatus+detector+environment, so the relevant R,E are the whole
    CONTEXT. Deterministic hidden-variable theories are normally contextual/global (Bell/KS), so λ's
    state naturally lives in the apparatus/environment/causal past — where the Bekenstein budget is
    enormous (a gram-scale apparatus at R~0.1 m ⇒ ~10^39 bits ⇒ untestable).
  • Hence 'single-electron generator already EXCLUDED' is an ARTIFACT of mis-assigning the budget to
    the bare particle. It excludes only the artificial toy where one isolated ~9-bit automaton emits
    the whole stream — NOT real deterministic/contextual models.

HONEST FRAME: still the speculative generator fork (Bell cost). Bekenstein is a smaller, energy-based
budget that makes ONLY a toy source-local generator testable; real contextual models stay untestable.
The genuine takeaway is the QUESTION it sharpens: WHERE does the generator's state live? Standard lib.
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
  A MINIMALLY-LOCALIZED elementary quantum has a small Bekenstein budget — O(10–100) bits. (The
  exact number is convention-dependent: 2π/ln2≈9 with the reduced wavelength, 4π²/ln2≈57 with the
  full wavelength; the electron-9-vs-photon-57 split above is that 2π artifact, NOT a clean
  invariant. A quantum spread over many wavelengths / a larger orbit has a proportionally larger
  budget.) This small budget bounds a generator ONLY IF its whole persistent state is confined to
  that bare quantum — a strong, probably-false assumption (see Part 4).""")

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
    print("  *** TOY MODEL ONLY: assumes the generator's WHOLE persistent state is confined to the bare")
    print("  quantum source. This is probably false (real QRNGs are apparatus-scale — see Part 4). ***")
    print("  A generator whose state has Bekenstein budget B bits fakes Born only up to ~2^B outcomes.")
    print("  Quantum-RNG data tested for structure ≈ 10^15 bits (≈ 2^{:.0f}); none found.\n".format(math.log2(tested)))
    print("  {:<26}{:<14}{:<22}{}".format("source (if it held λ-state)", "B (bits)", "break at 2^B", "vs ~10^15 tested?"))
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
            verdict = "excluded — but ONLY this toy"
        elif B < math.log2(tested) + 10:
            verdict = "toy at the frontier"
        else:
            verdict = "toy safe (break ≫ tested)"
        bstr = "{:.2e}".format(break_at) if B < 1023 else "> 10^300"
        print("  {:<26}{:<14.4g}{:<22}{}".format(name, B, bstr, verdict))
    print("""
  Read this ONLY as 'the toy source-local automaton is testable': a generator that is genuinely an
  isolated ~9-bit electron-automaton would repeat within ~500 outcomes and is trivially out. But a
  real QRNG amplifies the quantum event through a macroscopic apparatus, so the relevant state is
  apparatus-scale (Part 4), NOT 9 bits. So these rows do NOT exclude real deterministic models —
  they only kill the artificial 'one tiny isolated automaton makes the whole stream' caricature.""")

# ======================================================================
#  PART 4 — honest verdict
# ======================================================================
def run_verdict():
    print("\n" + "=" * 86)
    print("PART 4 — honest verdict")
    print("=" * 86)
    print("""  HONEST VERDICT (after the 13th GPT-5.5-pro consult, which deflated the strong claim):

   • Bekenstein gives a small budget (O(10–100) bits) ONLY for an autonomous generator whose entire
     persistent state is confined to a minimally-localized elementary quantum. That toy source-local
     model IS testable, and for B ≲ 50 is already incompatible with long QRNG records.

   • But that is a strawman for real physics. Bekenstein bounds the COMPLETE system, not a chosen
     subsystem; quantum outcomes depend on source + apparatus + detector + environment, and
     deterministic hidden-variable theories are normally contextual/global (Bell/Kochen–Specker), so
     λ's state naturally lives in the apparatus/environment/causal past. A gram-scale apparatus at
     R~0.1 m has a Bekenstein budget ~10^39 bits ⇒ a faking window ~2^(10^39) ⇒ UNTESTABLE again.

   • So Bekenstein does NOT give a real 'first contact with data'. The 'electron already excluded'
     line was an ARTIFACT of mis-assigning the generator's state to the bare particle. It excludes
     only the caricature, not deterministic/contextual models.

  WHAT SURVIVES (the honest, modest gain): Bekenstein is the right, energy-based way to ASK 'how
  small could the relevant budget be?', and it sharpens the genuine open question — WHERE does the
  λ-generator's state physically live? If one could argue, physically, that it is confined to a small
  system (against the Bell/KS pressure to make it contextual), the prediction would become testable.
  Absent that argument, the budget is apparatus/causal-past-scale and the prediction stays untestable.
  This does NOT belong on the public site as a testable claim — it would overclaim.""")

def main():
    run_systems()
    run_vs_holographic()
    run_test()
    run_verdict()

if __name__ == "__main__":
    main()
