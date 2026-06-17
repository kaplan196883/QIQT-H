#!/usr/bin/env python3
"""
The Schrödinger equation in limited bit space — the DYNAMICS rung.

The box and the oscillator (both Schrödinger) already appeared in the ladder, but only as STATIC
record-counting. The distinctive thing about the *equation* — the time evolution iℏ∂_tψ = Hψ — in
finite bit space is dynamical, and it has two effects the static picture missed:

  1. BOUNDED DISPERSION ⇒ an emergent MAXIMUM SPEED. A finite position grid (spacing a) turns the
     kinetic term p²/2m into a lattice Laplacian with E(k) = (2ℏ²/ma²)sin²(ka/2) — bounded above,
     so the group velocity is capped at v_max = ℏ/(ma): a 'lattice light cone' (Lieb–Robinson).
     And v_max = c EXACTLY when a = ℏ/mc = λ_C — so refining the bit-resolution raises the speed
     limit until, precisely at the Compton wavelength, it reaches c and HANDS OFF to the Dirac/KG
     rungs. The non-relativistic ladder connects to the relativistic one at the Compton grain.

  2. POINCARÉ RECURRENCE / REVIVALS. Finite bits ⇒ a discrete, bounded spectrum ⇒ the state is
     quasi-periodic: ψ(t) returns arbitrarily close to ψ(0). The recurrence time grows (doubly-)
     exponentially with the number of bits, so the continuum (infinite bits) generically never
     recurs. A genuinely small-bit world revisits its past.

HONEST FRAME (consistent with the whole ladder, pro-checked): these are real impacts of GENUINE
finiteness (a dynamical cutoff). They are large at small budget and scale away fast. QIQT-H's λ is
INERT and produces none of them; with the huge holographic Q_R the recurrence time is astronomical
and v_max ≫ any real speed ⇒ operationally = Everett. The effects are O(1) only for a tiny-Q_eff
toy or at a saturated horizon. Real dynamics, but not λ. Units: ℏ=1 unless SI shown. Needs numpy.
"""
import numpy as np

HBAR = 1.054571817e-34
C    = 2.99792458e8
ME   = 9.1093837015e-31
LAMBDA_C = HBAR/(ME*C)

# ======================================================================
#  PART 1 — bounded dispersion ⇒ a maximum speed, hitting c at λ_C
# ======================================================================
def run_dispersion():
    print("=" * 78)
    print("PART 1 — finite grid ⇒ bounded kinetic energy ⇒ an emergent MAXIMUM SPEED v_max=ℏ/ma")
    print("  E(k) = (2ℏ²/ma²) sin²(ka/2)  (lattice Laplacian) replaces ℏ²k²/2m; group velocity")
    print("  caps at v_max = ℏ/(ma).  v_max = c  ⟺  a = ℏ/mc = λ_C  ⇒ handoff to Dirac/KG.")
    print("=" * 78)
    L = 1e-9  # a 1 nm region
    print("  electron in L = 1 nm;  λ_C = {:.3e} m".format(LAMBDA_C))
    print("  B bits   a=L/2^B (m)     v_max=ℏ/ma (m/s)   v_max/c       note")
    print("  " + "-" * 70)
    for B in [4, 8, 12, 16, 20, 28]:
        a = L / 2**B
        vmax = HBAR / (ME * a)
        r = vmax / C
        if r < 0.1:
            note = "non-relativistic — Schrödinger fine"
        elif r < 1:
            note = "approaching c — Schrödinger straining"
        else:
            note = "v_max ≥ c ⇒ Schrödinger INVALID, go to Dirac/KG"
        print("  {:<8}{:<16.3e}{:<19.3e}{:<14.3e}{}".format(B, a, vmax, r, note))
    a_star = LAMBDA_C
    B_star = np.log2(L / a_star)
    print("\n  v_max = c exactly at a = λ_C = {:.2e} m  (B = log2(L/λ_C) = {:.1f} bits for this L)."
          .format(a_star, B_star))
    print("""
  So in limited bit space the Schrödinger equation acquires a finite signal speed — wavepackets
  cannot spread faster than v_max = ℏ/(ma) (a Lieb–Robinson bound on the lattice). Refining the
  resolution raises v_max, and it reaches the true light speed c PRECISELY at the Compton grid
  a = λ_C — exactly where the single-particle picture fails and the relativistic rungs (Dirac,
  Klein–Gordon) take over. The bit-limited non-relativistic ladder dovetails into the relativistic
  one at the Compton wavelength. (This is kinematics of the lattice, standard — not λ.)""")

# ======================================================================
#  PART 2 — Poincaré recurrence / revivals (the dynamical finiteness signature)
# ======================================================================
def return_amplitude(energies, probs, ts):
    """A(t) = Σ_n p_n e^{-i E_n t};  return probability is |A|²  (O(T) memory)."""
    A = np.zeros(ts.shape, complex)
    for E, p in zip(energies, probs):
        A += p * np.exp(-1j * E * ts)
    return np.abs(A) ** 2

def run_recurrence():
    print("\n" + "=" * 78)
    print("PART 2 — finite bits ⇒ POINCARÉ RECURRENCE: ψ(t) returns to ψ(0)")
    print("=" * 78)
    rng = np.random.default_rng(0)

    # (a) generic (incommensurate) spectrum: recurrence time grows with the number of bits.
    # Exclude the trivial t=0 peak: wait for the state to first decay (<0.5), then time the
    # first genuine return (>0.9).
    print("  (a) GENERIC spectrum (energies in [0,1], equal weights): first GENUINE recurrence")
    print("      (after the state has decayed) to |⟨ψ(0)|ψ(t)⟩|² > 0.9 — median over 9 random")
    print("      spectra, scanned to T=2e5.  Climbs steeply with the bit count.")
    print("      B bits   N=2^B    fraction recurring     median t_rec")
    print("      " + "-" * 58)
    ts = np.linspace(0, 2e5, 2_000_000)           # dt = 0.1
    NSEED = 9
    for B in [2, 3, 4, 5]:
        N = 2**B
        p = np.full(N, 1.0/N)
        trecs = []
        for _ in range(NSEED):
            E = np.sort(rng.random(N))
            ret = return_amplitude(E, p, ts)
            below = np.where(ret < 0.5)[0]
            if below.size:
                i0 = below[0]
                after = np.where(ret[i0:] > 0.9)[0]
                if after.size:
                    trecs.append(ts[i0 + after[0]])
        frac = "{}/{}".format(len(trecs), NSEED)
        med = "{:.3e}".format(np.median(trecs)) if trecs else "> 2e5 (window)"
        print("      {:<8}{:<8}{:<22}{}".format(B, N, frac, med))

    # (b) commensurate spectrum (the box, E_n ∝ n²): EXACT revival regardless of N.
    print("\n  (b) BOX spectrum E_n ∝ n² (commensurate): EXACT revival at t = 2π, any N")
    ts2 = np.linspace(0, 2*np.pi, 4001)
    for B in [2, 4, 6]:
        N = 2**B
        E = (np.arange(1, N+1).astype(float))**2          # n², units where revival at 2π
        p = np.full(N, 1.0/N)
        ret = return_amplitude(E, p, ts2)
        interior_min = ret[1:-1].min()                    # dips away from t=0
        print("      B={} (N={:>2}):  return prob at t=2π = {:.4f} ;  min on (0,2π) = {:.4f}  (genuine revival)"
              .format(B, N, ret[-1], interior_min))
    print("""
  Two regimes. GENERIC systems do not recur in the continuum, but ANY finite truncation does — and
  the recurrence time climbs steeply with the bit count (already unreachable by a handful of bits),
  so the continuum limit is recurrence-free. COMMENSURATE systems (the box E_n∝n², the oscillator
  E_n∝n) revive exactly even with few levels — the clean 'finite bits ⇒ the wavefunction comes
  back' picture. Either way, a genuinely small-bit world is quasi-periodic: no true irreversibility,
  guaranteed revivals. The more bits, the longer the wait — vanishing in the continuum.""")

# ======================================================================
#  PART 3 — two more dynamical consequences (brief)
# ======================================================================
def run_extras():
    print("\n" + "=" * 78)
    print("PART 3 — two more finite-bit dynamical consequences")
    print("=" * 78)
    print("""  • DEFORMED KINETIC TERM. The Schrödinger H = p²/2m + V needs [x,p]=iℏ, which a finite
    Hilbert space cannot represent (Tr[x,p]=0≠iℏN). So the kinetic operator is FORCED to be a
    bounded lattice Laplacian — which is exactly the bounded dispersion of Part 1. The emergent
    speed limit is the dynamical face of the deformed Heisenberg algebra.

  • ENERGY ALIASING (if TIME is also bit-limited). Evolving in finite steps Δt (a time-bit
    budget) makes phases e^{-iEΔt} periodic in E: energies above the Nyquist value π/Δt FOLD
    back (alias). So a finite time-resolution imposes a MAXIMUM representable energy — the
    time-domain dual of the position cutoff. Together: bounded x-grid ⇒ bounded momentum;
    bounded t-grid ⇒ bounded energy. A fully bit-limited Schrödinger world is a finite torus in
    phase space and in time.""")

# ======================================================================
#  PART 4 — honest verdict
# ======================================================================
def run_verdict():
    print("\n" + "=" * 78)
    print("PART 4 — honest verdict")
    print("=" * 78)
    L = 1.0
    print("  recurrence-time and speed-limit scaling (electron, region L):")
    print("    • v_max = ℏ/(ma): for L=1 m and the holographic-scale grid it is astronomically")
    print("      large; it only drops to c at a = λ_C (the relativistic handoff), never below.")
    print("    • t_rec grows ~ exponentially in the bit count, so for any macroscopic budget it")
    print("      exceeds the age of the universe by enormous margins.")
    print("""
  VERDICT (consistent with box/oscillator/Dirac/KG, pro-checked):
  • The Schrödinger EQUATION in limited bit space gains two real dynamical features: an emergent
    maximum speed v_max=ℏ/ma (a lattice light cone that hits c exactly at the Compton grain λ_C,
    dovetailing into the Dirac/KG rungs) and Poincaré recurrence/revivals (a discrete bounded
    spectrum makes ψ(t) return). Both are genuine and computable.
  • Both are STANDARD physics of finite/lattice quantum systems — Lieb–Robinson bounds, quantum
    revivals — not λ. Their size is set by the budget: v_max ≫ c and t_rec ≫ age-of-universe for
    any real system, so nothing is observable. They are O(1) only for a tiny-Q_eff toy or at a
    saturated horizon.
  • λ is non-dynamical and Born-transparent ⇒ it produces neither effect. With inert λ + the huge
    holographic Q_R the dynamics is exactly ordinary Schrödinger evolution ⇒ operationally Everett.
    Real lattice dynamics, but not λ — thesis-empty, like the rest of the ladder. The added value
    here is the CONNECTION: the bit-limited Schrödinger speed limit meets c at λ_C, stitching the
    non-relativistic and relativistic rungs into one ladder.""")

def main():
    run_dispersion()
    run_recurrence()
    run_extras()
    run_verdict()

if __name__ == "__main__":
    main()
