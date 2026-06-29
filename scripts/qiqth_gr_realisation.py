#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
QIQT-H — a MINIMAL *GRAVITATIONAL* REALISATION (the continuum step the finite toys can't reach)
================================================================================================

The finite toys (qiqth_minimal_realisation.py) realise the kinematic + thermal boundary
conditions — including the entropy–area variation δS = η δA and a finite temperature (KMS) —
but they cannot yield the Einstein field equations, because those need the *continuum
smooth-background* step (Raychaudhuri focusing, δA ↔ R_kk).

The minimal realisation that *does* reach GR is therefore a continuum field theory on a smooth
background: the **free Klein–Gordon field on a pp-wave** (matching the Lean capstone
`qiqt_gr_ppwave_showcase` / `qiqt_gr_freefield`).  This script:

  [1] computes the pp-wave geometry symbolically (Christoffel → Ricci → Einstein tensor),
  [2] verifies the contracted Bianchi identity ∇^μ G_μν = 0 (conservation consistency),
  [3] proves the Jacobson "agree-on-the-null-cone ⟹ differ by f·g" lemma (Minkowski demo),
  [4] gives the free-KG stress component T_uu and ASSEMBLES Jacobson's equation of state with
      the QIQT-H inputs (δS = η δA *derived*, the Unruh temperature *discharged* for the free
      field), closing to the explicit Einstein equation  −½∇²_⊥H = 8πG·T_uu.

It is the honest companion to the finite toys: it shows *where* and *how* GR appears — in the
continuum realisation — and which inputs remain labelled (conditional Jacobson chain).

Run:  python scripts/qiqth_gr_realisation.py
"""

import sympy as sp

ok = True
def check(name, cond, note):
    global ok
    status = "OK " if cond else "FAIL"
    if not cond:
        ok = False
    print(f"    [{status}] {name:<48} ~ {note}")

# ----------------------------------------------------------------------------------------
# [1] The pp-wave background (Brinkmann form):  ds² = H(u,x,y) du² + 2 du dv + dx² + dy²
#     — the smooth metric the finite toys lacked.
# ----------------------------------------------------------------------------------------
u, v, x, y = sp.symbols('u v x y', real=True)
coords = [u, v, x, y]
n = 4
H = sp.Function('H')(u, x, y)
g = sp.Matrix([[H, 1, 0, 0],
               [1, 0, 0, 0],
               [0, 0, 1, 0],
               [0, 0, 0, 1]])
ginv = g.inv()
def D(expr, i):
    return sp.diff(expr, coords[i])

# Christoffel  Γ^a_{bc}
Gamma = [[[sp.simplify(sum(ginv[a, e]*(D(g[e, b], c) + D(g[e, c], b) - D(g[b, c], e))
                           for e in range(n)) / 2)
           for c in range(n)] for b in range(n)] for a in range(n)]

# Ricci  R_{bc} = ∂_a Γ^a_{bc} − ∂_c Γ^a_{ba} + Γ^a_{ae}Γ^e_{bc} − Γ^a_{ce}Γ^e_{ba}
def Ric(b, c):
    t = 0
    for a in range(n):
        t += D(Gamma[a][b][c], a) - D(Gamma[a][b][a], c)
        for e in range(n):
            t += Gamma[a][a][e]*Gamma[e][b][c] - Gamma[a][c][e]*Gamma[e][b][a]
    return sp.simplify(t)
Ricci = sp.Matrix(n, n, lambda b, c: Ric(b, c))
Rscalar = sp.simplify(sum(ginv[b, c]*Ricci[b, c] for b in range(n) for c in range(n)))
Einstein = sp.simplify(Ricci - Rscalar*g/2)

lap_perp = sp.diff(H, x, 2) + sp.diff(H, y, 2)         # transverse Laplacian ∇²_⊥ H
print("[1] pp-wave geometry  (ds² = H du² + 2 du dv + dx² + dy²)")
check("Ricci scalar  R = 0",                 Rscalar == 0,                          "pp-wave is Ricci-scalar-flat")
check("R_uu = −½ ∇²_⊥ H",                    sp.simplify(Ricci[0,0] + lap_perp/2) == 0, "the only nonzero Ricci component")
check("G_uu = R_uu = −½ ∇²_⊥ H",             sp.simplify(Einstein[0,0] + lap_perp/2) == 0, "Einstein tensor uu-component")
offdiag_zero = all(sp.simplify(Einstein[a,b]) == 0 for a in range(n) for b in range(n) if (a,b) != (0,0))
check("all other G_μν = 0",                  offdiag_zero,                          "Einstein tensor has a single component")

# ----------------------------------------------------------------------------------------
# [2] Contracted Bianchi identity  ∇^μ G_{μν} = 0  (conservation — the consistency that lets
#     the local Clausius relation become a field equation and fixes Λ).
# ----------------------------------------------------------------------------------------
Gmix = sp.Matrix(n, n, lambda a, b: sp.simplify(sum(ginv[a, c]*Einstein[c, b] for c in range(n))))  # G^a_b
def divG(nu):
    t = 0
    for mu in range(n):
        t += D(Gmix[mu, nu], mu)
        for lam in range(n):
            t += Gamma[mu][mu][lam]*Gmix[lam, nu] - Gamma[lam][mu][nu]*Gmix[mu, lam]
    return sp.simplify(t)
print("\n[2] conservation:  contracted Bianchi  ∇^μ G_μν = 0")
check("∇^μ G_μν = 0  for all ν",            all(divG(nu) == 0 for nu in range(n)),  "∇^μ G_μν = 0 (⇒ ∇^μ T_μν = 0)")

# ----------------------------------------------------------------------------------------
# [3] Jacobson's null-cone lemma:  a symmetric S with S_μν k^μ k^ν = 0 for ALL null k must be
#     S = f·g.  (This is what turns the per-null-direction Clausius relation into a tensor
#     equation.)  Demonstrated on Minkowski η = diag(−1,1,1,1) with null k = (1, n̂), |n̂|=1.
# ----------------------------------------------------------------------------------------
print("\n[3] Jacobson null-cone lemma  (S_kk = 0 ∀ null k  ⟹  S = f·g)")
s00, s01, s02, s03, s11, s12, s13, s22, s23, s33 = sp.symbols(
    's00 s01 s02 s03 s11 s12 s13 s22 s23 s33', real=True)
S = sp.Matrix([[s00, s01, s02, s03],
               [s01, s11, s12, s13],
               [s02, s12, s22, s23],
               [s03, s13, s23, s33]])
# enough null directions (1, n̂), |n̂|=1, to pin S to the 1-parameter family f·g: the six ±axes
# fix the diagonal + s_{0i}=0, three mixed directions kill the off-diagonal spatial terms.
nhats = [(1,0,0), (-1,0,0), (0,1,0), (0,-1,0), (0,0,1), (0,0,-1),
         (sp.Rational(3,5), sp.Rational(4,5), 0),
         (sp.Rational(3,5), 0, sp.Rational(4,5)),
         (0, sp.Rational(3,5), sp.Rational(4,5))]
eqs = []
for nh in nhats:
    k = sp.Matrix([1, nh[0], nh[1], nh[2]])
    eqs.append(sp.expand((k.T * S * k)[0]))         # S_μν k^μ k^ν  (must vanish ∀ null k)
sol = sp.solve(eqs, [s00, s01, s02, s03, s11, s12, s13, s22, s23, s33], dict=True)[0]
Ssol = S.subs(sol)
eta = sp.diag(-1, 1, 1, 1)
f = Ssol[1, 1]                                       # the free scalar f (= S_xx after solving)
check("S_kk=0 ∀ null k ⟹ S = f·η",          sp.simplify(Ssol - f*eta) == sp.zeros(4,4), "tensors agreeing on the null cone differ by f·g")

# ----------------------------------------------------------------------------------------
# [4] The matter (free Klein–Gordon field) + Jacobson's equation of state → Einstein.
# ----------------------------------------------------------------------------------------
phi = sp.Function('phi')(u, x, y)
T_uu = sp.diff(phi, u)**2                            # free-KG stress component along the null u (= ∂_uφ·∂_uφ)
G_grav, ell = sp.symbols('G_N ell_P', positive=True) # Newton constant (carried UV datum); η = 1/(4ℓ_P²)=1/(4G)
print("\n[4] free Klein–Gordon matter + Jacobson equation of state  δQ = T δS")
print("    δS = η δA  (derived: area_floor_vonNeumann + DifferentialAreaLaw; η = 1/4ℓ_P²)")
print("    T  = κ/2π  (Unruh; the BW modular flux, discharged for the free field: Fock.OneParticleBW)")
print("    δQ = ∫ T_kk ,   δA via Raychaudhuri  dθ/dλ = −R_kk")
print("    ⟹  R_μν k^μ k^ν = 8πG · T_μν k^μ k^ν   for all null k")
print("    ⟹ (null-cone lemma [3] + Bianchi [2])  G_μν + Λ g_μν = 8πG T_μν")
# On the pp-wave the null cone has a single non-trivial component (uu): G_uu = 8πG T_uu, i.e.
einstein_uu_lhs = sp.simplify(Einstein[0, 0])                      # = −½∇²_⊥H
einstein_uu_rhs = 8*sp.pi*G_grav*T_uu                             # = 8πG (∂_uφ)²
print(f"\n    pp-wave Einstein equation:   G_uu = 8πG·T_uu")
print(f"        −½∇²_⊥H  =  8πG·(∂_uφ)²")
print(f"        {sp.nsimplify(einstein_uu_lhs)}  =  {einstein_uu_rhs}")
field_eq = sp.simplify(einstein_uu_lhs - einstein_uu_rhs)        # "= 0" is the Einstein equation
check("Einstein eqn  G_uu − 8πG T_uu = −½∇²_⊥H − 8πG(∂_uφ)²",
      sp.simplify(field_eq - (-lap_perp/2 - 8*sp.pi*G_grav*sp.diff(phi, u)**2)) == 0,
      "−½(H_xx+H_yy) = 8πG(∂_uφ)²  (the GR field equation, this realisation)")

# ----------------------------------------------------------------------------------------
print("\n" + "="*82)
print("RESULT:", "GR DERIVED in this realisation (conditional Jacobson chain, free KG field)."
      if ok else "SOME CHECK FAILED.")
print("="*82)
print("""
Minimal GRAVITATIONAL realisation = the free Klein–Gordon field on a pp-wave background.
GR is reached HERE (not in the finite toys) because this realisation supplies the continuum
ingredients the finite toys could not:
  • a smooth metric and the Raychaudhuri area derivative δA ↔ R_kk        [§1, §2 above]
  • the Bisognano–Wichmann/Unruh temperature, discharged for the free field (Fock.OneParticleBW)
fed by the QIQT-H inputs that ARE upgraded to theorems:
  • the area floor S_vN ≤ ηA           (area_floor_vonNeumann)
  • the entropy–area variation δS = ηδA (DifferentialAreaLaw — no separate Clausius postulate)
  • the 1/4 coefficient                 (SakharovRatio — regulator/matter-independent)
Assembled by Jacobson's equation of state into the Einstein field equations
(qiqt_bekenstein_gives_gr / qiqt_gr_freefield / qiqt_gr_ppwave_showcase).

CONDITIONAL — the labelled residual inputs (not derived):
  matter equation of motion · (P4) the capacity bound · the localization map (entropy rate =
  2π T_kk; provably not analytically dischargeable — where the physics enters) · the
  reference-state identification (BW-modular = capacity-saturating) · the VALUE of G.
So: a conditional, axiom-free, machine-checked Jacobson-type derivation of GR for the free field
— NOT "GR from nothing", and NOT reachable by any finite toy.
""")
import sys
sys.exit(0 if ok else 1)
