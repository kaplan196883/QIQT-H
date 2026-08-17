import sympy as sp

# ============================================================================
# J4-820 — QUANTITATIVE scaling of the field<->source transposition residual
# under the sqrt(eps) sliver window.
#
# Foundation (J4-819, WitnessSourceFieldTransposition.lean):
#   The transposition the live hCConv wall must reconcile is
#       kPrime  needs   d^2_firstslot H(field=0, source=z)   = G(-z)
#       sliver  gives   d^2_firstslot H(field=z, source=0)   = G(z)
#   where G(w) := (d^2 F)(w) is the SECOND partial of the (displacement-model)
#   kernel F, evaluated at the displacement w.  J4-819 proved: if F is EVEN,
#   G is even and the difference G(-z)-G(z) = 0 EXACTLY.
#
# This script establishes the GENERAL (non-even) EXACT residual formula and its
# leading small-z / sliver-window scaling, confirming the residual is subleading
# to the O(sqrt eps) rate the closed J4-817 sliver bound already carries.
# ============================================================================

w, z, tau, eps = sp.symbols('w z tau eps', positive=True)
wr = sp.Symbol('w', real=True)

# --- 1. EXACT residual formula: difference = G(-z) - G(z) = -2*(odd part of G).
# G arbitrary; split G = Geven + Godd.
G = sp.Function('G')
diff_general = G(-z) - G(z)
print("=== EXACT transposition residual (general kernel) ===")
print("   G(-z) - G(z)  =  -2 * Godd(z),  Godd(z) := (G(z)-G(-z))/2")
print("   difference =", sp.simplify(diff_general), "(unevaluated symbolic; = -2*Godd(z))")
print()

# --- 2. Concrete van-Vleck amplitude model.  F = Gaussian(EVEN) * A(w),
#   A(w) = a0 + a2 w^2 + a3 w^3 + a4 w^4  (RNC: a1 = 0 identically; a3 = nabla R).
a0, a2, a3, a4 = sp.symbols('a0 a2 a3 a4', real=True)
Gauss = sp.exp(-wr**2/(4*tau))
A = a0 + a2*wr**2 + a3*wr**3 + a4*wr**4
F = Gauss * A
G2 = sp.diff(F, wr, 2)                       # second partial G(w) = F''(w)
residual = sp.simplify(G2.subs(wr, -z) - G2.subs(wr, z))   # G(-z) - G(z)
print("=== EXACT residual for the van-Vleck displacement model ===")
print("   G(-z) - G(z) =")
print("  ", sp.simplify(residual))
print()

# The residual must be carried ENTIRELY by odd amplitude coeffs (a1,a3).
res_even = sp.simplify(residual.subs({a3: 0}))   # a1 already absent
print("=== residual with a3=0 (pure even amplitude): must be 0 ===")
print("  ", res_even)
assert res_even == 0, "even amplitude must give zero residual"
print("   CONFIRMED: even amplitude => zero transposition residual.")
print()

# --- 3. LEADING small-z scaling of the residual (Taylor about z=0).
ser = sp.series(residual, z, 0, 4).removeO()
print("=== residual Taylor in z to O(z^3) ===")
print("  ", sp.expand(ser))
lead = sp.simplify(sp.limit(residual/z, z, 0))
print("   leading order: residual = ", lead, "* z + O(z^3)   (LINEAR in z)")
print("   => |residual| = O(|z|),  driven by a3 = nabla R.")
print()

# --- 4. SLIVER-WINDOW integral: contribution of the residual over |z| <= sqrt(eps).
# The sliver window has spatial extent |z| <~ sqrt(eps).  The closed J4-817 sliver
# bound carries an O(sqrt eps) RATE.  We integrate the residual's magnitude over the
# window and confirm it is dominated by that rate.
#
# Model the residual as its leading linear term c*z (c = -a3 * 3/tau * const).
# Over the 1D window [-sqrt eps, sqrt eps], the L1 mass and the sup are:
c = sp.Symbol('c', positive=True)
res_model = c*z
sup_window = res_model.subs(z, sp.sqrt(eps))                 # sup over window
l1_window = sp.integrate(res_model, (z, 0, sp.sqrt(eps)))    # L1 mass on half-window
print("=== sliver-window (|z| <= sqrt eps) scaling of residual (leading term c*z) ===")
print("   sup over window      : |residual|_max = c * sqrt(eps)          =>  O(eps^{1/2})")
print("   L1 mass over window  : int_0^{sqrt eps} c z dz =", sp.simplify(l1_window), " =>  O(eps)")
print()
print("=== VERDICT ===")
print("The transposition residual G(-z)-G(z) is EXACTLY -2*(odd part of the second")
print("partial), carried entirely by the odd amplitude (a1 linear, a3 cubic).")
print("In RNC a1=0, so residual = O(a3 * z) = O(nabla R * z), LINEAR in z.")
print("Under the sqrt(eps) sliver window:")
print("  * pointwise sup      = O(sqrt eps)  -- SATURATES, does not exceed, the")
print("                          O(sqrt eps) rate the closed J4-817 sliver already carries;")
print("  * integrated L1 mass = O(eps)       -- STRICTLY SUBLEADING to sqrt eps.")
print("Hence the cubic nabla-R residual's contribution is absorbed within the existing")
print("sliver budget: it does NOT worsen the O(sqrt eps) transposition-difference rate.")
print("The Lean interface hypothesis (odd part of second partial is O(|z|), i.e. |G(-z)-G(z)|")
print("<= L*||z||) is therefore SATISFIED by the concrete van-Vleck amplitude, non-vacuously.")
