import sympy as sp

# Toy 1D sanity check of Sol's "frozen-model subtraction" proposal for r6.
# Freeze Bfac's coefficient structure at z=x (constants), keep the Gaussian
# argument v = z-x varying (leading-order normal-coordinate approx of U(z,x)).
# Claim to check: the FROZEN model kernel (quadratic-in-v * Gaussian, matching
# BRICK1's 4-term structure with constant coefficients) integrates to EXACTLY
# ZERO over all of R (parity/exact-derivative fact), independent of the
# specific constant values of the frozen coefficients -- i.e. this is a
# genuine IBP identity, not something requiring cancellation against a
# nonexistent companion term.

v, tau, c1, c2, c3 = sp.symbols('v tau c1 c2 c3', real=True, positive=False)
tau_p = sp.symbols('tau', positive=True)

G = sp.exp(-v**2/(4*tau_p)) / sp.sqrt(4*sp.pi*tau_p)

# BRICK1's 4-term normal form collapses (1D toy, i=j) to the standard
# Hessian-of-Gaussian structure: c1*v^2/(4 tau^2) - c2/(2 tau) is exactly
# d^2/dv^2 G up to matching c1,c2 to G's own second derivative -- i.e. the
# "frozen" kernel IS (a constant amplitude coefficient) times d^2G/dv^2.
# Check: integral of d^2G/dv^2 over R is 0 (boundary terms vanish).
d2G = sp.diff(G, v, 2)
I = sp.integrate(d2G, (v, -sp.oo, sp.oo))
print("integral of d^2G/dv^2 over R:", sp.simplify(I))

# Also check the FIRST-derivative term (the gr_i*dA, gr_j*dA linear pieces)
# integrates to zero by oddness of dG/dv (odd function).
dG = sp.diff(G, v, 1)
I1 = sp.integrate(dG, (v, -sp.oo, sp.oo))
print("integral of dG/dv over R:", sp.simplify(I1))

# Sanity: plain G integrates to 1 (not the vanishing case) -- confirms the
# vanishing above is specifically a derivative-order effect, not trivial.
I0 = sp.integrate(G, (v, -sp.oo, sp.oo))
print("integral of G over R:", sp.simplify(I0))
