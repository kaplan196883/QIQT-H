import sympy as sp

# ============================================================================
# Model: H(tau,p,q) = F(tau, V(q,p)), V=chart of field p based at source q.
# In flat/leading chart V(q,p) = p - q.  F(tau,w) = G(tau,w)*A(w) with
#   G = Gaussian (EVEN in w), A = amplitude Theta^{-1/2}*(u0+u1*tau).
# kPrime (center):  d^2_p H(tau,0,z)  = (G*A)''(-z)   [V(z,p)=p-z, eval p=0]
# sliver (z0=0):    d^2_p H(tau,z,0)  = (G*A)''(z)     [V(0,p)=p,   eval p=z]
# Need: reconcile (G*A)''(-z) vs (G*A)''(z).
# ============================================================================
w, z, tau = sp.symbols('w z tau', real=True)

# Gaussian (even): use generic even function g(w^2). Represent 1D factor.
# Use G = exp(-w**2/(4*tau)) (times const prefactor irrelevant for symmetry).
G = sp.exp(-w**2/(4*tau))

# Amplitude with EVEN part (quadratic: curvature R) + ODD part (cubic: nabla R).
# A(w) = a0 + a2*w**2 + a3*w**3 + a4*w**4 ...   (a1 linear also possible)
a0,a1,a2,a3,a4 = sp.symbols('a0 a1 a2 a3 a4', real=True)
A = a0 + a1*w + a2*w**2 + a3*w**3 + a4*w**4

F = G*A
F2 = sp.diff(F, w, 2)          # (G*A)''(w)
kprime = F2.subs(w, -z)        # (G*A)''(-z)
sliver = F2.subs(w,  z)        # (G*A)''(z)
diff = sp.simplify(kprime - sliver)
print("=== FULL difference (G*A)''(-z) - (G*A)''(z) ===")
print(sp.simplify(diff))
print()

# EVEN amplitude only (a1=a3=0): the curvature-relevant part.
diff_even = sp.simplify(diff.subs({a1:0, a3:0}))
print("=== difference with EVEN amplitude (a1=a3=0) ===")
print(diff_even)
print()

# Isolate contribution of the ODD amplitude part only.
diff_odd = sp.simplify(diff.subs({a0:0,a2:0,a4:0}))
print("=== difference from ODD amplitude part (a0=a2=a4=0) ===")
print(diff_odd)
print()

# Leading small-z order of the odd contribution (Taylor in z about 0):
ser = sp.series(diff_odd, z, 0, 4).removeO()
print("=== odd-part difference, Taylor in z to O(z^3) ===")
print(sp.expand(ser))

print()
print("=== VERDICT ===")
print("Transposition d^2_p H(0,z) = d^2_p H(z,0) holds EXACTLY iff amplitude A is EVEN.")
print("Difference is carried ENTIRELY by ODD amplitude coeffs (a1 linear, a3 cubic).")
print("In RNC: a1 = 0 (partial g(0)=0, Christoffel(0)=0), so obstruction = a3 = nabla-R (cubic).")
