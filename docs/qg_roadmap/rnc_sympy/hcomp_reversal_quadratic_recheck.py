import sympy as sp
# Augmented feasibility: does a QUADRATIC term in T_x (which my Lean bound HAS, unlike the
# pure-cubic sympy model) break the O(sqrt eps) conclusion?  T_x(v) = v + beta*v^2 + kappa*v^3.
# Van Vleck Hessian singular scalar Phi is EVEN.  Multi-D: singular scalar = phi(||V||^2).
# 1-D proxy consistent with the original script: Phi_tau(V) = G(tau,V)*V^2/(4 tau^2), even in V.
tau, v = sp.symbols('tau v', positive=True), sp.symbols('v', real=True)
tau = sp.symbols('tau', positive=True)
beta, kappa = sp.symbols('beta kappa', real=True)
def G(T,x): return 1/sp.sqrt(4*sp.pi*T)*sp.exp(-x**2/(4*T))
def Phi(V): return G(tau,V)*V**2/(4*tau**2)
Tx = v + beta*v**2 + kappa*v**3
# Phi even => Phi(-Tx)=Phi(Tx). Swap discrepancy = Phi(Tx) - Phi(v).
diff = Phi(Tx) - Phi(v)
# Expand to leading orders in the curvature parameters beta,kappa (near-identity):
ser = sp.series(sp.series(diff, beta, 0, 2).removeO(), kappa, 0, 2).removeO()
lead = sp.simplify(ser - Phi(v).subs(v,v)*0 - (diff.subs({beta:0,kappa:0})))  # drop the beta=kappa=0 (=0) part
lead = sp.expand(sp.simplify(lead))
# Write leading discrepancy as sum of terms  c * v^p / tau^q * G_tau(v); compute z-integral tau-power
Gt = G(tau,v)
P = sp.expand(sp.simplify(lead/Gt))
print("discrepancy/G_tau(v) = P(v,tau) =", P)
terms = P.as_ordered_terms()
print("\nterm-by-term z-moment tau-power (int G_tau v^p dz ~ tau^{(p+1)/2}; ODD p -> vanishes):")
alphas=[]
for term in terms:
    pv = sp.degree(sp.Poly(term.subs(tau,1), v))
    # tau power:
    tpow = sp.simplify(sp.diff(sp.log(sp.Abs(term.subs(v,1))),tau)*tau)
    if pv % 2 == 1:
        net=None
    else:
        net = sp.Rational(pv+1,2)+tpow
        alphas.append(net)
    print(f"  v^{pv} / tau-pow {tpow}  ->  {'VANISHES(odd)' if net is None else 'alpha='+str(net)}")
if alphas:
    am=min(alphas)
    print("\nworst surviving alpha =", am, " => sliver ds ~ O(eps^{%s})"%(am+1))
    print("O(sqrt eps) or better & integrable (alpha>-1):", am>-1 and (am+1)>=sp.Rational(1,2))
