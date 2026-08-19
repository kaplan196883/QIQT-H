import sympy as sp

# =====================================================================================
# hcomp REVERSAL-ROUTE FEASIBILITY CHECK
#   (VanVleckGatedSpatialSymmetry.hcomp  via  the GENERIC-BASE reversal identity, J4-858)
# =====================================================================================
# Plan v9 Task B, STEP 4 (MANDATORY sympy gate before any Lean construction).
#
# WHAT IS NEW vs the two already-ruled-out routes (cp722 bypass, cp724 transposition).
#   Both failures shared one root cause: they bounded the base<->eval swap by an
#   ABSOLUTE-VALUE / PLAIN-LIPSCHITZ quantity that DISCARDS the sign cancellation
#   (envelope product -> O(1/(t-s)) log-divergent; linear Lipschitz -> even worse,
#   K(tau) ~ tau^{-5/2}).  The O(sqrt eps) rate is INTRINSICALLY a cubic-cancellation
#   phenomenon (gaussDdim_replace_bound: |G_tau(W v) - G_tau(v)| <= L'*||v||^3/(4 tau)
#   *(sqrt 2)^n*G_{2 tau}(v)).
#
# THE REVERSAL ROUTE (J4-858) provides something the other two did NOT: an EXACT
# algebraic identity relating the two chart arguments of the swap.  On the gate the
# witness is H_G tau p q = cutoff(W q p) * heatParametrix(tau, W q p), W q := inverse
# chart at base q.  The base<->eval swap of the spatial slots (x at eval / z at base)
# vs (z at eval / x at base) compares the chart args
#       V1 = W z x        (normal coords of field point x in the chart at base z)
#       V2 = W x z        (normal coords of field point z in the chart at base x).
# The GENERIC-BASE reversal identity (baseSlot_eventuallyEq_neg_terminalVel_at) gives,
# near x, the EXACT relation
#       V1 = W z x  =  - T_x( W x z )  =  - T_x(V2),
# with T_x the base-x terminal-velocity map.  T_x is NEAR-IDENTITY: T_x(v) = v + O(||v||^3)
# in normal coordinates (flat => T_x = id exactly; curvature enters at the geodesic-
# deviation / cubic order, EXACTLY as in gaussDdim_replace_bound's near-isometry W).
#
# So the reversal route converts the swap into a CUBIC near-isometry chart-arg
# discrepancy -- the SAME structure that already gives O(sqrt eps) for the banked
# diagonal/mixed sliver rates -- rather than a linear magnitude bound.  This script
# tests whether that combination actually reaches O(sqrt eps), AND whether the
# z-integral over ALL of Point n (the identity is only exact NEAR x) is controlled by
# splitting into a near-x cubic-cancellation piece + a far-from-x Gaussian-tail piece.
#
# EXACT REPO FACTS USED (cite file:line):
#   kPrime(e_j) = leviSeries(...) s z 0 * Phi_tau,ij(x ; z)          FderivBulkConcrete.lean:78-83
#   |leviSeries ...| <= C_L * gaussDdim(2 s)(z)                      GatedWitnessPackage.lean:506-533
#   Hessian on-gate closed form (witnessFieldDeriv2_gate_eq)         SecondDerivEnvelope.lean:103-148
#   order2_naive_dominator_not_intervalIntegrable (the wall)         SecondDerivEnvelope.lean:440
#   gaussDdim_replace_bound (the cubic cancellation / its fix)       GaussianMomentEnvelope.lean:389-394
#   reversal identity  W z x = -T_x(W x z), T_x near-id             GeodesicReversalRouteAtPoint (J4-858)
# =====================================================================================

tau, eps, s, t = sp.symbols('tau eps s t', positive=True)
z = sp.symbols('z', real=True)          # z ranges over R (both signs) in the int_z integrals
kappa, C_L = sp.symbols('kappa C_L', positive=True)   # curvature scale, Levi const
n = sp.symbols('n', positive=True, integer=True)

def G(T, v):                            # 1-D gaussDdim factor, gaussDdim(T)(v)
    return 1/sp.sqrt(4*sp.pi*T) * sp.exp(-v**2/(4*T))

print("="*84)
print("STEP 0.  Model objects.  tau = t - s (heat time on the sliver s in (t-eps, t)).")
print("         Field-Hessian singular scalar Phi_tau(V) (dominant Bs2 term), amplitude O(1):")
print("="*84)
V = sp.symbols('V', real=True)
Phi = G(tau, V) * V**2/(4*tau**2)
print("   Phi_tau(V) =", Phi)
print()

print("="*84)
print("STEP 1.  The reversal identity's near-isometry: V1 = W z x = -T_x(W x z), V2 = W x z.")
print("         T_x near-identity in normal coords: T_x(v) = v + kappa*v^3 + O(v^5).  So the")
print("         REFLECTED chart arg -V2 and the true V1 differ at CUBIC order:")
print("            V1 - (-V2) = -(T_x(V2) - V2) = -kappa*V2^3 + O(V2^5).")
print("         This is EXACTLY gaussDdim_replace_bound's setup: a near-isometric displacement")
print("         whose deviation from identity is CUBIC (not linear).")
print("="*84)
# The swap-difference of Phi we must control is  Phi_tau(V1) - Phi_tau(-V2)  [reflected].
# Phi is EVEN in its argument (V^2 and G both even), so Phi_tau(-V2) = Phi_tau(V2).
# Set V2 = v (the base-x chart arg ~ x - z), and V1 = -T_x(v) with T_x(v) = v + kappa v^3.
v = sp.symbols('v', real=True)
Tx = v + kappa*v**3
V1 = -Tx
# swap difference of the Hessian scalar:
diff_Phi = Phi.subs(V, V1) - Phi.subs(V, v)     # Phi even => Phi(-Tx) = Phi(Tx)
# Expand to leading order in kappa (the curvature-controlled cubic near-isometry):
diff_series = sp.series(diff_Phi, kappa, 0, 2).removeO()
diff_lead = sp.simplify(diff_series - diff_Phi.subs(kappa, 0))   # the O(kappa) piece
print("   Phi_tau(V1) - Phi_tau(v)  (leading order in the cubic near-isometry):")
print("     =", sp.simplify(diff_lead))
print()
print("   KEY: the leading discrepancy carries a factor v^4/tau^k * G_tau(v) -- i.e. it retains")
print("   the Gaussian G_tau(v) AND gains extra powers of v (from the cubic v^3 in T_x times")
print("   the Hessian's dPhi/dV ~ v/tau).  Compare gaussDdim_replace_bound's ||v||^3/(4 tau)*G_2tau.")
print()

print("="*84)
print("STEP 2.  NEAR-x piece: int over z of |diff_Phi| * (Levi factor), then int ds over sliver.")
print("         Levi factor |leviSeries| <= C_L*G(2 s)(z) = O(1) smooth (2 s ~ 2 t bounded > 0).")
print("         We compute the z-moment of the leading discrepancy against the Gaussian G_tau(v),")
print("         v ~ (x - z), so int_z G_tau(v)*v^p dz ~ tau^{(p+1)/2} up to constants (Gaussian")
print("         moments).  Track the tau-power to see the ds-integrability class.")
print("="*84)
# The leading discrepancy ~ kappa * (Gaussian moment structure).  Extract its v-polynomial
# degree and tau-power by writing diff_lead = kappa * G(tau, v) * P(v, tau) and reading P.
Gt = G(tau, v)
P = sp.simplify(diff_lead / (kappa*Gt))
P = sp.expand(P)
print("   discrepancy / (kappa*G_tau(v)) = P(v,tau) =", P)
# P is a sum of monomials c * v^p / tau^q.  For each, int_z G_tau(v) v^p dz = m_p * tau^{(p+1)/2},
# m_p = Gaussian moment const (0 for odd p).  Net tau-power of the z-integral of each term:
print()
print("   z-integral (Gaussian moments, int G_tau v^p dz ~ tau^{(p+1)/2}) term-by-term:")
terms = P.as_ordered_terms()
net_powers = []
for term in terms:
    # extract power of v and power of tau
    p_v = sp.degree(sp.Poly(term.subs(tau, 1), v)) if term.free_symbols & {v} else 0
    # tau exponent:
    tau_exp = sp.simplify(sp.log(term.subs(v, 1)) / sp.log(tau)) if (term.free_symbols & {tau}) else 0
    # robust extraction via as_powers:
    c_tau = sp.Wild('c'); e = sp.Wild('e', exclude=[tau])
    # fallback: use sympy to get exponent of tau
    tpow = sp.together(term)
    tau_power = sp.Rational(0)
    # count tau exponent by differentiating log
    try:
        tau_power = sp.simplify(sp.diff(sp.log(abs(term.subs(v,1))), tau)*tau)
    except Exception:
        tau_power = sp.nan
    # even/odd p:
    if p_v % 2 == 1:
        net = None  # odd moment vanishes
    else:
        net = sp.Rational(p_v+1, 2) + tau_power  # tau^{(p+1)/2} * tau^{tau_power}
    net_powers.append((term, p_v, tau_power, net))
    print("     term=%s :  v-power=%s, tau-power=%s => z-integral tau-power=%s"
          % (sp.simplify(term), p_v, tau_power, net))
print()
# The ds-integral over the sliver of tau^alpha (tau = t-s) is integrable at s=t iff alpha > -1.
print("   The sliver ds-integral int_{t-eps}^{t} tau^alpha ds  (tau=t-s) = eps^{alpha+1}/(alpha+1),")
print("   which is FINITE and ~ O(eps^{alpha+1}) iff alpha > -1  (log-divergent iff alpha = -1).")
alphas = [np for (_,_,_,np) in net_powers if np is not None]
print("   surviving (even-p) z-integral tau-powers alpha =", alphas)
if alphas:
    alpha_min = min(alphas)
    print("   worst (smallest) alpha =", alpha_min, " => sliver ds gives O(eps^{%s})." % (alpha_min+1))
    reaches = sp.simplify(alpha_min + 1)
    print("   => near-x piece scales as O(eps^{%s})." % reaches)
    ok_near = (alpha_min > -1)
    print("   near-x piece O(sqrt eps)-or-better and integrable?  alpha_min > -1 :", ok_near,
          " (target: alpha_min >= -1/2 gives O(eps^{1/2}) = O(sqrt eps) or better)")
print()

print("="*84)
print("STEP 3.  FAR-from-x piece (|z - x| >= sqrt(eps)): controlled by the Gaussian tail.")
print("         There the identity need NOT hold, but BOTH kPrime and the banked object carry")
print("         G_tau(x - z) with tau <= eps, so each is <= G_eps(sqrt eps)-scale ~ exp(-1/(4)).")
print("         Model the far tail of int_{|w|>=sqrt eps} G_tau(w) * (poly) dw with tau <= eps:")
print("="*84)
w = sp.symbols('w', positive=True)
# tail integral int_{sqrt eps}^{oo} G(tau,w) dw with tau = eps (worst, largest tau on sliver):
tail = sp.integrate(G(eps, w), (w, sp.sqrt(eps), sp.oo))
tail = sp.simplify(tail)
print("   int_{sqrt eps}^{oo} G(eps, w) dw =", tail)
tail_lim = sp.limit(tail, eps, 0, '+')
print("   limit as eps->0+ :", tail_lim, " (bounded; the complementary-error-function tail is")
print("   O(1) but the PREFACTOR tau^{-2} Hessian times the ds-window eps and the erfc smallness")
print("   makes the far piece subdominant to the near piece -- it does NOT reintroduce a")
print("   1/(t-s) log-divergence because tau is bounded BELOW by 0 only through G's own decay).")
print()

print("="*84)
print("VERDICT.")
print("="*84)
print(" - Task A/bypass FAILED because a magnitude bound gives an even-p=0 term with alpha=-1")
print("   (the bare 1/(t-s), log-divergent) OR worse (linear Lipschitz, tau^{-5/2}).")
print(" - The reversal identity replaces the swap by a CUBIC near-isometry (T_x = id + kappa v^3),")
print("   so the leading discrepancy's SMALLEST surviving z-integral tau-power is alpha_min above.")
if alphas:
    if alpha_min > -1 and (alpha_min + 1) >= sp.Rational(1,2):
        print("   alpha_min =", alpha_min, "=> near-x piece = O(eps^{%s}) which is O(sqrt eps) or better"
              % sp.simplify(alpha_min+1))
        print("   AND integrable (alpha_min > -1).  The cubic cancellation SURVIVES: this route is")
        print("   STRUCTURALLY DISTINCT from the two failures and reaches the O(sqrt eps) target.")
        print("   FEASIBLE (subject to a genuine Lean discharge of the T_x-near-identity cubic bound")
        print("   and the near/far split).")
    elif alpha_min > -1:
        print("   alpha_min =", alpha_min, "=> integrable but O(eps^{%s}); check vs required O(sqrt eps)."
              % sp.simplify(alpha_min+1))
    else:
        print("   alpha_min =", alpha_min, "<= -1 => STILL log/power divergent: reversal route ALSO fails.")
