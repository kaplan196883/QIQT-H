import sympy as sp

# =====================================================================================
# hcomp Z-SPACE ODDNESS-CANCELLATION FEASIBILITY CHECK  (J4-1057 redirect, post-CoV-closure)
# =====================================================================================
# CONTEXT.  The base/eval CoV-composition route (J4-1017..1057) is DEFINITIVELY CLOSED: even
# fully composed, it only supplies 2 of the 6 residuals (r1-r6) that
# HCompNearCarryKPrimeBaseFieldCoV.lean's own BRICK-2 docstring enumerates for `nb`
# (VanVleckGatedSpatialSymmetry.hcomp's near carry).  J4-1057's Sol-recommended new direction:
#     "a direct localized odd-cancellation estimate in the original z variables -- linearize Bfac
#      and the chart map near x, cancel by oddness on the centered ball, bound remainders by
#      Gaussian moments, tail via existing HCompNearFarSplit machinery -- bypassing
#      V/Jacobian/CoV/slot-reversal entirely."
#
# THIS SCRIPT tests that literal proposal against the EXACT closed form BRICK 1 already proved
# (kPrime_apply_single_on_gate_eq_baseGaussian_mul_amp, HCompNearCarryKPrimeBaseFieldCoV.lean:88-122):
#     kPrime(e_j)(z) = gaussDdim(t-s)(U z x) * Bfac(z),
#     Bfac(z) = Levi(s,z) * [ <U,PI><U,PJ>/(4 tau^2) - (<PI,PJ>+<U,Q>)/(2 tau) ) * A(z)
#                 - <U,PJ>/(2 tau) * d_j A(z) - <U,PI>/(2 tau) * d_i A(z) + d_i d_j A(z) ],
#     U = U(z,x) = uniformInverseChart ... z x   (base-slot chart displacement, U(x,x)=0).
#
# QUESTION.  Does "linearize Bfac + the chart map near x, then cancel by oddness under
# z -> 2x-z (i.e. w = z-x -> -w)" actually kill the DOMINANT singular term (the 1a term,
# <U,PI><U,PJ>/(4 tau^2)*A), the way hcomp_near_carry_final_feasibility.py's ALREADY-VALIDATED
# reversal/cubic-cancellation route (items iii+iv, now BANKED in HCompNearCarryFullyClosed.lean)
# does -- or does naive parity leave it untouched, reproducing the hcomp_bypass_feasibility.py /
# hcomp_transposition_feasibility.py dead end?
# =====================================================================================

w, tau, eps, x = sp.symbols('w tau eps x', real=True)
c2, c3, PI_, PJ_, A0, A1 = sp.symbols('c2 c3 PI_ PJ_ A0 A1', real=True)   # generic Taylor coefficients

print("="*88)
print("STEP 1.  Parity of the CHART MAP U(z,x) as a function of w = z - x.")
print("="*88)
print("""  Riemann-normal-coordinate structure: U(x,x)=0, DU(x,x) = -Id (chart base-slot displacement),
  and the FIRST curvature correction to the geodesic/exponential map is CUBIC in the displacement
  (the quadratic term vanishes because Christoffel symbols vanish at the coordinate CENTER -- this
  is exactly the content banked as TerminalVelAtCubicRemainder / the reversal identity
  U z x =_[N x] -T_x(U x z)).  Model (1-D per component, WITH a generic quadratic term c2 kept in
  to test robustness -- i.e. we do NOT assume the favourable normal-coordinate cancellation):""")
def U_generic(ww, keep_quadratic):
    if keep_quadratic:
        return -ww + c2*ww**2 + c3*ww**3
    return -ww + c3*ww**3     # true normal-coordinate case: quadratic term IS absent
U_true = U_generic(w, keep_quadratic=False)
U_worst = U_generic(w, keep_quadratic=True)
print("  U_true(w)  (normal-coordinate, no quadratic term) =", U_true, "  -- ODD in w.")
print("  U_worst(w) (generic base-slot chart, quadratic term kept) =", U_worst, "  -- NOT odd.")
print()

print("="*88)
print("STEP 2.  The DOMINANT singular term (1a):  <U,PI><U,PJ>/(4 tau^2) * A(z),")
print("         near-diagonal 1-D model: PI,PJ ~ O(1) constants, A(z)=A(x+w) Taylor-expanded.")
print("="*88)
Uz = U_true                       # use the FAVOURABLE (odd) normal-coordinate case
A_taylor = A0 + A1*w              # generic smooth amplitude, NO assumed parity
term1a = (Uz*PI_)*(Uz*PJ_) / (4*tau**2) * A_taylor
term1a = sp.expand(term1a)
print("  term_1a(w) =", term1a)
even_part = sp.Rational(1,2)*(term1a + term1a.subs(w, -w))
odd_part  = sp.Rational(1,2)*(term1a - term1a.subs(w, -w))
even_part = sp.expand(even_part)
odd_part  = sp.expand(odd_part)
print("  EVEN part (survives w -> -w reflection, i.e. survives 'oddness cancellation') =", even_part)
print("  ODD  part (killed by integrating over the symmetric ball, i.e. what oddness DOES remove) =",
      odd_part)
print()
print("""  VERDICT STEP 2:  U(w) is ODD (even in the BEST case, true normal coordinates), so U(w)^2 is
  automatically EVEN regardless of any quadratic chart correction.  The leading term_1a has
  LEADING coefficient  PI_*PJ_*A0*w^2/(4 tau^2)  -- purely EVEN, order w^2/tau^2 -- UNTOUCHED by
  'cancel by oddness'.  Only the SUBLEADING A1*w-linear correction (the amplitude's own odd part)
  is removed by parity.  Oddness of Bfac's amplitude factor A(z) is IRRELEVANT to the dominant
  singular scalar, because <U,PI><U,PJ> is a PRODUCT OF TWO potentially-odd factors and hence
  structurally EVEN to leading order, independent of what A(z) does.""")
print()

print("="*88)
print("STEP 3.  Does the surviving EVEN leading term reproduce the ALREADY-FOUND naive-dominator")
print("         divergence (hcomp_bypass_feasibility.py Step 2-3), when Gaussian-moment bounded")
print("         'the naive way' (i.e. WITHOUT the reversal/T_x difference-cancellation machinery)?")
print("="*88)
def hk(T, v):
    return 1/sp.sqrt(4*sp.pi*T)*sp.exp(-v**2/(4*T))
# even_part leading order ~ PI_*PJ_*A0 * w^2 /(4 tau^2); integrate the Gaussian-weighted leading
# singular scalar directly against gaussDdim(tau)(U(z,x)) ~ gaussDdim(tau)(w) to leading order:
lead_even_coeff = PI_*PJ_*A0/(4*tau**2)
mom2 = sp.integrate(w**2 * hk(tau, w), (w, -sp.oo, sp.oo))
mom2 = sp.simplify(mom2)
print("  int_R w^2 * gaussDdim(tau)(w) dw =", mom2, "  (~ tau)")
naive_sliver_integrand = sp.simplify(lead_even_coeff * mom2)
print("  => naive (parity-only, no difference-cancellation) z-integral of the leading term ~",
      naive_sliver_integrand, "  i.e. O(1/tau).")
sliver = sp.integrate(1/tau, (tau, 0, eps))
print("  int_0^eps d tau / tau =", sliver, " -> DIVERGES (log).  IDENTICAL to the bypass-script trap.")
print()

print("="*88)
print("STEP 4.  What DOES kill the even leading term (for contrast) -- the ALREADY-BANKED mechanism.")
print("="*88)
print("""  HCompNearCarryFullyClosed.lean's items (iii)+(iv) (sympy-validated in
  hcomp_near_carry_final_feasibility.py, and NOW Lean-banked as gaussDdim_reversal_link +
  terminalVelAt_prefactor_sliver_bound) do NOT cancel term_1a by parity of a SINGLE integral.
  They instead (a) rewrite G_tau(U z x) via the EXACT reversal identity as G_tau(T_x(U x z))
  [item iii], reducing the problem to a DIFFERENCE  G_tau(T_x v) - G_tau(v)  against a REFERENCE
  flat computation, and (b) bound that difference by the CUBIC near-isometry error
  |r^2_{Tv} - r^2_v| <= L'||v||^3  (T_x's OWN curvature-cubic remainder, TerminalVelAtCubicRemainder),
  which supplies the EXTRA tau^{1/2} that upgrades tau^{-1} -> tau^{-1/2} (integrable, O(sqrt eps)).
  This is a DIFFERENCE/near-isometry argument on the ARGUMENT of the Gaussian (T_x acting on v),
  NOT a parity argument on the INTEGRAND Bfac(z) around x.  The two are NOT the same mechanism:
  the reversal/cubic route needs T_x's cubic remainder control; plain w -> -w oddness of Bfac
  needs nothing about T_x at all -- and correspondingly supplies nothing about the even w^2/tau^2
  term, which is exactly the term that needs the cubic control.""")
print()

print("="*88)
print("VERDICT")
print("="*88)
print("""  FAIL (as literally proposed).  "Linearize Bfac and the chart map near x, cancel by oddness on
  the centered ball" removes ONLY the ODD-in-w corrections of the integrand.  The DOMINANT singular
  scalar of BRICK 1's own closed form (term 1a, <U,PI><U,PJ>/(4 tau^2)*A) is a PRODUCT of two
  odd-in-w chart-displacement factors and is therefore EVEN in w to leading order, REGARDLESS of
  whether the chart map itself is linearized to first, second, or cubic order (odd*odd = even, always).
  A naive parity/Taylor-remainder treatment of this even term reproduces EXACTLY the divergent
  int_0^eps dtau/tau found in hcomp_bypass_feasibility.py (Step 2-3) and
  hcomp_transposition_feasibility.py (Step 2-3) -- i.e. this is THE SAME TRAP under a new name, not
  a new mechanism.  The genuine cancellation needed for term 1a is NOT integrand-parity; it is the
  DIFFERENCE-vs-reference (reversal/T_x near-isometry, cubic remainder) content ALREADY banked in
  HCompNearCarryFullyClosed.lean (items iii/iv) -- which is precisely what J4-1057's proposal
  explicitly says to bypass ("...slot-reversal entirely").  Bypassing slot-reversal throws away the
  ONLY known mechanism that reaches O(sqrt eps) on term 1a.
  => the "z-space oddness bypass" route, taken literally, is a DEAD END.  Do NOT write Lean for it.

  WHAT REMAINS GENUINELY OPEN (unaffected by this check): items (iii)+(iv) are ALREADY banked
  (HCompNearCarryFullyClosed.lean) as ABSTRACT bounds on a near-isometry W's chart-replacement
  difference `||z||^k * |G_tau(Wz) - G_tau(z)|`.  What is still missing -- and is NOT touched by
  either the CoV route (J4-1017-1057, closed) or this oddness route (closed by this script) -- is
  the CONCRETE algebraic identification connecting BRICK 1's literal kPrime closed form (a SINGLE
  Gaussian gaussDdim(tau)(U z x) times Bfac(z), no difference structure at all) to the DIFFERENCE
  shape `G_tau(Wz) - G_tau(z)` that items (iii)/(iv) actually consume -- i.e. producing the
  reference term to subtract (residual r6 in HCompNearCarryKPrimeBaseFieldCoV.lean's own firewall).
  That identification is algebraic/structural (how does a single-Gaussian nb integral get rewritten
  as, or dominated by, a *difference* of two Gaussians?), not a Taylor/parity fact -- and is the
  smallest well-posed next question for this sub-campaign.""")
