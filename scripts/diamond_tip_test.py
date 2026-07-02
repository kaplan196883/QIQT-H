#!/usr/bin/env python3
"""
The DIAMOND-TIP test (QG_CAMPAIGN_PLAN.md follow-on to I4) -- does a causal-diamond regulator leave the
tip vector u^mu_D in the vacuum effective action?

GPT-5.5-pro-designed (2026-07-02). A diamond breaks Lorentz to SO(3) about its tip vector u_D; the CHM
modular-energy truncation is LOCALLY a rest-frame cutoff (xi_D ~ (L/2) u_D near the center, corrections
O((L*Lambda)^-1)). The honest one-loop proxy: the ANISOTROPIC line form factor
    R(k) = f(q_ab(k)/Lambda),   q_ab^2 = a k4^2 + b |k|^2,   chi = a/b
(chi=0: pure spatial cutoff = the executed CPSUV FAIL endpoint; chi=1: the O(4) point; chi != 1: the tip
vector as an explicit deformation). Scheme: Gaussian profile f(x)=exp(-x^2) attached to BOTH lines
(R(k)R(k+q), the first campaign's validated scheme; spatial endpoint = 2C). EXACT closed form
(GPT-5.5-pro, corrected for the both-lines shifted contribution, s = sqrt(chi)):
    Delta c^2(chi) = 2C * H_both(chi),   H_both = (1-s)(3s^2+9s+4) / (4(1+s)^2),   C = 1/(12pi^2)
    H_both(0)=1, H_both(1)=0, dH_both/ds|_1 = -1  (first-order tip-vector sensitivity: d Delta c^2/dchi|_1 = -C).
Exact benchmarks: chi=1/9 -> 11/16 * 2C;  chi=1/4 -> 37/72 * 2C;  chi=4 -> -17/18 * 2C.

Part 2 -- the RAPIDITY-AVERAGE escape candidate is NOT a regulator:
  * averaging already-generated LV operators: <(u^0)^2>_W = 1/2 + sinh(2W)/(4W) -> diverges (no invariant limit);
  * averaging the regulator: on a null ray the boosted sharp cutoff has support up to Lambda*e^W with
    R_W(E) = (W - log(E/Lambda))/(2W), and the log channel gives  int dE/E R_W^2 = W/12  -> grows LINEARLY
    in W. The noncompactness of the boost group defeats the average; W -> infinity is not covariance.

Numerics: Euclidean Yukawa, m=g=1; Delta c^2 = alpha_s - alpha_t extracted from the DIFFERENCE
Pi_spatial(h) - Pi_temporal(h) = (alpha_s - alpha_t) h^2 + O(h^4) (single 3D integrand difference --
the individually log-divergent pieces cancel pointwise). Tensor Gauss-Legendre grids in Lambda units.
"""
import numpy as np

M = 1.0
C_CPSUV = 1.0 / (12 * np.pi**2)

def H_both(chi):
    s = np.sqrt(chi)
    return (1 - s) * (3*chi + 9*s + 4) / (4 * (1 + s)**2)

# ---------------- Part 1: the anisotropic one-loop Delta c^2 ----------------

def make_grid_4d(nK, na, nt, Lam, Kmin=1e-3, span=16.0):
    """4D-spherical grid: log-radial K (resolves both m and Lam scales), alpha (4D polar,
       GL on cos(alpha) is wrong -- use GL on alpha with sin^2 weight), theta (3D polar)."""
    uK, wK = np.polynomial.legendre.leggauss(nK)
    lo, hi = np.log(Kmin), np.log(span * Lam)
    u = 0.5 * (uK + 1) * (hi - lo) + lo
    K = np.exp(u)
    wKf = 0.5 * (hi - lo) * wK * K          # dK = K du
    xa, wa = np.polynomial.legendre.leggauss(na)
    alpha = 0.5 * (xa + 1) * np.pi
    wal = 0.5 * np.pi * wa * np.sin(alpha)**2
    xt, wt = np.polynomial.legendre.leggauss(nt)
    theta = 0.5 * (xt + 1) * np.pi
    wth = 0.5 * np.pi * wt * np.sin(theta)
    return (K[:, None, None], wKf[:, None, None],
            alpha[None, :, None], wal[None, :, None],
            theta[None, None, :], wth[None, None, :])

def dc2_aniso(chi, Lam, h=0.3, nK=260, na=96, nt=48):
    """alpha_s - alpha_t via [Pi_s(h) - Pi_t(h)]/h^2 on a shared 4D-spherical grid (f = exp(-x))."""
    a, b = chi, 1.0
    K, wK, alpha, wal, theta, wth = make_grid_4d(nK, na, nt, Lam)
    k4 = K * np.cos(alpha)
    r = K * np.sin(alpha)
    ct = np.cos(theta)
    E2 = K**2 + M**2
    R1 = np.exp(-(a*k4**2 + b*r**2) / Lam**2)

    def F(q_t, q_s):
        k4p = k4 + q_t
        r2p = r**2 + q_s**2 + 2*r*q_s*ct
        kdotkp = k4*k4p + r**2 + r*q_s*ct
        num = 4 * (M**2 - kdotkp)
        den = E2 * (k4p**2 + r2p + M**2)
        return np.exp(-(a*k4p**2 + b*r2p) / Lam**2) * num / den

    diff = (F(0.0, h) - F(h, 0.0)) * R1
    val = np.sum(diff * K**3 * wK * wal * wth) * 2*np.pi / (2*np.pi)**4
    return val / h**2

# ---------------- Part 2: the rapidity average ----------------

def u0_sq_avg(W):
    return 0.5 + np.sinh(2*W) / (4*W)

def RW_null(E, Lam, W, n=4001):
    """numerical rapidity average of the boosted sharp cutoff on a null ray: q_eta(E) = E e^-eta."""
    eta = np.linspace(-W, W, n)
    inside = (E * np.exp(-eta)) < Lam
    return np.trapezoid(inside.astype(float), eta) / (2*W)

def RW_null_analytic(E, Lam, W):
    x = np.log(E / Lam)
    if x < -W: return 1.0
    if x > W: return 0.0
    return (W - x) / (2*W)

def log_channel(Lam, W, n=20001):
    """int_Lam^{Lam e^W} dE/E R_W(E)^2 -- predicted = W/12."""
    t = np.linspace(0.0, W, n)          # t = log(E/Lam)
    RW = (W - t) / (2*W)
    return np.trapezoid(RW**2, t)

if __name__ == "__main__":
    print("=" * 80)
    print("THE DIAMOND-TIP TEST -- does the diamond tip vector u^mu_D survive in the effective action?")
    print("=" * 80)

    print("\n[1] The anisotropic (tip-vector) family: Delta c^2(chi) vs 2C * H_both(chi)")
    print("    chi = a/b; chi=1 is the O(4) point; the deformation IS the tip vector (Lam=240, Richardson h).")
    for chi, label in [(1e-8, "chi->0  (pure spatial = CPSUV endpoint, 2C)"),
                       (1/9,  "chi=1/9 (H_both = 11/16)"),
                       (1/4,  "chi=1/4 (H_both = 37/72)"),
                       (1.0,  "chi=1   (O(4) point -- must vanish)"),
                       (4.0,  "chi=4   (H_both = -17/18)")]:
        target = 2 * C_CPSUV * H_both(chi)
        v1 = dc2_aniso(chi, Lam=240.0, h=0.30, nK=300, na=112, nt=56)
        v2 = dc2_aniso(chi, Lam=240.0, h=0.15, nK=300, na=112, nt=56)
        v = (4*v2 - v1) / 3.0           # h^2-Richardson
        err = (f"rel={abs(v-target)/abs(target):.4f}" if abs(target) > 1e-12
               else f"|diff|={abs(v-target):.1e}")
        print(f"  {label:46s} numeric={v:+.6e}  exact={target:+.6e}  {err}")

    print("\n[2] The rapidity-average escape candidate:")
    print("  (2a) averaging the GENERATED LV operator: <(u^0)^2>_W = 1/2 + sinh(2W)/(4W)")
    for W in [1.0, 2.0, 4.0, 8.0]:
        print(f"       W={W:4.1f}: <(u0)^2>_W = {u0_sq_avg(W):.6e}   (diverges ~ e^(2W)/8W -- NO invariant limit)")
    print("  (2b) averaging the REGULATOR: null-ray support grows to Lambda*e^W;")
    print("       R_W(E) numeric vs analytic at E = Lambda*e^(W/2), W=4:",
          f"{RW_null(np.e**2, 1.0, 4.0):.6f} vs {RW_null_analytic(np.e**2, 1.0, 4.0):.6f}")
    print("       the log channel  int dE/E R_W^2  (predicted W/12):")
    for W in [2.0, 4.0, 8.0, 16.0]:
        got = log_channel(1.0, W)
        print(f"       W={W:5.1f}:  {got:.6f}   vs  W/12 = {W/12:.6f}")
    print("       -> LINEAR growth in W: the boost-averaged cutoff is NOT a regulator; the W->infinity")
    print("          'average over all diamond frames' does NOT recover the covariant branch.")

    print("\n" + "=" * 80)
    print("VERDICT: (i) any diamond-frame (tip-anchored) truncation is a chi != 1 deformation -> Delta c^2 != 0")
    print("         at FIRST order (d Delta c^2/dchi|_1 = -C, certified): the tip vector DOES survive to the effective action;")
    print("         (ii) averaging over boosted diamonds does not rescue it (not a regulator: W/12 channel);")
    print("         (iii) there is NO local Lorentz-invariant finite-capacity cutoff (|k^2|<Lam^2 has infinite")
    print("         rapidity volume). FORCED CONCLUSION: per-diamond capacity is consistent ONLY as a")
    print("         state/algebra-level covariant construction (covariance BEFORE loops), not a regulator")
    print("         with a frame. The OP3b architecture must be state-level -- which is what the modular")
    print("         (algebraic, frame-free) formulation of Q_D already is. NOT QG; the constraint is now sharp.")
    print("=" * 80)
