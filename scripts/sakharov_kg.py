#!/usr/bin/env python3
"""Sakharov / induced-gravity derivation of the Bekenstein-Hawking 1/4 for the free KG field.

Reproduces the Susskind-Uglum (1994) / Jacobson (1994) result: for a free scalar, the vacuum
ENTANGLEMENT ENTROPY across a surface and the INDUCED Newton constant come from the SAME UV
divergence, so their ratio is exactly 1/4 -- the cutoff CANCELS and the 1/4 is cutoff-independent.

This is the SYMBOLIC verification (Stage A of SAKHAROV_KG_PLAN.md).  It is a check of KNOWN physics;
the QIQT-H novelty (Stage B) is the finiteness regulator + the circularity audit, not the 1/4 value.

Honest scope: free, minimally-coupled scalar in 4D.  The individual coefficients (48pi, 12pi) are
scheme-dependent; only the RATIO 1/4 is robust, and -- as the script makes explicit -- the 1/4 is
the purely GEOMETRIC ratio (conical-deficit 4pi) / (Einstein-Hilbert normalization 16pi), the SAME
for every matter species (which is why the Bekenstein-Hawking 1/4 is universal).  The matter enters
only through the common factor 1/G_ind, which cancels in the ratio.
"""

import sympy as sp


def main() -> None:
    eps, A = sp.symbols("epsilon A", positive=True)   # UV cutoff, boundary area
    n = sp.symbols("n", positive=True)                # replica index

    # ---- 1.  Heat kernel (Seeley-DeWitt) of the scalar Laplacian in 4D -------------------------
    # Tr e^{-t Delta} = (4 pi t)^{-2} * Int sqrt(g) ( a0 + a1 t + ... ),  a0 = 1,  a1 = (1/6 - xi) R.
    # Minimal coupling xi = 0  =>  a1 = R/6.  The coefficient of R is:
    a1_R = sp.Rational(1, 6)

    # ---- 2.  Induced Newton constant (Sakharov) -----------------------------------------------
    # One-loop effective action  W = -(1/2) Int_{eps^2}^inf dt/t  Tr e^{-t Delta}.
    # The R-term:  W ⊃ -(1/2) (4 pi)^{-2} a1_R R  Int_{eps^2}^inf dt / t^2  = -(1/2)(4 pi)^{-2} a1_R R / eps^2.
    # Identify with the induced Einstein-Hilbert term  -(1/(16 pi G_ind)) Int sqrt(g) R :
    inv_16piG = sp.Rational(1, 2) * (4 * sp.pi) ** (-2) * a1_R / eps**2     # = 1/(16 pi G_ind)
    inv_G_ind = sp.simplify(16 * sp.pi * inv_16piG)                        # = 1/G_ind
    print(f"1/G_ind            = {inv_G_ind}")          # expect 1/(12 pi eps^2)
    assert sp.simplify(inv_G_ind - 1 / (12 * sp.pi * eps**2)) == 0

    # ---- 3.  Entanglement entropy (conical-deficit / replica) ----------------------------------
    # A conical singularity of deficit angle 2 pi (1 - n) on the surface Sigma (area A) carries a
    # delta-function curvature:  Int sqrt(g) R  ⊃  4 pi (1 - n) A.
    # So the induced EH action on the cone is  I_n ⊃ (1/(16 pi G_ind)) * 4 pi (1 - n) A.
    I_conical = inv_16piG * 4 * sp.pi * (1 - n) * A
    # Replica:  S_ent = (n d/dn - 1) ( -I_n ) |_{n=1}  =  (1 - n d/dn) I_n |_{n=1}.
    S_ent = sp.simplify((I_conical - n * sp.diff(I_conical, n)).subs(n, 1))
    print(f"S_ent              = {S_ent}")             # expect A/(48 pi eps^2)
    assert sp.simplify(S_ent - A / (48 * sp.pi * eps**2)) == 0

    # ---- 4.  The ratio: the 1/4 (cutoff- and matter-independent) -------------------------------
    ratio = sp.simplify(S_ent / (A * inv_G_ind))      # = S_ent / (A * (1/G_ind))
    print(f"S_ent/(A/G_ind)    = {ratio}            <-- the 1/4")
    assert ratio == sp.Rational(1, 4)

    # the SAME 1/4 as a purely geometric ratio: conical-deficit (4 pi) / EH normalization (16 pi)
    geometric_quarter = sp.Rational(4, 16)            # = (conical 4pi) / (EH 16pi)
    print(f"geometric 1/4      = {geometric_quarter}  =  (conical 4 pi) / (EH 16 pi)")
    assert geometric_quarter == sp.Rational(1, 4)

    # the Bekenstein-Hawking form  S = A / (4 G_ind),  the eps having cancelled in the ratio
    S_BH = sp.simplify(A * inv_G_ind / 4)
    print(f"A/(4 G_ind)        = {S_BH}")
    assert sp.simplify(S_ent - S_BH) == 0

    print("\nOK -- S_ent = A/(4 G_ind);  the 1/4 = (conical 4 pi)/(EH 16 pi) is cutoff- and "
          "matter-independent (the universal Bekenstein-Hawking coefficient).")


if __name__ == "__main__":
    main()
