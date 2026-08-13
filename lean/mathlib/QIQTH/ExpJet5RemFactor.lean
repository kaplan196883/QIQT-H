/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Jet_5 quadratic-remainder -- DIRECTIONAL factoring identity (rung J5-5c, `_P` closing ring)

Banks `factor_hklm`: the pure-real ring identity that folds the fifteen per-direction block
constants of `remAssembly_dir` into `C * (nh * nk * nl * nm)`.  After the concrete `_P` wrapper
instantiates each per-direction scale with its directional value (`Vh := eKs * ‖h‖`,
`Vhk := Cq2 * ‖h‖ * ‖k‖`, `Dh := Cdel * ‖h‖`, `Fh := Cd * ‖h‖`, the triple/`r` scales likewise),
every one of the ~130 monomials in the assembly constant carries exactly the four direction
factors `nh nk nl nm`, so the whole sum factors as `C * (nh nk nl nm)` with `C` the collected
29-term polynomial in the base constants.  Isolating this `ring` here keeps the heavy `_P`
elaboration free of any large `ring`/`whnf`.

Numeric self-check (sympy, random positive atoms): the substituted assembly constant divided by
`nh nk nl nm` is free of the direction norms and equals the collected `C`, relative error `0.0`.

## Honest firewall (binding)

Pure-real algebra ONLY.  Does NOT prove `expJet5_remainder_quadratic_bound_P`,
`expJet5_remainder_quadratic_bound_unif`, `expMap_fderiv4_hasFDerivAt`, `exp ∈ C⁵`, `κ = 1/6`,
the heat-kernel parametrix, or `a₁ = R/6` (CONDITIONAL).
-/

namespace QIQTH.ExpMap

set_option maxHeartbeats 6400000

/-- **Directional factoring identity.**  The fifteen per-direction block constants of
    `remAssembly_dir`, after the `_P` directional substitution, sum to `C * (nh * nk * nl * nm)`
    with `C` the collected 29-term polynomial in the base constants. -/
theorem factor_hklm
    (eKf eKs L2 L3 L4 L5 C2 Kstar2 Kstar3 Kstar4 Kstar5
      Cdel Cd Cq2 Cq3 Ce Ccr VFq Mc Ce0c nh nk nl nm : ℝ) :
    (L2 * eKf ^ 2 * (Mc * nh * nk * nl * nm) + Kstar2 * C2 * (Mc * nh * nk * nl * nm) + Kstar2 * eKs * (Ce0c * nh * nk * nl * nm))
        + (L5 * eKf ^ 2 * ((eKs * nh) * (eKs * nk) * (eKs * nl) * (eKs * nm)) + Kstar5 * C2 * ((eKs * nh) * (eKs * nk) * (eKs * nl) * (eKs * nm))
          + Kstar5 * eKs * (Cdel * nh) * (eKs * nk) * (eKs * nl) * (eKs * nm) + Kstar5 * eKs * (eKs * nh) * (Cdel * nk) * (eKs * nl) * (eKs * nm)
          + Kstar5 * eKs * (eKs * nh) * (eKs * nk) * (Cdel * nl) * (eKs * nm) + Kstar5 * eKs * (eKs * nh) * (eKs * nk) * (eKs * nl) * (Cdel * nm)
          + Kstar4 * (eKs * nh) * (eKs * nk) * (eKs * nl) * (Cd * nm) + Kstar4 * (eKs * nh) * (eKs * nk) * (Cd * nl) * (eKs * nm)
          + Kstar4 * (eKs * nh) * (eKs * nk) * (Cdel * nl) * (Cdel * nm) + 2 * Kstar4 * (eKs * nh) * (eKs * nk) * (Cd * nl) * (eKs * nm)
          + Kstar4 * (eKs * nh) * (Cd * nk) * (eKs * nl) * (eKs * nm) + Kstar4 * (eKs * nh) * (Cdel * nk) * (Cdel * nl) * (eKs * nm)
          + 2 * Kstar4 * (eKs * nh) * (Cd * nk) * (eKs * nl) * (eKs * nm) + Kstar4 * (eKs * nh) * (Cdel * nk) * (eKs * nl) * (Cdel * nm)
          + 2 * Kstar4 * (eKs * nh) * (Cd * nk) * (eKs * nl) * (eKs * nm) + Kstar4 * (Cd * nh) * (eKs * nk) * (eKs * nl) * (eKs * nm)
          + Kstar4 * (Cdel * nh) * (Cdel * nk) * (eKs * nl) * (eKs * nm) + 2 * Kstar4 * (Cd * nh) * (eKs * nk) * (eKs * nl) * (eKs * nm)
          + Kstar4 * (Cdel * nh) * (eKs * nk) * (Cdel * nl) * (eKs * nm) + 2 * Kstar4 * (Cd * nh) * (eKs * nk) * (eKs * nl) * (eKs * nm)
          + Kstar4 * (Cdel * nh) * (eKs * nk) * (eKs * nl) * (Cdel * nm) + 2 * Kstar4 * (Cd * nh) * (eKs * nk) * (eKs * nl) * (eKs * nm))
        + (L4 * eKf ^ 2 * ((eKs * nl) * (eKs * nm)) * (Cq2 * nh * nk) + Kstar4 * C2 * ((eKs * nl) * (eKs * nm)) * (Cq2 * nh * nk)
          + Kstar4 * eKs * (Cdel * nl) * (eKs * nm) * (Cq2 * nh * nk) + Kstar4 * eKs * (eKs * nl) * (Cdel * nm) * (Cq2 * nh * nk)
          + Kstar4 * eKs * (eKs * nl) * (eKs * nm) * (Ce * nh * nk)
          + Kstar3 * (eKs * nl) * (eKs * nm) * (Cd * nh * nk)
          + Kstar3 * (eKs * nl) * (Cd * nm) * (Cq2 * nh * nk) + Kstar3 * (eKs * nl) * (Cdel * nm) * (Ce * nh * nk)
          + 2 * Kstar3 * (eKs * nl) * (Cd * nm) * (Cq2 * nh * nk)
          + Kstar3 * (Cd * nl) * (eKs * nm) * (Cq2 * nh * nk) + Kstar3 * (Cdel * nl) * (Cdel * nm) * (Cq2 * nh * nk)
          + 2 * Kstar3 * (Cd * nl) * (eKs * nm) * (Cq2 * nh * nk) + Kstar3 * (Cdel * nl) * (eKs * nm) * (Ce * nh * nk)
          + 2 * Kstar3 * (Cd * nl) * (eKs * nm) * (Cq2 * nh * nk))
        + (L4 * eKf ^ 2 * ((eKs * nk) * (eKs * nm)) * (Cq2 * nh * nl) + Kstar4 * C2 * ((eKs * nk) * (eKs * nm)) * (Cq2 * nh * nl)
          + Kstar4 * eKs * (Cdel * nk) * (eKs * nm) * (Cq2 * nh * nl) + Kstar4 * eKs * (eKs * nk) * (Cdel * nm) * (Cq2 * nh * nl)
          + Kstar4 * eKs * (eKs * nk) * (eKs * nm) * (Ce * nh * nl)
          + Kstar3 * (eKs * nk) * (eKs * nm) * (Cd * nh * nl)
          + Kstar3 * (eKs * nk) * (Cd * nm) * (Cq2 * nh * nl) + Kstar3 * (eKs * nk) * (Cdel * nm) * (Ce * nh * nl)
          + 2 * Kstar3 * (eKs * nk) * (Cd * nm) * (Cq2 * nh * nl)
          + Kstar3 * (Cd * nk) * (eKs * nm) * (Cq2 * nh * nl) + Kstar3 * (Cdel * nk) * (Cdel * nm) * (Cq2 * nh * nl)
          + 2 * Kstar3 * (Cd * nk) * (eKs * nm) * (Cq2 * nh * nl) + Kstar3 * (Cdel * nk) * (eKs * nm) * (Ce * nh * nl)
          + 2 * Kstar3 * (Cd * nk) * (eKs * nm) * (Cq2 * nh * nl))
        + (L4 * eKf ^ 2 * ((eKs * nk) * (eKs * nl)) * (Cq2 * nh * nm) + Kstar4 * C2 * ((eKs * nk) * (eKs * nl)) * (Cq2 * nh * nm)
          + Kstar4 * eKs * (Cdel * nk) * (eKs * nl) * (Cq2 * nh * nm) + Kstar4 * eKs * (eKs * nk) * (Cdel * nl) * (Cq2 * nh * nm)
          + Kstar4 * eKs * (eKs * nk) * (eKs * nl) * (Ce * nh * nm)
          + Kstar3 * (eKs * nk) * (eKs * nl) * (Cd * nh * nm)
          + Kstar3 * (eKs * nk) * (Cd * nl) * (Cq2 * nh * nm) + Kstar3 * (eKs * nk) * (Cdel * nl) * (Ce * nh * nm)
          + 2 * Kstar3 * (eKs * nk) * (Cd * nl) * (Cq2 * nh * nm)
          + Kstar3 * (Cd * nk) * (eKs * nl) * (Cq2 * nh * nm) + Kstar3 * (Cdel * nk) * (Cdel * nl) * (Cq2 * nh * nm)
          + 2 * Kstar3 * (Cd * nk) * (eKs * nl) * (Cq2 * nh * nm) + Kstar3 * (Cdel * nk) * (eKs * nl) * (Ce * nh * nm)
          + 2 * Kstar3 * (Cd * nk) * (eKs * nl) * (Cq2 * nh * nm))
        + (L4 * eKf ^ 2 * ((eKs * nh) * (eKs * nm)) * (Cq2 * nk * nl) + Kstar4 * C2 * ((eKs * nh) * (eKs * nm)) * (Cq2 * nk * nl)
          + Kstar4 * eKs * (Cdel * nh) * (eKs * nm) * (Cq2 * nk * nl) + Kstar4 * eKs * (eKs * nh) * (Cdel * nm) * (Cq2 * nk * nl)
          + Kstar4 * eKs * (eKs * nh) * (eKs * nm) * (Ce * nk * nl)
          + Kstar3 * (eKs * nh) * (eKs * nm) * (Cd * nk * nl)
          + Kstar3 * (eKs * nh) * (Cd * nm) * (Cq2 * nk * nl) + Kstar3 * (eKs * nh) * (Cdel * nm) * (Ce * nk * nl)
          + 2 * Kstar3 * (eKs * nh) * (Cd * nm) * (Cq2 * nk * nl)
          + Kstar3 * (Cd * nh) * (eKs * nm) * (Cq2 * nk * nl) + Kstar3 * (Cdel * nh) * (Cdel * nm) * (Cq2 * nk * nl)
          + 2 * Kstar3 * (Cd * nh) * (eKs * nm) * (Cq2 * nk * nl) + Kstar3 * (Cdel * nh) * (eKs * nm) * (Ce * nk * nl)
          + 2 * Kstar3 * (Cd * nh) * (eKs * nm) * (Cq2 * nk * nl))
        + (L4 * eKf ^ 2 * ((eKs * nh) * (eKs * nl)) * (Cq2 * nk * nm) + Kstar4 * C2 * ((eKs * nh) * (eKs * nl)) * (Cq2 * nk * nm)
          + Kstar4 * eKs * (Cdel * nh) * (eKs * nl) * (Cq2 * nk * nm) + Kstar4 * eKs * (eKs * nh) * (Cdel * nl) * (Cq2 * nk * nm)
          + Kstar4 * eKs * (eKs * nh) * (eKs * nl) * (Ce * nk * nm)
          + Kstar3 * (eKs * nh) * (eKs * nl) * (Cd * nk * nm)
          + Kstar3 * (eKs * nh) * (Cd * nl) * (Cq2 * nk * nm) + Kstar3 * (eKs * nh) * (Cdel * nl) * (Ce * nk * nm)
          + 2 * Kstar3 * (eKs * nh) * (Cd * nl) * (Cq2 * nk * nm)
          + Kstar3 * (Cd * nh) * (eKs * nl) * (Cq2 * nk * nm) + Kstar3 * (Cdel * nh) * (Cdel * nl) * (Cq2 * nk * nm)
          + 2 * Kstar3 * (Cd * nh) * (eKs * nl) * (Cq2 * nk * nm) + Kstar3 * (Cdel * nh) * (eKs * nl) * (Ce * nk * nm)
          + 2 * Kstar3 * (Cd * nh) * (eKs * nl) * (Cq2 * nk * nm))
        + (L4 * eKf ^ 2 * ((eKs * nh) * (eKs * nk)) * (Cq2 * nl * nm) + Kstar4 * C2 * ((eKs * nh) * (eKs * nk)) * (Cq2 * nl * nm)
          + Kstar4 * eKs * (Cdel * nh) * (eKs * nk) * (Cq2 * nl * nm) + Kstar4 * eKs * (eKs * nh) * (Cdel * nk) * (Cq2 * nl * nm)
          + Kstar4 * eKs * (eKs * nh) * (eKs * nk) * (Ce * nl * nm)
          + Kstar3 * (eKs * nh) * (eKs * nk) * (Cd * nl * nm)
          + Kstar3 * (eKs * nh) * (Cd * nk) * (Cq2 * nl * nm) + Kstar3 * (eKs * nh) * (Cdel * nk) * (Ce * nl * nm)
          + 2 * Kstar3 * (eKs * nh) * (Cd * nk) * (Cq2 * nl * nm)
          + Kstar3 * (Cd * nh) * (eKs * nk) * (Cq2 * nl * nm) + Kstar3 * (Cdel * nh) * (Cdel * nk) * (Cq2 * nl * nm)
          + 2 * Kstar3 * (Cd * nh) * (eKs * nk) * (Cq2 * nl * nm) + Kstar3 * (Cdel * nh) * (eKs * nk) * (Ce * nl * nm)
          + 2 * Kstar3 * (Cd * nh) * (eKs * nk) * (Cq2 * nl * nm))
        + (L3 * eKf ^ 2 * ((Cq2 * nh * nk) * (Cq2 * nl * nm)) + Kstar3 * C2 * ((Cq2 * nh * nk) * (Cq2 * nl * nm))
          + Kstar3 * eKs * (Ce * nh * nk) * (Cq2 * nl * nm) + Kstar3 * eKs * (Cq2 * nh * nk) * (Ce * nl * nm)
          + Kstar2 * (Cq2 * nh * nk) * (Cd * nl * nm) + Kstar2 * (Ccr * nh * nk) * (Ccr * nl * nm) + Kstar2 * (Cq3 * nh * nk) * (Cd * nl * nm)
          + Kstar2 * (Cd * nh * nk) * (Cq2 * nl * nm) + Kstar2 * (Cd * nh * nk) * (Cq3 * nl * nm) + Kstar2 * (Cd * nh * nk) * (VFq * nl * nm))
        + (L3 * eKf ^ 2 * ((Cq2 * nh * nl) * (Cq2 * nk * nm)) + Kstar3 * C2 * ((Cq2 * nh * nl) * (Cq2 * nk * nm))
          + Kstar3 * eKs * (Ce * nh * nl) * (Cq2 * nk * nm) + Kstar3 * eKs * (Cq2 * nh * nl) * (Ce * nk * nm)
          + Kstar2 * (Cq2 * nh * nl) * (Cd * nk * nm) + Kstar2 * (Ccr * nh * nl) * (Ccr * nk * nm) + Kstar2 * (Cq3 * nh * nl) * (Cd * nk * nm)
          + Kstar2 * (Cd * nh * nl) * (Cq2 * nk * nm) + Kstar2 * (Cd * nh * nl) * (Cq3 * nk * nm) + Kstar2 * (Cd * nh * nl) * (VFq * nk * nm))
        + (L3 * eKf ^ 2 * ((Cq2 * nh * nm) * (Cq2 * nk * nl)) + Kstar3 * C2 * ((Cq2 * nh * nm) * (Cq2 * nk * nl))
          + Kstar3 * eKs * (Ce * nh * nm) * (Cq2 * nk * nl) + Kstar3 * eKs * (Cq2 * nh * nm) * (Ce * nk * nl)
          + Kstar2 * (Cq2 * nh * nm) * (Cd * nk * nl) + Kstar2 * (Ccr * nh * nm) * (Ccr * nk * nl) + Kstar2 * (Cq3 * nh * nm) * (Cd * nk * nl)
          + Kstar2 * (Cd * nh * nm) * (Cq2 * nk * nl) + Kstar2 * (Cd * nh * nm) * (Cq3 * nk * nl) + Kstar2 * (Cd * nh * nm) * (VFq * nk * nl))
        + (L3 * eKf ^ 2 * ((eKs * nh) * (Cq3 * nk * nl * nm)) + Kstar3 * C2 * ((eKs * nh) * (Cq3 * nk * nl * nm))
          + Kstar3 * eKs * (Cdel * nh) * (Cq3 * nk * nl * nm) + Kstar3 * eKs * (eKs * nh) * (Ce * nk * nl * nm)
          + Kstar2 * (Cdel * nh) * (Ce * nk * nl * nm) + 2 * Kstar2 * (Cd * nh) * (Cq3 * nk * nl * nm)
          + Kstar2 * (Cd * nh) * (Cq3 * nk * nl * nm) + Kstar2 * (eKs * nh) * (Cd * nk * nl * nm))
        + (L3 * eKf ^ 2 * ((eKs * nk) * (Cq3 * nh * nl * nm)) + Kstar3 * C2 * ((eKs * nk) * (Cq3 * nh * nl * nm))
          + Kstar3 * eKs * (Cdel * nk) * (Cq3 * nh * nl * nm) + Kstar3 * eKs * (eKs * nk) * (Ce * nh * nl * nm)
          + Kstar2 * (Cdel * nk) * (Ce * nh * nl * nm) + 2 * Kstar2 * (Cd * nk) * (Cq3 * nh * nl * nm)
          + Kstar2 * (Cd * nk) * (Cq3 * nh * nl * nm) + Kstar2 * (eKs * nk) * (Cd * nh * nl * nm))
        + (L3 * eKf ^ 2 * ((eKs * nl) * (Cq3 * nh * nk * nm)) + Kstar3 * C2 * ((eKs * nl) * (Cq3 * nh * nk * nm))
          + Kstar3 * eKs * (Cdel * nl) * (Cq3 * nh * nk * nm) + Kstar3 * eKs * (eKs * nl) * (Ce * nh * nk * nm)
          + Kstar2 * (Cdel * nl) * (Ce * nh * nk * nm) + 2 * Kstar2 * (Cd * nl) * (Cq3 * nh * nk * nm)
          + Kstar2 * (Cd * nl) * (Cq3 * nh * nk * nm) + Kstar2 * (eKs * nl) * (Cd * nh * nk * nm))
        + (L3 * eKf ^ 2 * ((eKs * nm) * (Cq3 * nh * nk * nl)) + Kstar3 * C2 * ((eKs * nm) * (Cq3 * nh * nk * nl))
          + Kstar3 * eKs * (Cdel * nm) * (Cq3 * nh * nk * nl) + Kstar3 * eKs * (eKs * nm) * (Ce * nh * nk * nl)
          + Kstar2 * (Cdel * nm) * (Ce * nh * nk * nl) + 2 * Kstar2 * (Cd * nm) * (Cq3 * nh * nk * nl)
          + Kstar2 * (Cd * nm) * (Cq3 * nh * nk * nl) + Kstar2 * (eKs * nm) * (Cd * nh * nk * nl))
      = (3*C2*Cq2^2*Kstar3 + 6*C2*Cq2*Kstar4*eKs^2 + 4*C2*Cq3*Kstar3*eKs + C2*Kstar2*Mc + C2*Kstar5*eKs^4 + 3*Ccr^2*Kstar2 + 6*Cd*Cq2*Kstar2 + 48*Cd*Cq2*Kstar3*eKs + 18*Cd*Cq3*Kstar2 + 3*Cd*Kstar2*VFq + 4*Cd*Kstar2*eKs + 6*Cd*Kstar3*eKs^2 + 16*Cd*Kstar4*eKs^3 + 6*Cdel^2*Cq2*Kstar3 + 6*Cdel^2*Kstar4*eKs^2 + 4*Cdel*Ce*Kstar2 + 12*Cdel*Ce*Kstar3*eKs + 12*Cdel*Cq2*Kstar4*eKs^2 + 4*Cdel*Cq3*Kstar3*eKs + 4*Cdel*Kstar5*eKs^4 + 6*Ce*Cq2*Kstar3*eKs + 4*Ce*Kstar3*eKs^2 + 6*Ce*Kstar4*eKs^3 + Ce0c*Kstar2*eKs + 3*Cq2^2*L3*eKf^2 + 6*Cq2*L4*eKf^2*eKs^2 + 4*Cq3*L3*eKf^2*eKs + L2*Mc*eKf^2 + L5*eKf^2*eKs^4) * (nh * nk * nl * nm) := by ring

end QIQTH.ExpMap
