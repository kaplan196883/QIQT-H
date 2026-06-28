/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# ELECTRON_FIELD_PLAN E1/E9 — the Dirac/Clifford relation, GROUNDED in PhysLean's gamma matrices

QIQT-H's `QIQTH/Fock/Dirac/DiracGamma.lean` works **abstractly** with `CliffordAlgebra Q` for a general
quadratic form — `diracGamma`, `diracSigma = [γ_a,γ_b]`, the spin–statistics dichotomy `(γ_aγ_b)² = ∓1`
(rotation vs boost), and the vector-covariance of `σ_ab`.  PhysLean's `Physlib.Relativity.CliffordAlgebra`
provides the **concrete** 4×4 Dirac-representation gamma matrices `γ0,…,γ3 : Matrix (Fin 4) (Fin 4) ℂ`
(with `γ0²=1`, `γi²=−1`, and the off-diagonal anticommutation `γμγν=−γνγμ`).

This is the **third PhysLean bridge** (after the Dirac CAR/`WickAlgebra` one and the photon EM one): it
packages PhysLean's per-pair facts into the single **Clifford/Dirac anticommutation relation**

  `{γ_μ, γ_ν} = γ_μγ_ν + γ_νγ_μ = 2 η_μν · 1`,   η = diag(+1,−1,−1,−1)  (Minkowski, mostly-minus),

the concrete realization of the abstract relation `DiracGamma.diracGamma_mul_add` proves for a general
`CliffordAlgebra Q`.  So the electron's Clifford structure is now grounded in PhysLean's reviewed concrete
Dirac representation, not only QIQT-H's abstract Clifford layer.

HONEST scope: this is the algebraic Clifford relation of the concrete γ matrices (free Dirac).  The
one-particle Dirac propagator `S_D=(iγ·∂+m)Δ_m`, its microcausality (inheriting the scalar Pauli–Jordan
spacelike wall), and the Belinfante `T_μν → 2πK_boost → Jacobson` chain remain the labelled E1/E9
frontier.  Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.  Free Dirac only.
-/
import Physlib.Relativity.CliffordAlgebra

namespace QIQTH.Fock.Dirac

open spaceTime

/-- The **Minkowski metric** `η = diag(+1,−1,−1,−1)` (mostly-minus signature) as a `ℂ`-valued function on
`Fin 4 × Fin 4`, the right-hand side of the Dirac anticommutation relation. -/
def minkowskiEta (μ ν : Fin 4) : ℂ := if μ = ν then (if μ = 0 then 1 else -1) else 0

/-- **The square of a concrete gamma matrix is the diagonal metric**: `γ_μ γ_μ = η_μμ · 1`
(`γ0²=1`, `γi²=−1`), packaging PhysLean's `γ0_mul_γ0`, `γ1_mul_γ1`, `γ2_mul_γ2`, `γ3_mul_γ3`. -/
theorem gamma_sq_eq_eta (μ : Fin 4) : γ μ * γ μ = minkowskiEta μ μ • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  fin_cases μ <;>
    simp [γ, minkowskiEta, γ0_mul_γ0, γ1_mul_γ1, γ2_mul_γ2, γ3_mul_γ3]

/-- **★ The Clifford/Dirac anticommutation relation on PhysLean's concrete gamma matrices:**
`{γ_μ, γ_ν} = γ_μγ_ν + γ_νγ_μ = 2 η_μν · 1`, with `η = diag(+1,−1,−1,−1)`.  This is the concrete realization
of the abstract Clifford relation (`DiracGamma.diracGamma_mul_add`, `γ_a γ_b + γ_b γ_a = 2·polar Q a b`) on
PhysLean's reviewed Dirac representation — the defining relation of the Dirac algebra, the algebraic seed of
microcausality (spacelike-separated Dirac fields anticommute) and of the spinor Lorentz generators
`σ_μν=[γ_μ,γ_ν]`. -/
theorem gamma_anticomm (μ ν : Fin 4) :
    γ μ * γ ν + γ ν * γ μ = (2 * minkowskiEta μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  fin_cases μ <;> fin_cases ν <;>
    simp [γ, minkowskiEta,
      γ0_mul_γ0, γ1_mul_γ1, γ2_mul_γ2, γ3_mul_γ3,
      γ1_mul_γ0, γ2_mul_γ0, γ3_mul_γ0, γ2_mul_γ1, γ3_mul_γ1, γ3_mul_γ2] <;>
    module

end QIQTH.Fock.Dirac
