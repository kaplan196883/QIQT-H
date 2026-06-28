/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# ELECTRON_FIELD_PLAN E1 (spinor core) — the Dirac gamma / Clifford algebra `{γ^μ, γ^ν} = 2 η^{μν}`

The electron field is a Dirac **spinor**, and its spin/Lorentz structure is governed by the **Clifford
algebra** of the spacetime metric: the gamma matrices `γ^μ` satisfy the defining anticommutation
relation
```
   {γ^μ, γ^ν} = 2 η^{μν}.
```
This module realizes the Dirac gamma operators as the Clifford generators `ι` of a real quadratic space
`(M, Q)` (with `Q = η` the Minkowski metric), and records the defining relations directly from Mathlib's
`CliffordAlgebra`.  This is the **spinor-representation core of E1** — the algebraic skeleton on which
the Dirac one-particle space and the `S_D = (iγ·∂ + m)Δ_m` causal anticommutator are built.

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`, or fewer).  No `sorry`.

HONEST scope (ELECTRON_FIELD_PLAN §1): this lands the **gamma / Clifford algebra** (the spin–Lorentz
structure).  The full Dirac one-particle Hilbert space — the positive/negative-energy (particle/
antiparticle) splitting, the Dirac inner product, the Wigner one-particle Poincaré representation — and
the causal anticommutator kernel `S_D = (iγ·∂ + m)Δ_m` (which need the field in momentum space) remain
the E1 frontier (checkpointed).  Free Dirac only.
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NoncommRing

namespace QIQTH.Fock.Dirac

variable {M : Type*} [AddCommGroup M] [Module ℝ M] (Q : QuadraticForm ℝ M)

/-- The **Dirac gamma operator** in direction `v` of a real quadratic space `(M, Q)` — the Clifford
generator `ι Q v`.  For an orthonormal basis `{e_μ}` of the Minkowski metric `Q = η`, the Dirac gamma
matrices are `γ_μ = diracGamma Q e_μ`. -/
noncomputable def diracGamma (v : M) : CliffordAlgebra Q := CliffordAlgebra.ι Q v

/-- `γ(v)² = η(v) = Q v` (a scalar): the squared gamma in a direction is that direction's metric norm.
For a unit timelike/spacelike basis vector this is the diagonal `η_μμ = ±1`. -/
theorem diracGamma_sq (v : M) :
    diracGamma Q v * diracGamma Q v = algebraMap ℝ (CliffordAlgebra Q) (Q v) := by
  unfold diracGamma; exact CliffordAlgebra.ι_sq_scalar Q v

/-- **The Dirac/Clifford anticommutation relation `{γ_a, γ_b} = 2 η(a,b)`.**  The defining relation of
the spinor representation: the symmetric product of two gamma operators is the scalar
`polar Q a b = Q(a+b) − Q a − Q b = 2 η(a,b)`. -/
theorem diracGamma_anticomm (a b : M) :
    diracGamma Q a * diracGamma Q b + diracGamma Q b * diracGamma Q a
      = algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q a b) := by
  unfold diracGamma; exact CliffordAlgebra.ι_mul_ι_add_swap a b

/-- Distinct (orthogonal) gamma directions anticommute to zero: `{γ_μ, γ_ν} = 0` for `η_μν = 0`
(`μ ≠ ν`). -/
theorem diracGamma_anticomm_ortho {a b : M} (h : Q.IsOrtho a b) :
    diracGamma Q a * diracGamma Q b + diracGamma Q b * diracGamma Q a = 0 := by
  unfold diracGamma; exact CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho h

/-- For orthogonal directions the gammas **anticommute**: `γ_μ γ_ν = − γ_ν γ_μ` (`μ ≠ ν`). -/
theorem diracGamma_swap_ortho {a b : M} (h : Q.IsOrtho a b) :
    diracGamma Q a * diracGamma Q b = -(diracGamma Q b * diracGamma Q a) := by
  unfold diracGamma; exact CliffordAlgebra.ι_mul_ι_comm_of_isOrtho h

/-! ### The Clifford ℤ₂-grading: single gammas are odd, the Lorentz generators are even

The Clifford algebra carries a `ℤ₂`-grading `evenOdd Q i` parallel to the CAR parity `Γ = (−1)^F`
(`QIQTH/Fock/Dirac/Parity.lean`).  A single gamma `γ_μ` is **odd**; a product of two gammas — and hence
the **Lorentz generator** `σ_ab = γ_a γ_b − γ_b γ_a` (∝ the spin generator `σ_μν = (i/4)[γ_μ,γ_ν]`) — is
**even**.  So the spinor representation of the Lorentz group sits in the even Clifford subalgebra: the
gamma-side of the even/odd structure that is the ELECTRON_FIELD_PLAN crux. -/

/-- A single Dirac gamma is **odd** (grade 1) in the Clifford `ℤ₂`-grading. -/
theorem diracGamma_mem_odd (v : M) : diracGamma Q v ∈ CliffordAlgebra.evenOdd Q 1 := by
  unfold diracGamma; exact CliffordAlgebra.ι_mem_evenOdd_one Q v

/-- A product of two gammas is **even** (grade 0): the bilinear / even Clifford sector. -/
theorem diracGamma_mul_mem_even (a b : M) :
    diracGamma Q a * diracGamma Q b ∈ CliffordAlgebra.evenOdd Q 0 := by
  unfold diracGamma; exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero Q a b

/-- The **Dirac Lorentz generator** `σ_ab = γ_a γ_b − γ_b γ_a` (the commutator `[γ_a, γ_b]`, ∝ the spin
generator `σ_μν = (i/4)[γ_μ,γ_ν]` of the Lorentz spinor representation). -/
noncomputable def diracSigma (a b : M) : CliffordAlgebra Q :=
  diracGamma Q a * diracGamma Q b - diracGamma Q b * diracGamma Q a

/-- **The Lorentz generators live in the EVEN Clifford subalgebra.**  `σ_ab ∈ evenOdd Q 0`: the spinor
representation of the Lorentz group sits in the even part of the Clifford `ℤ₂`-grading (while single
gammas are odd) — the gamma-side parallel of the CAR parity grading `Γ = (−1)^F`. -/
theorem diracSigma_mem_even (a b : M) : diracSigma Q a b ∈ CliffordAlgebra.evenOdd Q 0 := by
  unfold diracSigma
  exact Submodule.sub_mem _ (diracGamma_mul_mem_even Q a b) (diracGamma_mul_mem_even Q b a)

/-- **The Lorentz generator is antisymmetric in its indices**: `σ_ab = − σ_ba`.  The defining
antisymmetry of the spin/Lorentz generators `σ_μν` (so `σ_μμ = 0`, and the independent generators are the
6 = 3 rotations + 3 boosts of `σ_{μν}`, `μ < ν`).  Immediate from `σ_ab = [γ_a, γ_b]`. -/
theorem diracSigma_antisymm (a b : M) : diracSigma Q a b = -(diracSigma Q b a) := by
  unfold diracSigma; abel

/-- **For orthogonal directions the Lorentz generator is `σ_ab = 2 γ_a γ_b`.**  When `η(a,b) = 0` the
gammas anticommute (`diracGamma_swap_ortho`), so the commutator `σ_ab = γ_a γ_b − γ_b γ_a` collapses to
twice the product.  In particular the boost generator `σ_{0i} = 2 γ_0 γ_i` (time ⟂ space) — the spinor
representation of the Rindler boost whose flow is the electron's modular `Δ^{it}` (E1/E9). -/
theorem diracSigma_ortho {a b : M} (h : Q.IsOrtho a b) :
    diracSigma Q a b = diracGamma Q a * diracGamma Q b + diracGamma Q a * diracGamma Q b := by
  unfold diracSigma
  have hh : diracGamma Q b * diracGamma Q a = -(diracGamma Q a * diracGamma Q b) := by
    rw [diracGamma_swap_ortho Q h, neg_neg]
  rw [hh, sub_neg_eq_add]

/-- **The Lorentz generator squares to a scalar: `σ_ab² = −4·η(a)·η(b)` (orthogonal `a ⟂ b`).**  Since
`σ_ab = 2γ_aγ_b` and `(γ_aγ_b)² = −γ_a²γ_b² = −η(a)η(b)`, the spin generator squares to the *scalar*
`−4·Q(a)·Q(b)`.  This **distinguishes boosts from rotations**: with the Minkowski metric `η = (+,−,−,−)`,
the **boost** generator `σ_{0i}` has `η(e₀)η(eᵢ) = (+1)(−1) = −1`, so `σ_{0i}² = +4 > 0` (non-compact,
*hyperbolic* — the generator of the unbounded Rindler boost, whose `Δ^{it}` is the modular flow); a
**rotation** `σ_{ij}` has `η(eᵢ)η(eⱼ) = (−1)(−1) = +1`, so `σ_{ij}² = −4 < 0` (compact, *elliptic*).  The
sign of `σ²` is exactly the boost-vs-rotation (non-compact-vs-compact) dichotomy of the Lorentz spin
generators. -/
theorem diracSigma_sq_ortho {a b : M} (h : Q.IsOrtho a b) :
    diracSigma Q a b * diracSigma Q a b
      = algebraMap ℝ (CliffordAlgebra Q) (-(4 * Q a * Q b)) := by
  have hba : diracGamma Q b * diracGamma Q a = -(diracGamma Q a * diracGamma Q b) := by
    rw [diracGamma_swap_ortho Q h, neg_neg]
  have key : (diracGamma Q a * diracGamma Q b) * (diracGamma Q a * diracGamma Q b)
      = algebraMap ℝ (CliffordAlgebra Q) (-(Q a * Q b)) := by
    have e1 : (diracGamma Q a * diracGamma Q b) * (diracGamma Q a * diracGamma Q b)
        = diracGamma Q a * (diracGamma Q b * diracGamma Q a) * diracGamma Q b := by noncomm_ring
    rw [e1, hba]
    have e2 : diracGamma Q a * -(diracGamma Q a * diracGamma Q b) * diracGamma Q b
        = -((diracGamma Q a * diracGamma Q a) * (diracGamma Q b * diracGamma Q b)) := by noncomm_ring
    rw [e2, diracGamma_sq, diracGamma_sq, ← map_mul, ← map_neg]
  rw [diracSigma_ortho Q h,
      show (diracGamma Q a * diracGamma Q b + diracGamma Q a * diracGamma Q b)
          * (diracGamma Q a * diracGamma Q b + diracGamma Q a * diracGamma Q b)
        = (diracGamma Q a * diracGamma Q b) * (diracGamma Q a * diracGamma Q b)
          + (diracGamma Q a * diracGamma Q b) * (diracGamma Q a * diracGamma Q b)
          + (diracGamma Q a * diracGamma Q b) * (diracGamma Q a * diracGamma Q b)
          + (diracGamma Q a * diracGamma Q b) * (diracGamma Q a * diracGamma Q b) from by noncomm_ring,
      key, ← map_add, ← map_add, ← map_add]
  congr 1
  ring

end QIQTH.Fock.Dirac
