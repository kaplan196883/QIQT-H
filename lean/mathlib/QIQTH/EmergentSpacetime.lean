/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# EMERGENT SPACETIME — finite proto-geometry cores (Track B)

Honest, axiom-free Lean cores toward *emergent spacetime* from QIQT-H's finite-capacity substrate —
the Tier-2/Tier-3 "geometry from a finite quantum-information substrate" program (`docs/qg_roadmap/`).
See `FIELDS_AND_SPACETIME_PLAN.md`.

**Honest scope (enforced).** These build finite PROTO-spacetime objects (no-go guards, reconstructed
metrics, capacity/entropy skeletons, causal orders) with explicit error bounds — NOT a
background-independent 4D Lorentzian manifold (open physics). The Jacobson/BW/Sakharov material elsewhere
ASSUMES geometry (Tier 1) and is not emergence evidence. **min-cut is the AREA/entropy primitive, not a
metric** (it violates the triangle inequality). Capacity is a constraint, not a generator.

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic

namespace QIQTH.EmergentSpacetime

open Matrix
open scoped ComplexOrder

section NoGo

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **★★ B0 — the finite exact-continuum no-go guard.**  On a *finite-dimensional* space, a unitary
conjugation cannot *rescale* a nonzero operator.  If `U` is an isometry (`Uᴴ U = 1`, hence unitary on the
finite space) and `U P Uᴴ = r • P` with the squared modulus `star r · r ≠ 1` (i.e. `|r| ≠ 1`), then
`P = 0`.

Reason: unitary conjugation preserves the Hilbert–Schmidt (Frobenius) norm — `Tr(Pᴴ P)` is invariant —
while `r •` rescales it by `|r|² = star r · r`; so `(star r · r) Tr(Pᴴ P) = Tr(Pᴴ P)`, forcing
`Tr(Pᴴ P) = 0`, i.e. `P = 0`.

This is the structural reason a **finite** regional Hilbert space cannot host an *exact* noncompact
continuum symmetry that scales a generator: no exact finite Borchers dilation `Δ^{it} P Δ^{-it} = e^{-ct}P`
(`c ≠ 0`), no exact finite Weyl/boost scaling. Tier-2 emergence must therefore be *approximate / in a
scaling limit*, with quantified error — the honest constraint, not a defect. -/
theorem finiteDim_scaling_forces_zero
    (U P : Matrix n n ℂ) (hU : Uᴴ * U = 1) (r : ℂ) (hr : star r * r ≠ 1)
    (hscale : U * P * Uᴴ = r • P) : P = 0 := by
  -- the conjugated operator's HS norm both equals Tr(Pᴴ P) and equals (star r · r) Tr(Pᴴ P)
  have hmat : (U * P * Uᴴ)ᴴ * (U * P * Uᴴ) = U * (Pᴴ * P) * Uᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U (P * Uᴴ), hU, Matrix.one_mul]
  have e1 : ((U * P * Uᴴ)ᴴ * (U * P * Uᴴ)).trace = (Pᴴ * P).trace := by
    rw [hmat, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have e2 : ((U * P * Uᴴ)ᴴ * (U * P * Uᴴ)).trace = (star r * r) * (Pᴴ * P).trace := by
    rw [hscale]
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul]
    ring
  have key : (Pᴴ * P).trace = (star r * r) * (Pᴴ * P).trace := e1.symm.trans e2
  have htr0 : (Pᴴ * P).trace = 0 := by
    have hzero : ((star r * r) - 1) * (Pᴴ * P).trace = 0 := by
      rw [sub_mul, one_mul, ← key, sub_self]
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd (sub_eq_zero.mp h) hr
    · exact h
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htr0

/-- **★ B0 (corollary) — a nonzero operator cannot be scaled by a finite unitary conjugation.**  If
`U P Uᴴ = r • P` with `P ≠ 0`, then `star r · r = 1` (i.e. `|r| = 1`): the contrapositive of the guard.
So any exact finite "dilation/boost" symmetry acts on a nonzero charge/momentum operator only by a
*phase / unit-modulus* factor — never a genuine rescaling.  The exact noncompact dilation needed for
Borchers' theorem is thus unavailable in finite dimension; it is a continuum / scaling-limit object. -/
theorem scaling_of_nonzero_forces_unit_modulus
    (U P : Matrix n n ℂ) (hU : Uᴴ * U = 1) (r : ℂ) (hP : P ≠ 0)
    (hscale : U * P * Uᴴ = r • P) : star r * r = 1 := by
  by_contra h
  exact hP (finiteDim_scaling_forces_zero U P hU r h hscale)

end NoGo

end QIQTH.EmergentSpacetime
