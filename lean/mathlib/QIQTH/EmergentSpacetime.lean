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

section Metric

/-- An **approximate pseudometric** with slack `ε`: nonnegative, zero on the diagonal, symmetric, and
triangle up to `ε`.  `ε = 0` is an exact pseudometric.  This is the target type for any *emergent-distance
reconstruction* from the substrate's entanglement data — every reconstruction must be tagged with the `ε`
its error bound provides. -/
structure IsApproxPseudometric (ε : ℝ) {X : Type*} (d : X → X → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ d x y
  self : ∀ x, d x x = 0
  symm : ∀ x y, d x y = d y x
  triangle : ∀ x y z, d x z ≤ d x y + d y z + ε

/-- A 3-point "area / cut" function with the min-cut counterexample values: `λ(x,y)=λ(y,z)=2`,
`λ(x,z)=5` (and `0` on the diagonal, symmetric). -/
def cutEx : Fin 3 → Fin 3 → ℝ := fun i j => if i = j then 0 else if i.val + j.val = 2 then 5 else 2

/-- **★★ B1 — min-cut / RT-area is NOT a metric (the corrected-roadmap guard).**  There is a
nonnegative, symmetric, zero-diagonal "area / capacity" function (the shape of an RT/min-cut entanglement
area) that **violates the triangle inequality** — so min-cut area cannot be used as the emergent
*distance* (the error in the earlier Tier-3 §3.1 recipe).  Witness: `cutEx` with `λ(0,1)=λ(1,2)=2` but
`λ(0,2)=5 > 2+2`.  Distance must instead be reconstructed by a provably-metric rule (see
`embedDist_isPseudometric`); min-cut keeps its correct role as the *area/entropy* primitive. -/
theorem minCut_area_not_metric :
    ∃ (X : Type) (d : X → X → ℝ),
      (∀ x y, 0 ≤ d x y) ∧ (∀ x, d x x = 0) ∧ (∀ x y, d x y = d y x) ∧
      ¬ (∀ x y z, d x z ≤ d x y + d y z) := by
  refine ⟨Fin 3, cutEx, ?_, ?_, ?_, ?_⟩
  · intro x y; unfold cutEx; split_ifs <;> norm_num
  · intro x; unfold cutEx; rw [if_pos rfl]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [cutEx]
  · intro h
    have h12 := h 0 1 2
    have e02 : cutEx 0 2 = 5 := by simp [cutEx]
    have e01 : cutEx 0 1 = 2 := by simp [cutEx]
    have e12 : cutEx 1 2 = 2 := by simp [cutEx]
    rw [e02, e01, e12] at h12
    norm_num at h12

/-- A **metric-valid reconstruction**: the `L¹` / coordinate-embedding distance `d(x,y) = |f x − f y|`
pulled back from a reconstructed real "coordinate" `f`.  This is the 1-D case of the cut-cone / `L¹`
embedding reconstruction (a *genuine* metric, unlike raw min-cut). -/
def embedDist {X : Type*} (f : X → ℝ) : X → X → ℝ := fun x y => |f x - f y|

/-- **★★ B1 — the embedding reconstruction is an exact pseudometric.**  `embedDist f` satisfies all the
metric axioms (it is pulled back from `ℝ` along `f`): the honest, provably-metric replacement for the
min-cut "distance".  An emergent *coordinate* `f` (reconstructed from the substrate) yields an emergent
*distance* that really is one — with `ε = 0` (exact), the cleanest first Tier-3 reconstruction. -/
theorem embedDist_isPseudometric {X : Type*} (f : X → ℝ) :
    IsApproxPseudometric 0 (embedDist f) where
  nonneg := fun x y => abs_nonneg _
  self := fun x => by simp [embedDist]
  symm := fun x y => by rw [embedDist, embedDist, abs_sub_comm]
  triangle := fun x y z => by
    have := abs_sub_le (f x) (f y) (f z)
    simp only [embedDist, add_zero]
    linarith

end Metric

end QIQTH.EmergentSpacetime
