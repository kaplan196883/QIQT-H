/-
  E2 (MICROTHEORY_EARNS_GRAVITY_PLAN.md) — the explicit decoder: the metric reconstructed FROM the code's area data.

  A2 supplied the map h ↦ (area data) and proved it injective on symmetric perturbations
  (`area_probes_separate`). This module INVERTS it explicitly: from the ray-probe area measurements
  `A(v) = δA_ray(v)(h) = ½ h(v,v)` alone, the decoder
      h_ii = 2·A(e_i),   h_ij = A(e_i+e_j) − A(e_i) − A(e_j)   (polarization)
  returns the perturbation: `reconstruct (areaData h) = h` for symmetric `h`. THE METRIC IS A FUNCTION OF THE
  CODE'S AREA DATA — the emergent `h` can be *defined* from area measurements, and A1's `einsteinSymbol` applies
  to it verbatim.

  ⚠ Honest labels (verifier-binding): POINTWISE tensor reconstruction in a chosen basis — NOT a smooth global
  metric field; symmetry is REQUIRED (for general h the off-diagonal formula returns the symmetric part);
  vector-indexed probes (the `raySurf v` of A2 is vector-level, quadratically homogeneous — no projective
  quotient). Linearized, finite/model level.
-/
import Mathlib
import QIQTH.AreaEmergence

namespace QIQTH.AreaMap

open QIQTH.GravDyn

/-- The `i`-th coordinate basis vector. -/
def basisVec (i : Fin 4) : Fin 4 → ℝ := fun j => if j = i then 1 else 0

/-- **The decoder**: from ray-probe area data `A`, rebuild the tensor —
    `h_ii = 2A(e_i)`, `h_ij = A(e_i+e_j) − A(e_i) − A(e_j)`. -/
noncomputable def reconstruct (A : (Fin 4 → ℝ) → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j =>
    if i = j then 2 * A (basisVec i)
    else A (fun k => basisVec i k + basisVec j k) - A (basisVec i) - A (basisVec j)

/-- **E2 — the metric IS a function of the code's area data.** For a symmetric perturbation, the decoder applied
    to its ray-probe area measurements returns the perturbation itself: `reconstruct (v ↦ δA_ray(v)(h)) = h`.
    The inverse of A2's emergence map, explicit. -/
theorem reconstruct_areaVar (h : Matrix (Fin 4) (Fin 4) ℝ) (hSym : h.IsSymm) :
    reconstruct (fun v => areaVar (raySurf v) h) = h := by
  have h01 : h 1 0 = h 0 1 := hSym.apply 0 1
  have h02 : h 2 0 = h 0 2 := hSym.apply 0 2
  have h03 : h 3 0 = h 0 3 := hSym.apply 0 3
  have h12 : h 2 1 = h 1 2 := hSym.apply 1 2
  have h13 : h 3 1 = h 1 3 := hSym.apply 1 3
  have h23 : h 3 2 = h 2 3 := hSym.apply 2 3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reconstruct, areaVar_ray, quadForm, basisVec, Fin.sum_univ_four] <;>
    linarith [h01, h02, h03, h12, h13, h23]

/-- **Uniqueness**: two symmetric perturbations with the same area data are equal — the area data determines the
    metric (the decoder form of `area_probes_separate`). -/
theorem reconstruct_unique (h h' : Matrix (Fin 4) (Fin 4) ℝ) (hSym : h.IsSymm) (hSym' : h'.IsSymm)
    (hdata : ∀ v, areaVar (raySurf v) h = areaVar (raySurf v) h') : h = h' := by
  have := reconstruct_areaVar h hSym
  have h2 := reconstruct_areaVar h' hSym'
  calc h = reconstruct (fun v => areaVar (raySurf v) h) := this.symm
    _ = reconstruct (fun v => areaVar (raySurf v) h') := by
        congr 1; funext v; exact hdata v
    _ = h' := h2

end QIQTH.AreaMap
