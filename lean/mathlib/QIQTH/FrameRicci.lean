import Mathlib
import QIQTH.Curvature
import QIQTH.JacobiEquation

/-!
# M2b-4 — The frame Ricci trace: `∑_i ⟨R(e_i,v)v, e_i⟩_g = Ric(v,v)`

For a `g(x)`-orthonormal frame `{e_i}` the trace of the geodesic-deviation operator
`ξ ↦ R(ξ,v)v` against the frame reproduces the Ricci quadratic form:

  `∑_i ⟨R(e_i,v)v, e_i⟩_g  =  Ric(v,v)`.

This is the **coordinate-free** definition of Ricci.  Unlike the L3 identity
`QIQTH.ExpMap.geodesicDeviation_trace_eq_ricci` — which traces over the fixed *coordinate*
basis `δ_i = (fun k => if k = i then 1 else 0)` and therefore holds only where that basis is
`g`-orthonormal (the RNC centre) — the present statement carries the completeness relation
`∑_i e_i^μ e_i^b = g^{μb}(x)` as a hypothesis and so holds at **any point** `x`; in particular
it supplies `tr R̃ = Ric` **along the whole ray**, which is exactly what the parallel-frame route
(M2b) needs.

The algebra (fully worked, no gauge/regularity assumptions — pure finite-sum algebra):

  `∑_i ∑_{a,b} g_{ab} (R(e_i,v)v)^a e_i^b`
    `= ∑_{a,b,σ,μ,ν} g_{ab} R^a_{σμν} v^σ v^ν (∑_i e_i^μ e_i^b)`   [linearity + pull `∑_i` in]
    `= ∑_{a,b,σ,μ,ν} g_{ab} R^a_{σμν} v^σ v^ν g^{μb}`               [completeness `hcomplete`]
    `= ∑_{a,σ,μ,ν} R^a_{σμν} v^σ v^ν (∑_b g_{ab} g^{μb})`
    `= ∑_{a,σ,μ,ν} R^a_{σμν} v^σ v^ν δ_a^μ`                         [metric–inverse `hinv`]
    `= ∑_{a,σ,ν} R^a_{σaν} v^σ v^ν = ∑_{σ,ν} Ric_{σν} v^σ v^ν`.     [Ricci contraction]

## What is here / what is NOT here
* **`frame_ricci_trace`** — the trace identity, carrying `hcomplete` (frame completeness) and `hinv`
  (metric–inverse) as *standard, exact* hypotheses.  Neither assumes the conclusion.
* Deliverable #2 (`frame_completeness_of_orthonormal`, deriving `hcomplete` from orthonormality
  `Eᵀ G E = I ⟹ E Eᵀ = G⁻¹` via the `Matrix` inverse bridge) is **CHECKPOINTED / deferred**:
  it is the pure matrix identity `E Eᵀ = gi` and needs the `Matrix.mul_eq_one_comm` /
  `Matrix.inv` machinery wired to the index-level frame `e`.  Carrying `hcomplete` as a genuine
  frame hypothesis is standard and does not weaken `frame_ricci_trace`.

Explicitly **NOT** covered by this file (adjacent M2b / M6 walls, untouched here):
* the *existence* / construction of the parallel frame along the ray (M2b-2);
* expressing the Jacobi field in the frame and the wall-crossing `Ỹ'' = −R̃ Ỹ` (M2b-3);
* the heat-kernel coefficient `a₁ = R/6` (M6).
-/

namespace QIQTH.FrameRicci

open QIQTH.Curvature QIQTH.ExpMap Finset

variable {n : ℕ}

/-- Rotate the outermost of three nested finite sums to the innermost. -/
private lemma rot3 (f : Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

/-- Rotate the outermost of four nested finite sums to the innermost. -/
private lemma rot4 (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ b, ∑ c, ∑ d, ∑ a, f a b c d := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

/-- Rotate the outermost of six nested finite sums to the innermost. -/
private lemma rot6 (f : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ h, f a b c d e h
      = ∑ b, ∑ c, ∑ d, ∑ e, ∑ h, ∑ a, f a b c d e h := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]

/-- **Frame Ricci trace (M2b-4).**  For a `g(x)`-orthonormal frame `{e_i}` with completeness
    relation `∑_i e_i^μ e_i^b = g^{μb}(x)` (`hcomplete`) and metric–inverse relation
    `∑_b g_{ab} g^{μb} = δ_a^μ` (`hinv`), the frame trace of the geodesic-deviation operator
    `ξ ↦ R(ξ,v)v` equals the Ricci quadratic form:
      `∑_i ∑_{a,b} g_{ab} (R(e_i,v)v)^a e_i^b  =  ∑_{σν} R_{σν} v^σ v^ν`.
    Holds at ANY point `x` (hence along the whole ray); generalizes the coordinate-basis,
    RNC-centre-only `geodesicDeviation_trace_eq_ricci`. -/
theorem frame_ricci_trace (g gi : Point n → Fin n → Fin n → ℝ) (x v : Point n) (e : Fin n → Point n)
    (hcomplete : ∀ μ b, (∑ i, e i μ * e i b) = gi x μ b)
    (hinv : ∀ a μ, (∑ b, g x a b * gi x μ b) = if a = μ then (1:ℝ) else 0) :
    (∑ i, ∑ a, ∑ b, g x a b * (QIQTH.ExpMap.riemannGeodesicDeviation g gi x v (e i)) a * e i b)
      = ∑ σ, ∑ ν, QIQTH.Curvature.ricci g gi σ ν x * v σ * v ν := by
  calc
    (∑ i, ∑ a, ∑ b, g x a b * (riemannGeodesicDeviation g gi x v (e i)) a * e i b)
        = ∑ i, ∑ a, ∑ b, ∑ σ, ∑ μ, ∑ ν,
            g x a b * riemann g gi a σ μ ν x * v σ * v ν * e i μ * e i b := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
            Finset.sum_congr rfl fun b _ => ?_
          simp only [riemannGeodesicDeviation, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun μ _ =>
            Finset.sum_congr rfl fun ν _ => ?_
          ring
    _ = ∑ a, ∑ b, ∑ σ, ∑ μ, ∑ ν, ∑ i,
            g x a b * riemann g gi a σ μ ν x * v σ * v ν * e i μ * e i b := rot6 _
    _ = ∑ a, ∑ b, ∑ σ, ∑ μ, ∑ ν,
            (g x a b * riemann g gi a σ μ ν x * v σ * v ν) * gi x μ b := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun μ _ =>
            Finset.sum_congr rfl fun ν _ => ?_
          rw [← hcomplete μ b, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
    _ = ∑ a, ∑ σ, ∑ μ, ∑ ν,
            (riemann g gi a σ μ ν x * v σ * v ν) * (if a = μ then (1:ℝ) else 0) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [rot4]
          refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun μ _ =>
            Finset.sum_congr rfl fun ν _ => ?_
          rw [← hinv a μ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          ring
    _ = ∑ a, ∑ σ, ∑ ν, riemann g gi a σ a ν x * v σ * v ν := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun σ _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ν _ => ?_
          simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
            Finset.mem_univ, if_true]
    _ = ∑ σ, ∑ ν, QIQTH.Curvature.ricci g gi σ ν x * v σ * v ν := by
          rw [rot3]
          refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ν _ => ?_
          simp only [ricci, Finset.sum_mul]

end QIQTH.FrameRicci
