/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Orthonormal frame reconstruction `∑_i ⟨V,e_i⟩_g e_i = V`

A general linear-algebra identity: an orthonormal frame `e` reconstructs any vector `V`
from its metric components.  Concretely, with the metric inner product
`⟨V, e_i⟩_g = ∑_a ∑_b g_{ab} V^a e_i^b`, the frame expansion `∑_i ⟨V, e_i⟩_g e_i^μ`
equals `V^μ`, provided:

* completeness `∑_i e_i^μ e_i^ν = gi^{μν}` (the frame is dual to the inverse metric), and
* the metric–inverse relation `∑_b g_{ab} gi^{μb} = δ_a^μ` (with `gi` symmetric).

This is the `hexp` core of `expFlow_frame_raychaudhuri`: the frame components
`Yt_{ji} = ⟨V_j, e_i⟩_g` reconstruct the Jacobi field `V_j`, so that
`∑_i Yt_{ji} e_i = V_j`.

This is a pure finite-sum algebra fact; it is NOT the frame Raychaudhuri equation, NOT the
van-Vleck discharge, and NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.Curvature

set_option maxHeartbeats 800000

namespace QIQTH.Curvature

open Finset

variable {n : ℕ}

/-- Orthonormal frame reconstruction: `∑_i ⟨V, e_i⟩_g e_i^μ = V^μ`.

Given a frame `e : Fin n → (Fin n → ℝ)` that is complete
(`hcomplete : ∑_i e_i^μ e_i^ν = gi^{μν}`) and a metric–inverse pair `(g, gi)` with
`hinv : ∑_b g_{ab} gi^{μb} = δ_a^μ` and `gi` symmetric (`hgisymm`), the metric-frame
components of `V` reconstruct `V`. -/
theorem gorthonormal_frame_reconstruct (g gi : Point n → Fin n → Fin n → ℝ) (x : Point n)
    (e : Fin n → (Fin n → ℝ)) (V : Fin n → ℝ)
    (hcomplete : ∀ μ ν, (∑ i, e i μ * e i ν) = gi x μ ν)
    (hinv : ∀ a μ, (∑ b, g x a b * gi x μ b) = if a = μ then (1:ℝ) else 0)
    (hgisymm : ∀ p q, gi x p q = gi x q p)
    (μ : Fin n) :
    (∑ i, (∑ a, ∑ b, g x a b * V a * e i b) * e i μ) = V μ := by
  calc
    (∑ i, (∑ a, ∑ b, g x a b * V a * e i b) * e i μ)
        = ∑ i, ∑ a, ∑ b, (g x a b * V a * e i b) * e i μ := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.sum_mul]
    _ = ∑ a, ∑ b, ∑ i, (g x a b * V a * e i b) * e i μ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, g x a b * V a * (∑ i, e i b * e i μ) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
    _ = ∑ a, ∑ b, g x a b * V a * gi x b μ := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [hcomplete b μ]
    _ = ∑ a, V a * (∑ b, g x a b * gi x μ b) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [hgisymm b μ]
          ring
    _ = ∑ a, V a * (if a = μ then (1:ℝ) else 0) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [hinv a μ]
    _ = ∑ a, (if a = μ then V a else 0) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [mul_ite, mul_one, mul_zero]
    _ = V μ := by
          rw [Finset.sum_ite_eq' Finset.univ μ V]
          simp

end QIQTH.Curvature
