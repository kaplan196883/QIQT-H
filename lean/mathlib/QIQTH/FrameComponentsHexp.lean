/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Exp-flow frame Jacobi components and the `hexp` decomposition

Along a curve `γ : ℝ → Point n` carrying a moving orthonormal frame `e i s`, the
exp-flow frame Jacobi components are the metric inner products

  `Yt_{ji}(s) = ⟨(V j s).1, e_i s⟩_g = ∑_a ∑_b g(γ s)_{ab} (V j s).1^a e_i s^b`.

This file packages the pointwise frame-reconstruction identity
`gorthonormal_frame_reconstruct` as an eventual (near `t`) equality of functions,

  `(fun s a => ∑_i Yt_{ji}(s) e_i s^a) =ᶠ[nhds t] (fun s => (V j s).1)`,

i.e. the frame expansion `∑_i Yt_{ji} e_i = (V j).1` holds on a neighbourhood of `t`.

This is exactly the `hexp` hypothesis of `expFlow_frame_raychaudhuri` /
`expFlow_frame_h4`.  The geometric inputs are all genuine facts along the curve:
frame completeness `∑_i e_i^μ e_i^ν = gi^{μν}`, the metric–inverse relation
`∑_b g_{ab} gi^{μb} = δ_a^μ`, and symmetry of `gi`, each holding eventually near `t`.

This file does NOT build the `Yt`-matrix regularity (`hY`/`hYmat`), the frame velocity
`hu`, the full Raychaudhuri discharge, nor `a₁ = R/6`.
-/
import Mathlib
import QIQTH.FrameReconstruct

set_option maxHeartbeats 800000

namespace QIQTH.ExpMap

open Finset
open QIQTH.Curvature

variable {n : ℕ}

/-- The exp-flow frame Jacobi component `Yt_{ji}(s) = ⟨(V j s).1, e_i s⟩_g`, i.e. the
metric inner product of the Jacobi field `(V j s).1` with the frame vector `e i s`. -/
noncomputable def frameComponent (g : Point n → Fin n → Fin n → ℝ) (γ : ℝ → Point n)
    (e : Fin n → ℝ → Point n) (V : Fin n → ℝ → Point n × Point n) (j i : Fin n) (s : ℝ) : ℝ :=
  ∑ a, ∑ b, g (γ s) a b * (V j s).1 a * e i s b

/-- The `hexp` decomposition: near `t`, the frame expansion `∑_i Yt_{ji} e_i` of the metric
components reconstructs the Jacobi field `(V j).1`.  This is the pointwise
`gorthonormal_frame_reconstruct` promoted to an eventual equality of functions, and is exactly
the `hexp` hypothesis consumed by `expFlow_frame_raychaudhuri` / `expFlow_frame_h4`. -/
theorem frameComponents_hexp (g gi : Point n → Fin n → Fin n → ℝ) (γ : ℝ → Point n)
    (e : Fin n → ℝ → Point n) (V : Fin n → ℝ → Point n × Point n) {t : ℝ}
    (hcomplete : ∀ᶠ s in nhds t, ∀ μ ν, (∑ i, e i s μ * e i s ν) = gi (γ s) μ ν)
    (hinv : ∀ᶠ s in nhds t, ∀ a μ, (∑ b, g (γ s) a b * gi (γ s) μ b) = if a = μ then (1:ℝ) else 0)
    (hgisymm : ∀ᶠ s in nhds t, ∀ p q, gi (γ s) p q = gi (γ s) q p)
    (j : Fin n) :
    (fun s => fun a => ∑ i, frameComponent g γ e V j i s * e i s a)
      =ᶠ[nhds t] (fun s => (V j s).1) := by
  filter_upwards [hcomplete, hinv, hgisymm] with s hcs his hgs
  funext a
  simp only [frameComponent]
  exact gorthonormal_frame_reconstruct g gi (γ s) (fun i => e i s) (fun a' => (V j s).1 a')
    hcs his hgs a

end QIQTH.ExpMap
