/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# `C¹` regularity of the exp-flow frame Jacobi components

Along a curve `γ : ℝ → Point n` carrying a moving frame `e i s` and a Jacobi variation
`V j s`, the exp-flow frame Jacobi component is the metric inner product

  `frameComponent g γ e V j i s = ∑_a ∑_b g(γ s)_{ab} (V j s).1^a e_i s^b`.

This file establishes its pointwise `C¹` regularity from the `C¹` (`HasDerivAt`) data of the
metric along the curve, the variation, and the frame:

* **entry level (A)** — `frameComponent_hasDerivAt`: the product-rule `HasDerivAt` for each
  component `frameComponent g γ e V j k`, obtained by `HasDerivAt.mul` (twice, over the triple
  product `g·V·e`) and `HasDerivAt.sum` (twice, over the `a`- and `b`-sums).  Its `.deriv`
  names `deriv (frameComponent g γ e V j k) t`;
* **matrix level (B)** — `frameComponentMatrix_hasDerivAt`: the matrix-valued
  `HasDerivAt (fun s => Matrix.of (fun k j => frameComponent g γ e V j k s)) …`, assembled from
  (A) by `hasDerivAt_pi` (twice, over the row `k` and column `j`) under the elementwise matrix
  normed instance.

The matrix statement is exactly the `hYmat` ingredient consumed by
`expFlow_frame_raychaudhuri` / `expFlow_frame_h4` (with `Yt j k := frameComponent g γ e V j k`).

The `C¹` hypotheses (`hg`, `hV`, `he`) are carried as **genuine** `HasDerivAt` facts, with the
derivative values `dg`, `dV`, `de` carried as data; none is vacuous.  This file does NOT build the
frame-velocity `hu` (no-conjugate invertibility), the Raychaudhuri discharge, nor `a₁ = R/6`.

Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib
import QIQTH.FrameComponentsHexp

set_option maxHeartbeats 1200000

namespace QIQTH.ExpMap

open Finset
open QIQTH.Curvature
open scoped Matrix.Norms.Elementwise

variable {n : ℕ}

/-- **(A) Entry-level product rule.**  From the `C¹` data of the metric along the curve
(`hg`), the variation (`hV`), and the frame (`he`), each frame Jacobi component
`frameComponent g γ e V j k` is differentiable at `t`, with the double-sum product-rule
derivative

  `∑_a ∑_b ((dg_{ab} (V j t)^a + g(γ t)_{ab} dV_{ja}) e_k t^b + g(γ t)_{ab} (V j t)^a de_{kb})`.

Proof: each triple product `g(γ s)_{ab} · (V j s)^a · e_k s^b` is `HasDerivAt` by `HasDerivAt.mul`
twice, and the `a`- and `b`-sums by `HasDerivAt.sum` twice. -/
theorem frameComponent_hasDerivAt (g : Point n → Fin n → Fin n → ℝ) (γ : ℝ → Point n)
    (e : Fin n → ℝ → Point n) (V : Fin n → ℝ → Point n × Point n)
    {t : ℝ} {dg : Fin n → Fin n → ℝ} {dV : Fin n → Fin n → ℝ} {de : Fin n → Fin n → ℝ}
    (hg : ∀ a b, HasDerivAt (fun s => g (γ s) a b) (dg a b) t)
    (hV : ∀ j a, HasDerivAt (fun s => (V j s).1 a) (dV j a) t)
    (he : ∀ i b, HasDerivAt (fun s => e i s b) (de i b) t)
    (j k : Fin n) :
    HasDerivAt (frameComponent g γ e V j k)
      (∑ a, ∑ b,
        ((dg a b * (V j t).1 a + g (γ t) a b * dV j a) * e k t b
          + g (γ t) a b * (V j t).1 a * de k b)) t := by
  show HasDerivAt (fun s => ∑ a, ∑ b, g (γ s) a b * (V j s).1 a * e k s b) _ t
  exact HasDerivAt.fun_sum fun a _ =>
    HasDerivAt.fun_sum fun b _ => ((hg a b).mul (hV j a)).mul (he k b)

/-- The named derivative of a frame Jacobi component at `t` (the `.deriv` of
`frameComponent_hasDerivAt`). -/
theorem frameComponent_deriv (g : Point n → Fin n → Fin n → ℝ) (γ : ℝ → Point n)
    (e : Fin n → ℝ → Point n) (V : Fin n → ℝ → Point n × Point n)
    {t : ℝ} {dg : Fin n → Fin n → ℝ} {dV : Fin n → Fin n → ℝ} {de : Fin n → Fin n → ℝ}
    (hg : ∀ a b, HasDerivAt (fun s => g (γ s) a b) (dg a b) t)
    (hV : ∀ j a, HasDerivAt (fun s => (V j s).1 a) (dV j a) t)
    (he : ∀ i b, HasDerivAt (fun s => e i s b) (de i b) t)
    (j k : Fin n) :
    deriv (frameComponent g γ e V j k) t =
      ∑ a, ∑ b,
        ((dg a b * (V j t).1 a + g (γ t) a b * dV j a) * e k t b
          + g (γ t) a b * (V j t).1 a * de k b) :=
  (frameComponent_hasDerivAt g γ e V hg hV he j k).deriv

/-- The frame Jacobi component `HasDerivAt` with the *named* derivative `deriv (…) t` as value,
convenient for assembling the matrix statement below. -/
theorem frameComponent_hasDerivAt_deriv (g : Point n → Fin n → Fin n → ℝ) (γ : ℝ → Point n)
    (e : Fin n → ℝ → Point n) (V : Fin n → ℝ → Point n × Point n)
    {t : ℝ} {dg : Fin n → Fin n → ℝ} {dV : Fin n → Fin n → ℝ} {de : Fin n → Fin n → ℝ}
    (hg : ∀ a b, HasDerivAt (fun s => g (γ s) a b) (dg a b) t)
    (hV : ∀ j a, HasDerivAt (fun s => (V j s).1 a) (dV j a) t)
    (he : ∀ i b, HasDerivAt (fun s => e i s b) (de i b) t)
    (j k : Fin n) :
    HasDerivAt (frameComponent g γ e V j k) (deriv (frameComponent g γ e V j k) t) t := by
  have h := frameComponent_hasDerivAt g γ e V hg hV he j k
  rw [h.deriv]
  exact h

/-- **(B) Matrix-level regularity — the `hYmat` ingredient.**  Assembling the entry-level
product rule over rows `k` and columns `j` (via `hasDerivAt_pi`, twice, under the elementwise
matrix normed instance `Matrix.Norms.Elementwise`) yields the matrix-valued derivative

  `HasDerivAt (fun s => Matrix.of (fun k j => frameComponent g γ e V j k s))`
  `           (Matrix.of (fun k j => deriv (frameComponent g γ e V j k) t)) t`,

which is exactly the `hYmat` hypothesis of `expFlow_frame_raychaudhuri` /
`expFlow_frame_h4` with `Yt j k := frameComponent g γ e V j k`. -/
theorem frameComponentMatrix_hasDerivAt (g : Point n → Fin n → Fin n → ℝ) (γ : ℝ → Point n)
    (e : Fin n → ℝ → Point n) (V : Fin n → ℝ → Point n × Point n)
    {t : ℝ} {dg : Fin n → Fin n → ℝ} {dV : Fin n → Fin n → ℝ} {de : Fin n → Fin n → ℝ}
    (hg : ∀ a b, HasDerivAt (fun s => g (γ s) a b) (dg a b) t)
    (hV : ∀ j a, HasDerivAt (fun s => (V j s).1 a) (dV j a) t)
    (he : ∀ i b, HasDerivAt (fun s => e i s b) (de i b) t) :
    HasDerivAt
      (fun s => (Matrix.of (fun k j => frameComponent g γ e V j k s) : Matrix (Fin n) (Fin n) ℝ))
      (Matrix.of (fun k j => deriv (frameComponent g γ e V j k) t)) t := by
  refine hasDerivAt_pi.mpr (fun k => hasDerivAt_pi.mpr (fun j => ?_))
  exact frameComponent_hasDerivAt_deriv g γ e V hg hV he j k

end QIQTH.ExpMap
