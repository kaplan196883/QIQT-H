/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# JacobiC2 — the real exp-Jacobi field `B(s) = s • D(exp_p)_{s•v}` is `C²` at `s = 1`

This is the 2nd-order **REGULARITY FLOOR** for the real exp-differential matrix Jacobi field
```
  B s := s • expJacobianMat g gi hC p (s • v)   ( = s • D(exp_p)_{s•v} ).
```
We prove `ContDiffAt ℝ 2 B 1`, i.e. `B` is `C²` at the ray parameter `s = 1`.  Consequently the
first and second derivatives `B'(1)` and `B''(1)` both EXIST — the full 2nd-order regularity
precondition for the matrix Jacobi identity to even be stated on this concrete object.

## Mechanism (regularity only)

`expJacobianMat g gi hC p ·` is entrywise `C²` on the OPEN exp ball `Metric.ball 0 (expRho …)`
(`QIQTH.JacobianRegularity.expJacobianMat_entry_contDiffOn_two`).  Since `v` lies in that open
ball (`hv`), the ball is a neighbourhood of `v`, so each entry map is `ContDiffAt ℝ 2 · v`.  The
ray `s ↦ s • v` is `C^∞` (here `C²`) at `s = 1` with value `1 • v = v`, so the composition
`s ↦ expJacobianMat g gi hC p (s • v) a i` is `C²` at `1` (`ContDiffAt.comp`).  Multiplying by the
`C^∞` scalar `s` (`ContDiffAt.mul` with `contDiffAt_id`) and reassembling the `Fin n × Fin n`
entries (`contDiffAt_pi` twice, in the native `Matrix`/`Pi` normed instance, exactly as
`JacobiDerivReal` treats the same object) gives `ContDiffAt ℝ 2 B 1`.

## What this is NOT

This establishes only the 2nd-order **regularity** of `B = s • D(exp_p)_{s•v}` at `s = 1` (that
`B'` and `B''` exist there).  It does **NOT** prove the matrix Jacobi identity `B'' = −R̃ B`
(the deep 2nd-order geodesic smooth-dependence primitive), the van-Vleck radial ODE, or the
heat-kernel coefficient `a₁ = R/6`; those remain the documented geometric walls.

Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib
import QIQTH.ExpJacobianRegularity
import QIQTH.JacobianDet

namespace QIQTH.JacobianRegularity

open QIQTH.Curvature QIQTH.ExpMap QIQTH.Geodesic QIQTH.PullbackMetric
open Finset Matrix
open scoped Matrix.Norms.Elementwise

variable {n : ℕ}

set_option maxHeartbeats 800000

/-- **The real exp-Jacobi field `B(s) = s • D(exp_p)_{s•v}` is `C²` at `s = 1`.**

`expJacobianMat g gi hC p ·` is entrywise `C²` on the open exp ball
(`expJacobianMat_entry_contDiffOn_two`); `v` lies in that ball (`hv`), so each entry is
`ContDiffAt ℝ 2 · v`.  Composing with the `C^∞` ray `s ↦ s • v` (value `1 • v = v` at `s = 1`,
`ContDiffAt.comp`) and multiplying by the `C^∞` scalar `s` (`ContDiffAt.mul`), then reassembling
the `Fin n × Fin n` entries (`contDiffAt_pi` twice), yields `C²` regularity of `B` at `s = 1`.

REGULARITY ONLY: this guarantees `B'(1)` and `B''(1)` exist; it does NOT prove the matrix Jacobi
identity `B'' = −R̃ B`, the van-Vleck radial ODE, or `a₁ = R/6`. -/
theorem expJacobiRay_contDiffAt_two (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) (v : Point n) (hv : ‖v‖ < expRho g gi hC p) :
    ContDiffAt ℝ 2
      (fun s : ℝ => s • QIQTH.JacobianDet.expJacobianMat g gi hC p (s • v)) 1 := by
  -- `v` lies in the (open) exp ball, hence the ball is a neighbourhood of `v`.
  have hmem : Metric.ball (0 : Point n) (expRho g gi hC p) ∈ nhds v :=
    Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_zero_right] using hv)
  -- The ray `s ↦ s • v` is `C²` (indeed `C^∞`) at `s = 1`.
  have hray : ContDiffAt ℝ 2 (fun s : ℝ => s • v) 1 :=
    contDiffAt_id.smul contDiffAt_const
  -- Each composed entry `s ↦ (D(exp_p)_{s•v})_{a i}` is `C²` at `s = 1`.
  have hEntryComp : ∀ a i : Fin n, ContDiffAt ℝ 2
      (fun s : ℝ => QIQTH.JacobianDet.expJacobianMat g gi hC p (s • v) a i) 1 := by
    intro a i
    have hentry : ContDiffAt ℝ 2
        (fun x => QIQTH.JacobianDet.expJacobianMat g gi hC p x a i) ((1 : ℝ) • v) := by
      rw [one_smul]
      exact (expJacobianMat_entry_contDiffOn_two g gi hC p a i).contDiffAt hmem
    exact hentry.comp 1 hray
  -- Reassemble entrywise: `(s • M(s))_{a i} = s * M(s)_{a i}`, a `C²` product.
  refine contDiffAt_pi.mpr (fun a => contDiffAt_pi.mpr (fun i => ?_))
  have hmul : ContDiffAt ℝ 2
      (fun s : ℝ => s * QIQTH.JacobianDet.expJacobianMat g gi hC p (s • v) a i) 1 :=
    contDiffAt_id.mul (hEntryComp a i)
  simpa only [Matrix.smul_apply, smul_eq_mul] using hmul

end QIQTH.JacobianRegularity
