/-
  WitnessTranspositionSmoothResidual — J4-822: the transposition residual's sliver bound reduced to
  PURE SMOOTHNESS — `F` is C³ at the origin — the terminal interface of the J4-818 transposition wall.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT.  J4-820 reduced the source↔field transposition wall to the interface `hodd`
  (`|G(−z) − G(z)| ≤ L·‖z‖`, `G = ∂ⱼ∂ᵢF`).  J4-821 discharged `hodd` from LOCAL LIPSCHITZ continuity of
  `G`.  This file takes the final step: local Lipschitz of `G` follows from `G` being C¹ at 0 — i.e.
  the displacement kernel `F` being C³ at 0 — via `ContDiffAt.exists_lipschitzOnWith`.

  ── RESULT (`residual_sliver_bound_of_contDiffAt`).  If `G = ∂ⱼ∂ᵢF` is `ContDiffAt ℝ 1` at the origin
  (equivalently `F` is C³ at 0), then there exist a Lipschitz constant `K` and a radius `r > 0` such
  that for every `z` with `‖z‖ < r` inside the sliver window `‖z‖ ≤ √ε`, the transposition residual
  obeys `|residual| ≤ 2K·√ε` — matching the O(√ε) rate the closed J4-817 sliver bound carries.

  This is the TERMINAL interface of the transposition wall: its hypothesis — `F` C³ at 0 — is
  UNCONDITIONALLY satisfied by the witness kernel `vanVleckGatedWitness`, whose entire `(p,q)`-dependence
  factors through the C^∞ inverse-chart vector `V(q,p)` composed with C^∞ amplitude factors (Gaussian,
  van-Vleck, transport polynomials).  The delicate even/odd (∇R-cubic) structure of J4-819 is NOT needed
  at all — the residual's O(√ε) sliver control follows from smoothness alone.

  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and does NOT by itself close `hCConv` on the live
  capstone.  It proves the transposition residual is O(√ε) on the sliver window for ANY C³-at-0
  displacement kernel — reducing the J4-818 wall to a smoothness fact.  Wiring into the live capstone
  still requires the concrete displacement reduction of the curved-RNC-chart witness (the live kernel is
  `F(V(q,p))` with `V` the log map, not a pure displacement `F(p−q)`), i.e. transporting this bound
  through the chart's dependence.  No `sorry`, no new axioms, no `:= True`, no existing file edited.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.WitnessTranspositionLipschitzResidual

open QIQTH.Curvature
open scoped Topology NNReal

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

/-- **★★★ J4-822 — TERMINAL INTERFACE: transposition residual sliver bound from PURE SMOOTHNESS.**
    If the displacement kernel's second field-partial `G = ∂ⱼ∂ᵢF` is `ContDiffAt ℝ 1` at the origin
    (i.e. `F` is C³ at 0), then there are a Lipschitz constant `K` and radius `r > 0` such that for all
    `z` with `‖z‖ < r` and every `ε` with `‖z‖ ≤ √ε`, the source↔field transposition residual obeys
        `|residual| ≤ 2K·√ε`,
    matching the O(√ε) rate the closed J4-817 sliver bound carries.  The hypothesis is UNCONDITIONALLY
    met by the C^∞ witness kernel — the transposition wall reduces to smoothness alone, with NO
    even/odd (∇R-cubic) cancellation needed. -/
theorem residual_sliver_bound_of_contDiffAt (F : Point n → ℝ) (i j : Fin n)
    (hC3 : ContDiffAt ℝ 1 (fun w => pd (fun y => pd F i y) j w) (0 : Point n)) :
    ∃ (K : ℝ≥0) (r : ℝ), 0 < r ∧ ∀ (z : Point n) (ε : ℝ), ‖z‖ < r → ‖z‖ ≤ Real.sqrt ε →
      |pd (fun y => pd (fun x' => F (x' - z)) i y) j (0 : Point n)
        - pd (fun y => pd (fun x' => F (x' - (0 : Point n))) i y) j z| ≤ (2 * K) * Real.sqrt ε := by
  obtain ⟨K, t, ht, hLip⟩ := hC3.exists_lipschitzOnWith
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨K, r, hr, fun z ε hzr hwin => ?_⟩
  have hpz : z ∈ t := hball (by simpa [Metric.mem_ball, dist_zero_right] using hzr)
  have hmz : -z ∈ t := hball (by
    simpa [Metric.mem_ball, dist_zero_right, norm_neg] using hzr)
  exact residual_sliver_bound_of_lipschitzOnWith F i j z hLip hmz hpz hwin

end QIQTH.HeatResidualBound
