/-
  MixedSliverFieldQGlobal — the GLOBAL `∀ z` field-point `hJ3Q` supplier for the mixed sliver, obtained
  by lifting the per-point BALL bound (J4-801, `chartField_secondJet_contract_ball`) through the already-
  built gating layer (J4-799, `MixedSliverGatedEstimates.gateQ_bound_global`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6` and proves nothing new about `R/6`.  It is the tiny
  wiring brick (J4-801 item (c), flagged "scoped small") that closes the last mile of the mixed sliver's
  FIELD-POINT second-jet carry `hJ3Q : ∀ z, ‖Q z‖ ≤ C_Q`.

  ── WHAT IT CLOSES.  J4-801 supplied the per-point BALL bound
  `chartField_secondJet_contract_ball`: on a ball `ball 0 r` the FIELD-point mixed second-jet contraction
      `z ↦ (fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart g gi hC hK 0) y) z) (unitVec i) (unitVec j)`
  (the `Point n`-valued object whose `k`-component is `∂ᵢ∂ⱼ(inverse chart)_k(z)` at the FIXED base-`0`
  chart and the VARYING field point `z`) is `≤ C_Q`.  But the mixed sliver
  `MixedSliverXUniform.witness_sliver2_xuniform_mixed` carries the GLOBAL `∀ z : Point n` form, not the
  ball form.  The already-built gating layer (`MixedSliverGatedEstimates.gateQ_bound_global`, J4-799)
  turns any ball-local `∀ z ∈ G, ‖Q z‖ ≤ C_Q` into the global `∀ z, ‖gateQ G Q z‖ ≤ C_Q` by zeroing `Q`
  off the gate `G` (off-gate `0` satisfies the bound for free).  This file performs exactly that lift with
  `G := ball 0 r` and `Q := ` the concrete field-point contraction, producing the sliver's `hJ3Q` shape.

  ── WHAT LANDS (all DERIVED; no `sorry`, no new axioms, no `:= True`; NOT `a₁ = R/6`).
    * `gatedFieldSecondJet` — the CONCRETE `Point n → Point n` the sliver's `hJ3Q` slot takes: the gated
      field-point second-jet contraction of the van-Vleck inverse chart (raw contraction on `ball 0 r`,
      the trivial `0` placeholder off it).  Manifestly tied to the chart — not a hand-picked witness.
    * `gatedFieldSecondJet_global_bound` — the GLOBAL `∀ z, ‖gatedFieldSecondJet … z‖ ≤ C_Q` bound with an
      explicit `r > 0`, `C_Q ≥ 0`, exactly the `hJ3Q` carry the mixed sliver consumes, in FIELD-point
      form.  Proof: the ball bound (`chartField_secondJet_contract_ball`) supplies `r`, `C_Q` and the
      on-gate bound `∀ z ∈ ball 0 r, ‖Q z‖ ≤ C_Q`; feed it to `gateQ_bound_global`.

  ── HONEST SCOPE.  The gated `Q` agrees with the true chart Hessian ON the injectivity ball and is the
  trivial `0` off it (where the `.choose`-built chart is junk anyway); this is the standard gate pattern
  used for all five RNC chart-surface estimates (`hco`/`hVdisp`/`hJ3i`/`hJ3j`/`hJ3Q`).  Every hypothesis is
  satisfiable and non-vacuous (`0 ∈ K` genuine; the bound is the real chart Hessian on the ball), and the
  conclusion is a strict consequence, not an assumption.  This is J4-801 item (c)'s "lift to global `∀ z`".
  The `Qfield ↔ fderiv∘fderiv` component identity (matching this `Q` to the measurability layer's
  `Qfield`) is a SEPARATE certificate and is NOT claimed here.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MixedSliverFieldQBound
import QIQTH.MixedSliverGatedEstimates

open QIQTH.Curvature QIQTH.ExpMap QIQTH.ChartFieldC2General
open scoped Topology

namespace QIQTH.HeatResidualBound

open QIQTH.MixedSliverGatedEstimates

variable {n : ℕ}

/-- **The CONCRETE gated field-point second-jet the sliver's `hJ3Q` takes.**  On the injectivity ball
    `ball 0 r` it is the true field-point mixed second-jet contraction of the fixed base-`0` van-Vleck
    inverse chart (the `Point n`-vector whose `k`-component is `∂ᵢ∂ⱼ(chart)_k(z)`); off the ball it is the
    trivial `0` placeholder (where the `.choose`-built chart is junk).  Manifestly tied to the chart. -/
noncomputable def gatedFieldSecondJet (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (i j : Fin n) (r : ℝ) : Point n → Point n :=
  gateQ (Metric.ball (0 : Point n) r)
    (fun z => (fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart g gi hC hK 0) y) z)
      (unitVec i) (unitVec j))

/-- **★ `gatedFieldSecondJet_global_bound` — the mixed sliver's FIELD-POINT `hJ3Q`, GLOBAL `∀ z`.**  For
    the fixed base-`0` chart (`0 ∈ K`) there is an explicit ball radius `r > 0` and constant `C_Q ≥ 0`
    such that the CONCRETE gated field-point second-jet is uniformly bounded on ALL of `Point n`:
        `∀ z : Point n, ‖gatedFieldSecondJet g gi hC hK i j r z‖ ≤ C_Q`,
    the exact `hJ3Q : ∀ z, ‖Q z‖ ≤ C_Q` carry that `MixedSliverXUniform.witness_sliver2_xuniform_mixed`
    consumes.  Proof: the per-point ball bound `chartField_secondJet_contract_ball` (J4-801) supplies `r`,
    `C_Q` and `∀ z ∈ ball 0 r, ‖(chart Hessian contraction) z‖ ≤ C_Q`; lift through the gating layer
    `gateQ_bound_global` (J4-799), which zeroes `Q` off the ball.  ⚠ NOT `a₁ = R/6`. -/
theorem gatedFieldSecondJet_global_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K) (i j : Fin n) :
    ∃ r > (0 : ℝ), ∃ C_Q : ℝ, 0 ≤ C_Q ∧
      ∀ z : Point n, ‖gatedFieldSecondJet g gi hC hK i j r z‖ ≤ C_Q := by
  obtain ⟨r, hr0, C_Q, hC0, hball⟩ :=
    chartField_secondJet_contract_ball g gi hC hK hK0 i j
  refine ⟨r, hr0, C_Q, hC0, ?_⟩
  unfold gatedFieldSecondJet
  exact gateQ_bound_global (Metric.ball (0 : Point n) r) _ C_Q hC0 (fun z hz => hball z hz)

end QIQTH.HeatResidualBound

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms gatedFieldSecondJet_global_bound
end AxiomChecks
