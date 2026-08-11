/-
  CurvedA1FrameAudit — J4-583: the salvageability VERDICT for the curved a₁=R/6 capstone,
  with a small std-3 PINNING certificate.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is an
  ARCHITECTURE-AUDIT brick that pins the decisive fact behind the J4-583 verdict.

  ## THE CONTEXT (J4-582).
  `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired` was proven VACUOUS at the genuinely-curved
  witness (`κ ≠ 0`, `n ≥ 2`): its neighbourhood frame antecedent
      `hframeK : ∀ q ∈ K, curvedRNCMetric κ q = δ`
  together with `hK0 : 0 ∈ K` forces `K = {0}` (because `curvedRNCMetric κ = δ` ONLY at the origin),
  collapsing the `constGate`-gated source integral, so `hmassone` (base integral → 1) cannot hold.

  ## THE J4-583 QUESTION.  Is the R/6 content intrinsically FLAT-ONLY, or is `hframeK` a superficial
  over-strong normalization that a genuinely-curved metric could satisfy in a WEAKER (center-only) form?

  ## THE VERDICT: **SALVAGEABLE.**  `hframeK` is used, in EVERY curved consumer, ONLY as the gauge input
  `gauge_from_geometry g gi hK0 hframeK hinvF hdg0`, which consumes it ONLY as `hframeK 0 hK0` (the
  chain `memGaugeGi_of_geometry → hgi_of_geometry → hg0_of_hframeK`, where `hg0_of_hframeK := hframeK 0 hK0`)
  to extract the 0-jet VALUE `g(0) = δ` and produce the two POINTWISE-AT-0 gauge members
  `MemGaugeGi gi` (`gi(0) = δ`) and `MemGaugeGamma g gi` (`Γ(0) = 0`).  `hframeK` is NEVER used to
  substitute `curvedRNCMetric κ → δ` on the integration region (no `rw [hframeK …]`, no `hframeK q`
  at `q ≠ 0`, anywhere in the capstone chain: `CurvedA1FullyWired`, `CurvedA1Leg2Core`, `Leg2HLapFull`,
  `CurvedA1FullyWiredCapstone`, `CurvedA1MemAdjHiWired`).  The R/6 COEFFICIENT flows from `Ric(0)` of the
  CURVED metric (a CENTER fact; `curvedRNCMetric_ricci_trace_diag_ne` — nonzero for `κ ≠ 0`, `n ≥ 2`),
  compatible with a center-only gauge.  The vacuity is caused SOLELY by the neighbourhood strength of
  `hframeK` (via `curvedRNCMetric_frame_forces_origin`), NOT by the R/6 derivation.

  ## THE FIX (recommended J4-584).  Weaken the capstone's `hframeK` to the center-only VALUE gauge
      `hg0 : ∀ i j, curvedRNCMetric κ 0 i j = δ_{ij}`
  (which `curvedRNCMetric` SATISFIES via `curvedRNCMetric_zero`, curved or flat, and which does NOT force
  `K = {0}`), and re-thread the two gauge sites `gauge_from_geometry → DaLimCurvedGauge.gauge_from_pointwise`
  (the banked J4-512 curved-compatible drop-in, consuming only `{hg0, hinvF, hdg0}`).  The `hdg0`/`hinvF`
  inputs are already discharged for `curvedRNCMetric` (`curvedRNCMetric_pd_zero`, `curvedRNCMetric_hinvF`).

  ## THE PIN (this file).  `curved_gauge_from_center`: the genuinely-curved `curvedRNCMetric κ` (`κ < 0`)
  produces BOTH gauge members via the center-only `gauge_from_pointwise` — WITHOUT `hframeK`, WITHOUT
  `hK0`.  `curved_frame_salvage_certificate`: the same, paired with `Ric(0) ≠ 0` — so the center-only
  gauge path is inhabited by a GENUINELY CURVED metric, not a flat computation in disguise.

  ⚠ HONEST a₁ FRAMING: `a₁ = R/6` is established non-vacuously ONLY for the FLAT tower.  The curved
  capstone is vacuous at the curved witness (J4-582).  This file certifies that the vacuity is FIXABLE
  (weaken `hframeK` to center-only + rethread to `gauge_from_pointwise`) — it does NOT itself re-establish
  the curved `a₁ = R/6`; that is the J4-584 rethread.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.DaLimCurvedGauge
import QIQTH.CurvedRNCGaussWitness
import QIQTH.CurvedRNCGaugeBundle
import QIQTH.GaussGaugeToHgauge

open QIQTH.Curvature
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.GaussGaugeToHgauge
open QIQTH.DaLimLUWallRecon
open scoped BigOperators

namespace QIQTH.CurvedA1FrameAudit

variable {n : ℕ}

/-- **★ THE SALVAGE PIN — center-only gauge for the genuinely-curved metric.**  The two POINTWISE-AT-0
    gauge census members `MemGaugeGi (curvedRNCInv κ)` (`gi(0) = δ`) and
    `MemGaugeGamma (curvedRNCMetric κ) (curvedRNCInv κ)` (`Γ(0) = 0`) — exactly what the curved capstone
    consumes from `hframeK` — are produced for `g := curvedRNCMetric κ` (`κ < 0`, genuinely curved) via
    the banked center-only `DaLimCurvedGauge.gauge_from_pointwise`, from ONLY the pointwise RNC jet
    `{hg0 = curvedRNCMetric_zero, hinvF = curvedRNCMetric_hinvF, hdg0 = curvedRNCMetric_pd_zero}`.
    NO neighbourhood frame `hframeK`, NO `hK0`.  This is the drop-in the two curved gauge sites need.
    NOT `a₁ = R/6`. -/
theorem curved_gauge_from_center (κ : ℝ) (hκ : κ < 0) :
    MemGaugeGi (n := n) (curvedRNCInv κ)
      ∧ MemGaugeGamma (n := n) (curvedRNCMetric κ) (curvedRNCInv κ) :=
  QIQTH.DaLimCurvedGauge.gauge_from_pointwise (curvedRNCMetric κ) (curvedRNCInv κ)
    (fun i j => curvedRNCMetric_zero κ i j)
    (fun y c d => curvedRNCMetric_hinvF κ (le_of_lt hκ) y c d)
    (fun a b e => curvedRNCMetric_pd_zero κ a b e)

/-- **★ THE SALVAGE CERTIFICATE — center-only gauge holds AND the metric is genuinely curved.**  For
    `κ < 0`, `n ≥ 2`: the center-only gauge path (`curved_gauge_from_center`) produces both gauge members
    WHILE the diagonal metric-Hessian trace `Ric(0) ≠ 0` (`curvedRNCMetric_ricci_trace_diag_ne`).  So the
    weakened (center-only) gauge antecedent is inhabited by a GENUINELY CURVED metric — the curved
    capstone's gauge content is NOT a flat computation in disguise, and the J4-582 vacuity is a removable
    over-strong-`hframeK` artefact, NOT an intrinsic flatness of the R/6 derivation.  NOT `a₁ = R/6`. -/
theorem curved_frame_salvage_certificate (κ : ℝ) (hκ : κ < 0) (hn : 2 ≤ n) (c : Fin n) :
    (MemGaugeGi (n := n) (curvedRNCInv κ)
      ∧ MemGaugeGamma (n := n) (curvedRNCMetric κ) (curvedRNCInv κ))
    ∧ pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  ⟨curved_gauge_from_center κ hκ,
   curvedRNCMetric_ricci_trace_diag_ne κ (ne_of_lt hκ) hn c⟩

end QIQTH.CurvedA1FrameAudit

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.CurvedA1FrameAudit.curved_gauge_from_center
#print axioms QIQTH.CurvedA1FrameAudit.curved_frame_salvage_certificate
