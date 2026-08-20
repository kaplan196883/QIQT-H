/-
  RadialGaugeIsNamedFloor — the J4-893 `RadialNormalCoordinateGauge` interface (the `hDConv`
  centre-identity wall) IS the pre-existing J4-507 named geodesic floor `MetricGaussGauge`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  No `sorry`,
  no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or
  trivially yielding) the conclusion beyond the honest structural identity it records, no banked file
  edited.

  ## THE QUESTION THIS FILE SETTLES (the task).
  Is `RadialGaugeInterface.RadialNormalCoordinateGauge g gi` — the named hypothesis the `hDConv`
  centre-identity leg was reduced to (J4-893) — DISCHARGEABLE for the LIVE order-1 capstone's ACTUAL
  free metric `g`/`gi` (which carry only `hChr` = Christoffel smoothness and `hK` = compactness of the
  confinement set), or is it a genuinely-open geometric carry for the live object?

  ## THE ANSWER — it is EXACTLY the J4-507 named GEODESIC FLOOR, hence an HONEST IRREDUCIBLE carry.
  Unfolding the three fields of `RadialNormalCoordinateGauge g gi`:
    • `metricGauge : ∀ y i, ∑ⱼ g y i j · yʲ = yᵢ`   is **DEFINITIONALLY** `GaussLemmaGauge.MetricGaussGauge g`;
    • `invGauge    : ∀ y i, ∑ⱼ gi y i j · yʲ = yᵢ`   is **DEFINITIONALLY** `GaussLemmaGauge.MetricGaussGauge gi`;
    • `centerNorm  : ∀ i, g 0 i i = 1`               is the centre `g(0) = δ` diagonal.
  So `RadialNormalCoordinateGauge g gi ⟺ MetricGaussGauge g ∧ MetricGaussGauge gi ∧ (g(0) diag = 1)`.
  `MetricGaussGauge` (dual of `CoordGaussGauge`) was ADVERSARIALLY CLASSIFIED in the J4-507 audit
  (`GaussLemmaGauge`, header + ledger) as **verdict (c): the IRREDUCIBLE geodesic / exp-map FLOOR** —
    – NOT derivable from the finite RNC 2-jet (`g(0)=δ`, `∂g(0)=0`, symmetrised `∂Γ(0)=0`): the Sol
      counterexample `g = (1+ε‖x‖⁴)δ` matches the entire finite jet at `0` yet FAILS `∑ⱼ g_{ij}xʲ = xᵢ`
      off-origin (an all-orders `∀x` identity a finite jet cannot capture);
    – a fortiori NOT derivable from the live capstone's `hChr`/`hK` alone (weaker than the finite jet);
    – Mathlib has no exp-map/geodesic infrastructure to discharge it against a construction.
  Therefore `RadialNormalCoordinateGauge` for the live free `g`/`gi` is an HONEST additional geometric
  hypothesis at exactly the SAME status as `hChr` — it PINS DOWN that `g` is presented in Riemannian
  normal coordinates centred at the origin.  It is NOT a "should-be-derivable but not-yet-built" gap.

  ## WHAT THIS FILE LANDS — the identification + the consolidation (both non-vacuous).
    • `radialNormalCoordinateGauge_of_namedFloor` — ★ the interface FROM the named floor: from
      `MetricGaussGauge g`, `MetricGaussGauge gi` and the centre-δ diagonal, build
      `RadialNormalCoordinateGauge g gi`.  (Forward identification; the fields are the floor verbatim.)
    • `metricGaussGauge_g_of_radialGauge` / `metricGaussGauge_gi_of_radialGauge` — the reverse
      extractions: the interface delivers BOTH `MetricGaussGauge` floors.
    • `radialGauge_imp_mainline_hGaussGerm` — ★★ THE CONSOLIDATION: the interface implies the
      `a₁ = R/6` MAINLINE labelled input `hGauss` (the germ `=ᶠ[𝓝 0]` metric gauge) via
      `GaussLemmaGauge.metricGaussGauge_imp_hGaussGerm`.  So the `hDConv` gauge leg and the mainline
      gauge input are the SAME geometric floor — ONE shared carry, not two independent walls.
    • `radialNormalCoordinateGauge_flat_via_floor` — non-vacuity through the floor route (flat metric).
    • `radialNormalCoordinateGauge_curved_via_floor` — ★ the LOAD-BEARING non-vacuity gate: the
      genuinely CURVED witness `g^K = curvedRNCMetric κ` (`κ ≤ 0`, `Ric(0) = (n−1)κ·δ ≠ 0`) satisfies
      the interface REBUILT through the named floor (`metricGaussGauge_curvedRNC` +
      `curved_radialGauge_bundle`), so the identification does NOT collapse curvature.

  ⚠  a₁ = R/6 remains CONDITIONAL.  This file makes the `hDConv` gauge wall trace to the pre-existing
  named geodesic floor and shows it coincides with the mainline `hGauss` carry; it does NOT derive the
  floor (which J4-507 proved is not derivable from finite-jet / `hChr` data) and does NOT make
  `a₁ = R/6` unconditional.  ⚠ NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.RadialGaugeInterface
import QIQTH.GaussLemmaGauge

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.FlatHeatEquation QIQTH.ResidualFactorization
open QIQTH.RadialGaugeInterface QIQTH.GaussLemmaGauge
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedCenterIdentities
open scoped BigOperators Topology

namespace QIQTH.RadialGaugeIsNamedFloor

variable {n : ℕ}

/-! ###############################################################################
    ### §1 — the interface IS the named floor (forward + backward).
    ############################################################################### -/

/-- **★ `radialNormalCoordinateGauge_of_namedFloor`.**  The J4-893 interface FROM the J4-507 named
    geodesic floor: from the metric-side gauge `MetricGaussGauge g`, the inverse-side gauge
    `MetricGaussGauge gi`, and the centre-δ diagonal `g(0)_{ii} = 1`, build
    `RadialNormalCoordinateGauge g gi`.  The three fields ARE the floor verbatim (`metricGauge`/
    `invGauge` are `MetricGaussGauge g`/`MetricGaussGauge gi` definitionally).  ⚠ NOT `a₁ = R/6`. -/
theorem radialNormalCoordinateGauge_of_namedFloor (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : MetricGaussGauge g) (hgi : MetricGaussGauge gi)
    (h0 : ∀ i : Fin n, g (0 : Point n) i i = 1) :
    RadialNormalCoordinateGauge g gi where
  metricGauge := fun y i => hg y i
  invGauge := fun y i => hgi y i
  centerNorm := h0

/-- **`metricGaussGauge_g_of_radialGauge`.**  Reverse extraction: the interface delivers the metric-side
    named floor `MetricGaussGauge g`.  ⚠ NOT `a₁ = R/6`. -/
theorem metricGaussGauge_g_of_radialGauge (g gi : Point n → Fin n → Fin n → ℝ)
    (hgauge : RadialNormalCoordinateGauge g gi) : MetricGaussGauge g :=
  fun y i => hgauge.metricGauge y i

/-- **`metricGaussGauge_gi_of_radialGauge`.**  Reverse extraction: the interface delivers the
    inverse-side named floor `MetricGaussGauge gi`.  ⚠ NOT `a₁ = R/6`. -/
theorem metricGaussGauge_gi_of_radialGauge (g gi : Point n → Fin n → Fin n → ℝ)
    (hgauge : RadialNormalCoordinateGauge g gi) : MetricGaussGauge gi :=
  fun y i => hgauge.invGauge y i

/-! ###############################################################################
    ### §2 — ★★ THE CONSOLIDATION: interface ⟹ the mainline `hGauss` floor.
    ############################################################################### -/

/-- **★★ `radialGauge_imp_mainline_hGaussGerm`.**  The `hDConv` gauge interface implies the `a₁ = R/6`
    MAINLINE labelled input `hGauss` in its germ form (`∀ i, (fun x => ∑ⱼ g x i j · xʲ) =ᶠ[𝓝 0]
    (fun x => xᵢ)`), via `GaussLemmaGauge.metricGaussGauge_imp_hGaussGerm` applied to the interface's
    metric-side floor.  So the `hDConv` centre-identity gauge leg and the mainline gauge input are the
    SAME geometric floor — a single shared carry, NOT two independent walls.  ⚠ NOT `a₁ = R/6`. -/
theorem radialGauge_imp_mainline_hGaussGerm (g gi : Point n → Fin n → Fin n → ℝ)
    (hgauge : RadialNormalCoordinateGauge g gi) :
    ∀ i : Fin n, (fun x : Point n => ∑ j, g x i j * x j)
      =ᶠ[nhds (0 : Point n)] (fun x : Point n => x i) :=
  metricGaussGauge_imp_hGaussGerm g (metricGaussGauge_g_of_radialGauge g gi hgauge)

/-! ###############################################################################
    ### §3 — NON-VACUITY through the named-floor route (flat AND genuinely curved).
    ############################################################################### -/

/-- **`radialNormalCoordinateGauge_flat_via_floor`.**  Non-vacuity of the identification: the flat
    metric satisfies `RadialNormalCoordinateGauge` built THROUGH the named floor
    (`metricGaussGauge_flat` on both sides + centre-δ).  ⚠ NOT `a₁ = R/6`. -/
theorem radialNormalCoordinateGauge_flat_via_floor :
    RadialNormalCoordinateGauge (flatMetric n) (flatMetric n) :=
  radialNormalCoordinateGauge_of_namedFloor (flatMetric n) (flatMetric n)
    metricGaussGauge_flat metricGaussGauge_flat
    (fun i => by simp [flatMetric])

/-- **★ `radialNormalCoordinateGauge_curved_via_floor`.**  THE LOAD-BEARING non-vacuity gate: the
    genuinely CURVED witness `g^K = curvedRNCMetric κ` (`κ ≤ 0`, so `Ric(0) = (n−1)κ·δ ≠ 0`,
    `R/6 ≠ 0`) with its Sherman–Morrison inverse `gi^K = curvedRNCInv κ` satisfies
    `RadialNormalCoordinateGauge` REBUILT through the named floor: the metric side from
    `metricGaussGauge_curvedRNC`, the inverse side from `(curved_radialGauge_bundle κ hκ).2`
    (`= MetricGaussGauge gi^K`), the centre from `curvedRNCMetric_zero`.  Confirms the interface⇔floor
    identification is curvature-compatible — it does NOT collapse curvature (cf. cp466 vacuity trap).
    ⚠ NOT `a₁ = R/6`. -/
theorem radialNormalCoordinateGauge_curved_via_floor (κ : ℝ) (hκ : κ ≤ 0) :
    RadialNormalCoordinateGauge (curvedRNCMetric (n := n) κ) (curvedRNCInv (n := n) κ) :=
  radialNormalCoordinateGauge_of_namedFloor (curvedRNCMetric (n := n) κ) (curvedRNCInv (n := n) κ)
    (metricGaussGauge_curvedRNC κ)
    (fun y i => (curved_radialGauge_bundle κ hκ).2 y i)
    (fun i => by rw [curvedRNCMetric_zero]; simp)

end QIQTH.RadialGaugeIsNamedFloor

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.RadialGaugeIsNamedFloor.radialNormalCoordinateGauge_of_namedFloor
#print axioms QIQTH.RadialGaugeIsNamedFloor.metricGaussGauge_g_of_radialGauge
#print axioms QIQTH.RadialGaugeIsNamedFloor.metricGaussGauge_gi_of_radialGauge
#print axioms QIQTH.RadialGaugeIsNamedFloor.radialGauge_imp_mainline_hGaussGerm
#print axioms QIQTH.RadialGaugeIsNamedFloor.radialNormalCoordinateGauge_flat_via_floor
#print axioms QIQTH.RadialGaugeIsNamedFloor.radialNormalCoordinateGauge_curved_via_floor
