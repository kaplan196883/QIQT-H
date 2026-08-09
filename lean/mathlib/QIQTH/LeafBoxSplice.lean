/-
  LeafBoxSplice — J4-477: SPLICE the three x-slot witness-slice leaves `hpd1X` / `hpd2X` / `hDerivX`
  into ONE box-family reduction from a SINGLE gate-regularity carry `hBoundary`, feeding
  `XSlotBaseParts.hIterBase_xslot_grounded`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  consolidates the J4-476 (`WitnessSpatialPartialsX`) per-leaf leg-triples — off-gate identically-`0`
  (DISCHARGED), in-gate reduced-to-smooth (banked), gate-boundary gluing (the honest carry) — into a
  SINGLE box-family reduction.  The three leaves' box continuity is produced from ONE gate-regularity
  carry `hBoundary` plus the banked in-gate smooth-object regularity, exactly in the shape that
  `XSlotBaseParts.hIterBase_xslot_grounded` consumes.

  ── THE GATE (the minimal `hBoundary` form — the SMALL-`R` / box-inside-gate route).  The set-gate
     `S 0` is `τ`-independent SPATIAL, evaluated at the VARYING base `p.2` which ranges over the census
     box spatial factor `closedBall 0 R`.  The WEAKEST honest sufficient gluing input that makes the
     piecewise (in-gate smooth / off-gate `0`) definition continuous on the box is that the box lies
     ENTIRELY in the (open) interior of the gate, so NO gate boundary `∂(S 0)` is ever crossed:
       `hBoundary : (0 : Point n) ∈ K ∧ Metric.closedBall (0 : Point n) R ⊆ interior (S 0)`.
     • `0 ∈ K`  — the FROZEN second slot stays on-chart (`R`-independent; the `gatedKernel` chart gate).
     • `closedBall 0 R ⊆ interior (S 0)` — every base point of the box is an INTERIOR gate point, hence
       `S 0 ∈ 𝓝 p.2` there, so the in-gate reductions of J4-476 apply uniformly and the leaves EQUAL
       the smooth objects on the whole box (`ContinuousOn.congr`).  No boundary carry survives.
     ⚠ THE ALL-`R` AUDIT (dont-undercredit; honest).  `XSlotBaseParts.hIterBase_xslot_grounded` census
     quantifies over ALL `R : ℝ`.  Requiring `closedBall 0 R ⊆ interior (S 0)` for ALL `R` forces
     `interior (S 0)` to be the whole space — i.e. this small-`R` route lands the CONSTANT-CUTOFF /
     global (gate ≡ univ) regime.  A genuinely BOUNDED gate would instead need the boundary-vanishing
     route (the smooth piece → `0` at `∂(S 0)`); that is a strictly heavier carry, deferred.  We take
     the weakest per-box form and carry the `∀ R` quantifier honestly in the ledger.

  ── THE IN-GATE SMOOTH-OBJECT REGULARITY (the banked carry the box continuity welds onto).  On the box
     the three leaves equal, respectively:
       • `hDerivX` → the parametrix `τ`-derivative slice `deriv (fun u => radialCutoff a b (W 0 p.2) *
         heatParametrix 1 (vanVleck g) Θ* u (W 0 p.2)) p.1` (`hDerivX_ingate_eq_param`), whose box
         continuity is BANKED (`NonLeviBoxContinuity.heatParametrix_deriv_t_continuousOn_box`);
       • `hpd1X` → `pd (fun x' => globalCutoffParametrixWitnessN … p.1 x' 0) k p.2`, the `C^∞`
         chart-composed composite's first spatial partial (`hpd1X_ingate_eq`);
       • `hpd2X` → `pd (fun y => pd (fun x' => globalCutoffParametrixWitnessN … p.1 x' 0) j y) i p.2`,
         its SECOND spatial partial — via `hpd1X_ingate_eq` applied on the OPEN `interior (S 0)`
         (⟹ inner first-partials eventuallyEq) then `pd_congr_of_eventuallyEq` (no banked `hpd2X`
         in-gate lemma exists, so this leg is assembled here).
     Their box `ContinuousOn` is taken as the explicit smooth-object regularity carry (parametrix /
     chart-composite smoothness bank); genuinely-buried, satisfiable, NONE the conclusion.

  ── WHAT LANDS.
    • `leafBox_of_boundary`   — ★★★ the three leaves' SINGLE-box continuity (a conjunction) from
        `hBoundary` + the J4-476 in-gate legs + the smooth-object box regularity.
    • `hIterBase_final`       — ★★★ THE SPLICE: the census base rung `p ↦ heatOp g gi Wit p.1 p.2 0`
        `∀`-family, produced by feeding the `leafBox_of_boundary` triples into
        `XSlotBaseParts.hIterBase_xslot_grounded`.
    • `splice_residuals` (+ intro) — the enumerated surviving surface (THE SPLICE LEDGER).

  NO `sorry`, NO `:= True`, NO new axioms; std-3 only.  No existing file edited.
  ⚠  a₁ = R/6 remains CONDITIONAL.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.WitnessSpatialPartialsX
import QIQTH.XSlotBaseParts

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.LeviSeries QIQTH.HeatResidualBound
open QIQTH.TrueHeatKernel QIQTH.LaplaceBeltrami
open QIQTH.HeatParametrixAnsatz QIQTH.HeatTransportRecursion
open QIQTH.ParametrixFunction QIQTH.VanVleck
open QIQTH.UngatedChainRule QIQTH.WitnessSpatialPartialsX
open scoped Topology Interval BigOperators

namespace QIQTH.LeafBoxSplice

variable {n : ℕ}

/-! ###############################################################################
    ### ★★★ `leafBox_of_boundary` — the three leaves' SINGLE-box continuity from `hBoundary`.
    ############################################################################### -/

/-- **★★★ `leafBox_of_boundary`.**  THE SINGLE-BOX THREE-LEAF REDUCTION.  On the positive-time census box
    `Icc (τ₀/2) T ×ˢ closedBall 0 R`, from the SINGLE gate-regularity carry
      `hBoundary : (0 : Point n) ∈ K ∧ closedBall 0 R ⊆ interior (S 0)`
    (the box lies entirely in the open gate interior — no `∂(S 0)` crossed) PLUS the banked in-gate
    smooth-object box regularity:
      • `hParamDeriv` — box continuity of the parametrix `τ`-derivative slice (the `hDerivX` weld target);
      • `hComposite1` — box continuity of the `C^∞` composite's first spatial partial (per `k`);
      • `hComposite2` — box continuity of the composite's SECOND spatial partial (per `i j`),
    the three x-slot witness-slice leaves are jointly box-continuous:
      • `hpd1X`  — `p ↦ pd (fun q => Wit p.1 q 0) k p.2`  (`hpd1X_ingate_eq` + `ContinuousOn.congr`);
      • `hpd2X`  — `p ↦ pd (fun y => pd (fun q => Wit p.1 q 0) j y) i p.2`
                    (`hpd1X_ingate_eq` on the open `interior (S 0)` ⟹ eventuallyEq inner partials ⟹
                     `pd_congr_of_eventuallyEq`, then `ContinuousOn.congr`);
      • `hDerivX` — `p ↦ deriv (fun u => Wit u p.2 0) p.1`  (`hDerivX_ingate_eq_param` +
                    `ContinuousOn.congr`).
    ⚠ NOT `a₁ = R/6`. -/
theorem leafBox_of_boundary
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    {τ₀ : ℝ} (T R : ℝ)
    (hBoundary : (0 : Point n) ∈ K ∧
      Metric.closedBall (0 : Point n) R ⊆ interior (S (0 : Point n)))
    (hParamDeriv : ContinuousOn
      (fun p : ℝ × Point n =>
        deriv (fun u => radialCutoff a b (uniformInverseChart g gi hChr hK 0 p.2)
            * heatParametrix 1 (vanVleck g)
                (transportCoeff (transportOp (vanVleck g) g gi)) u
                (uniformInverseChart g gi hChr hK 0 p.2)) p.1)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hComposite1 : ∀ k, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun x' : Point n => globalCutoffParametrixWitnessN 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) a b
              (uniformInverseChart g gi hChr hK) p.1 x' 0) k p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hComposite2 : ∀ i j, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun y : Point n =>
              pd (fun x' : Point n => globalCutoffParametrixWitnessN 1 (vanVleck g)
                    (transportCoeff (transportOp (vanVleck g) g gi)) a b
                    (uniformInverseChart g gi hChr hK) p.1 x' 0) j y) i p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    (∀ k, ContinuousOn
        (fun p : ℝ × Point n =>
          pd (fun q => vanVleckGatedWitness g gi hChr hK S a b p.1 q 0) k p.2)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
      ∧ (∀ i j, ContinuousOn
        (fun p : ℝ × Point n =>
          pd (fun y => pd (fun q => vanVleckGatedWitness g gi hChr hK S a b p.1 q 0) j y) i p.2)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
      ∧ ContinuousOn
        (fun p : ℝ × Point n =>
          deriv (fun u => vanVleckGatedWitness g gi hChr hK S a b u p.2 0) p.1)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
  obtain ⟨hK0, hsub⟩ := hBoundary
  refine ⟨?_, ?_, ?_⟩
  · -- hpd1X: weld onto the composite first partial via `hpd1X_ingate_eq`.
    intro k
    refine (hComposite1 k).congr (fun p hp => ?_)
    have hp2 : p.2 ∈ Metric.closedBall (0 : Point n) R := hp.2
    have hxint : p.2 ∈ interior (S (0 : Point n)) := hsub hp2
    have hgate : S (0 : Point n) ∈ nhds p.2 := mem_interior_iff_mem_nhds.mp hxint
    exact hpd1X_ingate_eq g gi hChr hK S a b k p.1 p.2 hK0 hgate
  · -- hpd2X: inner first-partials eventuallyEq on the open interior, then `pd_congr_of_eventuallyEq`.
    intro i j
    refine (hComposite2 i j).congr (fun p hp => ?_)
    have hp2 : p.2 ∈ Metric.closedBall (0 : Point n) R := hp.2
    have hxint : p.2 ∈ interior (S (0 : Point n)) := hsub hp2
    have hnhd : interior (S (0 : Point n)) ∈ nhds p.2 := isOpen_interior.mem_nhds hxint
    have hinnerEq :
        (fun y => pd (fun q => vanVleckGatedWitness g gi hChr hK S a b p.1 q 0) j y)
          =ᶠ[nhds p.2]
        (fun y => pd (fun x' : Point n => globalCutoffParametrixWitnessN 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) a b
              (uniformInverseChart g gi hChr hK) p.1 x' 0) j y) := by
      filter_upwards [hnhd] with y hy
      have hgatey : S (0 : Point n) ∈ nhds y := mem_interior_iff_mem_nhds.mp hy
      exact hpd1X_ingate_eq g gi hChr hK S a b j p.1 y hK0 hgatey
    exact QIQTH.D2HExpandRecon.pd_congr_of_eventuallyEq _ _ i p.2 hinnerEq
  · -- hDerivX: weld onto the parametrix τ-derivative via `hDerivX_ingate_eq_param`.
    refine hParamDeriv.congr (fun p hp => ?_)
    have hp2 : p.2 ∈ Metric.closedBall (0 : Point n) R := hp.2
    have hxint : p.2 ∈ interior (S (0 : Point n)) := hsub hp2
    have hxS : p.2 ∈ S (0 : Point n) := interior_subset hxint
    exact hDerivX_ingate_eq_param g gi hChr hK S a b p.1 p.2 hK0 hxS

/-! ###############################################################################
    ### ★★★ `hIterBase_final` — the SPLICE into `XSlotBaseParts.hIterBase_xslot_grounded`.
    ############################################################################### -/

/-- **★★★ `hIterBase_final`.**  THE SPLICE.  The census base rung `p ↦ heatOp g gi Wit p.1 p.2 0`
    `∀ τ₀ ∈ Ioc 0 T, ∀ R` family, produced by feeding the three per-box leaf continuities of
    `leafBox_of_boundary` into `XSlotBaseParts.hIterBase_xslot_grounded`.  All three leaves now stand on
    the SINGLE `∀ R` gate-regularity carry `hBoundary` (`0 ∈ K` + `closedBall 0 R ⊆ interior (S 0)`),
    the geometry input `hgiC`, and the banked in-gate smooth-object box regularity
    (`hParamDeriv` / `hComposite1` / `hComposite2`).  ⚠ NOT `a₁ = R/6`. -/
theorem hIterBase_final
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (hgiC : ∀ i j, Continuous (fun w : Point n => gi w i j))
    (hBoundary : (0 : Point n) ∈ K ∧
      ∀ R : ℝ, Metric.closedBall (0 : Point n) R ⊆ interior (S (0 : Point n)))
    (hParamDeriv : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ContinuousOn
      (fun p : ℝ × Point n =>
        deriv (fun u => radialCutoff a b (uniformInverseChart g gi hChr hK 0 p.2)
            * heatParametrix 1 (vanVleck g)
                (transportCoeff (transportOp (vanVleck g) g gi)) u
                (uniformInverseChart g gi hChr hK 0 p.2)) p.1)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hComposite1 : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ k, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun x' : Point n => globalCutoffParametrixWitnessN 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) a b
              (uniformInverseChart g gi hChr hK) p.1 x' 0) k p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hComposite2 : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ i j, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun y : Point n =>
              pd (fun x' : Point n => globalCutoffParametrixWitnessN 1 (vanVleck g)
                    (transportCoeff (transportOp (vanVleck g) g gi)) a b
                    (uniformInverseChart g gi hChr hK) p.1 x' 0) j y) i p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n =>
          heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) p.1 p.2 0)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
  obtain ⟨hK0, hsub⟩ := hBoundary
  -- Assemble the three ∀-families from `leafBox_of_boundary` at each `(τ₀, R)`.
  have hLeaf : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      (∀ k, ContinuousOn
          (fun p : ℝ × Point n =>
            pd (fun q => vanVleckGatedWitness g gi hChr hK S a b p.1 q 0) k p.2)
          (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
        ∧ (∀ i j, ContinuousOn
          (fun p : ℝ × Point n =>
            pd (fun y => pd (fun q => vanVleckGatedWitness g gi hChr hK S a b p.1 q 0) j y) i p.2)
          (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
        ∧ ContinuousOn
          (fun p : ℝ × Point n =>
            deriv (fun u => vanVleckGatedWitness g gi hChr hK S a b u p.2 0) p.1)
          (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
    intro τ₀ hτ₀ R
    exact leafBox_of_boundary g gi hChr hK S a b T R ⟨hK0, hsub R⟩
      (hParamDeriv τ₀ hτ₀ R) (hComposite1 τ₀ hτ₀ R) (hComposite2 τ₀ hτ₀ R)
  refine QIQTH.XSlotBaseParts.hIterBase_xslot_grounded g gi hChr hK S a b T
    (fun τ₀ hτ₀ R => (hLeaf τ₀ hτ₀ R).2.2) hgiC
    (fun τ₀ hτ₀ R => (hLeaf τ₀ hτ₀ R).1)
    (fun τ₀ hτ₀ R => (hLeaf τ₀ hτ₀ R).2.1)

/-! ###############################################################################
    ### THE SPLICE LEDGER — the surviving surface after the three-leaf box splice.
    ############################################################################### -/

/-- **`splice_residuals`.**  THE ENUMERATED SURVIVING SURFACE after the J4-477 three-leaf box splice.
    A genuine conjunction (non-vacuous plumbing witness); each conjunct SATISFIABLE, none the conclusion.

    THE SPLICE LEDGER — the `htermBox` chain's final state after the census base rung
    `hIterBase_xslot_grounded` is fed by `hIterBase_final`:
      1. `hGeom`     — the geometry floor: `hgiC` (C² inverse-metric continuity
         `∀ i j, Continuous (gi·ij)`) + `hChr` (Christoffel `ContDiff ⊤`).  Carried verbatim.
      2. `hSmooth`   — the IN-GATE smooth-object box regularity (`hParamDeriv` + `hComposite1` +
         `hComposite2`): box continuity of the parametrix `τ`-derivative slice and of the `C^∞`
         chart-composed composite's first / second spatial partials.  Banked (parametrix /
         chart-composite smoothness); genuinely-buried; none the conclusion.
      3. `hBoundary` — THE SINGLE GATE-REGULARITY CARRY: `0 ∈ K` (frozen slot on-chart) +
         `∀ R, closedBall 0 R ⊆ interior (S 0)` (the box stays in the open gate interior, no
         `∂(S 0)` crossed).  ⚠ the all-`R` census forces the global (gate ≡ univ) regime; a bounded
         gate would need the strictly-heavier boundary-vanishing route (deferred).  The honest carry.
      4. `hDom`      — the UNCHANGED per-rung Gaussian domination bundle of `IterRungGrounding` (feeding
         the STEP rung) + the `hRestBox` phase-12 host, carried verbatim from `XSlotBaseParts`.

    DISCHARGED (NOT in this ledger): the OFF-GATE / OFF-CHART legs (all `0`, J4-476) and the LEAF ⇒
    SMOOTH-OBJECT welds (`ContinuousOn.congr` on the in-gate box); the varying-base Laplacian `hLapX`
    (J4-475, free from the geometry inputs).  ⚠ NOT `a₁ = R/6`; CONDITIONAL on exactly this surface. -/
def splice_residuals (hGeom hSmooth hBoundary hDom : Prop) : Prop :=
  hGeom ∧ hSmooth ∧ hBoundary ∧ hDom

/-- The splice ledger is a genuine conjunction projector (non-vacuous plumbing witness).
    ⚠ NOT `a₁ = R/6`. -/
theorem splice_residuals_intro {hGeom hSmooth hBoundary hDom : Prop}
    (h1 : hGeom) (h2 : hSmooth) (h3 : hBoundary) (h4 : hDom) :
    splice_residuals hGeom hSmooth hBoundary hDom :=
  ⟨h1, h2, h3, h4⟩

end QIQTH.LeafBoxSplice

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.LeafBoxSplice.leafBox_of_boundary
#print axioms QIQTH.LeafBoxSplice.hIterBase_final
#print axioms QIQTH.LeafBoxSplice.splice_residuals_intro
