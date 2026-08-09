/-
  XSlotBaseParts — J4-475: GROUND THE x-slot BASE PARTS `hDerivX` / `hLapX` of the `htermBox` chain.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  continues the `htermBox` rung-grounding surface: J4-474 (`IterRungGrounding`) re-oriented the census
  BASE rung onto two x-slot part carries — `hDerivX` (the x-slot `∂_τ` slice) and `hLapX` (the x-slot
  VARYING-BASE Laplacian slice).  This brick grounds those two base parts ONE LEVEL DOWN, onto their
  honest lower-level suppliers, at the transport granularity of the individual carries.

  ── `hLapX` (THE VARYING-BASE LAPLACIAN — THE GATE).  The census x-slot Laplacian slice is
       `p ↦ laplaceBeltrami g gi (fun q => Wit p.1 q 0) p.2`, whose BASE POINT is `p.2` (VARYING).
       Unfolding `laplaceBeltrami` at base `p.2`:
          `∑ i, ∑ j, gi p.2 i j · (pd (fun y => pd (Wit-slice) j y) i p.2
              − ∑ k, christoffel g gi k i j p.2 · pd (Wit-slice) k p.2)`,
       so — UNLIKE the banked N3 (base `0` FIXED, where `gi 0 i j` / `christoffel g gi k i j 0` are
       CONSTANTS killed by `continuousOn_const`) — the metric factor `gi p.2 i j` and the Christoffel
       factor `christoffel g gi k i j p.2` now VARY with `p.2`.  ⚠ THE GEOMETRY GATE: their joint
       continuity is FREE from the geometry inputs — `gi`-continuity from the C² inverse-metric input
       `hgiC : ∀ i j, Continuous (gi · i j)` (the exact geometric binder the campaign carries, cf.
       `AssemblyLadderR5`), and `christoffel`-continuity from `hChr` (`ContDiff ⊤ ⟹ Continuous`).  Both
       compose with `continuous_snd` (`p ↦ p.2`).  So `hLapX` REDUCES to {`hgiC`, `hChr`} (geometry
       inputs) + the two x-slot witness-partial leaves `hpd1X` / `hpd2X` (varying-base spatial partials —
       genuinely-buried witness-slice atoms, exactly the N3 partials re-based from `0` to `p.2`).

  ── `hDerivX` (THE `∂_τ` LEG — A LEAF).  The x-slot `∂_τ` slice `p ↦ deriv (fun u => Wit u p.2 0) p.1`
       is the TIME-derivative of the witness kernel; it involves NO metric / Christoffel data, so it does
       NOT reduce to the geometry inputs.  It is an irreducible analytic leaf at this granularity — the
       exact x-slot analogue of the N2 `hDeriv` carry (which `NonLeviBoxContinuity` likewise kept as the
       "honest remaining work of the `∂_τ` leg").  It is carried, not grounded.

  ── WHAT LANDS.
    • `hLapX_box_of_parts` — ★★★ single-box varying-base Laplacian reduction (the N3 route re-based to
        `p.2`), from `hgiC` + `hChr` + the two witness partials.
    • `hLapX_grounded`     — ★★★ the census `hLapX` `∀`-family, from the `∀`-quantified partials + the
        two geometry inputs, by `hLapX_box_of_parts` per `(τ₀,R)`.
    • `hIterBase_xslot_grounded` — ★★★ THE BASE-RUNG SPLICE: the census base rung
        `p ↦ heatOp g gi Wit p.1 p.2 0`, produced from `hDerivX` (`∂_τ` leaf) + the grounded `hLapX`,
        via `IterRungGrounding.hIterBase_grounded`.
    • `xslot_residuals` (+ intro) — the enumerated surviving surface after the two base-part groundings.

  NO `sorry`, NO `:= True`, NO new axioms; std-3 only.  No existing file edited.
  ⚠  a₁ = R/6 remains CONDITIONAL.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.IterRungGrounding
import QIQTH.NonLeviBoxContinuity

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.LeviSeries QIQTH.IterEContinuity QIQTH.HeatResidualBound
open QIQTH.TrueHeatKernel QIQTH.LaplaceBeltrami
open scoped Topology Interval BigOperators

namespace QIQTH.XSlotBaseParts

variable {n : ℕ}

/-! ###############################################################################
    ### ★★★ `hLapX_box_of_parts` — the single-box VARYING-BASE Laplacian reduction.
    ############################################################################### -/

/-- **★★★ `hLapX_box_of_parts`.**  THE x-slot VARYING-BASE laplaceBeltrami-SLICE REDUCTION (single box).
    Joint `(τ,z)`-continuity of the gated van-Vleck x-slot Laplacian slice
    `p ↦ laplaceBeltrami g gi (fun q => vanVleckGatedWitness g gi hChr hK S a b p.1 q 0) p.2` on the
    positive-time box `Icc (τ₀/2) T ×ˢ closedBall 0 R`, from:
      • `hgiC`  — the C² inverse-metric continuity input `∀ i j, Continuous (gi · i j)` (geometry input);
      • `hChr`  — the Christoffel `ContDiff ⊤` input (⟹ `Continuous`, geometry input);
      • `hpd1X` — the x-slot FIRST spatial partials at VARYING base `p ↦ pd (Wit-slice) k p.2`;
      • `hpd2X` — the x-slot SECOND spatial partials at VARYING base
                  `p ↦ pd (fun y => pd (Wit-slice) j y) i p.2`.
    ⚠ THE GEOMETRY GATE (vs N3): unfold `laplaceBeltrami` at base `p.2` — a finite
    `∑_i ∑_j gi p.2 i j·(∂²f − ∑_k Γ p.2·∂f)` — whose metric / Christoffel factors VARY with `p.2`
    (they are NOT the fixed-`0` constants of N3).  Their `p`-continuity is nonetheless FREE: `gi p.2 i j`
    from `(hgiC i j).comp continuous_snd`, `christoffel g gi k i j p.2` from
    `(hChr k i j).continuous.comp continuous_snd`; then `continuousOn_finsetSum` / `.mul` / `.sub`.  The
    carried partials `hpd1X` / `hpd2X` are the varying-base witness-slice atoms; none is the conclusion.
    ⚠ NOT `a₁ = R/6`. -/
theorem hLapX_box_of_parts
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    {τ₀ : ℝ} (T R : ℝ)
    (hgiC : ∀ i j, Continuous (fun w : Point n => gi w i j))
    (hpd1X : ∀ k, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun q => vanVleckGatedWitness g gi hChr hK S a b p.1 q 0) k p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hpd2X : ∀ i j, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun y => pd (fun q => vanVleckGatedWitness g gi hChr hK S a b p.1 q 0) j y) i p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn
      (fun p : ℝ × Point n =>
        laplaceBeltrami g gi
          (fun q => vanVleckGatedWitness g gi hChr hK S a b p.1 q 0) p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
  have hEq :
      (fun p : ℝ × Point n =>
        laplaceBeltrami g gi
          (fun q => vanVleckGatedWitness g gi hChr hK S a b p.1 q 0) p.2)
      = fun p : ℝ × Point n =>
          ∑ i, ∑ j, gi p.2 i j *
            (pd (fun y =>
                  pd (fun q => vanVleckGatedWitness g gi hChr hK S a b p.1 q 0) j y) i p.2
              - ∑ k, christoffel g gi k i j p.2
                  * pd (fun q => vanVleckGatedWitness g gi hChr hK S a b p.1 q 0) k p.2) := by
    funext p; simp only [laplaceBeltrami]
  rw [hEq]
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j _
  refine (((hgiC i j).comp continuous_snd).continuousOn).mul ((hpd2X i j).sub ?_)
  apply continuousOn_finsetSum
  intro k _
  exact (((hChr k i j).continuous.comp continuous_snd).continuousOn).mul (hpd1X k)

/-! ###############################################################################
    ### ★★★ `hLapX_grounded` — the census `hLapX` `∀`-family from geometry inputs + partials.
    ############################################################################### -/

/-- **★★★ `hLapX_grounded`.**  THE `hLapX` BASE-PART DISCHARGE — the census `∀ τ₀ ∈ Ioc 0 T, ∀ R`
    x-slot varying-base Laplacian box family EXACTLY in the shape consumed by
    `IterRungGrounding.hIterBase_grounded`, obtained from the two geometry inputs (`hgiC`, `hChr`) and
    the `∀`-quantified varying-base witness partials (`hpd1X`, `hpd2X`) by `hLapX_box_of_parts` at each
    `(τ₀, R)`.  ⚠ THE GATE: the varying-base metric / Christoffel factors are continuous FOR FREE from
    the geometry inputs — so `hLapX` grounds to {geometry inputs} + {varying-base witness partials}, with
    NO extra Laplacian carry.  The partials are genuinely-buried witness-slice atoms; NOT the conclusion.
    ⚠ NOT `a₁ = R/6`. -/
theorem hLapX_grounded
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (hgiC : ∀ i j, Continuous (fun w : Point n => gi w i j))
    (hpd1X : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ k, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun q => vanVleckGatedWitness g gi hChr hK S a b p.1 q 0) k p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hpd2X : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ i j, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun y => pd (fun q => vanVleckGatedWitness g gi hChr hK S a b p.1 q 0) j y) i p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n =>
          laplaceBeltrami g gi
            (fun q => vanVleckGatedWitness g gi hChr hK S a b p.1 q 0) p.2)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
  intro τ₀ hτ₀ R
  exact hLapX_box_of_parts g gi hChr hK S a b T R hgiC (hpd1X τ₀ hτ₀ R) (hpd2X τ₀ hτ₀ R)

/-! ###############################################################################
    ### ★★★ `hIterBase_xslot_grounded` — the census BASE rung from `hDerivX` (leaf) + grounded `hLapX`.
    ############################################################################### -/

/-- **★★★ `hIterBase_xslot_grounded`.**  THE BASE-RUNG SPLICE.  The census base rung
    `p ↦ heatOp g gi Wit p.1 p.2 0` (`= iterE E 1` at `E := heatOp g gi Wit`, on each positive-time box),
    PRODUCED from:
      • `hDerivX` — the x-slot `∂_τ` leaf carry `p ↦ deriv (fun u => Wit u p.2 0) p.1` (irreducible at
        this granularity; NO geometry content — the honest remaining `∂_τ` work);
      • `hgiC` + `hChr` (geometry inputs) + `hpd1X` + `hpd2X` (varying-base witness partials), from which
        the varying-base Laplacian family `hLapX` is GROUNDED via `hLapX_grounded`,
    fed into the banked base-rung reducer `IterRungGrounding.hIterBase_grounded` (`heatOp` unfold +
    `ContinuousOn.sub`).  So the census base rung now stands on {`hDerivX`} + {geometry inputs} +
    {varying-base witness partials} — NO free-standing `hLapX` carry survives.  ⚠ NOT `a₁ = R/6`. -/
theorem hIterBase_xslot_grounded
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (hDerivX : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n =>
          deriv (fun u => vanVleckGatedWitness g gi hChr hK S a b u p.2 0) p.1)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hgiC : ∀ i j, Continuous (fun w : Point n => gi w i j))
    (hpd1X : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ k, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun q => vanVleckGatedWitness g gi hChr hK S a b p.1 q 0) k p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hpd2X : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ i j, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun y => pd (fun q => vanVleckGatedWitness g gi hChr hK S a b p.1 q 0) j y) i p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n =>
          heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) p.1 p.2 0)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) :=
  QIQTH.IterRungGrounding.hIterBase_grounded g gi hChr hK S a b T hDerivX
    (hLapX_grounded g gi hChr hK S a b T hgiC hpd1X hpd2X)

/-! ###############################################################################
    ### THE X-SLOT LEDGER — the surviving surface after the two base-part groundings.
    ############################################################################### -/

/-- **`xslot_residuals`.**  THE ENUMERATED SURVIVING SURFACE after the J4-475 base-part groundings.  A
    genuine conjunction (non-vacuous plumbing witness); each conjunct SATISFIABLE, none the conclusion.

    THE X-SLOT LEDGER (what remains carried in place of the base-rung parts `hDerivX` / `hLapX` of
    `IterRungGrounding.rung_residuals`):
      1. `hDerivX` — the x-slot `∂_τ` slice leaf `p ↦ deriv (fun u => Wit u p.2 0) p.1` (irreducible at
         this granularity; NO geometry content — the honest remaining `∂_τ` work);
      2. `hGeom`   — the geometry inputs `hgiC` (C² inverse-metric continuity `∀ i j, Continuous (gi·ij)`)
         + `hChr` (Christoffel `ContDiff ⊤`), the intended geometric floor of the campaign;
      3. `hPart`   — the varying-base x-slot witness spatial partials `hpd1X` / `hpd2X` (the N3 partials
         re-based from the fixed `0` to the varying `p.2`; genuinely-buried witness-slice atoms);
      4. `hDom`    — the UNCHANGED per-rung Gaussian domination bundle of `IterRungGrounding` (feeding the
         step rung), plus the `hRestBox` phase-12 host — carried verbatim.

    DISCHARGED (NOT in this ledger): `hLapX` — grounded to `hGeom` + `hPart` via `hLapX_grounded` (the
    varying-base metric / Christoffel factors are continuous FOR FREE from the geometry inputs, so NO
    Laplacian carry survives).  ⚠ GEOMETRY GATE: unlike N3's fixed-`0`-constant collapse, the varying-base
    factors genuinely vary with `p.2` — but a C² field's continuity is free, so they cost only the
    geometry inputs, not a new carry.  ⚠ NOT `a₁ = R/6`; CONDITIONAL on exactly this surface. -/
def xslot_residuals (hDerivX hGeom hPart hDom : Prop) : Prop :=
  hDerivX ∧ hGeom ∧ hPart ∧ hDom

/-- The x-slot ledger is a genuine conjunction projector (non-vacuous plumbing witness).
    ⚠ NOT `a₁ = R/6`. -/
theorem xslot_residuals_intro {hDerivX hGeom hPart hDom : Prop}
    (h1 : hDerivX) (h2 : hGeom) (h3 : hPart) (h4 : hDom) :
    xslot_residuals hDerivX hGeom hPart hDom :=
  ⟨h1, h2, h3, h4⟩

end QIQTH.XSlotBaseParts

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.XSlotBaseParts.hLapX_box_of_parts
#print axioms QIQTH.XSlotBaseParts.hLapX_grounded
#print axioms QIQTH.XSlotBaseParts.hIterBase_xslot_grounded
#print axioms QIQTH.XSlotBaseParts.xslot_residuals_intro
