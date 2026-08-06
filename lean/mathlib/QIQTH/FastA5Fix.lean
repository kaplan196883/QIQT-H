/-
  FastA5Fix — J4-302: the FAST frozen-base full-gate capstone (the A5 fix).

  Context: the `a₁ = R/6` campaign, the Levi-continuity endgame.  `QIQTH.FullGateAssembly` (J4-301)
  banked the GENERIC transition-annulus core
      `heatOp_cutoffChart_jointContinuousOn_at` (A4) :
        `ContinuousOn (fun p => heatOp g gi (fun s x _ => radialCutoff a b (W₀ x)
            · heatParametrix N Θ u s (W₀ x)) p.1 p.2 q) (Icc t₁ t₂ ×ˢ closedBall c R)`
  — the mathematical content of T3 (plateau ∪ transition annulus in ONE product-rule argument), stated
  in the ABSTRACT `W₀`-generic cutoff·parametrix chart-composed KERNEL form.

  The CONCRETE frozen-base-`w` capstone (`E := heatOp (vanVleckGatedWitness …) (·,·,w)` continuity on the
  gate compact) was DEFERRED in `FullGateAssembly` because the obvious route — `A4.congr` with the F2
  reduction `FrozenBaseWChain.heatOpWitness_eq_heatOp_cutoffChart_at` — TYPECHECKS but elaborates in
  ~52 minutes: the `.congr` forces a `ContinuousOn`-LEVEL defeq of A4's abstract kernel against
  `heatOp (globalCutoffParametrixWitnessN 1 …)` with the `.choose`-heavy `uniformInverseChart`/
  `transportOp` terms substituted, re-triggering the heavy `heatOp`/`laplaceBeltrami`/`deriv`
  typeclass+whnf search over the kernel INSIDE the `ContinuousOn` obligation.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  THE FIX (this file).  Make the reduction a chain of SYNTACTIC `ContinuousOn.congr` steps whose
  `EqOn` witnesses are SCALAR equalities proved OUTSIDE any `ContinuousOn` obligation, so no
  `heatOp`-through-`ContinuousOn` defeq is ever forced.

    * (F5b') `heatOp_globalCutoff_eq_A4kernel_at` — the SCALAR kernel bridge.  At the FIXED base slot `w`,
      `heatOp` of the `globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK)` witness
      EQUALS `heatOp` of the A4 abstract kernel `fun s x _ => radialCutoff a b (W w x)·heatParametrix 1 Θ
      u s (W w x)` (with `W w = uniformInverseChart g gi hC hK w`).  Proof: `unfold heatOp` exposes the
      `globalCutoffParametrixWitnessN` occurrences FULLY APPLIED (`… u z w` / `… τ p w`); `simp only
      [globalCutoffParametrixWitnessN]` collapses the product def and the two sides become the same
      `deriv − laplaceBeltrami` of definitionally-equal sections (`Vmap w · = uniformInverseChart … w ·`).
      This is a cheap scalar/germ collapse, NOT a `ContinuousOn` defeq.

    * (F5b) `A4_concrete_continuousOn` — the A4 generic core APPLIED at the concrete data
      (`N = 1`, `Θ = vanVleck g`, `u = transportCoeff (transportOp (vanVleck g) g gi)`,
      `W₀ = uniformInverseChart g gi hC hK w`, centre/base `c = q = w`).  Pure function application;
      its conclusion is stated in the NAMED-definition A4-kernel form (no `.choose` unfolding).

    * (F5c) `heatOpWitness_fixedBase_fullGate` — THE FAST CONCRETE CAPSTONE.  Two `ContinuousOn.congr`
      steps: (i) transport A4-concrete (F5b) to the `globalCutoffParametrixWitnessN` form via the scalar
      bridge F5b' as an `EqOn`; (ii) transport that to the `vanVleckGatedWitness` form via the banked F2
      reduction `heatOpWitness_eq_heatOp_cutoffChart_at` as an `EqOn`.  Both `EqOn` witnesses are honest
      pointwise scalar equalities; neither `.congr` touches the `heatOp` kernel through a `ContinuousOn`
      obligation.  This is the ~52-min A5 re-landed as a FAST syntactic reduction over the banked core.

    * (F5d) `heatOpWitness_fixedBase_fullGate_chartFree` — F5c with the chart `C²` region INTERNAL: the
      `hWcd` carry is discharged from F1 `FrozenBaseWChain.chartField_contDiffOn_ball_at` (the `C²` ball
      `ball w ρc` of `W w` about its centre `w`), producing the radius `ρc` existentially.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  No `sorry` (this header prose aside), no new axioms, no `:= True`, no vacuous or
     unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing
     file edited.  The carries — the chart `C²` region (`hWcd`/F1), the gate data (`hwK`/`hSopen`/`hsub`),
     the coefficient regularity (`hw`/`hΘc`/`hΘne`/`huc`), the geometry continuities (`hgi`/`hChr`), the
     inverse-metric symmetry `hgisymm` — are all genuine and satisfiable; none is the conclusion.  The
     origin-vs-`w` reconciliation (`closedBall 0 R` slab) is the SAME named residual carried by
     `FrozenBaseWChain` / `GapACoverGapB`, NOT discharged here.  **NOT `a₁ = R/6`** — this is a
     regularity/coverage brick; it says NOTHING new about the curvature value.
-/
import Mathlib
import QIQTH.FullGateAssembly
import QIQTH.FrozenBaseWChain

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.HeatParametrixAnsatz QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.FullGateAssembly QIQTH.FrozenBaseWChain
open scoped Topology ContDiff

namespace QIQTH.FastA5Fix

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ## (F5b') — the SCALAR kernel bridge (fixed base `w`).
    ############################################################################### -/

/-- **★ (F5b') `heatOp_globalCutoff_eq_A4kernel_at`.**  At the FIXED base slot `w`, the spatial heat
    operator of the order-1 global-cutoff parametrix witness `globalCutoffParametrixWitnessN 1 Θ u a b
    (uniformInverseChart g gi hC hK)` equals that of the A4 abstract chart-composed kernel
    `fun s x _ => radialCutoff a b (W w x) · heatParametrix 1 Θ u s (W w x)` with
    `W w = uniformInverseChart g gi hC hK w`.  `heatOp` reads its kernel ONLY at base slot `w`, so the two
    kernel sections agree definitionally after `unfold heatOp` + `simp only [globalCutoffParametrixWitnessN]`
    (the product def collapses; `Vmap w · = uniformInverseChart … w ·`).  A SCALAR germ collapse — never a
    `ContinuousOn` obligation.  NOT `a₁ = R/6`. -/
theorem heatOp_globalCutoff_eq_A4kernel_at (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ)
    (w : Point n) (τ : ℝ) (z : Point n) :
    heatOp g gi (globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK)) τ z w
      = heatOp g gi (fun s x (_ : Point n) =>
          radialCutoff a b (uniformInverseChart g gi hC hK w x)
            * heatParametrix 1 Θ u s (uniformInverseChart g gi hC hK w x)) τ z w := by
  unfold heatOp
  simp only [globalCutoffParametrixWitnessN]

/-! ###############################################################################
    ## (F5b) — the A4 generic core applied at the concrete data.
    ############################################################################### -/

/-- **★ (F5b) `A4_concrete_continuousOn`.**  The GENERIC CORE `A4`
    (`FullGateAssembly.heatOp_cutoffChart_jointContinuousOn_at`) APPLIED at the concrete frozen-base data
    (`N = 1`, `Θ = vanVleck g`, `u = transportCoeff (transportOp (vanVleck g) g gi)`,
    `W₀ = uniformInverseChart g gi hC hK w`, centre/base `c = q = w`).  Pure function application; the
    conclusion is stated in the NAMED-definition A4-kernel form so no `.choose` unfolding is forced.  All
    carries are the genuine A4 carries (chart `C²` region `hWcd`, coefficient regularity, geometry
    continuities, metric symmetry).  NOT `a₁ = R/6`. -/
theorem A4_concrete_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (t₁ t₂ R ρc : ℝ) (w : Point n)
    (ht₁ : 0 < t₁) (hRρc : R < ρc)
    (hWcd : ContDiffOn ℝ 2 (uniformInverseChart g gi hC hK w) (Metric.ball w ρc))
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hΘc : Continuous (vanVleck g)) (hΘne : ∀ w', vanVleck g w' ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hgi : ∀ i j, ContinuousOn (fun p : ℝ × Point n => gi p.2 i j)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R))
    (hChr : ∀ k i j, ContinuousOn (fun p : ℝ × Point n => christoffel g gi k i j p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R))
    (hgisymm : ∀ z i j, gi z i j = gi z j i) :
    ContinuousOn (fun p : ℝ × Point n =>
        heatOp g gi (fun s x (_ : Point n) =>
          radialCutoff a b (uniformInverseChart g gi hC hK w x)
            * heatParametrix 1 (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) s
                (uniformInverseChart g gi hC hK w x)) p.1 p.2 w)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R) :=
  heatOp_cutoffChart_jointContinuousOn_at 1 g gi a b (vanVleck g)
    (transportCoeff (transportOp (vanVleck g) g gi)) (uniformInverseChart g gi hC hK w)
    w w t₁ t₂ R ρc ht₁ hRρc hWcd hw hΘc hΘne huc hgi hChr hgisymm

/-! ###############################################################################
    ## (F5c) — THE FAST CONCRETE FULL-GATE CAPSTONE.
    ############################################################################### -/

/-- **★★★ (F5c) `heatOpWitness_fixedBase_fullGate` — THE FAST FROZEN-BASE FULL-GATE CAPSTONE.**  The
    concrete base-`w` gated van-Vleck witness heat operator
        `E p := heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w`
    is `ContinuousOn (Icc t₁ t₂ ×ˢ closedBall w R)` (PLATEAU ∪ transition ANNULUS in one product-rule
    argument, covering the whole gate compact `closedBall w R ⊆ S w`).  This is the A5 capstone deferred
    in `FullGateAssembly`, re-landed as a FAST syntactic reduction: two `ContinuousOn.congr` steps over
    the banked generic core A4 (F5b), each `EqOn` witness a SCALAR equality — (i) the kernel bridge F5b'
    to the `globalCutoffParametrixWitnessN` form, (ii) the banked F2 reduction
    `heatOpWitness_eq_heatOp_cutoffChart_at` to the `vanVleckGatedWitness` form.  No `heatOp` kernel defeq
    is ever forced inside a `ContinuousOn` obligation.  Carries: the gate data (`hwK`/`hSopen`/`hsub`),
    the chart `C²` region `hWcd` (F1), the coefficient regularity, the geometry continuities, and the
    metric symmetry `hgisymm`.  None is the conclusion.  Co-centred at `w`; the origin-vs-`w`
    reconciliation is the named residual.  NOT `a₁ = R/6`. -/
theorem heatOpWitness_fixedBase_fullGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ R ρc : ℝ) {w : Point n} (ht₁ : 0 < t₁) (hRρc : R < ρc)
    (hwK : w ∈ K) (hSopen : IsOpen (S w)) (hsub : Metric.closedBall w R ⊆ S w)
    (hWcd : ContDiffOn ℝ 2 (uniformInverseChart g gi hC hK w) (Metric.ball w ρc))
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hΘc : Continuous (vanVleck g)) (hΘne : ∀ w', vanVleck g w' ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hgi : ∀ i j, ContinuousOn (fun p : ℝ × Point n => gi p.2 i j)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R))
    (hChr : ∀ k i j, ContinuousOn (fun p : ℝ × Point n => christoffel g gi k i j p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R))
    (hgisymm : ∀ z i j, gi z i j = gi z j i) :
    ContinuousOn (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R) := by
  -- (F5b) A4 generic core at the concrete data (A4-kernel form).
  have hA4 := A4_concrete_continuousOn g gi hC hK a b t₁ t₂ R ρc w ht₁ hRρc hWcd hw hΘc hΘne huc
    hgi hChr hgisymm
  -- (i) transport to the `globalCutoffParametrixWitnessN` form via the scalar bridge F5b'.
  have hglobal : ContinuousOn (fun p : ℝ × Point n =>
      heatOp g gi (globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b
        (uniformInverseChart g gi hC hK)) p.1 p.2 w)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R) :=
    hA4.congr (fun p _ => heatOp_globalCutoff_eq_A4kernel_at g gi hC hK (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b w p.1 p.2)
  -- (ii) transport to the `vanVleckGatedWitness` form via the banked F2 reduction.
  exact hglobal.congr (fun p hp =>
    heatOpWitness_eq_heatOp_cutoffChart_at g gi hC hK S a b t₁ t₂ R hwK hSopen hsub p hp)

/-! ###############################################################################
    ## (F5d) — chart-region internalization (the `hWcd` carry discharged from F1).
    ############################################################################### -/

/-- **★★ (F5d) `heatOpWitness_fixedBase_fullGate_chartFree`.**  The fast full-gate capstone F5c with the
    chart `C²` carry `hWcd` made INTERNAL: there is a radius `ρc > 0` (the `C²` region of
    `W w = uniformInverseChart g gi hC hK w` about its field centre `w`, from F1
    `FrozenBaseWChain.chartField_contDiffOn_ball_at`) such that for EVERY `R < ρc`, given the honest
    remaining carries — gate data / coefficient regularity / geometry continuities / metric symmetry —
    `E(·,·,w)` is `ContinuousOn (Icc t₁ t₂ ×ˢ closedBall w R)`.  NOT `a₁ = R/6`. -/
theorem heatOpWitness_fixedBase_fullGate_chartFree (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ : ℝ) {w : Point n} (ht₁ : 0 < t₁) (hwK : w ∈ K)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hΘc : Continuous (vanVleck g)) (hΘne : ∀ w', vanVleck g w' ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ ρc : ℝ, 0 < ρc ∧ ∀ R : ℝ, 0 < R → R < ρc →
      IsOpen (S w) →
      Metric.closedBall w R ⊆ S w →
      (∀ i j, ContinuousOn (fun p : ℝ × Point n => gi p.2 i j)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R)) →
      (∀ k i j, ContinuousOn (fun p : ℝ × Point n => christoffel g gi k i j p.2)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R)) →
      (∀ z i j, gi z i j = gi z j i) →
      ContinuousOn (fun p : ℝ × Point n =>
          heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R) := by
  obtain ⟨ρc, hρc, hball⟩ := chartField_contDiffOn_ball_at g gi hC hK hwK
  refine ⟨ρc, hρc, fun R hRpos hRρc hSopen hsub hgi hChr hgisymm => ?_⟩
  exact heatOpWitness_fixedBase_fullGate g gi hC hK S a b t₁ t₂ R ρc ht₁ hRρc hwK hSopen hsub hball
    hw hΘc hΘne huc hgi hChr hgisymm

#check @heatOp_globalCutoff_eq_A4kernel_at
#check @A4_concrete_continuousOn
#check @heatOpWitness_fixedBase_fullGate
#check @heatOpWitness_fixedBase_fullGate_chartFree

end QIQTH.FastA5Fix

/-! ## Axiom checks — every theorem should be `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.FastA5Fix
#print axioms heatOp_globalCutoff_eq_A4kernel_at
#print axioms A4_concrete_continuousOn
#print axioms heatOpWitness_fixedBase_fullGate
#print axioms heatOpWitness_fixedBase_fullGate_chartFree
end AxiomChecks
