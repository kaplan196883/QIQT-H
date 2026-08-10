/-
  HfgRadiusSelection — J4-522: the `hfgBundle` RADIUS-SELECTION wiring lemma.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure regularity-plumbing brick: it selects the existential radius `Rg` demanded by the boundary-chain
  `hfgBundle` carry from the already-banked base-`w` local continuity.  No `sorry` (header prose
  excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to
  (or trivially yielding) the conclusion, no existing file edited.

  ── THE PROBLEM (from the audit).
     The boundary-limit consumer (`EnvelopeWiringLocUnif` / `MovingCorrRecombination`, feeding the
     capstone `A1R6FromLabelledCurvedBoundary`) carries, for each base point `w ∈ K`, the bundle
        `hfgBundle : ∀ w ∈ K, ∀ s₁ s₂, 0 < s₁ → ∃ Rg cw ρ₀w C_Dw,
             0 < Rg ∧ ContinuousOn (E(·,·,w)) (Icc s₁ s₂ ×ˢ closedBall w Rg) ∧ (geometry) ∧
             b + C_Dw·b·b < Rg`,
     with `E τ z w := heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) τ z w`.  The genuine analytic
     content — the joint `(τ,z)`-continuity of `E(·,·,w)` on a positive-time compact — is ALREADY
     DERIVED by `FrozenBaseWChain.heatOpWitness_fixedBase_active_chartFree` (J4-293), but ONLY for radii
     `R < ρc`, where `ρc` is the `C²` region radius of the frozen chart `W w`.  The remaining gap is
     purely the SELECTION of an `Rg` that simultaneously lies below `ρc` AND above the geometric floor
     `b + C_Dw·b·b`.  That selection is possible EXACTLY when the honest margin `b + C_Dw·b·b < ρc`
     holds (the near-diagonal cutoff scale `b` fits strictly inside the chart region) — this file makes
     that margin an EXPOSED hypothesis, never hidden.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).

    * `exists_fgRadius_of_local_continuousOn` — ★★ THE RADIUS SELECTION.  Abstract: from a local
      `ContinuousOn F` on `Icc s₁ s₂ ×ˢ closedBall w R` for every `0 < R < ρc`, the exposed margin
      `b + C_D·b·b < ρc`, and any threaded geometry predicate `Geom`, produce the `hfgBundle`-shaped
      existential `∃ Rg, 0 < Rg ∧ ContinuousOn F … ∧ Geom ∧ b + C_D·b·b < Rg` at the midpoint radius
      `Rg = (max 0 (b+C_D·b·b) + ρc)/2`.  Pure order arithmetic (`max_lt`, `linarith`); NONE of the
      carried data is the conclusion.  The `max 0` guard removes any nonnegativity side-condition on the
      floor.

    * `witness_exists_fgRadius` — ★ the CONCRETE restatement at the Levi residual
      `F = fun p => heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w`: the exact
      continuity+margin core of `hfgBundle` at base `w`, from the banked local continuity `hcont`
      (dischargeable by `FrozenBaseWChain.heatOpWitness_fixedBase_active_chartFree` once the gate /
      cutoff-germ / geometry carries are supplied), the exposed margin, and the threaded geometry.

  ── HONEST RESIDUAL (precisely named; NOT the conclusion, NOT `a₁ = R/6`).
     This file selects the radius; it does NOT re-derive the local continuity (that is the banked
     `FrozenBaseWChain` chain) and does NOT establish the margin `b + C_Dw·b·b < ρc` (a genuine
     near-diagonal geometry fact, carried).  The `hbase` sibling (`∀ R > 0`, unbounded) is a STRICTLY
     larger claim — its `R ≥ ρc` tail needs a separate global off-support/local-zero lemma and is NOT
     touched here (per the J4-522 Sol audit).

  ⚠  STILL NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.FrozenBaseWChain

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open scoped Topology

namespace QIQTH.HfgRadiusSelection

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### The radius selection (abstract).
    ############################################################################### -/

/-- **★★ `exists_fgRadius_of_local_continuousOn` — THE `hfgBundle` RADIUS SELECTION.**  Given
    a family map `F : ℝ × Point n → Y`, a base point `w`, a time window `[s₁,s₂]`, a cutoff scale `b`,
    a remainder constant `C_D`, and a positive `C²`-region radius `ρc`, together with:
      • `hmargin` — the EXPOSED near-diagonal margin `b + C_D·b·b < ρc` (never hidden), and
      • `hcont` — the banked LOCAL continuity `ContinuousOn F (Icc s₁ s₂ ×ˢ closedBall w R)` for every
        `0 < R < ρc` (positive-time domain PRESERVED — this lemma introduces no `t = 0` claim), and
      • `hgeom` — any threaded geometry predicate `Geom`,
    there is an admissible radius `Rg` (the midpoint `(max 0 (b+C_D·b·b) + ρc)/2`) delivering the exact
    `hfgBundle` existential:
      `∃ Rg, 0 < Rg ∧ ContinuousOn F (Icc s₁ s₂ ×ˢ closedBall w Rg) ∧ Geom ∧ b + C_D·b·b < Rg`.
    Pure order arithmetic; curved-generic (no metric assumption on `F`); none of the data is the
    conclusion.  NOT `a₁ = R/6`. -/
theorem exists_fgRadius_of_local_continuousOn
    {Y : Type*} [TopologicalSpace Y]
    (F : ℝ × Point n → Y) (w : Point n) (s₁ s₂ b C_D ρc : ℝ) (Geom : Prop)
    (hρc : 0 < ρc)
    (hmargin : b + C_D * b * b < ρc)
    (hcont : ∀ R : ℝ, 0 < R → R < ρc →
      ContinuousOn F (Set.Icc s₁ s₂ ×ˢ Metric.closedBall w R))
    (hgeom : Geom) :
    ∃ Rg : ℝ, 0 < Rg ∧
      ContinuousOn F (Set.Icc s₁ s₂ ×ˢ Metric.closedBall w Rg) ∧
      Geom ∧ b + C_D * b * b < Rg := by
  set L : ℝ := max 0 (b + C_D * b * b) with hL
  set Rg : ℝ := (L + ρc) / 2 with hRg
  have hL0 : 0 ≤ L := le_max_left _ _
  have hLmarg : b + C_D * b * b ≤ L := le_max_right _ _
  have hLlt : L < ρc := max_lt hρc hmargin
  have hRgpos : 0 < Rg := by rw [hRg]; linarith
  have hRglt : Rg < ρc := by rw [hRg]; linarith
  have hmarglt : b + C_D * b * b < Rg := by rw [hRg]; linarith
  exact ⟨Rg, hRgpos, hcont Rg hRgpos hRglt, hgeom, hmarglt⟩

/-! ###############################################################################
    ### The concrete restatement at the Levi residual `E(·,·,w)`.
    ############################################################################### -/

/-- **★ `witness_exists_fgRadius` — the CONCRETE `hfgBundle` continuity+margin core.**  The radius
    selection specialized to the concrete gated van-Vleck witness heat operator
      `F = fun p => heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w`
    (the Levi residual at frozen base point `w`).  From the exposed margin `b + C_D·b·b < ρc`, the
    banked base-`w` local continuity `hcont` (each rung dischargeable by
    `FrozenBaseWChain.heatOpWitness_fixedBase_active_chartFree` after supplying its gate / cutoff-germ /
    geometry carries), and the threaded geometry `Geom`, it delivers the exact continuity-and-margin
    portion of the `hfgBundle` bundle at `w`:
      `∃ Rg, 0 < Rg ∧ ContinuousOn (E(·,·,w)) (Icc s₁ s₂ ×ˢ closedBall w Rg) ∧ Geom ∧ b + C_D·b·b < Rg`.
    Positive-time domain preserved (via `hcont`); curved-generic; none of the carries is the
    conclusion.  NOT `a₁ = R/6`. -/
theorem witness_exists_fgRadius
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (w : Point n) (s₁ s₂ C_D ρc : ℝ) (Geom : Prop)
    (hρc : 0 < ρc)
    (hmargin : b + C_D * b * b < ρc)
    (hcont : ∀ R : ℝ, 0 < R → R < ρc →
      ContinuousOn
        (fun p : ℝ × Point n =>
          heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
        (Set.Icc s₁ s₂ ×ˢ Metric.closedBall w R))
    (hgeom : Geom) :
    ∃ Rg : ℝ, 0 < Rg ∧
      ContinuousOn
        (fun p : ℝ × Point n =>
          heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
        (Set.Icc s₁ s₂ ×ˢ Metric.closedBall w Rg) ∧
      Geom ∧ b + C_D * b * b < Rg :=
  exists_fgRadius_of_local_continuousOn
    (fun p : ℝ × Point n =>
      heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
    w s₁ s₂ b C_D ρc Geom hρc hmargin hcont hgeom

#check @exists_fgRadius_of_local_continuousOn
#check @witness_exists_fgRadius

end QIQTH.HfgRadiusSelection

/-! ## Axiom checks — every theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HfgRadiusSelection
#print axioms exists_fgRadius_of_local_continuousOn
#print axioms witness_exists_fgRadius
end AxiomChecks
