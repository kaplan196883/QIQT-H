/-
  KernelJointContinuity — J4-214 (hEmeas-ladder brick B4, OBL-2): joint continuity of the concrete
  gated van-Vleck witness kernel `G = vanVleckGatedWitness g gi hC hK S a b`, assembled from the banked
  inner-kernel joint continuity (`InnerKernelJointMeas.witnessInner_jointContinuousOn_pos`) and a
  carried joint inverse-chart continuity.  ONE brick of the a₁=R/6 campaign; **NOT a₁=R/6 itself** and
  proves NOTHING about `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  Pure regularity brick.  No `sorry`, no new axioms, no `:= True`, no vacuous or
  unsatisfiable hypotheses, none of the results is a conclusion-in-disguise.

  ── THE TARGET (OBL-2, verbatim from `HEmeasRecon`).
       def HEmeasObligation_kernelJointCont (G : ℝ → Point n → Point n → ℝ) : Prop :=
         Continuous (fun w : ℝ × Point n × Point n => G w.1 w.2.1 w.2.2)
     i.e. FULL joint continuity, on ALL of `ℝ × Point n × Point n`, of the concrete space-time kernel.

  ── THE STRUCTURE OF THE CONCRETE KERNEL.
       vanVleckGatedWitness g gi hC hK S a b τ p q
         = gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
             (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK)) τ p q
         = if q ∈ K then (if p ∈ S q then  H_base τ p q  else 0) else 0,
     where the UNGATED base kernel is
       H_base τ p q  =  radialCutoff a b (V q p) · heatParametrix 1 Θ u τ (V q p),
       V := uniformInverseChart g gi hC hK   (base slot `q`, field slot `p`),
       Θ := vanVleck g,   u := transportCoeff (transportOp (vanVleck g) g gi).
     So the ENTIRE `(p,q)`-dependence of `H_base` runs through the inverse chart `V q p`, and the whole
     thing is the banked INNER kernel `witnessInner τ w = radialCutoff a b w · heatParametrix 1 Θ u τ w`
     evaluated at `w = V q p`.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁=R/6).

    * `kernelBase_jointContinuousOn_pos` — ★ item 1 (the bankable brick).  Joint `ContinuousOn` of the
      UNGATED base witness kernel `(τ,p,q) ↦ globalCutoffParametrixWitnessN 1 Θ u a b V τ p q` on any
      region `Ω ⊆ {τ > 0}` on which the inverse chart is jointly `(p,q)`-continuous.  Composed by
      `ContinuousOn.comp` of the banked inner joint continuity `witnessInner_jointContinuousOn_pos`
      (coefficient continuity `hΘc`/`hΘne`/`huc`) with `(τ,p,q) ↦ (τ, V q p)`.  The one genuinely
      non-banked input, the JOINT `(p,q)`-continuity of the inverse chart `hVjoint`, is carried
      honestly (satisfiable — flat case `V q p = p − q`; non-vacuous).

    * `kernelGated_jointContinuousOn_inGate` — ★ item 1b.  Joint `ContinuousOn` of the GATED concrete
      kernel `vanVleckGatedWitness g gi hC hK S a b` on any IN-GATE region `Ω ⊆ {τ>0}` (`q ∈ K` and
      `p ∈ S q` throughout `Ω`): on such an `Ω` the hard gate is transparent, so the gated kernel EQUALS
      `H_base` there and `ContinuousOn.congr` transfers item 1.

  ── ITEM 2 / GLOBALIZATION VERDICT — FULL OBL-2 IS UNSATISFIABLE FOR THE CONCRETE KERNEL (no faking).
     The literal `Continuous (fun w => G w.1 w.2.1 w.2.2)` on ALL of `ℝ × Point n × Point n` is
     GENUINELY FALSE for the concrete gated witness, for TWO independent reasons:

       (E-τ0)  τ=0 DIAGONAL GAUSSIAN BLOW-UP.  At `τ = 0` the parametrix VANISHES
               (`InnerKernelJointMeas.heatParametrix_eq_zero_of_nonpos`, `n ≥ 1`), so the kernel VALUE
               at `w = (0, q, q)` is `0`.  But along `τ ↓ 0` at a diagonal point `p = q` (where
               `V q q = 0`, `radialCutoff a b 0 = 1`), `gaussDdim τ 0 = (√(4πτ))⁻ⁿ → +∞`.  So the
               kernel is DISCONTINUOUS at every diagonal point `(0,q,q)` — even in the flat case.  The
               honest continuity domain is `{τ > 0}`, NOT all of `ℝ`.  (This is why item 1 is stated on
               `{τ>0}`; the sub `{τ<0}` half is separately trivially continuous — the kernel is `≡ 0`
               there by `heatParametrix_eq_zero_of_nonpos` — but the two halves do NOT join at `τ=0`.)

       (E-gate) HARD SET-GATE JUMP.  `gatedKernel` is a HARD indicator `if q ∈ K … if p ∈ S q …`, not a
               smooth cutoff.  `H_base` does not vanish on `∂K` / `∂(S q)` (the radial cutoff kills only
               `‖V q p‖ ≥ b`, unrelated to the set boundary), so the gated kernel jumps to `0` across the
               gate boundary and is discontinuous there.  Hence item 1b is confined to the IN-GATE
               region (`ContinuousOn`, not `Continuous`).

     Consequently the recon's "OBL-2 = LADDER reachable from flow continuity" is over-optimistic: the
     flow/chart joint continuity gives on-`{τ>0}`, in-gate `ContinuousOn` (item 1/1b), which is the
     maximal honest globalization, but the LITERAL global `Continuous` OBL-2 is unsatisfiable.

  ── ITEM 3 / WIRE-THROUGH VERDICT — HONESTLY BLOCKED, and NOT NEEDED.
     A `hEmeas_of_hKp1` instantiation of `HEmeasRecon.kernelCont_reduces_hEmeas` at the concrete gated
     witness would have to SUPPLY `hKcont : HEmeasObligation_kernelJointCont G` = the literal global
     `Continuous`, which (E-τ0)/(E-gate) show is UNSATISFIABLE for this `G`.  Carrying an unsatisfiable
     hypothesis is exactly the forbidden vacuous shape, so item 3 is NOT delivered here.  Note this costs
     nothing downstream: the joint strong MEASURABILITY that OBL-2's global-continuity route was meant to
     feed is ALREADY discharged, WITHOUT any global continuity, by the direct Borel route
     `InnerKernelJointMeas.hinnerJ_discharged` / `hjoint_final` (every building block is globally Borel
     measurable across `τ = 0`).  Global continuity was one over-strong sufficient path, now seen blocked;
     the measurability wall is closed by another.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.InnerKernelJointMeas
import QIQTH.HEmeasRecon
import QIQTH.ConvApproximants

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound QIQTH.VanVleck
open QIQTH.HeatTransportRecursion QIQTH.InnerKernelJointMeas
open QIQTH.ParametrixFunction QIQTH.HeatParametrixAnsatz
open scoped Topology BigOperators

namespace QIQTH.KernelJointContinuity

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ## ITEM 1 (B4) — joint continuity of the UNGATED base witness kernel on `{τ>0}`.
    ############################################################################### -/

/-- **★ item 1 / B4 — `kernelBase_jointContinuousOn_pos`.**  Joint `ContinuousOn` of the UNGATED base
    van-Vleck witness kernel
      `(τ,p,q) ↦ globalCutoffParametrixWitnessN 1 (vanVleck g) (transportCoeff …) a b
                    (uniformInverseChart g gi hC hK) τ p q`
    on any region `Ω ⊆ {τ > 0}` (`hΩpos`) on which the inverse chart is jointly `(p,q)`-continuous
    (`hVjoint`).  The whole `(p,q)`-dependence runs through `V q p`, and the base kernel is the banked
    inner kernel `radialCutoff a b w · heatParametrix 1 Θ u τ w` at `w = V q p`; so this is
    `ContinuousOn.comp` of `InnerKernelJointMeas.witnessInner_jointContinuousOn_pos` (needing the
    coefficient continuity `hΘc`/`hΘne`/`huc`, satisfiable a fortiori from the geometry) with the map
    `(τ,p,q) ↦ (τ, V q p)`.  The joint chart continuity `hVjoint` is carried honestly — it is the one
    non-banked input (the banked `ChartGeneralPContinuity.chartP_continuousOn` supplies only the `q`-slot
    slice at a fixed field point `p`, NOT the joint `(p,q)` continuity needed here), satisfiable and
    non-vacuous.  NOT `a₁ = R/6`. -/
theorem kernelBase_jointContinuousOn_pos (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ)
    (hΘc : Continuous (vanVleck g))
    (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    {Ω : Set (ℝ × Point n × Point n)} (hΩpos : ∀ w ∈ Ω, 0 < w.1)
    (hVjoint : ContinuousOn
      (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1) Ω) :
    ContinuousOn
      (fun w : ℝ × Point n × Point n =>
        globalCutoffParametrixWitnessN 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) a b
          (uniformInverseChart g gi hC hK) w.1 w.2.1 w.2.2) Ω := by
  -- banked inner kernel joint continuity on `{0 < τ}`.
  have hinner :
      ContinuousOn
        (fun r : ℝ × Point n =>
          radialCutoff a b r.2
            * heatParametrix 1 (vanVleck g)
                (transportCoeff (transportOp (vanVleck g) g gi)) r.1 r.2)
        {r : ℝ × Point n | 0 < r.1} :=
    witnessInner_jointContinuousOn_pos (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b hΘc hΘne huc
  -- the substitution map `(τ,p,q) ↦ (τ, V q p)` is jointly continuous on `Ω`.
  have hφ :
      ContinuousOn
        (fun w : ℝ × Point n × Point n =>
          (w.1, uniformInverseChart g gi hC hK w.2.2 w.2.1)) Ω :=
    (continuous_fst.continuousOn).prodMk hVjoint
  -- it maps `Ω` into the positive-time slab.
  have hmaps :
      Set.MapsTo
        (fun w : ℝ × Point n × Point n =>
          (w.1, uniformInverseChart g gi hC hK w.2.2 w.2.1)) Ω {r : ℝ × Point n | 0 < r.1} :=
    fun w hw => hΩpos w hw
  -- compose; the composite is the base kernel definitionally.
  have hcomp := hinner.comp hφ hmaps
  simpa only [globalCutoffParametrixWitnessN, Function.comp_def] using hcomp

/-! ###############################################################################
    ## ITEM 1b — joint continuity of the GATED concrete kernel on an IN-GATE region.
    ############################################################################### -/

/-- **★ item 1b — `kernelGated_jointContinuousOn_inGate`.**  Joint `ContinuousOn` of the concrete
    GATED van-Vleck witness kernel `vanVleckGatedWitness g gi hC hK S a b` on any region `Ω ⊆ {τ>0}`
    that lies ENTIRELY IN-GATE (`hgate : ∀ w ∈ Ω, w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2`).  On such an `Ω` the
    hard set-gate is transparent, so the gated kernel equals the ungated base kernel pointwise, and
    `ContinuousOn.congr` transfers item 1 (`kernelBase_jointContinuousOn_pos`).  Off the gate the hard
    indicator makes the kernel jump to `0` — full `Continuous` fails there (see the header verdict), so
    the IN-GATE `ContinuousOn` is the honest statement.  NOT `a₁ = R/6`. -/
theorem kernelGated_jointContinuousOn_inGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hΘc : Continuous (vanVleck g))
    (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    {Ω : Set (ℝ × Point n × Point n)} (hΩpos : ∀ w ∈ Ω, 0 < w.1)
    (hVjoint : ContinuousOn
      (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1) Ω)
    (hgate : ∀ w ∈ Ω, w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2) :
    ContinuousOn
      (fun w : ℝ × Point n × Point n =>
        vanVleckGatedWitness g gi hC hK S a b w.1 w.2.1 w.2.2) Ω := by
  classical
  have hbase :=
    kernelBase_jointContinuousOn_pos g gi hC hK a b hΘc hΘne huc hΩpos hVjoint
  refine hbase.congr ?_
  intro w hw
  obtain ⟨hqK, hpS⟩ := hgate w hw
  -- gated = base pointwise, on the gate.
  simp only [vanVleckGatedWitness, gatedKernel, if_pos hqK, if_pos hpS]

end QIQTH.KernelJointContinuity

/-! ## Axiom checks — every theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.KernelJointContinuity
#print axioms kernelBase_jointContinuousOn_pos
#print axioms kernelGated_jointContinuousOn_inGate
end AxiomChecks
