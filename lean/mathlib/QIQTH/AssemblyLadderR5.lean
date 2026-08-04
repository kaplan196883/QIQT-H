/-
  AssemblyLadderR5 — J4-225: LADDER RUNGS R1½ + R5 — the measurable-supplier discharge.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is a pure
  RE-PLUMBING brick on top of `AssemblyLadderR3.a1_R6_assembled_v3` (J4-224): it discharges /
  deepens the CONCRETE-DISCHARGEABLE measurable-supplier binders in that capstone's surface, threading
  the residue verbatim into `a1_R6_assembled_v3`.  No new analysis; only compositions.

  ────────────────────────────────────────────────────────────────────────────────────────────────
  ## R1½ — the measurable-supplier existentials.  PER-TARGET VERDICTS.

     · `hchrMeas`  (`∀ k i j, Measurable (christoffel g gi k i j ·)`)  —  ★ FREE (strict −1).  v3
       ALREADY carries `hChr : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y)`.  So
       `hchrMeas` is `fun k i j => (hChr k i j).continuous.measurable` — `ContDiff.continuous` then
       `Continuous.measurable` (Point n = Fin n → ℝ is a finite-dim, hence Borel + second-countable,
       normed space; ℝ is `BorelSpace`).  The binder is DROPPED from the v4 surface (a real −1).

     · `hgiMeas`   (`∀ i j, Measurable (gi · i j)`)  —  ★ DEEPENED (net-neutral, +0).  Unlike
       `christoffel`, `gi` is an INDEPENDENT function argument constrained ONLY pointwise at `0`
       (`hgi : gi 0 i j = δᵢⱼ`); v3 carries NO smoothness/continuity on `gi` (only `hg` on `g`).  So
       `hgiMeas` CANNOT be derived for free.  We replace the raw `Measurable` binder by the strictly
       STRONGER, more geometric `hgiC : ∀ i j, Continuous (gi · i j)` and recover the measurability via
       `Continuous.measurable`.  Net binder count unchanged (−1 `hgiMeas`, +1 `hgiC`); the surface is
       DEEPER (a regularity hypothesis in place of a bare measurability one).

     · `hcarTau` / `hcarField` / `hcarField2`  —  ⛔ BLOCKED (kept verbatim).  Each existential's FIRST
       conjunct is the JOINT-in-`(base, field)` chart measurability
         `Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)`.
       Grep of the entire `QIQTH/` tree shows this exact joint measurability appears ONLY ever as a
       HYPOTHESIS (in these existentials and their upstream `GatedTauDerivRep`/`GatedDerivRepProduct`/
       `ChartJetHessianMixed` slots) — it is CONCLUDED by NO standalone theorem.  The banked chart
       joint-regularity is `KernelJointContinuity.kernelBase_jointContinuousOn_pos` /
       `kernelGated_jointContinuousOn_inGate` and `FlowJointContinuity.uniformFlowExp_joint_*` — all
       `ContinuousOn`/`ContinuousWithinAt` on the POSITIVE-time / IN-GATE set, NOT global joint
       measurability on `ℝ × Point n × Point n`.  The concrete on-gate `HasDerivAt` field-jets DO exist
       (`ChartJetBounds`, lines ~201/226/255), but without the joint chart measurability the
       existentials cannot be closed from banked lemmas.  Discharging them requires a NEW global
       joint-measurability theorem for `uniformInverseChart` (the off-gate/off-pos completion), which is
       genuine new analysis — out of scope for a pure re-plumbing brick.  KEPT as carried suppliers.

  ────────────────────────────────────────────────────────────────────────────────────────────────
  ## R5 — `hgD1` (the per-coordinate scalar jets `∀ i, ContDiffAt ℝ 1 (gcoef i) 0`).  ⛔ SIZE-REJECTED.
     The interface discharger is `XUniformSliverFull.hD1_from_data` at `gfull := gcoef i`, but it is an
     ABSTRACT theorem: its carries `{hbulkderiv, hbulk_tendsto, hsliver, hb, hcont}` are supplied by the
     ABSTRACT skeletons `HD1SliverRoute.gcoef_bulk_hasFDerivAt`, `HD1ConcreteWiring.bulk_tendsto_of_`
     `primitive`, `XUniformSliverFull.witness_sliver2_xuniform`, `HD1ConcreteWiring.sliver_bound_`
     `tendsto_zero`, `HD1ConcreteWiring.gderiv_continuousAt`.  NONE is a single "banked at the concrete
     `gcoef i`" fact.  In particular `witness_sliver2_xuniform` alone demands ~30 fresh concrete carries
     (`Y P Q A0 A1 A2` fields, the `M₀ M₁ M₂ C_W C_P C_Q` bounds, `hco`/`hYdisp`/`hJ3`/`hJ3Q`, the
     `hNormalForm` normal form, `hqLip`, and the per-slice integrabilities `hIntT1..3`/`hInt1`/`hInt2`)
     in the PER-SLICE form — NOT the already-integrated `pdpdH`-form of the v3 `D0`/`D1`/`hbnd` binders,
     so the v3 sliver amplitudes do NOT feed this slot.  Threading `hD1_from_data` therefore replaces the
     SINGLE binder `hgD1 : ∀ i, ContDiffAt ℝ 1 (gcoef i) 0` with dozens of new concrete-data binders:
     a MASSIVE net enlarge.  REJECT — `hgD1` is kept as ONE clean per-coordinate-jet binder.

  ────────────────────────────────────────────────────────────────────────────────────────────────
  ## R5-CAP — `a1_R6_assembled_v4`.  DONE (builds; std-3).
     `a1_R6_assembled_v3` with:
       REMOVED : `hchrMeas`                       (derived internally from `hChr`, FREE −1).
       DEEPENED: `hgiMeas` → `hgiC`               (`Continuous` in place of `Measurable`, net +0).
     Everything else — the geometry, the still-carried `hcarTau`/`hcarField`/`hcarField2`, `hgD1`, the
     `hDerivConv` limit, the CConv facades, and the entire `hDConv` analytic residue pile — is threaded
     VERBATIM into `a1_R6_assembled_v3`.  Same conclusion.  Pure composition — no new analysis.

  ────────────────────────────────────────────────────────────────────────────────────────────────
  ## POST-R5 SURFACE (toward R6/R7).  Relative to `a1_R6_assembled_v3` the DELTA is only the two
     supplier binders above.  Still open toward the final `a1_R6_of_geometry`:
       GEOMETRY   g,gi,Ric,…,hgi,hΓ,hdg0,htr,hsrc                (RNC/Ricci input the theorem is ABOUT)
       CD         `hcarTau`/`hcarField`/`hcarField2`             (R1½ HARD residue = global joint chart
                                                                  measurability — genuine new analysis)
       CD         `hgD1 i`                                       (R5 SIZE-REJECTED)
       CD         `hInterchange`/`hLapFull`/`hEcomb`             (R2 size-REJECTED)
       DATA       the whole hDConv analytic residue pile         (R6: dominations/integrabilities/sliver)
       DATA       `hEboundFull`, `hAdom`/`hEdom`/…               (R6: Gaussian-envelope banked bounds)
       DATA       `hDerivConv` (the ONE F2-family limit)         (R3½ / R6)
       DATA       the CConv facade scaffolding + 5 bundles       (R4)
     GENUINE-GAP: NONE at the a₁ = R/6 CONDITIONAL level.

  NO `sorry`.  NO new axioms.  NO `:= True`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.AssemblyLadderR3

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel QIQTH.VanVleck
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.GaussianConvolution QIQTH.HeatParametrixAnsatz QIQTH.ResidueBound
open QIQTH.HeatKernelA1 QIQTH.LaplaceBeltrami
open QIQTH.HeatResidualBound
open QIQTH.CConvFacade QIQTH.LeviSeries
open QIQTH.CConvConcreteThreading
open QIQTH.HDConvThreading QIQTH.TruncatedDuhamelData
open QIQTH.DaLimLUWallRecon QIQTH.ETailRateBound QIQTH.HD1CLMLift
open QIQTH.GrandAssemblyRecon QIQTH.ChartJetHessianMixed
open QIQTH.AssemblyLadderR1R2 QIQTH.AssemblyLadderR3
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.AssemblyLadderR5

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ R5 — `a1_R6_assembled_v4`: `hchrMeas` discharged, `hgiMeas` deepened.
    ############################################################################### -/

/-- **★★★ J4-225 — `a1_R6_assembled_v4`.**  `AssemblyLadderR3.a1_R6_assembled_v3` with the two
    concrete-dischargeable measurable-supplier binders resolved:
      · `hchrMeas` — DROPPED; derived internally as `(hChr k i j).continuous.measurable` (v3 already
        carries the `hChr` christoffel-`ContDiff`, so this is a strict −1, FREE);
      · `hgiMeas` — DEEPENED to `hgiC : ∀ i j, Continuous (gi · i j)` (`gi` carries no v3 smoothness, so
        the raw measurability cannot be free; a stronger, more geometric continuity binder replaces it,
        net-neutral, and `Continuous.measurable` recovers what v3 wants).
    Everything else (the still-carried `hcarTau`/`hcarField`/`hcarField2` — blocked on global joint
    chart measurability — the `hgD1` jets — size-rejected — the `hDerivConv` limit, the CConv facades,
    and the whole `hDConv` residue) is threaded VERBATIM into `a1_R6_assembled_v3`.  Same conclusion as
    v3.  Pure composition — no new analysis.  NOT `a₁ = R/6`. -/
theorem a1_R6_assembled_v4 (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (C : ℝ) (hCnn : 0 ≤ C)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0)
    -- (i) RNC / Ricci geometric data (flat):
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    -- the `tripleHEmeas_concrete` measurable-supplier block (v2):
    (hn : 0 < n) (hKmeasSet : MeasurableSet K)
    (hcarTau : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ S w.2.2 ∧
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hChr hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hcarField : ∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ (∀ jj, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 jj))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
            (∀ jj, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update w.2.1 k s) jj)
              (Pfield w.2.2 w.2.1 jj) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1))
    (hcarField2 : ∀ i j : Fin n, ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) i w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n =>
              pd (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update y i s) k)
              (Pifield w.2.2 y k) (y i)) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update y j s) k)
              (Pjfield w.2.2 y k) (y j)) ∧
            (∀ k, HasDerivAt
              (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
              (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
            (∀ y, PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) i w.2.1 ∧
            PdiffAt (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1))
    -- ★ R1½: `hgiMeas` DEEPENED to a continuity (more geometric; recovers measurability internally).
    (hgiC : ∀ i j : Fin n, Continuous (fun p : Point n => gi p i j))
    -- (`hchrMeas` REMOVED — derived internally from `hChr`.)
    (hEboundFull : ∀ τ p q, 0 < τ →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    -- the `core` bundle's THIRD limit residue (v3):
    (hDerivConv : Filter.Tendsto
        (fun m => DaTrunc (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m t
          + BoundaryTrunc (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m t) Filter.atTop
        (𝓝 (deriv (fun u => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u 0 0) t)))
    (hCH : ContDiffAt ℝ 2 (fun p => vanVleckGatedWitness g gi hChr hK S a b t p 0) (0 : Point n))
    -- (ii) the CConv `C²` facade bundles (v6, verbatim):
    (uu : Set (Point n)) (hu_open : IsOpen uu) (hu0 : (0 : Point n) ∈ uu)
    (Bs Ba Bd Cf : ℝ) (Dmap : Point n → (Point n →L[ℝ] ℝ))
    (metric : CConvMetricData g gi)
    (chart : CConvChartGateData g gi hChr hK S a b t uu)
    (source : CConvSourceData
      (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) t Cf)
    (derivData : CConvDerivativeData g gi hChr hK S a b t uu
      (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
      Dmap)
    (env : CConvEnvelopeData g gi hChr hK S a b t uu Bs Ba Bd)
    -- v7 route: per-coordinate SCALAR jets.
    (hgD1 : ∀ i : Fin n, ContDiffAt ℝ 1
        (fun x => ∫ s in (0:ℝ)..t, ∫ z, witnessFieldDeriv g gi hChr hK S a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
            ∂(volume : Measure (Point n))) (0 : Point n))
    -- (v) the `hDConv` analytic residue block (v6 residue, verbatim — MINUS `DaLim`/`hDaLimLU`):
    (T : ℝ) (hT : 0 < T)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (r₀ τ₀ : ℝ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀)
    (u₀ u₁ : Point n → ℝ)
    (hAnear : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z ∈ Metric.ball (0 : Point n) r₀,
        vanVleckGatedWitness g gi hChr hK S a b τ 0 z = gaussDdim τ z * (u₀ z + τ * u₁ z))
    (hu₀cont : ContinuousAt u₀ 0) (hu₀one : u₀ 0 = 1)
    (C₀ C₁ : ℝ) (hu₀bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₀ z| ≤ C₀)
    (hu₁bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₁ z| ≤ C₁)
    (A₀ A₁ C_L : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hC_L : 0 ≤ C_L)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness g gi hChr hK S a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness g gi hChr hK S a b τ p q = 0)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y))
    (hBcont : ContinuousOn
        (fun x : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) x.1 x.2 0)
        (Set.Ioc 0 T ×ˢ Set.univ))
    (hAmeas : ∀ τ, AEStronglyMeasurable
        (fun z : Point n => vanVleckGatedWitness g gi hChr hK S a b τ 0 z) volume)
    (hBmeas : ∀ s, AEStronglyMeasurable
        (fun z : Point n => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume)
    (hu₀meas : AEStronglyMeasurable u₀ volume) (hu₁meas : AEStronglyMeasurable u₁ volume)
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    (hUfloor : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ U, c ≤ u)
    (hInnerCont : ∀ u ∈ U, ContinuousOn
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (Set.Ioo 0 u))
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas : ∀ (m : ℕ), ∀ u ∈ U, ∀ a', AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (a' - s) 0 z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s)
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundD : ℕ → ℝ → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a' ∈ nb m u,
      ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (a' - s)
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ boundD m u s)
    (hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a' ∈ nb m u,
      HasDerivAt (fun a' => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (a' - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (a' - s)
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) a')
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) (u + h) (u - epsSeq m + k) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) (u + h) (u - epsSeq m) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u (u - epsSeq m + k) 0 0
          + heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|))
    -- the `hDaLimLU_from_data` DATA carries (the WALL, turned into data) — R2 trio KEPT (size-rejected).
    (pdpdH : Fin n → ℝ → Point n → ℝ)
    (hInterchange : MemInterchange (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U pdpdH)
    (hLapFull : MemLapFull g gi (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U pdpdH)
    (hII_lo : MemAdjLo (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U pdpdH)
    (hII_hi : MemAdjHi (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U pdpdH)
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1nn : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (E₀ E₁ : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁)
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hEzeroE : ∀ τ, τ ≤ 0 → ∀ p q : Point n,
        heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q = 0)
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z y = 0)
    (hIlo : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
          volume 0 (u - epsSeq m))
    (hIhi : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
          volume (u - epsSeq m) u)
    (hEcomb : MemECombine g gi (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))) :
    heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) ) t 0 0 = 0
    ∧ trueHeatKernel (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, Ric i i) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv (vanVleckGatedWitness g gi hChr hK S a b)
                            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
                            t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  -- R1½ `hchrMeas` (FREE, −1): christoffel measurability from the carried `hChr` `ContDiff`.
  have hchrMeas : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p) :=
    fun k i j => (hChr k i j).continuous.measurable
  -- R1½ `hgiMeas` (DEEPENED, +0): recover the measurability from the stronger continuity `hgiC`.
  have hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j) :=
    fun i j => (hgiC i j).measurable
  -- feed `a1_R6_assembled_v3` with the two recovered suppliers; everything else verbatim.
  exact QIQTH.AssemblyLadderR3.a1_R6_assembled_v3
    g gi Ric t ht C hCnn hChr hK S a b ha hab hK0 hS0
    hg hg0 hgi hΓ hdg0 htr hsrc
    hn hKmeasSet hcarTau hcarField hcarField2 hgiMeas hchrMeas hEboundFull
    hDerivConv hCH
    uu hu_open hu0 Bs Ba Bd Cf Dmap metric chart source derivData env hgD1
    T hT U hUopen htU hUpos hUT r₀ τ₀ hr₀ hτ₀ u₀ u₁ hAnear hu₀cont hu₀one C₀ C₁ hu₀bdd hu₁bdd
    A₀ A₁ C_L hA₀ hA₁ hC_L hAdom hAzero hBdom hBcont hAmeas hBmeas hu₀meas hu₁meas
    hMeasFII hUfloor hInnerCont nb hnb hFmeas hFint hF'meas boundD hbdd hbound hpardiff
    L hLnn hCross
    pdpdH hInterchange hLapFull hII_lo hII_hi D0 D1 hD0 hD1nn hbnd
    E₀ E₁ hE₀ hE₁ hEdom hEzeroE hFzero hIlo hIhi hEcomb

end QIQTH.AssemblyLadderR5

section AxiomChecks
open QIQTH.AssemblyLadderR5
#print axioms a1_R6_assembled_v4
end AxiomChecks
