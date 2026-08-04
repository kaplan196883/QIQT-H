/-
  HEmeasRecon — Ph10 RECON (J4-212): the `hEmeas`-family OBLIGATION MAP for the a₁=R/6 endgame.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a RECON
  map: it names the exact propositions of the `hEmeas`-family measurability/continuity obligations that
  live INSIDE the capstone's provider residues, encodes each as a build-checked `def … : Prop`, and
  records — as genuine (std-3, axiom-free) theorems wired to ALREADY-PROVEN banked suppliers — which
  obligations are discharged, which reduce to named ladders, and which remain a wall.  No `sorry`, no
  new axioms, no vacuous hypotheses, no conclusion-in-disguise.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE TWO AXES OF `hEmeas` (the load-bearing structural finding).

  `hEmeas` — the joint strong measurability of the cutoff error kernel `E` fed to the Levi/Duhamel
  tower — factorises into TWO ORTHOGONAL axes:

    • FACTOR / DIAGONAL axis.  The residual in NORMAL FORM `E = χ·(G_τ·A) − annulusTerms` over a SINGLE
      base point (the diagonal coordinate `v`), jointly `(τ,v)`-measurable.  This axis is **FULLY
      DISCHARGED from geometry** `{hn, hg, hgi, hgpos}` alone
      (`ParametrixGradientMeas.cutoffError_normalForm_measurable_final`, `hDH` eliminated by
      `heatParametrix_pd_measurable_from_geometry`).  It never touches the `.choose` flow.

    • FLOW / TRIPLE axis.  The kernel `E = heatOp g gi H` over the TRIPLE `(τ,p,q)` with the base point
      `q` running through the `.choose`-built geodesic flow `uniformFlowExp` (via the inverse chart
      `uniformInverseChart`).  `heatOp = ∂_τ − Δ_g` has TWO nested spatial `pd`s in the FIELD slot `p`;
      `GatedWitnessEmeas` (E3a–E3e) reduces the triple `hEmeas` to
        {hKcont : the kernel is jointly CONTINUOUS in (τ,p,q)}  and
        {hKp1   : each first-order `pd` field is jointly CONTINUOUS in (τ,p,q)},
      plus continuous coefficient fields.  hKcont needs the flow value jointly continuous (C⁰);
      hKp1 needs the kernel jointly `C¹`, i.e. the flow's joint `C¹` base-point regularity.

  The `.choose` entry point (identical for every flow-axis obligation):
      `uniformFlowExp g gi hC hK q w := (uniformFlowTube g gi hC hK q w 1).1`,
      `uniformFlowTube … q w      := (uniformFlow_tube_exists g gi hC hK q w).choose`   (UniformFlowNondeg),
  a `Classical.choose` of a per-`(q,w)` geodesic phase-space curve.  The base point `q` enters every
  witness kernel `H = vanVleckGatedWitness …` ONLY through `uniformInverseChart g gi hC hK z p`, the
  local inverse of `w ↦ uniformFlowExp g gi hC hK z w`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## OBLIGATION → SOURCE FILE → discharging regularity input.

    OBL-1  triple `hEmeas`  (StronglyMeasurable (τ,p,q) ↦ heatOp g gi H)
           SOURCE : CapstoneAssembly (banked bundle) · InterchangeLocalRebase (`hEmeas` slot) ·
                    ResidueThreading.a1_R6_of_residue_hCH_hInter_discharged (T5b) · GatedWitnessEmeas.
           .choose: H = vanVleckGatedWitness … ← uniformInverseChart ← uniformFlowExp ← `.choose`.
           INPUT  : joint (τ,p,q)-continuity of the kernel AND its first `pd` field (E3e reduction).

    OBL-2  hKcont  (Continuous (τ,p,q) ↦ G)
           SOURCE : GatedWitnessEmeas.heatOp_stronglyMeasurable_of_jointContinuous (E3e / E3a / E3b).
           INPUT  : flow ENDPOINT VALUE jointly continuous in (q,w)  [C⁰].

    OBL-3  hKp1  (∀ j, Continuous (τ,p,q) ↦ pd (G τ · q) j p)   ⟵ the W2 wall
           SOURCE : GatedWitnessEmeas.stronglyMeasurable_pd2_field_of_jointContinuous (E3c).
           INPUT  : kernel jointly `C¹` in (τ,p,q), i.e. flow jointly `C¹` in the BASE `q`.

    OBL-4  factor / diagonal normal-form measurability (Measurable (τ,v) ↦ χ·G·A − annulusTerms)
           SOURCE : ParametrixGradientMeas.cutoffError_normalForm_measurable_final.
           INPUT  : geometry `{hn, hg, hgi, hgpos}` — NOTHING else.   ⟶ DISCHARGED.

    OBL-5  hVmapMeas  (∀ p, AEStronglyMeasurable z ↦ uniformInverseChart g gi hC hK z p)
           SOURCE : GateChartMeasurability.hIn_concrete_of_chart_measurable /
                    .hKmeas_concrete_v2 (the `hIn` slot).
           INPUT  : base-point (z)-continuity of the inverse chart at each field point `p`.

    OBL-6  hWmeas₀  (∀ τ, AEStronglyMeasurable z ↦ gaussDdim τ (uniformInverseChart … z 0))
           SOURCE : GeodesicGronwall.hWmeas₀_unconditional (W4b) · ResidueThreading.T5a.
           INPUT  : base-point continuity of the ORIGIN chart `z ↦ W₀ z`  ⟶ DISCHARGED (Grönwall)
                    modulo the three carried geometric side-conditions (hball/hnorm/hRI).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## PER-OBLIGATION VERDICT.

    OBL-4  DISCHARGEABLE-NOW.  `factorDiagonal_discharged` re-exposes the banked final discharge:
           the whole diagonal axis of `hEmeas` from geometry, `.choose`-free.

    OBL-6  DISCHARGEABLE-NOW.  `hWmeas0_discharged` re-exposes GeodesicGronwall's `hWmeas₀_unconditional`:
           the nonlinear two-solution Grönwall (W1–W3) already closes the base-flow difference, so the
           origin-chart measurability holds modulo the carried geometric side-conditions.

    OBL-5  LADDER.  Reduces to `ContinuousOn (fun z ↦ uniformInverseChart … z p) S`.  For the ORIGIN
           slot `p = 0` this is banked (GeodesicGronwall.chartOrigin_continuousOn).  For a GENERAL field
           point `p` it needs the base-continuity of the inverse chart at `p` — the missing bricks:
             L5a  forward-flow joint continuity at general velocity (the STRETCH below gives the base
                  slot; velocity slot is `contDiffAt2_uniformFlowExp`);
             L5b  invert L5a to base-continuity of `uniformInverseChart · p` on the chart's reach.

    OBL-2  LADDER.  Reduces (`kernelCont_reduces_hEmeas`) OBL-1 to hKcont+hKp1+coeff.  hKcont needs the
           flow value jointly continuous; the STRETCH `flow_base_continuousOn_of_gronwall` supplies the
           BASE slot from Grönwall (W3), `contDiffAt2_uniformFlowExp` the velocity slot.  Missing brick:
             L2  weld base-Lipschitz (uniform in w) + velocity-continuity ⟶ JOINT continuity of the flow
                 value on `K ×ˢ ball`, then push through the chart to hKcont.

    OBL-3  WALL.  hKp1 = the first-`pd` field jointly continuous needs the kernel jointly `C¹` in
           (τ,p,q), hence the flow's joint `C¹` dependence on the base point `q`.  The banked Grönwall
           (`uniformFlowExp_base_diff_bound`) gives only `C⁰` LIPSCHITZ in `q` (a modulus, not a
           derivative); there is NO exposed base-point `fderiv`/`ContDiffAt` of the `.choose` flow
           (FlowJointRegularity §3).  A base-point `C¹` variational Grönwall (the nonlinear analogue of
           BasepointJetModulus's linear two-point jet bound, differentiated in the base seed) is the
           genuinely-open multi-brick endeavour.

  ## RECOMMENDED LADDER (ordered, one-line specs) toward `a1_R6_of_geometry_and_heatOp_qregularity`.
     B1  flow_base_continuousOn_of_gronwall   — base-slot continuity of the forward flow  [DONE below].
     B2  flow_joint_continuousOn              — weld B1 (uniform-in-w) + contDiffAt2 velocity slot ⟶
                                                joint continuity on `K ×ˢ ball 0 ρ`.
     B3  inverseChart_base_continuousOn       — invert B2 (open-map / inverse-germ) ⟶ base-continuity of
                                                `z ↦ uniformInverseChart … z p` ⟹ OBL-5 (hVmapMeas).
     B4  kernel_joint_continuous              — compose B2/B3 with the smooth spatial factors ⟹ OBL-2
                                                (hKcont).
     B5  ★ flow_base_C1_variational           — the WALL: base-point `C¹` variational Grönwall ⟹ hKp1
                                                (OBL-3).  Multi-brick; genuinely open.
     B6  a1_R6_of_geometry_and_heatOp_qregularity — final wrapper carrying ONLY B5's `C¹` base-regularity
                                                (`hFlowBaseC1`) alongside `hDaLimLU`.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GeodesicGronwall
import QIQTH.GatedWitnessEmeas
import QIQTH.ParametrixGradientMeas
import QIQTH.GateChartMeasurability

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation QIQTH.ExpMap
open QIQTH.HeatResidualBound QIQTH.TrueHeatKernel QIQTH.ErrorKernelFactorization
open QIQTH.VanVleck QIQTH.ParametrixFunction QIQTH.HeatParametrixAnsatz QIQTH.HeatTransportRecursion
open scoped Topology BigOperators NNReal ContDiff

namespace QIQTH.HEmeasRecon

variable {n : ℕ}

/-! ###############################################################################
    ## PART 1 — THE OBLIGATION MAP (build-checked `def … : Prop`).
    ############################################################################### -/

/-- **OBL-1 — the TRIPLE `hEmeas`.**  The base joint strong measurability of the cutoff error kernel
    `E` over the triple `(τ,p,q)`.  This is the exact `hEmeas` slot of
    `InterchangeLocalRebase.heatConv_leviSeries_interchange` and of
    `ResidueThreading.a1_R6_of_residue_hCH_hInter_discharged` (T5b), with `E := heatOp g gi H`. -/
def HEmeasObligation_triple (E : ℝ → Point n → Point n → ℝ) : Prop :=
  StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2)

/-- **OBL-2 — `hKcont`.**  Joint continuity of the space-time kernel `G` in `(τ,p,q)` — the `hKcont`
    input to `GatedWitnessEmeas.heatOp_stronglyMeasurable_of_jointContinuous` (E3e). -/
def HEmeasObligation_kernelJointCont (G : ℝ → Point n → Point n → ℝ) : Prop :=
  Continuous (fun w : ℝ × Point n × Point n => G w.1 w.2.1 w.2.2)

/-- **OBL-3 — `hKp1` (the W2 wall).**  Joint continuity of each first-order `pd` field of `G` in
    `(τ,p,q)` — the `hP1cont` input to E3e / the joint-continuity hypothesis of
    `stronglyMeasurable_pd2_field_of_jointContinuous` (E3c). -/
def HEmeasObligation_firstPdJointCont (G : ℝ → Point n → Point n → ℝ) : Prop :=
  ∀ j : Fin n, Continuous (fun w : ℝ × Point n × Point n =>
    pd (fun x => G w.1 x w.2.2) j w.2.1)

/-- **OBL-4 — the FACTOR / DIAGONAL normal-form measurability.**  Joint `(τ,v)`-measurability of the
    residual normal form `χ·(G_τ·A) − annulusTerms` (which equals the diagonal cutoff error kernel on
    `{τ>0}`).  The `.choose`-free axis of `hEmeas`. -/
def HEmeasObligation_factorDiagonal (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ) : Prop :=
  Measurable (fun w : ℝ × Point n =>
    radialCutoff a b w.2
        * (gaussDdim w.1 w.2 * residualCoeffA N g gi (vanVleck g)
            (transportCoeff (transportOp (vanVleck g) g gi)) w.1 w.2)
      - annulusTerms g gi a b
          (heatParametrix N (vanVleck g)
            (transportCoeff (transportOp (vanVleck g) g gi)) w.1) w.2)

/-- **OBL-5 — `hVmapMeas`.**  `z`-ae-strong-measurability of the base-chart pullback
    `z ↦ uniformInverseChart g gi hC hK z p` for every field point `p` — the reduced `hIn` slot of
    `GateChartMeasurability.hKmeas_concrete_v2`. -/
def HEmeasObligation_chartPullbackMeas (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) : Prop :=
  ∀ p : Point n, AEStronglyMeasurable
    (fun z => uniformInverseChart g gi hC hK z p) (volume : Measure (Point n))

/-- **OBL-6 — `hWmeas₀`.**  `z`-ae-strong-measurability of the Gaussian at the ORIGIN chart coordinate
    `z ↦ gaussDdim τ (uniformInverseChart g gi hC hK z 0)` on a measurable `S` — the base-point
    consumer input closed by `GeodesicGronwall.hWmeas₀_unconditional`. -/
def HEmeasObligation_originChartMeas (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Set (Point n)) : Prop :=
  ∀ τ : ℝ, AEStronglyMeasurable
    (fun z : Point n => gaussDdim τ (uniformInverseChart g gi hC hK z 0)) (volume.restrict S)

/-! ###############################################################################
    ## PART 2 — THE VERDICTS (each wired to an already-proven banked supplier).
    ############################################################################### -/

/-- **VERDICT OBL-4 : DISCHARGEABLE-NOW.**  The factor / diagonal axis of `hEmeas` holds from geometry
    `{hn, hg, hgi, hgpos}` alone — re-exposing
    `ParametrixGradientMeas.cutoffError_normalForm_measurable_final` (with `hDH` already eliminated).
    The `.choose` flow is never touched on this axis.  NOT `a₁ = R/6`. -/
theorem factorDiagonal_discharged (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ) (hn : 0 < n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v)) :
    HEmeasObligation_factorDiagonal N g gi a b :=
  QIQTH.ParametrixGradientMeas.cutoffError_normalForm_measurable_final N g gi a b hn hg hgi hgpos

/-- **VERDICT OBL-6 : DISCHARGEABLE-NOW.**  The origin-chart measurability holds via the nonlinear
    two-solution Grönwall — re-exposing `GeodesicGronwall.hWmeas₀_unconditional` — modulo the three
    carried geometric side-conditions `{hball, hnorm, hRI}` (satisfiable, non-vacuous; `hRI` itself is
    supplied by `ResidueThreading.chartW0_rightInverse`).  NOT `a₁ = R/6`. -/
theorem hWmeas0_discharged (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    {S : Set (Point n)} (hS : MeasurableSet S) (hSK : S ⊆ K)
    (hball : ∀ z ∈ S, uniformInverseChart g gi hC hK z 0
      ∈ Metric.ball (0 : Point n) (QIQTH.GeodesicGronwall.chartOrigin_lipschitz_modulus g gi hC hK).choose)
    (hnorm : ∀ z ∈ S, ‖uniformInverseChart g gi hC hK z 0‖ ≤ uniformFlowRadius g gi hC hK)
    (hRI : ∀ z ∈ S, uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z 0) = 0) :
    HEmeasObligation_originChartMeas g gi hC hK S :=
  QIQTH.GeodesicGronwall.hWmeas₀_unconditional g gi hC hK hS hSK hball hnorm hRI

/-- **VERDICT OBL-2 (the reduction) : LADDER.**  OBL-1 (triple `hEmeas` for `E := heatOp g gi G`)
    follows from OBL-2 (`hKcont`) + OBL-3 (`hKp1`) + the continuous coefficient fields, via
    `GatedWitnessEmeas.heatOp_stronglyMeasurable_of_jointContinuous` (E3a–E3e).  This EXHIBITS the
    reduction of the triple to the two joint-continuity axes; OBL-2 needs the flow value jointly
    continuous (ladder), OBL-3 is the wall.  NOT `a₁ = R/6`. -/
theorem kernelCont_reduces_hEmeas (g gi : Point n → Fin n → Fin n → ℝ) (G : ℝ → Point n → Point n → ℝ)
    (hKcont : HEmeasObligation_kernelJointCont G)
    (hKp1 : HEmeasObligation_firstPdJointCont G)
    (hgi : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)) :
    HEmeasObligation_triple (fun τ p q => heatOp g gi G τ p q) :=
  QIQTH.HeatResidualBound.heatOp_stronglyMeasurable_of_jointContinuous g gi G hKcont hKp1 hgi hchr

/-! ###############################################################################
    ## PART 3 — STRETCH : one representative joint-continuity-family lemma (B1).
    ############################################################################### -/

/-- **★ STRETCH / B1 — `flow_base_continuousOn_of_gronwall`.**  The forward geodesic-flow endpoint map
    is CONTINUOUS in the BASE point, at any fixed velocity `w` on the flow radius:
        `ContinuousOn (fun q ↦ uniformFlowExp g gi hC hK q w) K`.
    This is a genuinely NEW base-slot continuity fact about the `.choose`-built flow (per
    FlowJointRegularity §3 the tower exposes NO `ContinuousOn` of the flow in the base), obtained by
    composing GeodesicGronwall's two-solution Grönwall bound `uniformFlowExp_base_diff_bound`
    (`‖φ_q w − φ_{q'} w‖ ≤ exp L · ‖q − q'‖`, uniform over `‖w‖ ≤ ρ`) with `LipschitzOnWith.continuousOn`.
    It is the base-slot input to the ladder brick B2 (joint continuity ⟹ `hKcont` = OBL-2); the velocity
    slot is `contDiffAt2_uniformFlowExp`.  NOT `a₁ = R/6`. -/
theorem flow_base_continuousOn_of_gronwall (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (w : Point n)
    (hw : ‖w‖ ≤ uniformFlowRadius g gi hC hK) :
    ContinuousOn (fun q : Point n => uniformFlowExp g gi hC hK q w) K := by
  obtain ⟨L, _hL0, hbase⟩ := QIQTH.GeodesicGronwall.uniformFlowExp_base_diff_bound g gi hC hK
  have hLip : LipschitzOnWith (Real.exp L).toNNReal
      (fun q : Point n => uniformFlowExp g gi hC hK q w) K := by
    apply LipschitzOnWith.of_dist_le_mul
    intro q hq q' hq'
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (le_of_lt (Real.exp_pos _))]
    exact hbase q hq q' hq' w hw
  exact hLip.continuousOn

/-! ###############################################################################
    ## PART 4 — the NAMED-WALL wrapper SHAPE for the final capstone (B6).
    ############################################################################### -/

/-- **B6 (wrapper shape) — `heatOp_qregularity`.**  The single residual hypothesis the final capstone
    `a1_R6_of_geometry_and_heatOp_qregularity` would carry ALONGSIDE `hDaLimLU`: the triple `hEmeas` for
    the concrete witness kernel `E := heatOp g gi H`.  Encoding it as a named predicate makes explicit
    that — after OBL-4/OBL-5/OBL-6 are discharged and OBL-2 is laddered — the ONLY genuinely-open piece
    on the flow axis is OBL-3 (`hKp1`, the flow's base-point `C¹` regularity), which this predicate
    packages.  NOT `a₁ = R/6`. -/
def heatOp_qregularity (g gi : Point n → Fin n → Fin n → ℝ) (H : ℝ → Point n → Point n → ℝ) : Prop :=
  HEmeasObligation_triple (fun τ p q => heatOp g gi H τ p q)

/-- The wrapper predicate is exactly the E3e-reducible triple `hEmeas`: given the two joint-continuity
    axes (`hKcont`, `hKp1`) and continuous coefficients, `heatOp_qregularity` holds.  This certifies the
    wrapper is a faithful repackaging (not a vacuous placeholder) — its content is precisely OBL-2+OBL-3.
    NOT `a₁ = R/6`. -/
theorem heatOp_qregularity_of_jointCont (g gi : Point n → Fin n → Fin n → ℝ)
    (H : ℝ → Point n → Point n → ℝ)
    (hKcont : HEmeasObligation_kernelJointCont H)
    (hKp1 : HEmeasObligation_firstPdJointCont H)
    (hgi : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)) :
    heatOp_qregularity g gi H :=
  kernelCont_reduces_hEmeas g gi H hKcont hKp1 hgi hchr

end QIQTH.HEmeasRecon

/-! ## Axiom checks — every theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HEmeasRecon
#print axioms factorDiagonal_discharged
#print axioms hWmeas0_discharged
#print axioms kernelCont_reduces_hEmeas
#print axioms flow_base_continuousOn_of_gronwall
#print axioms heatOp_qregularity_of_jointCont
end AxiomChecks
