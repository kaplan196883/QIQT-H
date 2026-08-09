/-
  HProvGrounding — J4-470: REDUCE THE `hProvP` DIAGONAL-PROVIDER CARRY.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  continues the phase-2..12 census-surface reduction (`BoxCensusGrounding.v2Census_phase12`) by
  GROUNDING the per-point DIAGONAL provider carry `hProvP` — the `nbP`-local seven-leg linewise
  diff-under-∫ bundle (the J4-405 D-feeder legs, threaded through `hlin_as_D` at the DIAGONAL
  non-truncated `heatConv` window) — one level DOWN, onto its honest lower-level suppliers.

  ── THE DIAGONAL vs THE FROZEN PROVIDER (dont-undercredit).  `hProvP` is the SAME seven-leg first-
  order diff-under-∫ shape that `FrozenProviderLegs`/`FrozenHdiffLeg` already shrank 7 → 3 for the
  hQ1 FROZEN provider `hFrozenData`, but on the DIAGONAL window `uIoc 0 u` (heat-time `t := u`,
  `heatConvFrozen → heatConv`, NO `− epsSeq m` truncation) at the moving base `x ∈ nbP u` — exactly
  the `hProv` shape `PerUProviders.hlin_field_concrete` consumes.  J4-444 flagged the diagonal as
  DIFFERENT from the frozen provider, and here is precisely WHY: the diagonal window `[0, u]` REACHES
  the singular endpoint `τ = u − s → 0` (at `s = u`), whereas the frozen window `[0, u − εₘ]` keeps
  `τ ≥ εₘ > 0` off the singularity.  So the two `s`-slice MEASURABILITY legs (2)/(4) and the outer
  `HasDerivAt` leg (7) — which never touch the singularity — DISCHARGE on the diagonal exactly as in
  the frozen case (Fubini `innerIntegral_aesm`; the base-general `innerZ_line_hasDerivAt` + the
  FIRST-order gate dichotomy `hWdiff_offGate`/`hWdiff_onGate`), but the INTERVAL-INTEGRABILITY legs
  (3)/(5)/(6) do NOT: the banked capped-ceiling engine `pairing_intervalIntegrable_lowerCapped`
  needs a positive lower cap `εₘ` on `τ`, absent on the diagonal.  They stay honest carries.

  ── WHAT LANDS.
    • `diagLeg_hFmeas`  — ★ leg (2), DISCHARGED (Fubini) at the diagonal window `u`, base `x`.
    • `diagLeg_hF'meas` — ★ leg (4), DISCHARGED (Fubini) at the diagonal window `u`, base `x`.
    • `diagLeg_hdiff`   — ★ leg (7), DISCHARGED (HasDerivAt-under-∫ + gate dichotomy) at window `u`,
        base `x`, from a per-`(s,w)` `z`-level reduced core.
    • `hProvP_grounded` — ★★ the EXACT census `hProvP` shape, PRODUCED per-`(u,x,i)` from the diagonal
        joint / gate carries + the honest remainder (legs 1/3/5/6 + the `z`-level reduced core).
    • `v2Census_phase13` — ★★★★★ `v2Census_phase12` with the `hProvP` binder REMOVED and supplied
        internally from the strictly-lower-level diagonal carries.

  NO `sorry`, NO `:= True`, NO new axioms; std-3 only.  No existing file edited.
  ⚠  a₁ = R/6 remains CONDITIONAL.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.BoxCensusGrounding
import QIQTH.FrozenHdiffLeg

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.LeviSeries QIQTH.ExpMap QIQTH.HeatKernelA1
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.WitnessMeasDeriv QIQTH.SupConstantFamily QIQTH.UngatedChainRule QIQTH.PullbackMetric
open QIQTH.DuhamelCoreThreaded QIQTH.PerUCensusTuple QIQTH.W2Finish
open QIQTH.HDuhamelExportRethread QIQTH.TruncatedDuhamelData
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.V2CensusInstantiation QIQTH.WallAInstantiation QIQTH.WallAThreading
open QIQTH.HInterGrounding QIQTH.HAdom2capGrounding
open QIQTH.InnerDataInstantiation QIQTH.InnerDataEnvelope QIQTH.HdiffGrounding
open QIQTH.InnerDataCensusThread QIQTH.PresentationBridges QIQTH.CLSlotWire
open QIQTH.SliverTailMatched QIQTH.AmplitudeDataOnCollar
open QIQTH.AmpGeometryBundle QIQTH.DataAmpAssembly
open QIQTH.OffSVanishing QIQTH.HcapEndpointGrounding QIQTH.BoxCensusGrounding
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.HProvGrounding

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (Leg 2) `diagLeg_hFmeas` — the `∀ w` witness-value `s`-slice measurability, diagonal window.
    ############################################################################### -/

/-- **★ `diagLeg_hFmeas` — DIAGONAL PROVIDER LEG (2), DISCHARGED (Fubini).**  For every `w`, the
    `s`-ae-strong-measurability of the shifted witness-value inner pairing on the DIAGONAL window
    `(0, u]` (no `−εₘ` truncation), at the moving base `x`:
      `s ↦ ∫ z, vanVleckGatedWitness … (u−s) (update x i w) z · leviSeries (heatOp g gi W) s z 0`.
    Runs the banked Fubini engine `InnerMeasFubini.innerIntegral_aesm` on `.mul` of the joint
    witness carry `hWitJoint` (∀ `w`) and the Levi joint carry `hLeviJoint`.  Identical to
    `FrozenProviderLegs.frozenLeg_hFmeas` but at the diagonal window `u` and moving base `x`.  Honest
    carries {`hWitJoint`, `hLeviJoint`}, both window-`u`.  NOT `a₁ = R/6`. -/
theorem diagLeg_hFmeas (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (u : ℝ) (x : Point n) (i : Fin n)
    (hWitJoint : ∀ w : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        vanVleckGatedWitness g gi hC hK S a b (u - p.1) (Function.update x i w) p.2)
      ((volume.restrict (Set.uIoc 0 u)).prod (volume : Measure (Point n))))
    (hLeviJoint : AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
      ((volume.restrict (Set.uIoc 0 u)).prod (volume : Measure (Point n)))) :
    ∀ w : ℝ, AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update x i w) z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
      (volume.restrict (Set.uIoc 0 u)) := by
  intro w
  exact QIQTH.InnerMeasFubini.innerIntegral_aesm
    (fun p : ℝ × Point n =>
      vanVleckGatedWitness g gi hC hK S a b (u - p.1) (Function.update x i w) p.2
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
    ((hWitJoint w).mul hLeviJoint)

/-! ###############################################################################
    ### (Leg 4) `diagLeg_hF'meas` — the field-derivative `s`-slice measurability, diagonal window.
    ############################################################################### -/

/-- **★ `diagLeg_hF'meas` — DIAGONAL PROVIDER LEG (4), DISCHARGED (Fubini).**  The
    `s`-ae-strong-measurability of the FIRST field-derivative inner pairing at base `x`, diagonal
    window `(0, u]`:
      `s ↦ ∫ z, witnessFieldDeriv … i (u−s) x z · leviSeries (heatOp g gi W) s z 0`.
    Runs `InnerMeasFubini.innerIntegral_aesm` on `.mul` of the joint field-derivative carry
    `hWFDjoint` and the Levi joint carry `hLeviJoint`.  Identical to
    `FrozenProviderLegs.frozenLeg_hF'meas` but at the diagonal window `u` and moving base `x`.  Honest
    carries {`hWFDjoint`, `hLeviJoint`}, window-`u`.  NOT `a₁ = R/6`. -/
theorem diagLeg_hF'meas (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (u : ℝ) (x : Point n) (i : Fin n)
    (hWFDjoint : AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        witnessFieldDeriv g gi hC hK S a b i (u - p.1) x p.2)
      ((volume.restrict (Set.uIoc 0 u)).prod (volume : Measure (Point n))))
    (hLeviJoint : AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
      ((volume.restrict (Set.uIoc 0 u)).prod (volume : Measure (Point n)))) :
    AEStronglyMeasurable
      (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
      (volume.restrict (Set.uIoc 0 u)) :=
  QIQTH.InnerMeasFubini.innerIntegral_aesm
    (fun p : ℝ × Point n =>
      witnessFieldDeriv g gi hC hK S a b i (u - p.1) x p.2
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
    (hWFDjoint.mul hLeviJoint)

/-! ###############################################################################
    ### (Leg 7) `diagLeg_hdiff` — the outer `HasDerivAt` leg, diagonal window, moving base `x`.
    ############################################################################### -/

/-- **★★ `diagLeg_hdiff` — DIAGONAL PROVIDER LEG (7), DISCHARGED (HasDerivAt-under-∫).**  The outer
    `s`-level `HasDerivAt` family in the EXACT `hProvP` diagonal shape:
      `∀ᵐ s, s ∈ (0, u] → ∀ w ∈ snb,
         HasDerivAt (w ↦ ∫z W (u−s) (update x i w) z · F s z 0)
                    (∫z dH i (u−s) (update x i w) z · F s z 0) w`.
    Per-`(s, w)` it fires `HeatResidualBound.innerZ_line_hasDerivAt` (base line-point `p := w`), fed
    by the per-`(s,w)` base-`x` `z`-level REDUCED CORE `hRemainderDiff`, with the innermost
    `z`-pointwise `HasDerivAt` family DISCHARGED from the per-`z` GATE DICHOTOMY via the banked
    `FrozenHdiffLeg.innerZ_prod_hasDerivAt_witnessValue`.  Identical to `FrozenHdiffLeg.frozenLeg_hdiff`
    but at the diagonal window `u` and moving base `x`.  Honest carry: `hRemainderDiff`.  NOT
    `a₁ = R/6`. -/
theorem diagLeg_hdiff (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (u : ℝ) (x : Point n) (i : Fin n) (snb : Set ℝ)
    (hRemainderDiff : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
        ∃ (znb : Set ℝ) (bnd : Point n → ℝ),
          znb ∈ 𝓝 w ∧
          (∀ w' : ℝ, AEStronglyMeasurable
            (fun z => vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update x i w') z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume) ∧
          Integrable
            (fun z => vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update x i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume ∧
          AEStronglyMeasurable
            (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume ∧
          Integrable bnd volume ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb,
            ‖witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w') z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bnd z) ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb,
            z ∉ K ∨ PdiffAt (fun x' : Point n =>
                vanVleckGatedWitness g gi hC hK S a b (u - s) x' z) i (Function.update x i w'))) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
      HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s)
          (Function.update x i w) z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
        (∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) w := by
  filter_upwards [hRemainderDiff] with s hcore hmem w hw
  obtain ⟨znb, bnd, hznb, hWmeas, hbaseInt, hWFDmeas, hbndInt, hdom, hzGate⟩ := hcore hmem w hw
  refine QIQTH.HeatResidualBound.innerZ_line_hasDerivAt
    (vanVleckGatedWitness g gi hC hK S a b)
    (witnessFieldDeriv g gi hC hK S a b i)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)))
    u s i x w znb hznb hWmeas hbaseInt hWFDmeas bnd hbndInt hdom ?_
  filter_upwards [hzGate] with z hz w' hw'
  exact QIQTH.FrozenHdiffLeg.innerZ_prod_hasDerivAt_witnessValue g gi hC hK S a b i (u - s) x z w'
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) (hz w' hw')

/-! ###############################################################################
    ### ★★ `hProvP_grounded` — the census `hProvP` shape, produced from the diagonal carries.
    ############################################################################### -/

/-- **★★ `hProvP_grounded`.**  THE `hProvP` DISCHARGE (the DIAGONAL provider).  Produces the EXACT
    census `hProvP` seven-leg bundle — per `(u ∈ U, x ∈ nbP u, i)` — from:
      • the DISCHARGED legs (2)/(4)/(7): `diagLeg_hFmeas`/`diagLeg_hF'meas` on the window-`u` joint
        carries {`hLeviJoint`, `hWitJointXupd`, `hWFDjointX`} via the Fubini engine, and `diagLeg_hdiff`
        on the `z`-level reduced core (bundled in `hRemainderDiag`) via the HasDerivAt engine + gate;
      • the honest REMAINDER `hRemainderDiag` — legs (1) `snbx`, (3) `hFint` (the diagonal
        witness-value interval-integrability, NOT dischargeable — singular endpoint), (5)/(6) the
        interval-integrable dominator + domination, and the `z`-level reduced core for (7), all bundled
        under the SAME existential `snbx`/`bound`.
    m-UNIFORMITY: there is NO `m` on the diagonal (the window is the full `[0, u]`), so the frozen
    provider's m-uniformity trap is vacuous.  Every carry is satisfiable, non-vacuous, none the
    conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem hProvP_grounded (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (nbP : ℝ → Set (Point n))
    (hLeviJoint : ∀ d : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hWitJointXupd : ∀ (i : Fin n) (u : ℝ), u ∈ U → ∀ x ∈ nbP u, ∀ (w d : ℝ),
      AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        vanVleckGatedWitness g gi hC hK S a b (u - p.1) (Function.update x i w) p.2)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hWFDjointX : ∀ (i : Fin n) (u : ℝ), u ∈ U → ∀ x ∈ nbP u, ∀ d : ℝ,
      AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        witnessFieldDeriv g gi hC hK S a b i (u - p.1) x p.2)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hRemainderDiag : ∀ u ∈ U, ∀ x ∈ nbP u, ∀ i : Fin n,
        ∃ (snbx : Set ℝ) (bound : ℝ → ℝ),
          snbx ∈ 𝓝 (x i) ∧
          IntervalIntegrable
            (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) x z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume 0 u ∧
          IntervalIntegrable bound volume 0 u ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snbx,
            ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bound s) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snbx,
            ∃ (znb : Set ℝ) (bnd : Point n → ℝ),
              znb ∈ 𝓝 w ∧
              (∀ w' : ℝ, AEStronglyMeasurable
                (fun z => vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update x i w') z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume) ∧
              Integrable
                (fun z => vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update x i w) z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume ∧
              AEStronglyMeasurable
                (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume ∧
              Integrable bnd volume ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ znb,
                ‖witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w') z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bnd z) ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ znb,
                z ∉ K ∨ PdiffAt (fun x' : Point n =>
                    vanVleckGatedWitness g gi hC hK S a b (u - s) x' z) i (Function.update x i w')))) :
    ∀ u ∈ U, ∀ x ∈ nbP u, ∀ i : Fin n,
      ∃ (snbx : Set ℝ) (bound : ℝ → ℝ),
        snbx ∈ 𝓝 (x i) ∧
        (∀ w, AEStronglyMeasurable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u))) ∧
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume 0 u ∧
        AEStronglyMeasurable
          (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u)) ∧
        IntervalIntegrable bound volume 0 u ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snbx,
          ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bound s) ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snbx,
          HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s)
              (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) w) := by
  intro u hu x hx i
  obtain ⟨snbx, bound, hsnbx, hFint, hbdd, hbound, hRedCore⟩ := hRemainderDiag u hu x hx i
  refine ⟨snbx, bound, hsnbx, ?_, hFint, ?_, hbdd, hbound, ?_⟩
  · exact diagLeg_hFmeas g gi hC hK S a b u x i
      (fun w => hWitJointXupd i u hu x hx w u) (hLeviJoint u)
  · exact diagLeg_hF'meas g gi hC hK S a b u x i (hWFDjointX i u hu x hx u) (hLeviJoint u)
  · exact diagLeg_hdiff g gi hC hK S a b u x i snbx hRedCore

/-! ###############################################################################
    ### ★★★★★ `v2Census_phase13` — phase-12 with `hProvP` supplied internally.
    ############################################################################### -/

/-- **★★★★★ `v2Census_phase13`.**  `BoxCensusGrounding.v2Census_phase12` with the `hProvP`
    diagonal-provider carry REMOVED from the ∃-body and SUPPLIED INTERNALLY via `hProvP_grounded`
    from the strictly-lower-level diagonal carries {`hLeviJointDiag`, `hWitJointXupd`, `hWFDjointX`,
    `hRemainderDiag`}: the two `s`-slice measurability legs (2)/(4) and the outer `HasDerivAt` leg
    (7) are discharged (Fubini + HasDerivAt-under-∫ + gate dichotomy) from the window-`u` joint / gate
    carries; the interval-integrability legs (1)/(3)/(5)/(6) + the `z`-level reduced core stay honest
    carries in `hRemainderDiag` (the diagonal window reaches the singular endpoint `τ = 0`, so the
    capped-ceiling engine that discharged them in the frozen case does not apply).  The signature is
    exactly `v2Census_phase12`'s minus `{hProvP}` plus `{hLeviJointDiag, hWitJointXupd, hWFDjointX,
    hRemainderDiag}`.

    ⚠  THE GATE.  The reconstructed `hProvP` references the ∃-obtained `S`; `hProvP_grounded` produces
    it in the EXACT census shape, so the swap is exact.  ⚠ Pure surface re-plumbing; closes NOTHING
    deeper.  NOT `a₁ = R/6`. -/
theorem v2Census_phase13 (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hwtop : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hn : 1 ≤ n) (T : ℝ) (hT : 0 < T) :
    ∃ (a b : ℝ) (S : Point n → Set (Point n)), 0 < a ∧ a < b ∧
      ∀ (F : ℝ → Point n → Point n → ℝ)
        (_hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
        (t : ℝ) (U : Set ℝ) (_hUopen : IsOpen U) (_htU : t ∈ U)
        (_hUT : ∀ u ∈ U, u ≤ T)
        (_hBoundaryLim : Tendsto
            (fun m => BoundaryTrunc (vanVleckGatedWitness g gi hChr hK S a b) F m t) atTop
            (𝓝 (F t 0 0)))
        (_hgi : MemGaugeGi (n := n) gi) (_hΓ : MemGaugeGamma (n := n) g gi)
        (V : Set (Point n)) (_hVopen : IsOpen V) (_hV0 : (0 : Point n) ∈ V)
        (snb : Set ℝ) (_hsnb : snb ∈ 𝓝 (0 : ℝ))
        (_hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
            pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u
                (u - epsSeq m) x 0) i y
              = ∫ s in (0)..(u - epsSeq m),
                  ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) y z * F s z 0)
        (_hFmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
            (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w) z * F s z 0)
            (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
        (_hFint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
            (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (0 : Point n) z * F s z 0)
            volume 0 (u - epsSeq m))
        (_hF'meas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
            (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s) (0 : Point n) z * F s z 0)
            (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
        (bnd : ℕ → Fin n → ℝ → ℝ)
        (_hbdd : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
            IntervalIntegrable (bnd m i) volume 0 (u - epsSeq m))
        (_hbound : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
            s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
              ‖∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                  (Function.update (0 : Point n) i w) z * F s z 0‖ ≤ bnd m i s)
        (D0 D1 : Fin n → ℝ) (_hD0 : ∀ i, 0 ≤ D0 i) (_hD1 : ∀ i, 0 ≤ D1 i)
        (_hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
            |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
                witnessSecondXDeriv g gi hChr hK S a b i (u - s) z * F s z 0|
              ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
        (E₀ E₁ C_L aT : ℝ) (_hE₀ : 0 ≤ E₀) (_hE₁ : 0 ≤ E₁) (_hC_L : 0 ≤ C_L) (_haT : 0 < aT)
        (_hUlb : ∀ u ∈ U, aT ≤ u)
        (_hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
            |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
              ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
        (_hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
        (_hIlo : ∀ (m : ℕ), ∀ u ∈ U,
            IntervalIntegrable (fun s => ∫ (z : Point n),
                heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z * F s z 0)
              volume 0 (u - epsSeq m))
        (_hIhi : ∀ (m : ℕ), ∀ u ∈ U,
            IntervalIntegrable (fun s => ∫ (z : Point n),
                heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z * F s z 0)
              volume (u - epsSeq m) u)
        (_hEcomb : MemECombine g gi (vanVleckGatedWitness g gi hChr hK S a b) F)
        (A₀ A₁ : ℝ) (_hA₀ : 0 ≤ A₀) (_hA₁ : 0 ≤ A₁)
        (_hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
            |vanVleckGatedWitness g gi hChr hK S a b τ p q|
              ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
        (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness g gi hChr hK S a b τ p q = 0)
        (_hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
            (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
            (volume.restrict (Set.uIoc 0 u)))
        (_hUfloor : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ U, c ≤ u)
        (_hInnerCont : ∀ u ∈ U,
            ContinuousOn (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
              (Set.Ioo 0 u))
        (nb : ℕ → ℝ → Set ℝ) (_hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
        (_hFmeas_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ c, AEStronglyMeasurable
          (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (c - s) 0 z * F s z 0)
          (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
        (_hFint_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
          volume 0 (u - epsSeq m))
        (_hF'meas_d : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
          (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s) * F s z 0)
          (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
        (boundD : ℕ → ℝ → ℝ → ℝ)
        (_hbdd_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
        (_hbound_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb m u,
          ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (c - s) * F s z 0‖
            ≤ boundD m u s)
        (_hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb m u,
          HasDerivAt (fun c => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (c - s) 0 z * F s z 0)
            (∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (c - s) * F s z 0) c)
        (L : ℕ → ℝ → ℝ) (_hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
        (_hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
          |heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F (u + h) (u - epsSeq m + k) 0 0
              - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F (u + h) (u - epsSeq m) 0 0
              - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u (u - epsSeq m + k) 0 0
              + heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u (u - epsSeq m) 0 0|
            ≤ L m u * (|h| * |k|))
        (ρ lam CW Cf τ₀ : ℝ) (ta tb : ℝ)
        (_hρ : 0 < ρ) (_hlam : 0 < lam) (_hCW : 0 ≤ CW) (_hτ₀ : 0 < τ₀)
        (_hWmeas : ∀ τ, AEStronglyMeasurable
            (fun z => vanVleckGatedWitness g gi hChr hK S a b τ (0 : Point n) z) volume)
        (_hffro_meas : ∀ u, AEStronglyMeasurable (fun z => F u z (0 : Point n)) volume)
        (_hfmov_meas : ∀ m u, AEStronglyMeasurable (fun z => F (u - epsSeq m) z (0 : Point n)) volume)
        (_hffro_bdd : ∀ u z, |F u z (0 : Point n)| ≤ Cf)
        (_hfmov_bdd : ∀ m u z, |F (u - epsSeq m) z (0 : Point n)| ≤ Cf)
        (_hWDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z,
          |vanVleckGatedWitness g gi hChr hK S a b τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z)
        (_hmass : ∀ᶠ m in atTop,
          ∫ z, |vanVleckGatedWitness g gi hChr hK S a b (epsSeq m) (0 : Point n) z| ≤ CW)
        (_hmassone : Tendsto
            (fun m => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (epsSeq m) (0 : Point n) z) atTop (𝓝 1))
        (_hmod : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ u ∈ Set.Icc ta tb,
            ∀ z ∈ Metric.ball (0 : Point n) δ,
              |F u z (0 : Point n) - F u (0 : Point n) (0 : Point n)| < ε)
        (_hsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ u ∈ Set.Icc ta tb,
            ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
              |F (u - epsSeq m) z (0 : Point n) - F u z (0 : Point n)| < ε)
        (_hUsub : U ⊆ Set.Icc ta tb)
        (τc wA2 : ℝ)
        (_hwA2 : 0 < wA2)
        (hτc : epsSeq 0 ≤ τc)
        (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
        (Cdata : ℝ)
        (data : LeviSeriesLocalData
            (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) Cdata T)
        (hpd2diag : ∀ i : Fin n, ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
          ContinuousOn
            (fun p : ℝ × Point n =>
              pd (fun x : Point n =>
                  pd (fun x' : Point n =>
                    vanVleckGatedWitness g gi hChr hK S a b p.1 x' p.2) i x) i (0 : Point n))
            (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
        (htermBox : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ k : ℕ,
          ContinuousOn
            (fun p : ℝ × Point n =>
              iterE (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) (k + 1) p.1 p.2 0)
            (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
        (Ccrude : ℝ) (_hCcrude : 0 ≤ Ccrude)
        (_hcrude : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
            |witnessSecondXDeriv g gi hChr hK S a b i τ z|
              ≤ Ccrude * τ⁻¹ * gaussDdim (wA2 * τ) (0 - z))
        (Lc Bcomp Q Sconst : ℝ)
        (hLc : 0 ≤ Lc) (_hBcomp : 0 ≤ Bcomp) (_hQ : 0 ≤ Q) (_hSconst : 0 ≤ Sconst)
        (rr0 cc : ℝ)
        (ampData : ∀ i : Fin n,
          AmplitudeDerivativeDataOn g gi hChr hK S a b
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) i T τc
            (collarRegime (K := K) rr0 cc τc))
        (qcF IchartF : Fin n → ℝ → ℝ → Point n → ℝ)
        (_hgateC : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
          ∀ z ∈ collar (cc * Real.sqrt τ), z ∈ K ∧ ‖z‖ < rr0)
        (_hoffC : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
          ∀ z ∈ (collar (cc * Real.sqrt τ))ᶜ,
            witnessSecondXDeriv g gi hChr hK S a b i τ z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
              = IchartF i τ s z
                + z i / (2 * τ) * gaussDdim τ z * (ampData i).A1amp τ z
                    * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
                + gaussDdim τ z * (ampData i).A2amp τ z
                    * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (_hWintC : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
          Integrable (fun z => witnessSecondXDeriv g gi hChr hK S a b i τ z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
        (_hf2C : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
          Integrable (fun z => z i / (2 * τ) * gaussDdim τ z * (ampData i).A1amp τ z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
        (_hf3C : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
          Integrable (fun z => gaussDdim τ z * (ampData i).A2amp τ z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
        (_hqzC : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc → ∀ z w,
          |(ampData i).Aamp τ z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
              - (ampData i).Aamp τ w
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s w 0|
            ≤ Lc * dist z w)
        (_hqzmeasC : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
          AEStronglyMeasurable (fun z => (ampData i).Aamp τ z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
        (_hqcC : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc → ∀ z w,
          |qcF i τ s z - qcF i τ s w| ≤ Lc * dist z w)
        (_hqcmeasC : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
          AEStronglyMeasurable (qcF i τ s) volume)
        (_h0C : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
          (ampData i).Aamp τ 0
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s 0 0
            = qcF i τ s 0)
        (_hIchartC : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
          IntegrableOn (IchartF i τ s) (collar (cc * Real.sqrt τ))ᶜ volume)
        (_hcompC : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
          ‖∫ z in (collar (cc * Real.sqrt τ))ᶜ,
              (IchartF i τ s z - hessGaussFactor i τ z * qcF i τ s z)‖ ≤ Bcomp / Real.sqrt τ)
        (_hf2boundC : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
          |∫ z, z i / (2 * τ) * gaussDdim τ z * (ampData i).A1amp τ z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
            ≤ Q / Real.sqrt τ)
        (_hf3boundC : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
          |∫ z, gaussDdim τ z * (ampData i).A2amp τ z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
            ≤ Sconst)
        (ρc : ℝ) (_hρc : 0 < ρc)
        (_hwInf : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
          (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
        (_hC1geom : ∀ (i : Fin n), ∀ w ∈ snb,
          ContinuousOn
            (fun q : ℝ × Point n =>
              uniformInverseChart g gi hChr hK q.2 (Function.update (0 : Point n) i q.1))
            (Set.Icc (w - ρc) (w + ρc) ×ˢ K)
          ∧ Set.MapsTo
            (fun q : ℝ × Point n =>
              (q.2, uniformInverseChart g gi hChr hK q.2 (Function.update (0 : Point n) i q.1)))
            (Set.Icc (w - ρc) (w + ρc) ×ˢ K)
            (K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hChr hK))
          ∧ (∀ q ∈ Set.Icc (w - ρc) (w + ρc) ×ˢ K,
              IsUnit (fderiv ℝ (uniformFlowExp g gi hChr hK q.2)
                (uniformInverseChart g gi hChr hK q.2 (Function.update (0 : Point n) i q.1))))
          ∧ (∀ q ∈ Set.Icc (w - ρc) (w + ρc) ×ˢ K,
              fderiv ℝ (uniformInverseChart g gi hChr hK q.2) (Function.update (0 : Point n) i q.1)
                = Ring.inverse (fderiv ℝ (uniformFlowExp g gi hChr hK q.2)
                    (uniformInverseChart g gi hChr hK q.2 (Function.update (0 : Point n) i q.1))))
          ∧ (∀ q ∈ Set.Icc (w - ρc) (w + ρc) ×ˢ K,
              DifferentiableAt ℝ (uniformInverseChart g gi hChr hK q.2)
                (Function.update (0 : Point n) i q.1))
          ∧ (∀ q ∈ Set.Icc (w - ρc) (w + ρc) ×ˢ K,
              S q.2 ∈ nhds (Function.update (0 : Point n) i q.1)))
        (hEmeas : StronglyMeasurable (fun w : ℝ × Point n × Point n =>
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) w.1 w.2.1 w.2.2))
        (hGateCoreRR : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
            s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
            ∃ (znb : Set ℝ) (C₂ : ℝ),
              znb ∈ 𝓝 w ∧ 0 ≤ C₂ ∧
              (∀ w' : ℝ, AEStronglyMeasurable
                (fun z => witnessFieldDeriv g gi hChr hK S a b i (u - s)
                    (Function.update (0 : Point n) i w') z) volume) ∧
              AEStronglyMeasurable
                (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
                volume ∧
              AEStronglyMeasurable
                (fun z => witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                    (Function.update (0 : Point n) i w) z) volume ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ znb, z ∈ K →
                |witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                    (Function.update (0 : Point n) i w') z| ≤ C₂) ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ znb,
                z ∉ K ∨ PdiffAt (fun x' : Point n =>
                    witnessFieldDeriv g gi hChr hK S a b i (u - s) x' z) i
                  (Function.update (0 : Point n) i w')))
        (nbP : ℝ → Set (Point n)) (_hnbP_open : ∀ u ∈ U, IsOpen (nbP u))
        (_hnbP0 : ∀ u ∈ U, (0 : Point n) ∈ nbP u)
        -- ★ THE `hProvP` BINDER of `v2Census_phase12` IS REPLACED BY THESE LOWER-LEVEL CARRIES
        --   (underscore-named in the statement, re-bound in the proof — the `_hProvP` convention):
        (_hLeviJointDiag : ∀ d : ℝ, AEStronglyMeasurable
          (fun p : ℝ × Point n =>
            leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
          ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
        (_hWitJointXupd : ∀ (i : Fin n) (u : ℝ), u ∈ U → ∀ x ∈ nbP u, ∀ (w d : ℝ),
          AEStronglyMeasurable
          (fun p : ℝ × Point n =>
            vanVleckGatedWitness g gi hChr hK S a b (u - p.1) (Function.update x i w) p.2)
          ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
        (_hWFDjointX : ∀ (i : Fin n) (u : ℝ), u ∈ U → ∀ x ∈ nbP u, ∀ d : ℝ,
          AEStronglyMeasurable
          (fun p : ℝ × Point n =>
            witnessFieldDeriv g gi hChr hK S a b i (u - p.1) x p.2)
          ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
        (_hRemainderDiag : ∀ u ∈ U, ∀ x ∈ nbP u, ∀ i : Fin n,
            ∃ (snbx : Set ℝ) (bound : ℝ → ℝ),
              snbx ∈ 𝓝 (x i) ∧
              IntervalIntegrable
                (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) x z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume 0 u ∧
              IntervalIntegrable bound volume 0 u ∧
              (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snbx,
                ‖∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (Function.update x i w) z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ bound s) ∧
              (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snbx,
                ∃ (znb : Set ℝ) (bnd : Point n → ℝ),
                  znb ∈ 𝓝 w ∧
                  (∀ w' : ℝ, AEStronglyMeasurable
                    (fun z => vanVleckGatedWitness g gi hChr hK S a b (u - s) (Function.update x i w') z
                      * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume) ∧
                  Integrable
                    (fun z => vanVleckGatedWitness g gi hChr hK S a b (u - s) (Function.update x i w) z
                      * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume ∧
                  AEStronglyMeasurable
                    (fun z => witnessFieldDeriv g gi hChr hK S a b i (u - s) (Function.update x i w) z
                      * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume ∧
                  Integrable bnd volume ∧
                  (∀ᵐ z ∂volume, ∀ w' ∈ znb,
                    ‖witnessFieldDeriv g gi hChr hK S a b i (u - s) (Function.update x i w') z
                      * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ bnd z) ∧
                  (∀ᵐ z ∂volume, ∀ w' ∈ znb,
                    z ∉ K ∨ PdiffAt (fun x' : Point n =>
                        vanVleckGatedWitness g gi hChr hK S a b (u - s) x' z) i (Function.update x i w'))))
        (fderivBulk : ℝ → Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
        (gderiv : ℝ → Fin n → Point n → (Point n →L[ℝ] ℝ))
        (C₀ C₁ C₂ : ℝ → Fin n → ℝ)
        (_hGintP : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), IntervalIntegrable
            (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) x z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
                ∂(volume : Measure (Point n)))
            volume 0 u)
        (_hbulkderiv : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
            HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK S a b u i m)
              (fderivBulk u i m x) x)
        (_hsliver : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
            dist (fderivBulk u i m x) (gderiv u i x)
              ≤ (C₀ u i + C₁ u i) * (2 * Real.sqrt (epsSeq m)) + C₂ u i * epsSeq m)
        (_hcont : ∀ u ∈ U, ∀ i : Fin n, ContinuousOn (gderiv u i) (Set.univ : Set (Point n)))
        (_hfrozen_pd1 : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ),
            (fun y => pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
                (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
                (u - epsSeq m) x 0) i y)
              =ᶠ[𝓝 (0 : Point n)]
              QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK S a b u i m),
        TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t := by
  obtain ⟨a, b, S, ha, hab, hbody12⟩ :=
    QIQTH.BoxCensusGrounding.v2Census_phase12 g gi hg hChr hK hgnd hgsymm hinvF hframeK hwtop
      hdg0 hg0 hn T hT
  refine ⟨a, b, S, ha, hab, fun F hFeq t U hUopen htU hUT hBoundaryLim hgi hΓ V hVopen hV0
    snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound D0 D1 hD0 hD1 hbnd
    E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hEdom hFdom hIlo hIhi hEcomb A₀ A₁ hA₀ hA₁ hAdom hAzero
    hMeasFII hUfloor hInnerCont nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff
    L hLnn hCross ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd
    hfmov_bdd hWDom hmass hmassone hmod hsup hUsub τc wA2 hwA2 hτc hεU Cdata data hpd2diag htermBox
    Ccrude hCcrude hcrude Lc Bcomp Q Sconst hLc hBcomp hQ hSconst
    rr0 cc ampData qcF IchartF hgateC hoffC hWintC hf2C hf3C hqzC hqzmeasC hqcC hqcmeasC
    h0C hIchartC hcompC hf2boundC hf3boundC
    ρc hρc hwInf hC1geom hEmeas hGateCoreRR nbP hnbP_open hnbP0
    hLeviJointDiag hWitJointXupd hWFDjointX hRemainderDiag
    fderivBulk gderiv C₀ C₁ C₂ hGintP hbulkderiv hsliver hcont hfrozen_pd1 => ?_⟩
  -- ★ GROUND `hProvP` from the diagonal joint / gate carries + the honest remainder.
  have hProvP := hProvP_grounded g gi hChr hK S a b U nbP
    hLeviJointDiag hWitJointXupd hWFDjointX hRemainderDiag
  -- ★ THREAD the reconstructed diagonal provider through the phase-12 body.
  exact hbody12 F hFeq t U hUopen htU hUT hBoundaryLim hgi hΓ V hVopen hV0
    snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound D0 D1 hD0 hD1 hbnd
    E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hEdom hFdom hIlo hIhi hEcomb A₀ A₁ hA₀ hA₁ hAdom hAzero
    hMeasFII hUfloor hInnerCont nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff
    L hLnn hCross ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd
    hfmov_bdd hWDom hmass hmassone hmod hsup hUsub τc wA2 hwA2 hτc hεU Cdata data hpd2diag htermBox
    Ccrude hCcrude hcrude Lc Bcomp Q Sconst hLc hBcomp hQ hSconst
    rr0 cc ampData qcF IchartF hgateC hoffC hWintC hf2C hf3C hqzC hqzmeasC hqcC hqcmeasC
    h0C hIchartC hcompC hf2boundC hf3boundC
    ρc hρc hwInf hC1geom hEmeas hGateCoreRR nbP hnbP_open hnbP0 hProvP
    fderivBulk gderiv C₀ C₁ C₂ hGintP hbulkderiv hsliver hcont hfrozen_pd1

/-! ###############################################################################
    ### THE PROVIDER LEDGER — the per-leg table for the `hProvP` DIAGONAL provider.
    ############################################################################### -/

/-- **`hprov_grounding_residuals`.**  THE ENUMERATED SURVIVING RESIDUALS after the J4-470 diagonal
    `hProvP` grounding.  A genuine conjunction (non-vacuous plumbing witness), machine-checkable; each
    conjunct SATISFIABLE, none the conclusion.

    THE PROVIDER LEDGER (`v2Census_phase13` carries these in place of `hProvP`):
      leg          role                                          status         supplier / m-UNIFORMITY
      ──────────   ───────────────────────────────────────────  ─────────────  ──────────────────────
      (1) snbx     real-line nbhd 𝓝(x i)                        REMAINDER      `hRemainderDiag`; per-(i,x)
      (2) hFmeas   `∀w, s↦∫z W(u−s)(update x i w)·F` aesm         ★ DISCHARGED   `diagLeg_hFmeas` =
                                                                                `innerIntegral_aesm` on
                                                                                `hWitJointXupd`·`hLeviJointDiag`
      (3) hFint    `s↦∫z W(u−s) x·F` interval-integrable          REMAINDER      `hRemainderDiag`; NOT
                                                                                dischargeable — the DIAGONAL
                                                                                window `[0,u]` reaches the
                                                                                singular endpoint `τ=0`, no
                                                                                lower cap for the capped
                                                                                engine (the J4-444 point)
      (4) hF'meas  `s↦∫z dH i(u−s) x·F` aesm                      ★ DISCHARGED   `diagLeg_hF'meas` =
                                                                                `innerIntegral_aesm` on
                                                                                `hWFDjointX`·`hLeviJointDiag`
      (5) bound+hbdd  interval-integrable `s`-dominator           REMAINDER      `hRemainderDiag`
      (6) hbound   `‖∫z dH…(update x i w)·F‖ ≤ bound s`            REMAINDER      `hRemainderDiag`
      (7) hdiff    outer `s`-level `HasDerivAt (∫z W)(∫z dH)`      ★ DISCHARGED   `diagLeg_hdiff` =
                                                                                `innerZ_line_hasDerivAt`
                                                                                (base `p:=w`) + `innerZ_prod_
                                                                                hasDerivAt_witnessValue` on
                                                                                the FIRST-order gate dichotomy;
                                                                                fed the `z`-level reduced core
                                                                                in `hRemainderDiag`

    ⚠ VERDICT.  The diagonal provider shrinks 7 → 4: legs (2)/(4)/(7) DISCHARGED in the provider's exact
    shape from window-`u` joint / gate carries via the banked Fubini + HasDerivAt-under-∫ engines; the
    honest REMAINDER is {snbx, hFint, dominator triple, `z`-level reduced core} = the analytic
    domination + witness-value integrability content no measurability/HasDerivAt engine can supply.  The
    m-UNIFORMITY trap is VACUOUS (no `m` on the diagonal).  ⚠ NOT `a₁ = R/6`; CONDITIONAL on exactly
    this surface. -/
def hprov_grounding_residuals (hSnbx hFint hDom hRedCore hFmeas hF'meas hHdiff : Prop) : Prop :=
  hSnbx ∧ hFint ∧ hDom ∧ hRedCore ∧ hFmeas ∧ hF'meas ∧ hHdiff

/-- The provider ledger is a genuine conjunction projector (non-vacuous plumbing witness).
    ⚠ NOT `a₁ = R/6`. -/
theorem hprov_grounding_residuals_intro
    {hSnbx hFint hDom hRedCore hFmeas hF'meas hHdiff : Prop}
    (h1 : hSnbx) (h2 : hFint) (h3 : hDom) (h4 : hRedCore)
    (h5 : hFmeas) (h6 : hF'meas) (h7 : hHdiff) :
    hprov_grounding_residuals hSnbx hFint hDom hRedCore hFmeas hF'meas hHdiff :=
  ⟨h1, h2, h3, h4, h5, h6, h7⟩

end QIQTH.HProvGrounding

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HProvGrounding.diagLeg_hFmeas
#print axioms QIQTH.HProvGrounding.diagLeg_hF'meas
#print axioms QIQTH.HProvGrounding.diagLeg_hdiff
#print axioms QIQTH.HProvGrounding.hProvP_grounded
#print axioms QIQTH.HProvGrounding.v2Census_phase13
#print axioms QIQTH.HProvGrounding.hprov_grounding_residuals_intro
