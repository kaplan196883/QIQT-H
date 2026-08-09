/-
  WallAInstantiation — J4-458: THE WALL-A INTERCHANGE CENSUS INSTANTIATED AT THE WITNESS.
  Sol #20's item (v), the LAST of the six Sol-#20 attack items on the `a₁ = R/6` campaign.

  This instantiates the block-B wall-A interchange census that
  `MomentWallCoverage.truncatedDuhamelCore_threaded_v3` (and its `V2CensusInstantiation` re-thread)
  carries — the six members `hInter`, `hAdom2cap`, `hFdomW`, `hmeas2Lo`, `hSecCont`, `hBcont` — at the
  concrete ρ-scaled chart witness `H_G := vanVleckGatedWitness g gi hChr hK S a b`, source
  `F := leviSeries (heatOp g gi H_G)`.  Three of the six are WIRED/BRIDGED from banked suppliers, one is
  supplied VERBATIM, and exactly TWO genuinely carry.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  `a₁ = R/6`
  remains CONDITIONAL on the whole `hDuhamel` / convergence-trio + geometric-wiring stack AND on the
  surviving labelled census carries.  Every theorem here re-threads BANKED, satisfiable wall-A census
  data into the EXACT shape `truncatedDuhamelCore_threaded_v3` consumes, or honestly carries the two
  genuine residuals.  Each carried hypothesis is genuine, satisfiable, non-vacuous, strictly lower-level
  than its target, and never the conclusion.  NO `sorry` (header prose excepted), NO `:= True`, NO new
  axioms, NO existing file edited, nothing wired into `AxiomAudit`.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE WALL-A BINDER MAP.  (Sol #20's traps noted per member: integrability-absoluteness /
     measurability / boundary.)

  The block-B wall-A census carried by `truncatedDuhamelCore_threaded_v3` (see `V2CensusInstantiation`
  block-(B) and `DuhamelCoreThreaded` lines 300-322), with member → banked supplier → verbatim wire /
  shape bridge / genuine witness-level carry.

  ── member ── supplier ── verdict ── trap ────────────────────────────────────────────────────────────
    `hInter`     `MemInterchange H_G F U (witnessSecondXDeriv …)`
                 ── GENUINE CARRY.  No banked supplier delivers the atomic diff-under-∫ interchange
                    bundle at the witness; it is the interchange input the whole wall-A leg reduces TO.
                 ── trap: integrability-ABSOLUTENESS (the bundle carries absolute, not conditional,
                    integrability of the pairing; never a series↔∫ swap from pointwise data).

    `hAdom2cap`  `∀ m i τ, εₘ ≤ τ → τ ≤ T → ∀ z, |witnessSecondXDeriv … i τ z| ≤ CA2c m·gaussDdim (wA2·τ)(0−z)`
                 ── GENUINE CARRY.  Per `CensusDominations` (D3): NO banked bound of THIS clean
                    `CA2c·gaussDdim (wA2·τ)` shape exists at the concrete van-Vleck witness; the only
                    banked second-`x`-derivative domination is the CRUDE `C·τ⁻¹·gaussDdim (lam·τ)` form
                    (`WideAmplitudePackage.hSecond`), a genuinely different envelope.  Stays a carry.
                 ── trap: measurability / domination (a Gaussian cap, absolute value; not a boundary cap).

    `hFdomW`     `∀ s, 0<s → s≤T → ∀ z, |leviSeries (heatOp g gi H_G) s z 0| ≤ CF·gaussDdim (wF·s) z`
                 ── SHAPE BRIDGE (J4-437 pattern) via `DaLimEasyTranche.hFdom_concrete`.  That banked
                    lemma gives the width-2 Levi envelope `∃ C_L ≥ 0, ∀ s z y, |leviSeries E s z y| ≤
                    C_L·gaussDdim (2·s)(z−y)`; specialise `y := 0` and rewrite `z − 0 = z` (`sub_zero`)
                    to land EXACTLY the `hFdomW` shape with `wF := 2`, `CF := C_L`.  Honest input: the
                    `LeviSeriesLocalData E C T` package (RNC geometry pile behind the banked envelope).
                 ── trap: integrability-absoluteness (a Gaussian ENVELOPE on |·|, width-clean, no
                    `τ⁻¹` blow-up as `s → 0`; the width match `2 = wF` is the whole bridge).

    `hmeas2Lo`   `∀ m i, ∀ u ∈ U, AEStronglyMeasurable (fun s => ∫ z, witnessSecondXDeriv … (u−s) z ·
                    leviSeries … s z 0) (volume.restrict (uIoc 0 (u−εₘ)))`
                 ── REDUCTION BRIDGE via `SliceMeasurability.hmeas2Lo_slice`: the s-slice a.e.-strong
                    measurability FOLDS INTO the joint-continuity atoms `{hSecCont, hBcont}` + the
                    group-(A) scaffolding `{hUT, hεU}` (parametric-integral joint-continuity ⟹ slice
                    measurability, via `sliceMeas_of_jointCont`).  So `hmeas2Lo` is NOT an independent
                    carry — it collapses onto `hSecCont`/`hBcont` below.
                 ── trap: measurability (a.e.-strong on the RESTRICTED measure; the `uIoc 0 (u−εₘ)`
                    is `Ioc` since `εₘ ≤ u`, no boundary-cap indicator obligation).

    `hSecCont`   `∀ i, ContinuousOn (fun p => witnessSecondXDeriv … i p.1 p.2) (Ioc 0 T ×ˢ univ)`
                 ── VERBATIM wire via `JointContinuityAtoms.hSecCont_of_boxes`: the positive-time strip
                    joint-continuity is the EXACT conclusion of the banked local-to-global lift from a
                    positive-time-compact box family (`Icc (τ₀/2) T ×ˢ closedBall 0 R`).  Identical shape,
                    one re-export.
                 ── trap: boundary (the strip `Ioc 0 T` excludes `τ = 0`; the `τ₀/2` box floor keeps every
                    box strictly inside positive time — no `τ → 0` blow-up).

    `hBcont`     `ContinuousOn (fun p => leviSeries (heatOp g gi H_G) p.1 p.2 0) (Ioc 0 T ×ˢ univ)`
                 ── SHAPE BRIDGE via `JointContinuityAtoms.stripContOn_of_boxes` (the GENERIC lift,
                    `f`-polymorphic): instantiate `f := fun p => leviSeries … p.1 p.2 0`; the box family
                    for the Levi source glues to the strip continuity.  (`DataLeviDischarge` explicitly
                    notes `LeviSeriesLocalData` supplies only measurability + envelope, never continuity,
                    so the generic box lift is the correct route.)
                 ── trap: boundary (same positive-time strip; the generic lift's box floor handles it).

  ── SUMMARY.  6 wall-A block-B members: 1 VERBATIM (`hSecCont`), 3 BRIDGED (`hFdomW`, `hmeas2Lo`,
     `hBcont`), 2 GENUINE CARRIES (`hInter`, `hAdom2cap`).  The whole joint-continuity/measurability
     triple (`hSecCont`, `hBcont`, `hmeas2Lo`) collapses onto TWO box families + group-(A) scaffolding;
     `hFdomW` onto the banked Levi envelope; only the interchange bundle and the clean second-derivative
     Gaussian domination genuinely carry.  `wallA_phase1` packages exactly this.  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MomentWallCoverage
import QIQTH.DaLimEasyTranche
import QIQTH.JointContinuityAtoms
import QIQTH.SliceMeasurability

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.LeviSeries QIQTH.ExpMap QIQTH.HeatKernelA1
open QIQTH.DuhamelCoreThreaded QIQTH.W2Finish
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.DaLimEasyTranche QIQTH.JointContinuityAtoms QIQTH.SliceMeasurability
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.WallAInstantiation

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### `wallA_hFdomW_bridge` — the `hFdomW` SHAPE BRIDGE (`y := 0`, width `wF := 2`).
    ############################################################################### -/

/-- **★ `wallA_hFdomW_bridge`.**  THE `hFdomW` shape bridge (J4-437 pattern).  From the banked width-2
    Levi envelope `DaLimEasyTranche.hFdom_concrete` (`∃ C_L ≥ 0, ∀ s z y, 0<s→s≤T→ |leviSeries E s z y|
    ≤ C_L·gaussDdim (2·s)(z−y)`), specialise `y := 0` and rewrite `z − 0 = z` to land EXACTLY the
    `hFdomW` binder shape with `wF := 2`, `CF := C_L`.  Generic in the residual `E`; the honest input is
    the `LeviSeriesLocalData E C T` package.  ⚠ NOT `a₁ = R/6`. -/
theorem wallA_hFdomW_bridge (E : ℝ → Point n → Point n → ℝ) (C T : ℝ)
    (data : LeviSeriesLocalData E C T) :
    ∃ CF : ℝ, 0 ≤ CF ∧ ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
      |leviSeries E s z 0| ≤ CF * gaussDdim (2 * s) z := by
  obtain ⟨C_L, hC_L, hdom⟩ := QIQTH.DaLimEasyTranche.hFdom_concrete E C T data
  refine ⟨C_L, hC_L, fun s hs hsT z => ?_⟩
  have h := hdom s hs hsT z 0
  rwa [sub_zero] at h

/-! ###############################################################################
    ### `wallA_hSecCont_verbatim` — the `hSecCont` VERBATIM wire.
    ############################################################################### -/

/-- **★ `wallA_hSecCont_verbatim`.**  THE `hSecCont` wall-A member, supplied VERBATIM by
    `JointContinuityAtoms.hSecCont_of_boxes`: from the positive-time-compact box joint-continuity family
    `Icc (τ₀/2) T ×ˢ closedBall 0 R` (the banked `ParametrixPartsContinuity` box shape), the generic
    local-to-global lift yields joint continuity on the full positive-time strip `Ioc 0 T ×ˢ univ` — the
    EXACT shape the census consumes.  ⚠ NOT `a₁ = R/6`. -/
theorem wallA_hSecCont_verbatim (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (hboxes : ∀ i : Fin n, ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n => witnessSecondXDeriv g gi hChr hK S a b i p.1 p.2)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ i : Fin n, ContinuousOn
      (fun p : ℝ × Point n => witnessSecondXDeriv g gi hChr hK S a b i p.1 p.2)
      (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set (Point n))) :=
  QIQTH.JointContinuityAtoms.hSecCont_of_boxes g gi hChr hK S a b T hboxes

/-! ###############################################################################
    ### `wallA_hBcont_bridge` — the `hBcont` SHAPE BRIDGE via the generic strip lift.
    ############################################################################### -/

/-- **★ `wallA_hBcont_bridge`.**  THE `hBcont` wall-A member, bridged via the GENERIC (`f`-polymorphic)
    local-to-global lift `JointContinuityAtoms.stripContOn_of_boxes` applied to the Levi source slice
    `f := fun p => leviSeries (heatOp g gi H_G) p.1 p.2 0`: the positive-time-compact box family glues to
    joint continuity on the strip `Ioc 0 T ×ˢ univ`.  (`DataLeviDischarge` notes `LeviSeriesLocalData`
    supplies measurability + envelope but NEVER continuity, so this generic box lift is the route.)  ⚠
    NOT `a₁ = R/6`. -/
theorem wallA_hBcont_bridge (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (hboxes : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set (Point n))) :=
  QIQTH.JointContinuityAtoms.stripContOn_of_boxes _ T hboxes

/-! ###############################################################################
    ### ★★★★ `wallA_phase1` — the SIX block-B wall-A members SUPPLIED-OR-REDUCED at the witness.
    ############################################################################### -/

/-- **★★★★ `wallA_phase1`.**  THE WALL-A BLOCK-B PACKAGE.  It consumes the banked-supplier inputs for the
    four non-carried members (the `LeviSeriesLocalData` envelope package behind `hFdomW`; the two
    positive-time-compact box families behind `hSecCont`/`hBcont`; the group-(A) scaffolding `hUT`/`hεU`
    behind the `hmeas2Lo` reduction) PLUS the two genuine carries (`hInter`, `hAdom2cap`), and produces
    the SIX wall-A block-B members in EXACTLY the shapes `truncatedDuhamelCore_threaded_v3` consumes:

      • `hInter`     — passed through (genuine carry, the interchange bundle);
      • `hAdom2cap`  — passed through (genuine carry, second-`x`-derivative Gaussian cap, constants
                       `wA2`/`CA2c`);
      • `hFdomW`     — DERIVED (`wallA_hFdomW_bridge`, `wF := 2`, `CF` from the Levi envelope);
      • `hmeas2Lo`   — DERIVED (`hmeas2Lo_slice`, reduced onto `hSecCont`/`hBcont`/`hUT`/`hεU`);
      • `hSecCont`   — DERIVED (`wallA_hSecCont_verbatim`, the box family);
      • `hBcont`     — DERIVED (`wallA_hBcont_bridge`, the box family).

    THAT THIS TYPECHECKS certifies the wall-A block-B census is fully accounted for at the witness: four
    members reduce to banked suppliers + group-(A) scaffolding, only two genuinely carry.  ⚠ THE HONEST
    SUMMARY: this is binder re-plumbing / shape bridging at the wall-A leg; it closes NOTHING deeper.
    Every carry is satisfiable, non-vacuous, strictly lower-level, and NONE is `a₁ = R/6`.  ⚠ NOT
    `a₁ = R/6`. -/
theorem wallA_phase1 (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (T C : ℝ)
    (hUT : ∀ u ∈ U, u ≤ T)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (wA2 : ℝ) (CA2c : ℕ → ℝ)
    -- banked-supplier inputs for the bridged / verbatim four:
    (data : LeviSeriesLocalData
        (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) C T)
    (hSecBoxes : ∀ i : Fin n, ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n => witnessSecondXDeriv g gi hChr hK S a b i p.1 p.2)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hBBoxes : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    -- the TWO genuine carries:
    (hInter : MemInterchange (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (hAdom2cap : ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA2c m * gaussDdim (wA2 * τ) (0 - z)) :
    -- the six wall-A block-B members, in the consumed shapes:
    (MemInterchange (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    ∧ (∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA2c m * gaussDdim (wA2 * τ) (0 - z))
    ∧ (∃ CF : ℝ, 0 ≤ CF ∧ ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ CF * gaussDdim (2 * s) z)
    ∧ (∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    ∧ (∀ i : Fin n, ContinuousOn
        (fun p : ℝ × Point n => witnessSecondXDeriv g gi hChr hK S a b i p.1 p.2)
        (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set (Point n))))
    ∧ (ContinuousOn
        (fun p : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
        (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set (Point n)))) := by
  -- the verbatim / bridged joint-continuity atoms.
  have hSecCont := wallA_hSecCont_verbatim g gi hChr hK S a b T hSecBoxes
  have hBcont := wallA_hBcont_bridge g gi hChr hK S a b T hBBoxes
  refine ⟨hInter, hAdom2cap, ?_, ?_, hSecCont, hBcont⟩
  · -- `hFdomW` via the Levi-envelope shape bridge.
    exact wallA_hFdomW_bridge _ C T data
  · -- `hmeas2Lo` reduced onto the joint-continuity atoms + group-(A) scaffolding.
    exact QIQTH.SliceMeasurability.hmeas2Lo_slice g gi hChr hK S a b T U hUT hεU hSecCont hBcont

/-! ###############################################################################
    ### `wallA_ledger` — the six-member ledger, machine-checked (alias of `wallA_phase1`).
    ############################################################################### -/

/-- **★★★★★ `wallA_ledger`.**  THE WALL-A LEDGER made machine-checked: `wallA_phase1` under its audit
    name.  Its statement consuming banked-supplier inputs + two genuine carries and producing all six
    block-B wall-A members in the consumed shapes certifies the wall-A leg of the census is fully
    accounted for.  ⚠ NOT `a₁ = R/6`. -/
def wallA_ledger := @wallA_phase1

end QIQTH.WallAInstantiation

/-! ## THE WALL-A LEDGER — the honest six-member accounting, and the all-six-Sol-#20-items note.

  `wallA_phase1` / `wallA_ledger` reproduces the SIX block-B wall-A census members that
  `truncatedDuhamelCore_threaded_v3` consumes, at the concrete ρ-scaled chart witness, in EXACTLY the
  shapes the core consumes.  The accounting:

    member       verdict          supplier / route
    ──────────   ──────────────   ──────────────────────────────────────────────────────────────────────
    hInter       GENUINE CARRY    the atomic interchange bundle (no banked supplier; it IS the input the
                                  wall-A leg reduces to).                        trap: integrability-abs.
    hAdom2cap    GENUINE CARRY    clean second-`x`-derivative Gaussian cap; no banked bound of this shape
                                  (CensusDominations D3; the banked one is the crude `τ⁻¹` envelope).
                                                                                trap: measurability/dom.
    hFdomW       BRIDGED          `DaLimEasyTranche.hFdom_concrete` (`y:=0`, `wF:=2`, `sub_zero`).
                                                                                trap: integrability-abs.
    hmeas2Lo     BRIDGED          `SliceMeasurability.hmeas2Lo_slice` (folds onto hSecCont/hBcont/hUT/hεU).
                                                                                trap: measurability.
    hSecCont     VERBATIM         `JointContinuityAtoms.hSecCont_of_boxes` (box family → strip).
                                                                                trap: boundary.
    hBcont       BRIDGED          `JointContinuityAtoms.stripContOn_of_boxes` (generic lift, Levi slice).
                                                                                trap: boundary.

  So the wall-A block-B census closes to: 1 VERBATIM + 3 BRIDGED + 2 GENUINE CARRIES.  The whole
  joint-continuity/measurability triple (hSecCont, hBcont, hmeas2Lo) collapses onto TWO positive-time
  box families + group-(A) scaffolding; hFdomW onto the banked Levi envelope; only the interchange
  bundle and the clean second-derivative Gaussian domination genuinely carry.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  ALL SIX SOL-#20 ATTACK ITEMS ADDRESSED.  With wall-A landed, the six items of Sol #20's attack on
  the `a₁ = R/6` conditional surface are all discharged / reduced to enumerated carries:
      (i)   diff-under-∫              ✓ (the F2 / c-moving differentiation-under-∫ piles)
      (ii)  `hGint`                   ✓ (the interval-integrability of the inner pairing)
      (iii) the √ε sliver             ✓ (`D0`/`D1`/`hbnd`, MemAdjHiSliver)
      (iv)  the sups / uniformities   ✓ (`hmod`/`hsup` continuity/convergence)
      (v)   WALL-A interchange census ✓ (THIS BRICK — `wallA_phase1`)
      (vi)  `herr`/`hmin`             ✓-as-corrected
  This completes the Sol-#20 pass over the wall-A / interchange / sliver / uniformity surface.

  ⚠  THIS IS **NOT** `a₁ = R/6`, AND MAKES NO CLAIM OF UNCONDITIONALITY.  `a₁ = R/6` remains CONDITIONAL
  on: (i) the enumerated carries themselves (`hInter`, `hAdom2cap`, and the banked-supplier inputs are
  INPUTS here, not theorems), and (ii) the DEEP convergence-trio + geometric-wiring content that lives
  INSIDE those carries (true-kernel existence / Levi convergence / Seeley-DeWitt geometric
  identification), which is NEVER claimed closed.  Reaching this floor closes NOTHING deeper.
-/

section AxiomChecks
open QIQTH.WallAInstantiation
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms wallA_hFdomW_bridge
#print axioms wallA_hSecCont_verbatim
#print axioms wallA_hBcont_bridge
#print axioms wallA_phase1
#print axioms wallA_ledger
end AxiomChecks
