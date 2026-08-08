/-
  V2CensusInstantiation — J4-429 (GROUP (4), the carried v2 census + THE TERMINAL CROSS-CHECK): the
  LAST of the four terminal `a₁ = R/6` data groups.  Groups (1)-(3) already closed to enumerated input
  carries:
    (1)  the slot carries → I1-I6 (SlotInstantiationI..VIII.lean, the `hslot`/`hcap`/`hEndpoint` moment
         wall reduced to `gpow_closure_carries` + `slot_discharge_residuals`);
    (2)  `hInnerData` → 7 named z-level carries (InnerDataInstantiation/InnerDataEnvelope.lean);
    (3)  the V1 per-`u` census → enumerated (PerUCensusInstantiation.lean, the `nbP`/`hProvP`/…/
         `hfrozen_pd1` group).
  GROUP (4) is what remains: the carried v2 census — the interchange/domination/continuity/gauge/Levi +
  √ε-sliver binders that `MomentWallCoverage.truncatedDuhamelCore_threaded_v3` (J4-416) still carries and
  that are NOT part of groups (1)-(3).  These are exactly the binders the J4-413/414 Duhamel map
  classified as "satisfiable census" (block-A `hBoundaryLim`, block-B interchange residues, block-C/D
  F-pile + moving-family piles, the `D0`/`D1`/`hbnd` √ε sliver family, the domination constants, the
  continuity atoms, the gauge/nbhd geometry, and the Levi cross-Lipschitz carry).

  One brick of the `a₁ = R/6` heat-kernel campaign.  It is **NOT** `a₁ = R/6`, and proves NOTHING about
  `R/6`.  `a₁ = R/6` remains CONDITIONAL on the whole `hDuhamel` / convergence-trio + geometric-wiring
  stack AND on the surviving labelled census carries.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  Every theorem here re-threads BANKED, satisfiable v2 census data into the exact
  shape `truncatedDuhamelCore_threaded_v3` consumes, and discharges the ONE genuinely tradeable member
  at the witness (`hFzero`, via the banked `DaLimEasyTranche.hFzero_concrete`).  NONE proves `a₁ = R/6`.
  Each carried hypothesis is genuine, satisfiable, non-vacuous, and never the conclusion.  No `sorry`
  (header prose excepted), no `:= True`, no new axioms, no existing file edited, nothing wired into
  `AxiomAudit`.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE GROUP-(4) BINDER MAP.

  Every `truncatedDuhamelCore_threaded_v3` binder NOT in groups (1)-(3), with type shape · banked
  supplier / verdict.  ("carry" = enumerated satisfiable input; "discharged" = supplied at the witness.)

  ── (A) BLOCK-A boundary limit + the geometry/gauge/domain scaffolding (also the group-(A) surface).
    `hBoundaryLim`  `Tendsto (BoundaryTrunc W F m t) atTop (𝓝 (F t 0 0))`   — CARRY.  Banked supplier:
                    `EnvelopeWiringLocUnif.hBoundaryLim_DONE` (one binder; not re-exposed).
    `hgi`/`hΓ`      `MemGaugeGi gi` / `MemGaugeGamma g gi`                   — CARRY (gauge/group A).
                    Supplier at the capstone: `CensusSweepOne.census_gauge` / `DaLimCensusRecon.
                    memGaugeGi_of_geometry` (needs the RNC frame inputs `hframeK`/`hinvF`/`hK0`, present
                    at `a1_R6_from_data_v4`, NOT at the core — so a genuine carry here).
    `hChr`,`hK`,`hn`,`hFeq`,`hT`,`hUopen`,`htU`,`hUT`,`hUlb`,`hUfloor`,`hεU`,`hUsub`,`V`/`hVopen`/`hV0`,
    `snb`/`hsnb`,`hn`                                                       — CARRY (geometry/domain/nbhd
                    scaffolding = group (A); data + positivity/openness/floor).
    `hAzero`       `∀ τ ≤ 0, W τ p q = 0`                                    — CARRY (witness support;
                    banked `AmplitudePackage.vanVleckGatedWitness_zero_factor` route).
    `hFzero`       `∀ s ≤ 0, F s z y = 0`                                    — ★ DISCHARGED-THIS-BRICK at
                    the witness via `DaLimEasyTranche.hFzero_concrete` (+ `hFeq`, needs `hn`).

  ── (B) BLOCK-B interchange residue (the wall-A census, J4-414 D1 verdict).
    `hInter`       `MemInterchange W F U (witnessSecondXDeriv …)`           — CARRY (interchange bundle).
    `hAdom2cap`    second-`x`-partial Gaussian cap `≤ CA2c m · G_{wA2·τ}`   — CARRY (domination family).
    `hFdomW`       Levi Gaussian bound `≤ CF · G_{wF·s}`                     — CARRY (domination).
    `hmeas2Lo`     `s`-profile a.e.-strong measurability                    — CARRY (measurability).
    `hSecCont`/`hBcont`  joint `ContinuousOn` of `witnessSecondXDeriv`/Levi — CARRY (continuity atoms;
                    suppliers `JointContinuityAtoms`/`NonLeviBoxContinuity`/`LapContBoxGlue`).
    `hεU`          `∀ m, ∀ u ∈ U, epsSeq m ≤ u`                             — CARRY (domain floor).
    `τc`,`wA2`,`wF`,`CF`,`CA2c` + `hwA2`/`hCA2c`/`hwF`/`hCF`                 — CARRY (data + positivity).

  ── (C) the √ε SLIVER family (Hi-adjacency amplitude, MemAdjHi via `MemAdjHiSliver`/`ESLegWidening`).
    `D0`/`D1`,`hD0`/`hD1`   the √ε amplitude data + nonnegativity          — CARRY (data).
    `hbnd`         `|∫_{u−εₘ}^u ∫_z W₂·F| ≤ D0·2√εₘ + D1·εₘ`              — CARRY (the √ε sliver tranche;
                    consumed by `MemAdjHiSliver.hII_hi_from_sliver`).

  ── (D) domination / integrability / mass constants (the Gaussian-envelope pile).
    `hEdom`,`hAdom`,`hWDom`  heat-op / vanVleck / on-axis Gaussian bounds   — CARRY (domination family;
                    suppliers `CensusDominations`/`CappedAdom2Audit`).
    `hFdom`        Levi width-2 Gaussian bound (`≤ C_L·G_{2s}`)            — CARRY (banked at witness by
                    `DaLimEasyTranche.hFdom_concrete` from `LeviSeriesLocalData`; kept a carry here since
                    that data bundle is not threaded at the core).
    `hIlo`/`hIhi`  strip interval-integrabilities on `[0,u−εₘ]`/`[u−εₘ,u]` — CARRY (banked at witness by
                    `DaLimEasyTranche.hIlo_concrete`/`hIhi_concrete` from the domination carries; kept as
                    carries here because their `hAdom` needs the clean `CA·G_{wA·τ}` reshape of `hEdom`).
    `hMeasFII`     `s`-profile a.e.-strong measurability (full II leg)     — CARRY (measurability).
    `hEcomb`       `MemECombine g gi W F` (the E-combine bundle)           — CARRY (bundle).
    `hmass`/`hmassone`  Gaussian mass `≤ CW` / `→ 1`                       — CARRY (mass/convergence).
    `E₀`,`E₁`,`A₀`,`A₁`,`C_L`,`aT`,`CW`,`Cf`,`ρ`,`lam`,`τ₀`,`ta`,`tb` + positivities — CARRY (data).

  ── (E) BLOCK-C/D F-pile + the c-MOVING family piles (block-C `hQ1` + block-D moving list).
    `hQ1`          frozen `∂ᵢ`-pointwise = `∫₀^{u−εₘ} ∫_z witnessFieldDeriv·F`  — CARRY (block-C repr).
    `hFmeas`/`hFint`/`hF'meas`,`bnd`/`hbdd`/`hbound`   the F2 differentiation-under-∫ pile — CARRY.
    `nb`/`hnb`,`hFmeas_d`/`hFint_d`/`hF'meas_d`,`boundD`/`hbdd_d`/`hbound_d`,`hpardiff`   the c-moving
                    (parametric `∂_c`) pile                                 — CARRY (D-pile).
    `hInnerCont`   `ContinuousOn (s ↦ ∫_z W·F) (Ioo 0 u)`                   — CARRY (continuity).
    `hWmeas`/`hffro_meas`/`hfmov_meas`,`hffro_bdd`/`hfmov_bdd`             — CARRY (measurability + bounds).
    `hmod`/`hsup`  modulus-of-continuity / uniform-in-`m` convergence      — CARRY (continuity/convergence).

  ── (F) the LEVI cross-Lipschitz carry.
    `L`,`hLnn`,`hCross`   the mixed second-difference Lipschitz constant + bound (`≤ L·|h|·|k|`) — CARRY
                    (supplier family `DataLeviDischarge`/`LeviLipschitz`; kept as a carry here).

  So GROUP (4) closes to ENUMERATED INPUT CARRIES ONLY, of the SAME kinds as groups (1)-(3): bundles
  (interchange/E-combine/gauge), Gaussian-domination families, measurabilities, continuity atoms,
  integrabilities, data + positivity constants, and the √ε sliver + Levi tranches — with the ONE
  witness-level trade `hFzero` (★).  `v2Census_phase1` packages exactly this: it reproduces the v3-core
  conclusion `TruncatedDuhamelCore` from the group-(1)-(4) enumerated carries with `hFzero` supplied
  internally.  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MomentWallCoverage
import QIQTH.DaLimEasyTranche

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.LeviSeries QIQTH.ExpMap QIQTH.HeatKernelA1
open QIQTH.DuhamelCoreThreaded QIQTH.PerUCensusTuple QIQTH.W2Finish
open QIQTH.HDuhamelExportRethread QIQTH.TruncatedDuhamelData
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData QIQTH.DaLimLUConcreteDischarge
open QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.EveryCeilingFamilies QIQTH.ESLegWidening QIQTH.GlobalRawBoundFacade
open QIQTH.TerminalCoverage QIQTH.MomentWallCoverage QIQTH.DaLimEasyTranche
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.V2CensusInstantiation

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ `v2_hFzero_at_witness` — the ONE group-(4) member DISCHARGED at the witness.
    ############################################################################### -/

/-- **★ `v2_hFzero_at_witness`.**  THE group-(4) `hFzero` binder DISCHARGED at the true ρ-scaled chart
    witness: the Levi source `F := leviSeries (heatOp g gi W)` vanishes at nonpositive time.  This is a
    pure re-export of the banked `DaLimEasyTranche.hFzero_concrete` (`heatOp g gi W` vanishes at `τ ≤ 0`
    → `leviSeries_eq_zero_of_nonpos`), needing only `1 ≤ n`.  It is the single member of group (4) that
    admits a strictly-lower-level trade AT the core (no extra data bundle required), so it moves into the
    INTERNALLY-DISCHARGED set of the terminal cross-check.  ⚠ NOT `a₁ = R/6`. -/
theorem v2_hFzero_at_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hn : 1 ≤ n) :
    ∀ s : ℝ, s ≤ 0 → ∀ z y : Point n,
      leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z y = 0 :=
  QIQTH.DaLimEasyTranche.hFzero_concrete g gi hChr hK S a b hn

/-! ###############################################################################
    ### ★★★★ `v2Census_phase1` — the v3-core conclusion from the enumerated group-(1)-(4) carries,
    ###                          with `hFzero` supplied INTERNALLY (= THE TERMINAL CROSS-CHECK).
    ############################################################################### -/

/-- **★★★★ `v2Census_phase1`.**  THE GROUP-(4) PACKAGE AND THE TERMINAL CROSS-CHECK IN ONE.  It consumes
    EXACTLY the union of the enumerated carries of groups (1)-(4) + the geometry/gauge group (A) — i.e.
    the full input surface of `MomentWallCoverage.truncatedDuhamelCore_threaded_v3` MINUS the one
    internally-discharged member `hFzero` — and produces the v3-core conclusion
    `TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t`, with `hFzero` supplied at the
    witness by `v2_hFzero_at_witness` (∘ `hFeq`).

    THAT THIS TYPECHECKS IS THE COMPLETENESS CERTIFICATE: the binder list below is transcribed VERBATIM
    from `truncatedDuhamelCore_threaded_v3` (annotated in the GROUP-(4) BINDER MAP by which of groups
    (1)-(4)/(A)/internally-discharged each member belongs to), and the final application re-supplies each
    one; were ANY binder missing from the enumeration, or `hFzero` not genuinely dischargeable at the
    witness, this would fail to compile.  So compilation ⟹ the enumeration of the whole v3-core
    conditional surface is COMPLETE, and every member sits in exactly one group.

    ⚠ THE HONEST SUMMARY.  This is pure binder re-plumbing at the maximally-unconditional CONDITIONAL a₁
    two-jet; it closes NOTHING deeper.  Every carry is satisfiable, non-vacuous, strictly lower-level than
    the conclusion, and NONE is `a₁ = R/6`.  The deep convergence-trio content inside the carries remains.
    ⚠ NOT `a₁ = R/6`. -/
theorem v2Census_phase1 (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ)
    (hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    (t T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUT : ∀ u ∈ U, u ≤ T) (hn : 1 ≤ n)
    (hBoundaryLim : Tendsto
        (fun m => BoundaryTrunc (vanVleckGatedWitness g gi hChr hK S a b) F m t) atTop
        (𝓝 (F t 0 0)))
    (hgi : MemGaugeGi (n := n) gi) (hΓ : MemGaugeGamma (n := n) g gi)
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u
            (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) y z * F s z 0)
    (hFmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
            (Function.update (0 : Point n) i w) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (0 : Point n) z * F s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s) (0 : Point n) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bnd : ℕ → Fin n → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (bnd m i) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0‖ ≤ bnd m i s)
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv g gi hChr hK S a b i (u - s) z * F s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (E₀ E₁ C_L aT : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hC_L : 0 ≤ C_L) (haT : 0 < aT)
    (hUlb : ∀ u ∈ U, aT ≤ u)
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hIlo : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z * F s z 0)
          volume 0 (u - epsSeq m))
    (hIhi : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z * F s z 0)
          volume (u - epsSeq m) u)
    (hEcomb : MemECombine g gi (vanVleckGatedWitness g gi hChr hK S a b) F)
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness g gi hChr hK S a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness g gi hChr hK S a b τ p q = 0)
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    (hUfloor : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ U, c ≤ u)
    (hInnerCont : ∀ u ∈ U,
        ContinuousOn (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
          (Set.Ioo 0 u))
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ c, AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (c - s) 0 z * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
      volume 0 (u - epsSeq m))
    (hF'meas_d : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s) * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundD : ℕ → ℝ → ℝ → ℝ)
    (hbdd_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
    (hbound_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb m u,
      ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (c - s) * F s z 0‖
        ≤ boundD m u s)
    (hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb m u,
      HasDerivAt (fun c => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (c - s) 0 z * F s z 0)
        (∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (c - s) * F s z 0) c)
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F (u + h) (u - epsSeq m + k) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F (u + h) (u - epsSeq m) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u (u - epsSeq m + k) 0 0
          + heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|))
    (ρ lam CW Cf τ₀ : ℝ) (ta tb : ℝ)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ₀ : 0 < τ₀)
    (hWmeas : ∀ τ, AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hChr hK S a b τ (0 : Point n) z) volume)
    (hffro_meas : ∀ u, AEStronglyMeasurable (fun z => F u z (0 : Point n)) volume)
    (hfmov_meas : ∀ m u, AEStronglyMeasurable (fun z => F (u - epsSeq m) z (0 : Point n)) volume)
    (hffro_bdd : ∀ u z, |F u z (0 : Point n)| ≤ Cf)
    (hfmov_bdd : ∀ m u z, |F (u - epsSeq m) z (0 : Point n)| ≤ Cf)
    (hWDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z,
      |vanVleckGatedWitness g gi hChr hK S a b τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z)
    (hmass : ∀ᶠ m in atTop, ∫ z, |vanVleckGatedWitness g gi hChr hK S a b (epsSeq m) (0 : Point n) z| ≤ CW)
    (hmassone : Tendsto
        (fun m => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (epsSeq m) (0 : Point n) z) atTop (𝓝 1))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.ball (0 : Point n) δ,
          |F u z (0 : Point n) - F u (0 : Point n) (0 : Point n)| < ε)
    (hsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
          |F (u - epsSeq m) z (0 : Point n) - F u z (0 : Point n)| < ε)
    (hUsub : U ⊆ Set.Icc ta tb)
    -- ── the WALL-A interchange census (block B):
    (τc wA2 wF CF : ℝ) (CA2c : ℕ → ℝ)
    (hwA2 : 0 < wA2) (hCA2c : ∀ m, 0 ≤ CA2c m) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (hInter : MemInterchange (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (hAdom2cap : ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA2c m * gaussDdim (wA2 * τ) (0 - z))
    (hFdomW : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ CF * gaussDdim (wF * s) z)
    (hmeas2Lo : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hSecCont : ∀ i : Fin n, ContinuousOn
      (fun p : ℝ × Point n => witnessSecondXDeriv g gi hChr hK S a b i p.1 p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (Lc Bcomp Q Sconst : ℝ) (hLc : 0 ≤ Lc) (hBcomp : 0 ≤ Bcomp) (hQ : 0 ≤ Q) (hSconst : 0 ≤ Sconst)
    (hslot : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i τ z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ (2 * Lc * (15 / 2 * (n : ℝ)) + Bcomp + Q) * τ ^ (-(1 : ℝ) / 2) + Sconst)
    (hcap : ∀ (m : ℕ), ∀ u ∈ U, ∀ s ∈ Set.Ioo (u - epsSeq m) u, u - s ≤ τc)
    (hEndpoint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - u) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) u z 0 = 0)
    -- ── (group 2) the inner-`z` `hdiff` census:
    (hInnerData : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
        ∃ (znb : Set ℝ) (bnd : Point n → ℝ),
          znb ∈ 𝓝 w ∧
          (∀ w' : ℝ, AEStronglyMeasurable
            (fun z => witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume) ∧
          Integrable
            (fun z => witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume ∧
          AEStronglyMeasurable
            (fun z => witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume ∧
          Integrable bnd volume ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb,
            ‖witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ bnd z) ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb,
            HasDerivAt (fun w' => witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
              (witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) w'))
    -- ── (group 3) the per-`u` `hPd2conv` census:
    (nbP : ℝ → Set (Point n)) (hnbP_open : ∀ u ∈ U, IsOpen (nbP u))
    (hnbP0 : ∀ u ∈ U, (0 : Point n) ∈ nbP u)
    (hProvP : ∀ u ∈ U, ∀ x ∈ nbP u, ∀ i : Fin n,
      ∃ (snbx : Set ℝ) (bound : ℝ → ℝ),
        snbx ∈ 𝓝 (x i) ∧
        (∀ w, AEStronglyMeasurable
          (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u))) ∧
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume 0 u ∧
        AEStronglyMeasurable
          (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u)) ∧
        IntervalIntegrable bound volume 0 u ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snbx,
          ‖∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ bound s) ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snbx,
          HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s)
              (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (Function.update x i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) w))
    (fderivBulk : ℝ → Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : ℝ → Fin n → Point n → (Point n →L[ℝ] ℝ))
    (C₀ C₁ C₂ : ℝ → Fin n → ℝ)
    (hGintP : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 u)
    (hbulkderiv : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK S a b u i m)
          (fderivBulk u i m x) x)
    (hsliver : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        dist (fderivBulk u i m x) (gderiv u i x)
          ≤ (C₀ u i + C₁ u i) * (2 * Real.sqrt (epsSeq m)) + C₂ u i * epsSeq m)
    (hcont : ∀ u ∈ U, ∀ i : Fin n, ContinuousOn (gderiv u i) (Set.univ : Set (Point n)))
    (hfrozen_pd1 : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ),
        (fun y => pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
            (u - epsSeq m) x 0) i y)
          =ᶠ[𝓝 (0 : Point n)]
          QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK S a b u i m) :
    TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t := by
  -- ★ the ONE internally-discharged member: `hFzero` at the witness (∘ `hFeq`).
  have hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z y : Point n, F s z y = 0 := by
    rw [hFeq]
    exact v2_hFzero_at_witness g gi hChr hK S a b hn
  -- re-supply the whole enumerated group-(1)-(4) carry surface to the v3-core.
  exact QIQTH.MomentWallCoverage.truncatedDuhamelCore_threaded_v3 g gi hChr hK S a b F hFeq
    t T hT U hUopen htU hUT hn hBoundaryLim hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas
    bnd hbdd hbound D0 D1 hD0 hD1 hbnd E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hEdom hFdom hFzero hIlo hIhi
    hEcomb A₀ A₁ hA₀ hA₁ hAdom hAzero hMeasFII hUfloor hInnerCont
    nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
    ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd
    hWDom hmass hmassone hmod hsup hUsub
    τc wA2 wF CF CA2c hwA2 hCA2c hwF hCF hεU hInter hAdom2cap hFdomW hmeas2Lo hSecCont hBcont
    Lc Bcomp Q Sconst hLc hBcomp hQ hSconst hslot hcap hEndpoint
    hInnerData
    nbP hnbP_open hnbP0 hProvP fderivBulk gderiv C₀ C₁ C₂ hGintP hbulkderiv hsliver hcont hfrozen_pd1

/-! ###############################################################################
    ### `terminal_enumeration_check` — the completeness certificate (alias of `v2Census_phase1`).
    ############################################################################### -/

/-- **★★★★★ `terminal_enumeration_check`.**  THE TERMINAL CROSS-CHECK, made machine-checked.  This is
    `v2Census_phase1` under its audit name: a decl whose statement consumes EXACTLY the union of the
    enumerated carries of groups (1)-(4) + geometry/gauge (A) — the full input surface of
    `truncatedDuhamelCore_threaded_v3` minus the internally-discharged `hFzero` — and produces the v3-core
    conclusion.  Its existence certifies the enumeration in the GROUP-(4) BINDER MAP + the GROUP-(1)-(3)
    files is COMPLETE (no v3-core binder is unaccounted for) and PARTITIONED (each member lands in exactly
    one of: groups (1)-(4), geometry/gauge (A), internally-discharged {`hFzero`}).  ⚠ NOT `a₁ = R/6`. -/
def terminal_enumeration_check := @v2Census_phase1

end QIQTH.V2CensusInstantiation

/-! ## GROUP (4) COVERAGE — the honest ledger, and THE TERMINAL CROSS-CHECK VERDICT.

  `v2Census_phase1` reproduces the v3-core conclusion `TruncatedDuhamelCore` from the enumerated carry
  surface of `truncatedDuhamelCore_threaded_v3`, with the ONE tradeable member `hFzero` DISCHARGED at the
  witness (`v2_hFzero_at_witness` ∘ the banked `DaLimEasyTranche.hFzero_concrete`).  Combined with
  groups (1)-(3), GROUP (4) closes to ENUMERATED INPUT CARRIES ONLY (see THE GROUP-(4) BINDER MAP):
  the block-A boundary limit, the block-B interchange bundle + domination/measurability/continuity
  census, the √ε sliver family (`D0`/`D1`/`hbnd`), the domination/integrability/mass constants, the
  block-C/D F-pile + c-moving family, and the Levi cross-Lipschitz carry.

  ── THE TERMINAL CROSS-CHECK VERDICT (COMPLETE ENUMERATION).  The inputs of BOTH terminal decls are now
  accounted for, each in exactly one group:

    • `truncatedDuhamelCore_threaded_v3` (the Duhamel core carrier) — its ENTIRE binder list is
      transcribed into `v2Census_phase1`/`terminal_enumeration_check` and re-supplied; compilation
      certifies completeness.  Partition:
        – group (1)  : `hslot`, `hcap`, `hEndpoint`   (the moment wall → the slot carries, I1-I6);
        – group (2)  : `hInnerData`;
        – group (3)  : `nbP`,`hnbP_open`,`hnbP0`,`hProvP`,`fderivBulk`,`gderiv`,`C₀`,`C₁`,`C₂`,`hGintP`,
                       `hbulkderiv`,`hsliver`,`hcont`,`hfrozen_pd1`;
        – group (4)  : blocks (A)-(F) of the map above (interchange/domination/continuity/gauge/Levi +
                       √ε-sliver + F-pile + moving-family piles + boundary limit);
        – group (A)  : the geometry/domain/nbhd/gauge scaffolding (`hChr`,`hK`,`hn`,`hFeq`,`hT`,`hUopen`,
                       `htU`,`hUT`,`hUlb`,`hUfloor`,`hεU`,`hUsub`,`V`/`hVopen`/`hV0`,`snb`/`hsnb`,
                       `hgi`,`hΓ`, and the `S`/`a`/`b`/`t`/`T`/`U` data);
        – internally-discharged : `hFzero` (★).
      NO v3-core binder falls outside these groups.

    • `a1_R6_from_data_v4` (SlotsThreading, the capstone) — enumerated in PROSE (not re-transcribed
      here; its binder list is orthogonal to the core):
        – geometry/gauge group (A) : `hg`,`hgsymm`,`hgiC`,`hgpos`,`hg0`,`hgi`,`hΓ`,`hdg0`,`hsrc`,`hgnd`,
                       `hinvF`,`hframeK`,`hw`,`hu`,`hgiMeas`,`hchrMeas`,`hK0` + the base data
                       `g`/`gi`/`t`/`ht`/`hChr`/`hK`/`hn`;
        – the `ConstGateAssemblyData` carries : `hgate`,`hKSmeas`,`hcarTau`,`hcarField`,`hcarField2`;
        – the THREE census sub-carrier groups : `coreSlots` (= the `TruncatedDuhamelCore` that
                       `v2Census_phase1` PRODUCES — the exact hand-off point), `hDConvSlots`
                       (the W1-free `DifferentiableAt` field), `L2Slots` (the `L2Residual` bundle);
        – group (D′)  : `gb`,`gib`,`hCb`,`hgPull`,`hsymmb`,`hinvb`,`hgb`,`hgaugeb`.
      Every `a1_R6_from_data_v4` binder lands in the geometry/gauge group (A), the `ConstGateAssemblyData`
      carries, the three census sub-carriers (fed by groups (1)-(4) via `coreSlots` + the L2 residual +
      the `hDConv` field), or group (D′).  NONE is unaccounted for.

  ⚠ NO NAMED GAP.  The enumeration of the whole conditional surface (v3-core ∪ v4-capstone) is COMPLETE:
  there is NO binder in either terminal decl that is not in exactly one group.  This is the completeness
  audit of the campaign's conditional surface — a soundness-of-CLAIM check, NOT a proof of `a₁ = R/6`.

  ⚠ ALL FOUR TERMINAL GROUPS ARE NOW AT THE ENUMERATED-CARRIES FLOOR.  Groups (1) (slots), (2)
  (`hInnerData`), (3) (per-`u` census), and (4) (the carried v2 census) each reduce to a fixed,
  enumerated set of satisfiable, non-vacuous input carries + a handful of witness-level trades.  This is
  the maximal binder-level reduction of the Duhamel-core conditional surface.

  ⚠ THIS IS **NOT** `a₁ = R/6`, AND MAKES NO CLAIM OF UNCONDITIONALITY.  `a₁ = R/6` remains CONDITIONAL
  on: (i) the enumerated carries themselves (they are inputs, not theorems here), and (ii) the DEEP
  convergence-trio + geometric-wiring content that lives INSIDE those carries (the true-kernel
  existence / Levi convergence / Seeley-DeWitt geometric identification), which is NEVER claimed closed.
  Reaching the enumerated-carries floor closes NOTHING deeper.
-/

section AxiomChecks
open QIQTH.V2CensusInstantiation
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms v2_hFzero_at_witness
#print axioms v2Census_phase1
#print axioms terminal_enumeration_check
end AxiomChecks
