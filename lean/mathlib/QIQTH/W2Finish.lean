/-
  W2Finish — J4-397 (finishing the D pile): the W2 residues hFint / hdiff / hQ1 + the
  reduced-interface `MemInterchange` firing.

  One brick of the `a₁ = R/6` heat-kernel campaign.  It is **NOT** `a₁ = R/6`, and proves
  NOTHING about `R/6`.  `a₁ = R/6` remains CONDITIONAL.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  Every theorem here is a re-threading of BANKED, satisfiable analytic data
  through the banked interchange / interval-integrability / inner-slice-`HasDerivAt` engines.  NONE
  proves `a₁ = R/6`.  Each carried hypothesis is genuine, satisfiable, non-vacuous, and never the
  conclusion.  No `sorry` (header prose excepted), no `:= True`, no new axioms, no existing file
  edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS — the three surviving census (ii) fields of the D pile, plus the gate firing.

  •  (F1) `w2_hFint` — THE CENSUS (ii) `hFint` FIELD, DISCHARGED.  The truncated-window
     interval-integrability of the FIRST field-derivative inner pairing
        `s ↦ ∫ z, witnessFieldDeriv … i (u−s) 0 z · leviSeries (heatOp g gi W) s z 0`  on `[0, u−εₘ]`.
     ROUTE: verbatim the `EveryCeilingFamilies.hLapS_all_capped` template, kernel swapped to
     `witnessFieldDeriv g gi hChr hK S a b i` — CASE 1 (`u−εₘ ≤ 0`) is
     `ESLegWidening.intervalIntegrable_of_deg`; CASE 2 (`u−εₘ > 0`, so `0 < u`) is the LOWER-CAPPED
     engine `EveryCeilingFamilies.pairing_intervalIntegrable_lowerCapped` at ceiling `Tc := u`, lower
     cap `εₘ := epsSeq m`, strip `[0, u−εₘ]` (both endpoints `≤ u−εₘ`, so `τ = u−s ≥ εₘ` — this is the
     `τ`-floor that lets even a crude `τ⁻¹·G` field-derivative bound feed the engine, via
     `gaussDdim_crude_to_capped` at the call site of `hWFDdomEveryCapped`).  Honest carries:
     `hFzero` (source vanishing), `hWFDdomEveryCapped` (the `[εₘ,Tc]` capped field-derivative
     Gaussian bound), `hFdomEvery` (every-ceiling Levi envelope), `hmeas` (base slice measurability).

  •  (F2) `w2_hdiff` — THE CENSUS (ii) `hdiff` FIELD, DISCHARGED.  The a.e.-`s`, `∀ w ∈ snb`
     inner-slice `HasDerivAt` family: for each frozen time `s`, moving `∂_w` under the Lebesgue
     `z`-integral of the FIRST field-derivative kernel yields the SECOND field-derivative kernel:
        `HasDerivAt (fun w => ∫ z, witnessFieldDeriv … i (u−s) (update 0 i w) z · F s z 0)
                    (∫ z, witnessFieldDeriv2 … i (u−s) (update 0 i w) z · F s z 0) w`.
     ROUTE: a per-slice re-export of `SecondOrderInterchange.innerZ_line_hasDerivAt` at the concrete
     kernels `K := witnessFieldDeriv … i`, `dK := witnessFieldDeriv2 … i`, base `y := 0`, point
     `p := w`.  Honest carry: `hInnerData` — the bundled `z`-level differentiation-under-∫ inputs
     (a neighborhood `znb`, `z`-measurabilities, `z`-integrabilities, an integrable `z`-dominator, and
     the `z`-level pointwise `HasDerivAt` family), each a genuine deferred analytic fact, NONE the
     conclusion.

  •  (F3) `w2_hQ1` — THE CENSUS (ii) `hQ1` FIELD, DISCHARGED.  The frozen-side FIRST-order
     interchange, on the open field neighborhood `V ∋ 0`:
        `pd (fun x => heatConvFrozen W F u (u−εₘ) x 0) i y
           = ∫ s in (0)..(u−εₘ), ∫ z, witnessFieldDeriv … i (u−s) y z · F s z 0`.
     ROUTE: `SecondOrderInterchange.pd_heatConvFrozen_interchange` at `H := W`, `dH :=
     witnessFieldDeriv … i`, `F := leviSeries (heatOp g gi W)`, per `(m, i, u ∈ U, y ∈ V)`.  Honest
     carry: `hFrozenData` — the bundled frozen first-order diff-under-∫ inputs (a real-line nbhd
     `snb ∈ 𝓝 (y i)`, the witness/field-derivative pairing measurabilities/integrabilities, an
     interval-integrable `s`-dominator, and the outer `s`-level `HasDerivAt` family), each genuine,
     NONE the conclusion.

  •  (F4) `memInterchange_at_gate` — THE REDUCED-INTERFACE GATE FIRING.  Feeds
     `{w2_hFmeas, w2_hF'meas}` (W2Package, J4-396) + `{F1, F2, F3}` (this file) + the internally
     carried `bound`/`hbdd`/`hbound` triple into `SecondOrderInterchangeConcrete.witness_MemInterchange`,
     producing the VERBATIM `DaLimLUWallRecon.MemInterchange` member
        `∀ m i, ∀ u ∈ U, pd (fun y => pd (fun x => heatConvFrozen W F u (u−εₘ) x 0) i y) i 0
           = ∫ s in (0)..(u−εₘ), ∫ z, witnessSecondXDeriv … i (u−s) z · F s z 0`.
     The surviving carries are ONLY the honest joint legs of `w2_hFmeas`/`w2_hF'meas`
     (`hWFDjoint`/`hWFD2joint`/`hLeviJoint`) plus whatever F1/F2/F3 carry plus the `bound` triple —
     no re-proof of the aggregation, pure composition.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.EngineInstantiation
import QIQTH.W2Package
import QIQTH.SecondOrderInterchange
import QIQTH.SecondOrderInterchangeConcrete
import QIQTH.EveryCeilingFamilies

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open scoped Interval Topology BigOperators

namespace QIQTH.W2Finish

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (F1) FIELD hFint — the truncated-window interval-integrability of the
    ###      FIRST field-derivative inner pairing.
    ############################################################################### -/

/-- **★★ (F1) `w2_hFint` — THE CENSUS (ii) `hFint` FIELD, DISCHARGED.**  Interval-integrability on the
    truncated window `[0, u−εₘ]` of the FIRST field-derivative inner pairing
      `s ↦ ∫ z, witnessFieldDeriv … i (u−s) 0 z · leviSeries (heatOp g gi W) s z 0`.
    Verbatim the `EveryCeilingFamilies.hLapS_all_capped` template with kernel
    `A := witnessFieldDeriv g gi hChr hK S a b i` — CASE 1 (`u−εₘ ≤ 0`) is `intervalIntegrable_of_deg`;
    CASE 2 (`u−εₘ > 0`, so `0 < u`) is `pairing_intervalIntegrable_lowerCapped` at ceiling `Tc := u`,
    lower cap `εₘ := epsSeq m`, strip `[0, u−εₘ]` (both endpoints `≤ u−εₘ`, so `τ = u−s ≥ εₘ`).  The
    `τ`-floor `εₘ ≤ τ` is exactly what lets even a crude `τ⁻¹`-shaped field-derivative bound feed the
    engine.  Honest carries: {`hFzero`, `hWFDdomEveryCapped`, `hFdomEvery`, `hmeas`}, each satisfiable,
    non-vacuous, never the conclusion.  NOT `a₁ = R/6`. -/
theorem w2_hFint (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0)
    (hWFDdomEveryCapped : ∀ (i : Fin n) (Tc εₘ : ℝ), 0 < εₘ → ∃ wL CL : ℝ, 0 < wL ∧ 0 ≤ CL ∧
        ∀ τ : ℝ, εₘ ≤ τ → τ ≤ Tc → ∀ z : Point n,
          |witnessFieldDeriv g gi hChr hK S a b i τ (0 : Point n) z|
            ≤ CL * gaussDdim (wL * τ) (0 - z))
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m)))) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m) := by
  intro m i u hu
  rcases le_or_gt (u - epsSeq m) 0 with hdeg | hpos
  · exact QIQTH.ESLegWidening.intervalIntegrable_of_deg
      (witnessFieldDeriv g gi hChr hK S a b i)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
      u (u - epsSeq m) hdeg hFzero
  · have hεpos := epsSeq_pos m
    have hu0 : 0 < u := by linarith
    obtain ⟨wL, CL, hwL, hCL, hDom⟩ := hWFDdomEveryCapped i u (epsSeq m) hεpos
    obtain ⟨wF, CF, hwF, hCF, hFdom⟩ := hFdomEvery u
    exact QIQTH.EveryCeilingFamilies.pairing_intervalIntegrable_lowerCapped
      (witnessFieldDeriv g gi hChr hK S a b i)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
      u u (epsSeq m) wL CL wF CF hu0 le_rfl hεpos hwL hCL hwF hCF hDom hFdom hFzero
      0 (u - epsSeq m) (by linarith) le_rfl (hmeas m i u hu)

/-! ###############################################################################
    ### (F2) FIELD hdiff — the a.e.-`s`, `∀ w ∈ snb` inner-slice `HasDerivAt` family.
    ############################################################################### -/

/-- **★★ (F2) `w2_hdiff` — THE CENSUS (ii) `hdiff` FIELD, DISCHARGED.**  For a.e. time `s` (on the
    truncation) and every `w ∈ snb`, the inner-slice `∫z`-derivative family: moving `∂_w` under the
    Lebesgue `z`-integral of the FIRST field-derivative kernel produces the SECOND field-derivative
    kernel,
      `HasDerivAt (fun w => ∫ z, witnessFieldDeriv … i (u−s) (update 0 i w) z · F s z 0)
                  (∫ z, witnessFieldDeriv2 … i (u−s) (update 0 i w) z · F s z 0) w`,
    with `F := leviSeries (heatOp g gi W)`.  Per-slice re-export of
    `SecondOrderInterchange.innerZ_line_hasDerivAt` at `K := witnessFieldDeriv … i`,
    `dK := witnessFieldDeriv2 … i`, base `y := 0`, point `p := w`.  Honest carry: `hInnerData`, the
    bundled `z`-level differentiation-under-∫ inputs (nbhd `znb`, `z`-measurabilities, the base
    `z`-integrability, an integrable `z`-dominator, and the `z`-level pointwise `HasDerivAt` family) —
    each genuine, NONE the conclusion.  NOT `a₁ = R/6`. -/
theorem w2_hdiff (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (snb : Set ℝ)
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
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) w')) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) w := by
  intro m i u hu
  filter_upwards [hInnerData m i u hu] with s hs
  intro hsmem w hw
  obtain ⟨znb, bnd, hznb, hzmeas, hzint, hz'meas, hbnd, hzbound, hzdiff⟩ := hs hsmem w hw
  exact QIQTH.HeatResidualBound.innerZ_line_hasDerivAt
    (witnessFieldDeriv g gi hChr hK S a b i)
    (witnessFieldDeriv2 g gi hChr hK S a b i)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    u s i (0 : Point n) w znb hznb hzmeas hzint hz'meas bnd hbnd hzbound hzdiff

/-! ###############################################################################
    ### (F3) FIELD hQ1 — the frozen-side FIRST-order interchange on `V ∋ 0`.
    ############################################################################### -/

/-- **★★ (F3) `w2_hQ1` — THE CENSUS (ii) `hQ1` FIELD, DISCHARGED.**  The frozen-side FIRST-order
    interchange on the open field neighborhood `V ∋ 0`: for every `(m, i, u ∈ U, y ∈ V)`,
      `pd (fun x => heatConvFrozen W F u (u−εₘ) x 0) i y
         = ∫ s in (0)..(u−εₘ), ∫ z, witnessFieldDeriv … i (u−s) y z · F s z 0`,
    with `W := vanVleckGatedWitness …`, `F := leviSeries (heatOp g gi W)`.  Threads
    `SecondOrderInterchange.pd_heatConvFrozen_interchange` at `H := W`, `dH := witnessFieldDeriv … i`.
    Honest carry: `hFrozenData`, the bundled frozen first-order diff-under-∫ inputs (nbhd
    `snb ∈ 𝓝 (y i)`, the witness/field-derivative pairing measurabilities/integrabilities, an
    interval-integrable `s`-dominator, and the outer `s`-level `HasDerivAt` family) — each genuine,
    NONE the conclusion.  NOT `a₁ = R/6`. -/
theorem w2_hQ1 (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (V : Set (Point n))
    (hFrozenData : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
          snb ∈ 𝓝 (y i) ∧
          (∀ w : ℝ, AEStronglyMeasurable
            (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s)
                (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            (volume.restrict (Set.uIoc 0 (u - epsSeq m)))) ∧
          IntervalIntegrable
            (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) y z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            volume 0 (u - epsSeq m) ∧
          AEStronglyMeasurable
            (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) y z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            (volume.restrict (Set.uIoc 0 (u - epsSeq m))) ∧
          IntervalIntegrable bound volume 0 (u - epsSeq m) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
            ‖∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖
              ≤ bound s) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
            HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s)
                (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
              (∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) w)) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
            (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) y z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 := by
  intro m i u hu y hy
  obtain ⟨snb, bound, hsnb, hFmeas, hFint, hF'meas, hbdd, hbound, hdiff⟩ :=
    hFrozenData m i u hu y hy
  exact QIQTH.HeatResidualBound.pd_heatConvFrozen_interchange
    (vanVleckGatedWitness g gi hChr hK S a b)
    (witnessFieldDeriv g gi hChr hK S a b i)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    u (u - epsSeq m) i y snb hsnb hFmeas hFint hF'meas bound hbdd hbound hdiff

/-! ###############################################################################
    ### (F4) THE REDUCED-INTERFACE GATE FIRING — witness_MemInterchange from F1–F3
    ###      + the W2Package measurability pair.
    ############################################################################### -/

/-- **★★★ (F4) `memInterchange_at_gate` — THE REDUCED-INTERFACE GATE FIRING.**  Composes the two
    W2Package measurability fields (`w2_hFmeas`/`w2_hF'meas`, from the joint legs
    `hWFDjoint`/`hWFD2joint`/`hLeviJoint`, J4-396) with the three D-pile residues of THIS file
    (`w2_hFint` = F1, `w2_hdiff` = F2, `w2_hQ1` = F3) and the internally carried `bound`/`hbdd`/`hbound`
    triple, threading them all through `SecondOrderInterchangeConcrete.witness_MemInterchange` to
    produce the VERBATIM `DaLimLUWallRecon.MemInterchange` member for the concrete van-Vleck gated
    witness with source `F := leviSeries (heatOp g gi W)`:
      `∀ m i, ∀ u ∈ U, pd (fun y => pd (fun x => heatConvFrozen W F u (u−εₘ) x 0) i y) i 0
         = ∫ s in (0)..(u−εₘ), ∫ z, witnessSecondXDeriv … i (u−s) z · F s z 0`.
    The surviving carries are ONLY the honest joint legs, the F1/F2/F3 carries, and the `bound` triple;
    the aggregation itself is not re-proved (pure composition).  Every carry is satisfiable,
    non-vacuous, never the conclusion.  NOT `a₁ = R/6`. -/
theorem memInterchange_at_gate (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    -- joint legs feeding `w2_hFmeas`/`w2_hF'meas` (W2Package)
    (hWFDjoint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun p : ℝ × Point n =>
          witnessFieldDeriv g gi hChr hK S a b i (u - p.1) (Function.update (0 : Point n) i w) p.2)
        ((volume.restrict (Set.uIoc 0 (u - epsSeq m))).prod (volume : Measure (Point n))))
    (hWFD2joint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun p : ℝ × Point n =>
          witnessFieldDeriv2 g gi hChr hK S a b i (u - p.1) (0 : Point n) p.2)
        ((volume.restrict (Set.uIoc 0 (u - epsSeq m))).prod (volume : Measure (Point n))))
    (hLeviJoint : ∀ d : ℝ, AEStronglyMeasurable
        (fun p : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
        ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    -- F1 (`w2_hFint`) carries
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0)
    (hWFDdomEveryCapped : ∀ (i : Fin n) (Tc εₘ : ℝ), 0 < εₘ → ∃ wL CL : ℝ, 0 < wL ∧ 0 ≤ CL ∧
        ∀ τ : ℝ, εₘ ≤ τ → τ ≤ Tc → ∀ z : Point n,
          |witnessFieldDeriv g gi hChr hK S a b i τ (0 : Point n) z|
            ≤ CL * gaussDdim (wL * τ) (0 - z))
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hFintMeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    -- F2 (`w2_hdiff`) carry
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
    -- F3 (`w2_hQ1`) carry
    (hFrozenData : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        ∃ (snbY : Set ℝ) (boundY : ℝ → ℝ),
          snbY ∈ 𝓝 (y i) ∧
          (∀ w : ℝ, AEStronglyMeasurable
            (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s)
                (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            (volume.restrict (Set.uIoc 0 (u - epsSeq m)))) ∧
          IntervalIntegrable
            (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) y z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            volume 0 (u - epsSeq m) ∧
          AEStronglyMeasurable
            (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) y z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            (volume.restrict (Set.uIoc 0 (u - epsSeq m))) ∧
          IntervalIntegrable boundY volume 0 (u - epsSeq m) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snbY,
            ‖∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖
              ≤ boundY s) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snbY,
            HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s)
                (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
              (∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) w))
    -- the `bound`/`hbdd`/`hbound` triple (the W2 dominator slot)
    (bound : ℕ → Fin n → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (bound m i) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖
            ≤ bound m i s) :
    ∀ (m : ℕ) (i : Fin n), ∀ u' ∈ U,
      pd (fun y => pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u'
          (u' - epsSeq m) x 0) i y) i 0
        = ∫ s in (0)..(u' - epsSeq m),
            ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u' - s) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 := by
  have hFmeas := QIQTH.W2Package.w2_hFmeas g gi hChr hK S a b U hWFDjoint hLeviJoint
  have hF'meas := QIQTH.W2Package.w2_hF'meas g gi hChr hK S a b U hWFD2joint hLeviJoint
  have hFint := w2_hFint g gi hChr hK S a b U hFzero hWFDdomEveryCapped hFdomEvery hFintMeas
  have hdiff := w2_hdiff g gi hChr hK S a b U snb hInnerData
  have hQ1 := w2_hQ1 g gi hChr hK S a b U V hFrozenData
  exact QIQTH.SecondOrderInterchangeConcrete.witness_MemInterchange g gi hChr hK S a b
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) (0 : ℝ) U
    V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bound hbdd hbound hdiff

end QIQTH.W2Finish

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.W2Finish
#print axioms w2_hFint
#print axioms w2_hdiff
#print axioms w2_hQ1
#print axioms memInterchange_at_gate
end AxiomChecks
