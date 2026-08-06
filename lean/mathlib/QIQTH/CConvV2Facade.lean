/-
  CConvV2Facade — J4-330 (facade-v2 brick 14 of 14): ★★★ THE FACADE.  Assembles the EXACT capstone
  `hCConv` antecedent `hCConvSlot_AT_GATE_v2` from the facade-v2 census ONLY — no adjudicated-false
  field anywhere in the dependency cone.  The final brick of the 14-brick plan (SOL CONSULT #9,
  docs/qg_roadmap/JET4_TOWER_PLAN.md).  ONE brick of the `a₁ = R/6` heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It performs
  the MECHANICAL composition
      `hfam_v2`               (the L1 `∃`-`HasFDerivAt` family, from the linewise family + `hD1`)
        ∘  `hCConv_reduction`  (`hfam` + `hD1` ⟹ the spatial-`C²` slot, via `2 = 1 + 1`)
  at the CONCRETE left kernel `H := vanVleckGatedWitness g gi hChr hK S a b` and the CONCRETE Levi
  source `F := leviSeries (heatOp g gi H)`, producing the EXACT antecedent the `∞`-capstone demands:
      `ContDiffAt ℝ 2 (fun p ↦ heatConv H (leviSeries (heatOp g gi H)) t p 0) 0`.
  NO `sorry` (header prose excepted), NO new axioms, NO `:= True`, NO vacuous / unsatisfiable
  hypothesis in this file's OWN theorems.  No existing file is edited, nothing committed.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (W0) RECONNAISSANCE — the three verdicts.

  ### (W0.1) `hCConv_reduction`'s L1 SHAPE (`SpatialC2.lean`, `QIQTH.HeatResidualBound`).
    It consumes exactly two layers and returns the `C²` slot:
      (L1) `hfam : ∃ u ∈ 𝓝 0, ∀ x ∈ u, HasFDerivAt (fun p ↦ heatConv H F t p 0) (D x) x`;
      (L2) `hD1  : ContDiffAt ℝ 1 D 0`.
    So the facade's job is: build `hfam` (L1) at the concrete kernels and the explicit representative
    `D := Dmap …`, and feed the carried `hD1` (L2).

  ### (W0.2) THE OLD SKELETON'S LINEWISE→FRÉCHET BRIDGE (`CConvFacade.hCConv_discharged_from_data`).
    The old L1 chain ended at `GcoefContinuity.hCConv_L1_final`, which takes THREE inputs on an OPEN
    nbhd `u ∋ 0`:
      • `hlin`  — the per-coordinate `HasDerivAt` LINEWISE family, value `(D x)(Pi.single i 1)`;
      • `hcont` — the coefficient-continuity family `∀ x ∈ u, ∀ i, ContinuousAt (gcoef i) x`;
      • `hDrep` — the coordinate representation `D x = ∑ i, gcoef i x • proj i`,
    and returns the L1 `∃`-`HasFDerivAt` shape (the classical "continuous partials ⟹ Fréchet" route).
    In the OLD skeleton `hcont` was produced by the POISONED envelope chain
    (`hjoint_instantiated → henv/hdomS_assembled → g2_bundle_assembled`), which consumed the
    adjudicated-false `hGateData`/`hGateData'`/`hFbd`.

  ### (W0.3) ★ THE v2 BRIDGE (the key resolution).  `hcont` need NOT come from the poisoned chain:
    the coefficient function `gcoef i x = (D x)(Pi.single i 1)` (`CConvV2DerivRep.Dmap_apply_single`),
    so its continuity FOLLOWS from the continuity of `D` — which is exactly what the L2 carry
    `hD1 : ContDiffAt ℝ 1 D 0` GIVES on a neighbourhood (`ContDiffAt.eventually` at `1 ≠ ∞` ⟹
    `∀ᶠ x, ContinuousAt D x`, then `ContinuousAt.clm_apply`).  Thus the linewise→Fréchet bridge routes
    `hcont` THROUGH `hD1`, and the poisoned envelope chain is BYPASSED ENTIRELY.  This is the W0
    verdict the mission anticipated: the old bridge is reusable as-is, fed a `hD1`-derived `hcont`.

  ## WHAT THIS FILE LANDS.
    • (W1a) `hfam_v2` — the L1 `∃`-`HasFDerivAt` family from `hlin` (= the ∀x∈u∀i re-export of
      `CConvV2DerivRep.hlin_as_D`) + `hD1`, via the v2 bridge (W0.3) into `hCConv_L1_final`.
    • (W1b) `hD1_v2` — the L2 re-export of `CConvV2DerivRep.hD1_conditional`.
    • (W2)  `hCConvSlot_AT_GATE_v2` — ★★★ the EXACT capstone antecedent from the v2 census ONLY.

  ## (W3) THE v1→v2 CENSUS-COUNT.  THREE adjudicated-false fields DIE:
      `CConvEnvelopeData.hGateData`  (∀ᶠx→∀ᵐs constant-`Bs` Gaussian log-gradient — FALSE,
                                      `GaussianJetTheorem.gateData_numerator_shape_unsat`),
      `CConvEnvelopeData.hGateData'` (∀ᵐs→∀ᶠx twin — same falsification),
      `CConvSourceData.hFbd`         (uniform `|F s z| ≤ Cf` — FALSE for the Levi source at the
                                      diagonal).
    In their place: the honest `hStar`/`hFpair` legs already banked (bricks 1–13) as the WIDE envelope
    (`hStarWide_concrete`, `hFpairWide`, `envelope_integrable_v2Wide`), which discharge the diff-under-∫
    domination `hlin` needs; and the poisoned coefficient-continuity chain (`g2_bundle_assembled`) is
    REMOVED, `hcont` now derived from `hD1` (W0.3).  NONE of `hGateData`/`hGateData'`/`hFbd`/`hAnear`
    appears anywhere in `hCConvSlot_AT_GATE_v2`'s dependency cone (stated as fact below).

  ## THE COMPLETE SURVIVING CENSUS of `hCConvSlot_AT_GATE_v2` (no silent caps).
    (a) the OPEN field nbhd `{u, hu_open, hu0}`;
    (b) the LINEWISE family `hlin` (= ∀x∈u∀i `CConvV2DerivRep.hlin_as_D`; its OWN diff-under-∫ census —
        `snb ∈ 𝓝 (x i)`, the `AEStronglyMeasurable` legs `hFmeas`/`hF'meas`, the base interval-
        integrability `hFint`, the `(t−s)^{−1/2}` interval-integrable dominator `bound`/`hbdd`/`hbound`,
        and the pointwise inner `HasDerivAt` family `hdiff` — is DISCHARGEABLE from the WIDE legs
        `CConvV2WitnessStar.{hStarWide_concrete, hFpairWide, envelope_integrable_v2Wide}` for the
        dominator, the chart-opaque `WitnessDerivMeasurability` bank + `CConvV2LeviSource.
        sourceDataV2_concrete`'s `hFjoint`/`hFmeas` for the measurability legs, and the honest
        pointwise `hdiff`; carried here as the assembled family);
    (c) the L2 SLIVER census `{sSet, hsOpen, hsnhds, fbulk, fderivBulk, gderiv, bb, hb, hbulkderiv,
        hbulk_tendsto, hsliver, hcont}` — the named per-coordinate uniform-limit-of-derivatives data
        feeding `hD1_conditional` (`XUniformSliverFull.hD1_from_data` per coordinate + the
        `HD1CLMLift` lift).
    NO `hGateData`, `hGateData'`, `hFbd`, `hAnear` — dead.  Every surviving carry is SATISFIABLE,
    non-vacuous, strictly lower-level than the `C²` conclusion, and NONE equals `a₁ = R/6`.

  ## THE HONEST DISTANCE (what remains after the v2 chain).  The two surviving census families are the
    genuine still-open analytic inputs: (b)'s diff-under-∫ pointwise family `hdiff` (the `∂_w`-under-∫₀ᵗ∫
    step) and (c)'s uniform-limit-of-derivatives sliver data (the `hDaLimLU` census, the `(†)` limit,
    the `R0`/`R1` residues).  They are NOT `a₁ = R/6`; the `1/(2τ)→∞` blow-up (`hGateData`) and the
    uniform source bound (`hFbd`) are the ONLY things that were FALSE, and both are gone.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CConvV2DerivRep
import QIQTH.CConvConcreteThreading

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.HeatDuhamel QIQTH.CConvFacade
open QIQTH.TrueHeatKernel QIQTH.GcoefContinuity QIQTH.CConvV2DerivRep
open scoped Topology BigOperators Interval ContDiff

namespace QIQTH.CConvV2Facade

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### W1a — `hfam_v2` : the L1 `∃`-`HasFDerivAt` family (linewise + `hD1` bridge).
    ############################################################################### -/

/-- **★★ (W1a) `hfam_v2`.**  The L1 `∃`-`HasFDerivAt` family carried by `SpatialC2.hCConv_reduction`,
    assembled from
      • `hlin` — the per-coordinate LINEWISE `HasDerivAt` family (= ∀x∈u∀i the re-export
        `CConvV2DerivRep.hlin_as_D`), value `(Dmap … x)(Pi.single i 1)`;
      • `hD1`  — the `C¹` regularity of the representative `Dmap … Fconv t`,
    via the **v2 bridge** (W0.3): `hcont` (the coefficient continuity the old
    `GcoefContinuity.hCConv_L1_final` demands) is NOT taken from the poisoned envelope chain — it is
    DERIVED from `hD1` (`ContDiffAt.eventually` at `1 ≠ ∞` ⟹ `∀ᶠ x, ContinuousAt (Dmap …) x`;
    `Dmap_apply_single` identifies each coefficient with `(D x)(Pi.single i 1)`; `ContinuousAt.clm_apply`
    transfers continuity).  `hDrep` is `Dmap`'s definition (`hDrep_of_def`).  The neighbourhood is
    shrunk to `u ∩ v` where `v` is the `hD1`-continuity nbhd — still a nbhd of `0`.  Generic in the
    scalar-source kernel `Fconv`.  NOT `a₁ = R/6`. -/
theorem hfam_v2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Fconv : ℝ → Point n → Point n → ℝ) (t : ℝ)
    (u : Set (Point n)) (hu_open : IsOpen u) (hu0 : (0 : Point n) ∈ u)
    (hlin : ∀ x ∈ u, ∀ i : Fin n,
      HasDerivAt (fun w => heatConv (vanVleckGatedWitness g gi hC hK S a b) Fconv t
          (Function.update x i w) 0)
        ((Dmap g gi hC hK S a b Fconv t x) (Pi.single i (1 : ℝ))) (x i))
    (hD1 : ContDiffAt ℝ 1 (Dmap g gi hC hK S a b Fconv t) (0 : Point n)) :
    ∃ w ∈ 𝓝 (0 : Point n), ∀ x ∈ w,
      HasFDerivAt (fun p => heatConv (vanVleckGatedWitness g gi hC hK S a b) Fconv t p 0)
        (Dmap g gi hC hK S a b Fconv t x) x := by
  set D := Dmap g gi hC hK S a b Fconv t with hDdef
  -- (v2 bridge) continuity of `D` on an OPEN nbhd `v ∋ 0`, from `hD1`.
  have hev : ∀ᶠ x in 𝓝 (0 : Point n), ContinuousAt D x := by
    filter_upwards [hD1.eventually (by norm_num)] with x hx using hx.continuousAt
  rw [eventually_nhds_iff] at hev
  obtain ⟨v, hv_cont, hv_open, hv0⟩ := hev
  -- feed the banked linewise→Fréchet bridge on the open nbhd `u ∩ v`.
  refine hCConv_L1_final (vanVleckGatedWitness g gi hC hK S a b) Fconv t D (u ∩ v)
    (hu_open.inter hv_open) ⟨hu0, hv0⟩
    (fun i x => ∫ s in (0:ℝ)..t, ∫ z,
        witnessFieldDeriv g gi hC hK S a b i (t - s) x z * Fconv s z 0
        ∂(volume : Measure (Point n)))
    (fun x hx i => hlin x hx.1 i)
    (fun x hx i => ?_)
    (fun x _ => by rw [hDdef]; exact hDrep_of_def g gi hC hK S a b Fconv t x)
  -- the coefficient continuity at `x ∈ u ∩ v`, via `hDdef`+`Dmap_apply_single`+`clm_apply`.
  have hDc : ContinuousAt D x := hv_cont x hx.2
  have hfe : (fun y => ∫ s in (0:ℝ)..t, ∫ z,
        witnessFieldDeriv g gi hC hK S a b i (t - s) y z * Fconv s z 0
        ∂(volume : Measure (Point n)))
      = (fun y => (D y) (Pi.single i (1 : ℝ))) := by
    funext y; rw [hDdef, Dmap_apply_single g gi hC hK S a b Fconv t y i]
  show ContinuousAt (fun y => ∫ s in (0:ℝ)..t, ∫ z,
      witnessFieldDeriv g gi hC hK S a b i (t - s) y z * Fconv s z 0
      ∂(volume : Measure (Point n))) x
  rw [hfe]
  exact hDc.clm_apply continuousAt_const

/-! ###############################################################################
    ### W1b — `hD1_v2` : the L2 re-export of `CConvV2DerivRep.hD1_conditional`.
    ############################################################################### -/

/-- **(W1b) `hD1_v2`.**  The L2 layer `ContDiffAt ℝ 1 (Dmap … Fconv t) 0` — a re-export of
    `CConvV2DerivRep.hD1_conditional` (`XUniformSliverFull.hD1_from_data` per coordinate + the
    `HD1CLMLift` lift), carrying the named per-coordinate sliver census.  NOT `a₁ = R/6`. -/
theorem hD1_v2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Fconv : ℝ → Point n → Point n → ℝ) (t : ℝ)
    (sSet : Set (Point n)) (hsOpen : IsOpen sSet) (hsnhds : sSet ∈ 𝓝 (0 : Point n))
    (fbulk : Fin n → ℕ → Point n → ℝ)
    (fderivBulk : Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : Fin n → Point n → (Point n →L[ℝ] ℝ))
    (bb : Fin n → ℕ → ℝ) (hb : ∀ i, Filter.Tendsto (bb i) atTop (𝓝 (0 : ℝ)))
    (hbulkderiv : ∀ i : Fin n, ∀ m : ℕ, ∀ x ∈ sSet, HasFDerivAt (fbulk i m) (fderivBulk i m x) x)
    (hbulk_tendsto : ∀ i : Fin n, ∀ x ∈ sSet, Filter.Tendsto (fun m => fbulk i m x) atTop
      (𝓝 (∫ s in (0:ℝ)..t, ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z * Fconv s z 0
          ∂(volume : Measure (Point n)))))
    (hsliver : ∀ i : Fin n, ∀ m : ℕ, ∀ x ∈ sSet, dist (fderivBulk i m x) (gderiv i x) ≤ bb i m)
    (hcont : ∀ i : Fin n, ContinuousOn (gderiv i) sSet) :
    ContDiffAt ℝ 1 (Dmap g gi hC hK S a b Fconv t) (0 : Point n) :=
  hD1_conditional g gi hC hK S a b Fconv t sSet hsOpen hsnhds fbulk fderivBulk gderiv bb hb
    hbulkderiv hbulk_tendsto hsliver hcont

/-! ###############################################################################
    ### W2 — `hCConvSlot_AT_GATE_v2` : ★★★ THE EXACT CAPSTONE ANTECEDENT (v2 census only).
    ############################################################################### -/

/-- **★★★ (W2) `hCConvSlot_AT_GATE_v2`.**  The EXACT spatial-`C²` `hCConv` antecedent of the
    `∞`-capstone, at the concrete left kernel `H := vanVleckGatedWitness g gi hChr hK S a b` and the
    concrete Levi source `F := leviSeries (heatOp g gi H)`:
      `ContDiffAt ℝ 2 (fun p ↦ heatConv H (leviSeries (heatOp g gi H)) t p 0) 0`,
    assembled from the facade-v2 census ONLY (`hfam_v2 ∘ hCConv_reduction`, `D := Dmap …`).

    ── THE COMPLETE SURVIVING CENSUS (no silent caps).
      (a) `{u, hu_open, hu0}` — the OPEN field neighbourhood of `0`.
      (b) `hlin` — the LINEWISE `HasDerivAt` family (= ∀x∈u∀i `CConvV2DerivRep.hlin_as_D`), value
          `(Dmap … x)(Pi.single i 1)`.  Its OWN carries (the diff-under-∫ census: `snb`, `hFmeas`,
          `hF'meas`, `hFint`, `bound`/`hbdd`/`hbound`, `hdiff`) are dischargeable from the WIDE legs
          `CConvV2WitnessStar.{hStarWide_concrete, hFpairWide, envelope_integrable_v2Wide}` (dominator),
          the chart-opaque `WitnessDerivMeasurability` bank + `CConvV2LeviSource.sourceDataV2_concrete`
          `hFjoint`/`hFmeas` (measurability), and the honest pointwise `hdiff`.
      (c) `{sSet, hsOpen, hsnhds, fbulk, fderivBulk, gderiv, bb, hb, hbulkderiv, hbulk_tendsto,
          hsliver, hcont}` — the L2 SLIVER census feeding `hD1_conditional`.

    ── NOT IN THE DEPENDENCY CONE:  `hGateData`, `hGateData'`, `hFbd`, `hAnear` (the adjudicated-false
    fields) appear NOWHERE.  `hcont` (coefficient continuity) is DERIVED from the carried `hD1`, so the
    poisoned `g2_bundle_assembled` chain is bypassed.  Every surviving carry is SATISFIABLE,
    non-vacuous, and strictly lower-level than the `C²` conclusion.  ⚠ STILL NOT `a₁ = R/6`. -/
theorem hCConvSlot_AT_GATE_v2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b t : ℝ)
    (u : Set (Point n)) (hu_open : IsOpen u) (hu0 : (0 : Point n) ∈ u)
    (hlin : ∀ x ∈ u, ∀ i : Fin n,
      HasDerivAt (fun w => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t
          (Function.update x i w) 0)
        ((Dmap g gi hChr hK S a b
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t x)
          (Pi.single i (1 : ℝ))) (x i))
    (sSet : Set (Point n)) (hsOpen : IsOpen sSet) (hsnhds : sSet ∈ 𝓝 (0 : Point n))
    (fbulk : Fin n → ℕ → Point n → ℝ)
    (fderivBulk : Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : Fin n → Point n → (Point n →L[ℝ] ℝ))
    (bb : Fin n → ℕ → ℝ) (hb : ∀ i, Filter.Tendsto (bb i) atTop (𝓝 (0 : ℝ)))
    (hbulkderiv : ∀ i : Fin n, ∀ m : ℕ, ∀ x ∈ sSet, HasFDerivAt (fbulk i m) (fderivBulk i m x) x)
    (hbulk_tendsto : ∀ i : Fin n, ∀ x ∈ sSet, Filter.Tendsto (fun m => fbulk i m x) atTop
      (𝓝 (∫ s in (0:ℝ)..t, ∫ z,
          witnessFieldDeriv g gi hChr hK S a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
          ∂(volume : Measure (Point n)))))
    (hsliver : ∀ i : Fin n, ∀ m : ℕ, ∀ x ∈ sSet, dist (fderivBulk i m x) (gderiv i x) ≤ bb i m)
    (hcont : ∀ i : Fin n, ContinuousOn (gderiv i) sSet) :
    ContDiffAt ℝ 2 (fun p => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t p 0)
        (0 : Point n) := by
  -- (L2) the `C¹` regularity of the representative, from the sliver census.
  have hD1 : ContDiffAt ℝ 1 (Dmap g gi hChr hK S a b
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t) (0 : Point n) :=
    hD1_v2 g gi hChr hK S a b
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t
      sSet hsOpen hsnhds fbulk fderivBulk gderiv bb hb hbulkderiv hbulk_tendsto hsliver hcont
  -- (L1) the `∃`-`HasFDerivAt` family, from the linewise family + the `hD1`-bridge.
  have hfam := hfam_v2 g gi hChr hK S a b
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t
    u hu_open hu0 hlin hD1
  -- (L1 + L2) lift to `C²` via `2 = 1 + 1`.
  exact hCConv_reduction (vanVleckGatedWitness g gi hChr hK S a b)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t
    (Dmap g gi hChr hK S a b
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t)
    hfam hD1

end QIQTH.CConvV2Facade

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CConvV2Facade
#print axioms hfam_v2
#print axioms hD1_v2
#print axioms hCConvSlot_AT_GATE_v2
end AxiomChecks
