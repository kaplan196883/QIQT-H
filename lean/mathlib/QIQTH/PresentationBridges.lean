/-
  PresentationBridges — J4-464: WIRE THE GROUNDED SUP THEOREMS INTO THE CENSUS `hGateCore` SLOTS.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It closes
  the two PRESENTATION bridges that J4-463 (`InnerDataCensusThread`) left open between the census
  `hGateCore` C₁/C_L slots and their GROUNDED counterparts, then re-threads the census C₁ slot onto its
  grounded geometric inputs.  `a₁ = R/6` remains CONDITIONAL on the whole convergence-trio + geometric-
  wiring stack AND on the surviving envelope/box/scaffold/gate/amplitude inputs.  NO `sorry` (header
  prose excepted), NO `:= True`, NO new axioms; std-3 only.  No existing file is edited.

  ── THE TWO BRIDGES J4-463 LEFT OPEN.
    census `hGateCore` C_L slot :  `|leviSeries … s z 0| ≤ C_L · gaussDdim σ z`         (gaussDdim form)
    census `hGateCore` C₁ slot  :  `∀ᵐ z, z ∈ K → |witnessFieldDeriv … (update 0 i w) z| ≤ C₁`  (on-gate)
    grounded C_L  (`SupConstantFamily.levi_C_L_grounded`)  : `… ≤ C_L · baseKernelW 2 0 s z 0`  (kernel)
    grounded C₁-machinery (`SupFamilyFirstOrder`/`UngatedChainRule`)  : the JOINT continuity of the
        witness first field-derivative `witnessFieldDeriv_jointContinuousOn` (J4-443).

  ── BRIDGE 1 (C_L, expected easy — CONFIRMED).  `census_C_L_grounded` delegates to `levi_C_L_grounded`
  and rewrites its `baseKernelW 2 0 τ p q` dominator to the plain Gaussian `gaussDdim (2·τ) (p − q)` via
  the banked identity `HeatResidualBound.baseKernelW_zero_apply` (`baseKernelW κ 0 τ p q =
  gaussDdim (κ·τ) (p − q)`).  The kernel is DEFINITIONALLY the census witness (`vanVleckGatedWitness
  g gi hC hK S a b = gatedKernel K S (globalCutoffParametrixWitnessN 1 …)`, `ConvApproximants`), so no
  further bridge is needed for the SHAPE.  HONEST RESIDUE: `levi_C_L_grounded` EXISTENTIALLY chooses its
  own gate `S` (and radii `a b`) — the domination holds for the theorem's `S,a,b`, not an arbitrary
  census-fixed gate; so the gaussDdim SHAPE is grounded but the slot cannot be wired for an arbitrary
  census `S` (it fixes `S`).  This is the honest reason C_L stays carried in `v2Census_phase7`.

  ── BRIDGE 2 (C₁, the substantive one — COMPOSED, via the DIRECT witness route).  `census_C1_grounded`
  grounds the census C₁ slot object ITSELF (`witnessFieldDeriv`, not the `chartAmp` derivative): the
  J4-443 `UngatedChainRule.witnessFieldDeriv_jointContinuousOn` gives the JOINT continuity of
  `(w',z) ↦ witnessFieldDeriv … i τ (update 0 i w') z` on `Icc (w−ρ)(w+ρ) ×ˢ K`; restricting to the
  `w`-slice and applying `IsCompact.exists_bound_of_continuousOn` on the compact `K` yields
    `∃ C₁ ≥ 0, ∀ z ∈ K, |witnessFieldDeriv … i τ (update 0 i w) z| ≤ C₁`,
  which is EXACTLY the census C₁ on-gate slot (`∀ᵐ z, z ∈ K → …`, via `Filter.Eventually.of_forall`).
  DON'T-UNDERCREDIT: the germ↔`chartAmp` conversion the J4-463 audit feared is UNNECESSARY — the J4-443
  joint continuity already lives at the WITNESS level, so compactness bounds the census object directly.

  ── THE WIRE.  `v2Census_phase7` = `v2Census_phase6` with `hGateCore` replaced by a REDUCED gate core
  `hGateCoreR` (the six non-C₁ conjuncts) + the C₁-geometry bundle; the full `hGateCore` is
  RECONSTRUCTED internally by supplying the C₁ conjuncts from `census_C1_grounded`.  C_L stays inside
  `hGateCoreR` (see BRIDGE 1 residue).  Conclusion is the SAME v3-core `TruncatedDuhamelCore`.

  ⚠  a₁ = R/6 remains CONDITIONAL.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.InnerDataCensusThread
import QIQTH.SupConstantFamily
import QIQTH.SupFamilyFirstOrder
import QIQTH.UngatedChainRule

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
open QIQTH.InnerDataCensusThread
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.PresentationBridges

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ BRIDGE 1 — the C_L slot: `baseKernelW 2 0` ↦ `gaussDdim (2·τ)`.
    ############################################################################### -/

/-- **★ `census_C_L_grounded` — BRIDGE 1: the grounded Levi domination in the census `gaussDdim`
    presentation.**  Delegates to `SupConstantFamily.levi_C_L_grounded` (= the banked
    `leviSeries_gatedWitnessN1_dominated`) and rewrites its `baseKernelW 2 0 τ p q` dominator to the
    plain Gaussian `gaussDdim (2·τ) (p − q)` via `baseKernelW_zero_apply`.  The kernel is
    DEFINITIONALLY the census witness `vanVleckGatedWitness g gi hC hK S a b`.  So the census C_L slot
    SHAPE `|leviSeries …| ≤ C_L · gaussDdim (2τ)` is grounded.  HONEST RESIDUE: the gate `S` (and radii
    `a b`) are EXISTENTIALLY chosen here, so this grounds the SHAPE, not the slot for an arbitrary
    census-fixed `S`.  ⚠ NOT `a₁ = R/6`. -/
theorem census_C_L_grounded (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hn : 1 ≤ n) (T : ℝ) (hT : 0 < T) :
    ∃ a b C : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ ∃ S : Point n → Set (Point n),
      (∀ (t : ℝ), ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) τ p q|
          ≤ (C * (1 + t)) * gaussDdim (2 * τ) (p - q))
      ∧ (StronglyMeasurable (fun w : ℝ × Point n × Point n =>
            heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) w.1 w.2.1 w.2.2) →
          ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ τ p q, 0 < τ → τ ≤ T →
            |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) τ p q|
              ≤ C_L * gaussDdim (2 * τ) (p - q)) := by
  obtain ⟨a, b, C, ha, hab, hC0, S, hbound, hLevi⟩ :=
    levi_C_L_grounded g gi hg hC hK hgnd hgsymm hinvF hframeK hw hdg0 hg0 hn T hT
  refine ⟨a, b, C, ha, hab, hC0, S, ?_, ?_⟩
  · intro t τ p q hτ hτt
    have h := hbound t τ p q hτ hτt
    rwa [baseKernelW_zero_apply] at h
  · intro hEmeas
    obtain ⟨C_L, hC_Lnn, hdom⟩ := hLevi hEmeas
    refine ⟨C_L, hC_Lnn, fun τ p q hτ hτT => ?_⟩
    have h := hdom τ p q hτ hτT
    rwa [baseKernelW_zero_apply] at h

/-! ###############################################################################
    ### ★★ BRIDGE 2 — the C₁ slot: the on-gate sup of `witnessFieldDeriv`, grounded.
    ############################################################################### -/

/-- **★★ `census_C1_grounded` — BRIDGE 2: the census C₁ on-gate sup, grounded from geometry.**  The
    census C₁ slot is `∃ C₁ ≥ 0, ∀ z ∈ K, |witnessFieldDeriv … i τ (update 0 i w) z| ≤ C₁`.  Route
    (DIRECT witness route — no `chartAmp` detour): `UngatedChainRule.witnessFieldDeriv_jointContinuousOn`
    (J4-443) gives the JOINT continuity of `(w',z) ↦ witnessFieldDeriv … i τ (update 0 i w') z` on
    `Icc (w−ρ)(w+ρ) ×ˢ K` from the chart-geometry inputs `hw`/`hW0`/`hmaps`/`hunit`/`hIFT`/`hWdiff` and
    the in-gate carry `hGate`; restrict to the `w`-slice (`w ∈ Icc (w−ρ)(w+ρ)` since `ρ > 0`) and apply
    `IsCompact.exists_bound_of_continuousOn` on the compact `K`.  This bounds the ACTUAL census object.
    ⚠ NOT `a₁ = R/6`. -/
theorem census_C1_grounded (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (w ρ : ℝ) (hρ : 0 < ρ)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hW0 : ContinuousOn
      (fun q : ℝ × Point n =>
        uniformInverseChart g gi hC hK q.2 (Function.update (0 : Point n) i q.1))
      (Set.Icc (w - ρ) (w + ρ) ×ˢ K))
    (hmaps : Set.MapsTo
      (fun q : ℝ × Point n =>
        (q.2, uniformInverseChart g gi hC hK q.2 (Function.update (0 : Point n) i q.1)))
      (Set.Icc (w - ρ) (w + ρ) ×ˢ K)
      (K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)))
    (hunit : ∀ q ∈ Set.Icc (w - ρ) (w + ρ) ×ˢ K,
      IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK q.2)
        (uniformInverseChart g gi hC hK q.2 (Function.update (0 : Point n) i q.1))))
    (hIFT : ∀ q ∈ Set.Icc (w - ρ) (w + ρ) ×ˢ K,
      fderiv ℝ (uniformInverseChart g gi hC hK q.2) (Function.update (0 : Point n) i q.1)
        = Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK q.2)
            (uniformInverseChart g gi hC hK q.2 (Function.update (0 : Point n) i q.1))))
    (hWdiff : ∀ q ∈ Set.Icc (w - ρ) (w + ρ) ×ˢ K,
      DifferentiableAt ℝ (uniformInverseChart g gi hC hK q.2) (Function.update (0 : Point n) i q.1))
    (hGate : ∀ q ∈ Set.Icc (w - ρ) (w + ρ) ×ˢ K,
      S q.2 ∈ nhds (Function.update (0 : Point n) i q.1)) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ z ∈ K,
      |witnessFieldDeriv g gi hC hK S a b i τ (Function.update (0 : Point n) i w) z| ≤ C₁ := by
  have hjoint := witnessFieldDeriv_jointContinuousOn g gi hC hK S a b i τ (0 : Point n) w ρ
    hw hW0 hmaps hunit hIFT hWdiff hGate
  -- restrict the joint continuity to the `w`-slice `z ↦ (w, z)`
  have hslice : ContinuousOn
      (fun z : Point n =>
        witnessFieldDeriv g gi hC hK S a b i τ (Function.update (0 : Point n) i w) z) K := by
    have hcont : Continuous (fun z : Point n => ((w : ℝ), z)) :=
      continuous_const.prodMk continuous_id
    have hmapsto : Set.MapsTo (fun z : Point n => ((w : ℝ), z)) K
        (Set.Icc (w - ρ) (w + ρ) ×ˢ K) := by
      intro z hz
      exact ⟨⟨by linarith, by linarith⟩, hz⟩
    have hcomp := hjoint.comp hcont.continuousOn hmapsto
    simpa [Function.comp] using hcomp
  obtain ⟨C, hCbd⟩ := hK.exists_bound_of_continuousOn hslice
  refine ⟨max C 0, le_max_right _ _, fun z hz => ?_⟩
  have h := hCbd z hz
  rw [Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

/-! ###############################################################################
    ### ★★★ THE RECONSTRUCTION — the full `hGateCore` from the reduced core + C₁-geometry.
    ############################################################################### -/

/-- **★★★ `gateCore_reconstruct` — the full `hGateCore` binder, C₁-slot GROUNDED.**  Reconstructs the
    exact `v2Census_phase6` `hGateCore` binder (the 7-conjunct-per-`(m,i,u)`/a.e.-`s`/`∀ w` existential
    with witnesses `znb σ C₁ C₂ C_L`) from a REDUCED gate core `hGateCoreR` carrying the six non-C₁
    conjuncts (existential witnesses `znb σ C₂ C_L`) plus the C₁-geometry bundle `hC1geom`.  Per
    instance the C₁ nonneg + on-gate conjuncts are SUPPLIED by `census_C1_grounded` (τ := u − s, field
    point `update 0 i w`); the on-gate `∀ z ∈ K` bound becomes the a.e.-`z` conjunct via
    `Filter.Eventually.of_forall`.  C_L stays inside `hGateCoreR` (BRIDGE 1 residue: `census_C_L_grounded`
    fixes the gate `S`).  ⚠ NOT `a₁ = R/6`. -/
theorem gateCore_reconstruct (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (snb : Set ℝ) (ρc : ℝ) (hρc : 0 < ρc)
    (hwInf : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hC1geom : ∀ (i : Fin n), ∀ w ∈ snb,
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
          DifferentiableAt ℝ (uniformInverseChart g gi hChr hK q.2) (Function.update (0 : Point n) i q.1))
      ∧ (∀ q ∈ Set.Icc (w - ρc) (w + ρc) ×ˢ K,
          S q.2 ∈ nhds (Function.update (0 : Point n) i q.1)))
    (hGateCoreR : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
        ∃ (znb : Set ℝ) (σ C₂ C_L : ℝ),
          znb ∈ 𝓝 w ∧ 0 < σ ∧ 0 ≤ C₂ ∧ 0 ≤ C_L ∧
          (∀ w' : ℝ, AEStronglyMeasurable
            (fun z => witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z) volume) ∧
          AEStronglyMeasurable
            (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            volume ∧
          AEStronglyMeasurable
            (fun z => witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w) z) volume ∧
          (∀ᵐ z ∂volume,
            |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
              ≤ C_L * gaussDdim σ z) ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb, z ∈ K →
            |witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z| ≤ C₂) ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb,
            z ∉ K ∨ PdiffAt (fun x' : Point n =>
                witnessFieldDeriv g gi hChr hK S a b i (u - s) x' z) i
              (Function.update (0 : Point n) i w'))) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
        ∃ (znb : Set ℝ) (σ C₁ C₂ C_L : ℝ),
          znb ∈ 𝓝 w ∧ 0 < σ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ C_L ∧
          (∀ w' : ℝ, AEStronglyMeasurable
            (fun z => witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z) volume) ∧
          AEStronglyMeasurable
            (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            volume ∧
          AEStronglyMeasurable
            (fun z => witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w) z) volume ∧
          (∀ᵐ z ∂volume,
            |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
              ≤ C_L * gaussDdim σ z) ∧
          (∀ᵐ z ∂volume, z ∈ K →
            |witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w) z| ≤ C₁) ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb, z ∈ K →
            |witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z| ≤ C₂) ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb,
            z ∉ K ∨ PdiffAt (fun x' : Point n =>
                witnessFieldDeriv g gi hChr hK S a b i (u - s) x' z) i
              (Function.update (0 : Point n) i w')) := by
  intro m i u hu
  filter_upwards [hGateCoreR m i u hu] with s hs
  intro hsmem w hwmem
  obtain ⟨znb, σ, C₂, C_L, hznb, hσ, hC₂nn, hC_Lnn, hmeas1, hmeas2, hmeas3,
    hLevidom, hC₂gate, hdich⟩ := hs hsmem w hwmem
  obtain ⟨hg1W0, hg1maps, hg1unit, hg1IFT, hg1Wdiff, hg1gate⟩ := hC1geom i w hwmem
  obtain ⟨C₁, hC₁nn, hC₁gate⟩ :=
    census_C1_grounded g gi hChr hK S a b i (u - s) w ρc hρc hwInf
      hg1W0 hg1maps hg1unit hg1IFT hg1Wdiff hg1gate
  exact ⟨znb, σ, C₁, C₂, C_L, hznb, hσ, hC₁nn, hC₂nn, hC_Lnn, hmeas1, hmeas2, hmeas3,
    hLevidom, Filter.Eventually.of_forall hC₁gate, hC₂gate, hdich⟩

/-! ###############################################################################
    ### ★★★★ `v2Census_phase7` — `v2Census_phase6` with the C₁ slot GROUNDED from geometry.
    ############################################################################### -/

/-- **★★★★ `v2Census_phase7`.**  THE C₁-grounded terminal cross-check.  It is `v2Census_phase6` with the
    opaque `hGateCore` carry TRADED for a REDUCED gate core `hGateCoreR` (the six non-C₁ conjuncts) +
    the C₁-geometry bundle `hC1geom` (with radius `ρc`) + the smooth-coefficient carry `hwInf`.  The
    full `hGateCore` is RECONSTRUCTED internally by `gateCore_reconstruct`, which supplies the C₁ nonneg
    and on-gate sup conjuncts from `census_C1_grounded` (BRIDGE 2 — compactness of `K` on the J4-443
    witness-derivative joint continuity).  C_L stays inside `hGateCoreR` (BRIDGE 1 residue: the grounded
    Levi domination `census_C_L_grounded` fixes its own gate `S`, so it cannot be wired for an arbitrary
    census `S`).  The conclusion is the SAME v3-core `TruncatedDuhamelCore`.  ⚠ Pure surface reduction at
    the C₁ leg; closes NOTHING deeper.  NOT `a₁ = R/6`. -/
theorem v2Census_phase7 (g gi : Point n → Fin n → Fin n → ℝ)
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
    (τc wA2 : ℝ)
    (hwA2 : 0 < wA2)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (Cdata : ℝ)
    (data : LeviSeriesLocalData
        (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) Cdata T)
    (hSecBoxes : ∀ i : Fin n, ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n => witnessSecondXDeriv g gi hChr hK S a b i p.1 p.2)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hBBoxes : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (Ccrude : ℝ) (hCcrude : 0 ≤ Ccrude)
    (hcrude : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z|
          ≤ Ccrude * τ⁻¹ * gaussDdim (wA2 * τ) (0 - z))
    (Lc Bcomp Q Sconst : ℝ) (hLc : 0 ≤ Lc) (hBcomp : 0 ≤ Bcomp) (hQ : 0 ≤ Q) (hSconst : 0 ≤ Sconst)
    (hslot : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i τ z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ (2 * Lc * (15 / 2 * (n : ℝ)) + Bcomp + Q) * τ ^ (-(1 : ℝ) / 2) + Sconst)
    (hcap : ∀ (m : ℕ), ∀ u ∈ U, ∀ s ∈ Set.Ioo (u - epsSeq m) u, u - s ≤ τc)
    (hEndpoint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - u) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) u z 0 = 0)
    (ρc : ℝ) (hρc : 0 < ρc)
    (hwInf : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hC1geom : ∀ (i : Fin n), ∀ w ∈ snb,
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
          DifferentiableAt ℝ (uniformInverseChart g gi hChr hK q.2) (Function.update (0 : Point n) i q.1))
      ∧ (∀ q ∈ Set.Icc (w - ρc) (w + ρc) ×ˢ K,
          S q.2 ∈ nhds (Function.update (0 : Point n) i q.1)))
    (hGateCoreR : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
        ∃ (znb : Set ℝ) (σ C₂ C_L : ℝ),
          znb ∈ 𝓝 w ∧ 0 < σ ∧ 0 ≤ C₂ ∧ 0 ≤ C_L ∧
          (∀ w' : ℝ, AEStronglyMeasurable
            (fun z => witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z) volume) ∧
          AEStronglyMeasurable
            (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            volume ∧
          AEStronglyMeasurable
            (fun z => witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w) z) volume ∧
          (∀ᵐ z ∂volume,
            |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
              ≤ C_L * gaussDdim σ z) ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb, z ∈ K →
            |witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z| ≤ C₂) ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb,
            z ∉ K ∨ PdiffAt (fun x' : Point n =>
                witnessFieldDeriv g gi hChr hK S a b i (u - s) x' z) i
              (Function.update (0 : Point n) i w')))
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
  -- ★ RECONSTRUCT the full `hGateCore` from the reduced core + the C₁-geometry (BRIDGE 2 grounded).
  have hGateCore := gateCore_reconstruct g gi hChr hK S a b U snb ρc hρc hwInf hC1geom hGateCoreR
  exact v2Census_phase6 g gi hChr hK S a b F hFeq
    t T hT U hUopen htU hUT hn hBoundaryLim hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas
    bnd hbdd hbound D0 D1 hD0 hD1 hbnd E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hEdom hFdom hIlo hIhi
    hEcomb A₀ A₁ hA₀ hA₁ hAdom hAzero hMeasFII hUfloor hInnerCont
    nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
    ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd
    hWDom hmass hmassone hmod hsup hUsub
    τc wA2 hwA2 hεU Cdata data hSecBoxes hBBoxes
    Ccrude hCcrude hcrude
    Lc Bcomp Q Sconst hLc hBcomp hQ hSconst hslot hcap hEndpoint
    hGateCore
    nbP hnbP_open hnbP0 hProvP fderivBulk gderiv C₀ C₁ C₂ hGintP hbulkderiv hsliver hcont hfrozen_pd1

end QIQTH.PresentationBridges

/-! ## THE CONVERGENCE LEDGER v2 — the census C₁/C_L slots after J4-464.

  J4-463 (`InnerDataCensusThread`) reduced the census differentiation-under-∫ leg to `hGateCore`'s seven
  named atoms and flagged C₁ (on-gate `witnessFieldDeriv` sup) and C_L (Levi Gaussian domination) as
  living in a DIFFERENT presentation from their grounded counterparts.  J4-464 closes both bridges:

    census slot        grounded route (J4-464)                                     status
    ────────────────   ─────────────────────────────────────────────────────────  ─────────────────────
    C_L                `census_C_L_grounded` : `levi_C_L_grounded` + the banked      SHAPE GROUNDED;
    (`|Lev| ≤          `baseKernelW_zero_apply` (`baseKernelW 2 0 τ p q =            slot-wire BLOCKED —
     C_L·gaussDdim σ`) gaussDdim (2τ)(p−q)`).  Kernel is DEFEQ the census witness.   the theorem FIXES its
                       BRIDGE 1 = a one-step rewrite (as J4-431 predicted).          own gate `S`,a,b.
    ────────────────   ─────────────────────────────────────────────────────────  ─────────────────────
    C₁                `census_C1_grounded` : `witnessFieldDeriv_jointContinuousOn`   SLOT GROUNDED &
    (`∀ᵐ z, z∈K →      (J4-443, the WITNESS-level joint continuity) restricted to     WIRED into
     |dH(w)| ≤ C₁`)    the `w`-slice + `IsCompact.exists_bound_of_continuousOn` on    `v2Census_phase7`
                       `K`; on-gate `∀z∈K` ⟹ a.e.-`z` via `Eventually.of_forall`.     via
                       BRIDGE 2 COMPOSED — bounds the ACTUAL census object.           `gateCore_reconstruct`.

  ── THE WIRE.  `v2Census_phase7` = `v2Census_phase6` with `hGateCore` TRADED for the REDUCED gate core
  `hGateCoreR` (six non-C₁ conjuncts) + the C₁-geometry bundle `hC1geom` (radius `ρc`) + `hwInf`; the
  full `hGateCore` is reconstructed internally by `gateCore_reconstruct`, the C₁ conjuncts supplied by
  `census_C1_grounded`.  So the census C₁ slot no longer carries a RAW sup — it carries the chart-
  geometry / gate inputs (`hC1geom`) + compactness (`hK`), i.e. the grounded theorem's OWN inputs.

  ── WHY C_L STAYS CARRIED (honest, BRIDGE 1 residue).  `census_C_L_grounded` grounds the gaussDdim SHAPE
  of the Levi domination, but `levi_C_L_grounded`/`leviSeries_gatedWitnessN1_dominated` EXISTENTIALLY
  choose the gate `S` (and radii `a b`) so the parametrix bound holds — the domination is NOT available
  for an arbitrary census-fixed `S`.  Hence C_L cannot be injected into `hGateCore` for a general census
  `S`; it remains inside `hGateCoreR` (with `σ` still existentially per-instance).  Wiring C_L would
  require fixing the census `S,a,b` to the grounded theorem's choices — a global restructure, not a slot
  swap; recorded as the C_L residual, NOT a new obstruction.

  ── DON'T-UNDERCREDIT FINDINGS (paid off).
    • The germ↔`chartAmp`-derivative conversion the J4-463 audit feared for C₁ is UNNECESSARY: J4-443
      already delivers the joint continuity at the WITNESS level (`witnessFieldDeriv_jointContinuousOn`),
      so compactness of `K` bounds the census object directly — the `chartAmp` route
      (`baseSlotAmpDeriv1_grounded`) is a SEPARATE presentation and was not needed.
    • BRIDGE 1's `baseKernelW 2 0 = gaussDdim(2τ)` was already a banked one-liner
      (`baseKernelW_zero_apply`, `HeatResidualBound`); the J4-431 note ("deferred, not a new
      obstruction") was accurate.
    • `vanVleckGatedWitness g gi hC hK S a b` is DEFINITIONALLY the gated kernel of
      `leviSeries_gatedWitnessN1_dominated` (`ConvApproximants`), so the kernel matched with no bridge.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ★ v3-CORE SURFACE AFTER THIS BRICK.  The census C₁ slot is now grounded (wired into `v2Census_phase7`);
  the C_L slot's gaussDdim SHAPE is grounded (`census_C_L_grounded`) but stays carried pending the S-fix
  restructure.  ⚠ THIS IS **NOT** `a₁ = R/6`: the surviving inputs are INPUTS, and the DEEP convergence-
  trio + geometric-wiring content OUTSIDE the census is NEVER claimed closed.  Grounding two slot shapes
  closes NOTHING deeper.
-/

section AxiomChecks
open QIQTH.PresentationBridges
#print axioms census_C_L_grounded
#print axioms census_C1_grounded
#print axioms gateCore_reconstruct
#print axioms v2Census_phase7
end AxiomChecks
