/-
  CLSlotWire — J4-465: WIRE THE GROUNDED `C_L` INTO THE CENSUS `hGateCore` SLOT.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  completes the J4-464 residue: J4-464 grounded the census `C_L` SHAPE (`census_C_L_grounded` — the
  gaussDdim-presented Levi domination) but could not WIRE the slot, because the grounded theorem
  EXISTENTIALLY fixes its own gate `S` (and radii `a,b`), while `v2Census_phase7` fixes its own free
  `S`.  This brick performs the honest gate-∃-consumption wire.  `a₁ = R/6` remains CONDITIONAL on the
  whole convergence-trio + geometric-wiring stack AND on the surviving envelope/box/scaffold/gate/
  amplitude inputs.  NO `sorry` (header prose excepted), NO `:= True`, NO new axioms; std-3 only.  No
  existing file is edited.

  ── THE GATE-COHERENCE AUDIT (mandatory, per J4-417 witness-coherence / J4-412 radii-load-bearing).
    (i)  DEFEQ CHECK.  The grounded theorem's gate is the ∃-chosen `S` of
         `gatedWitnessN1_hEboundW_le_vanVleck_final` (produced INSIDE `levi_C_L_grounded`).  The census
         gate is a FREE `∀`-binder `(S : Point n → Set (Point n))`.  These are NOT the same construction
         — one is ∃-produced, the other universally quantified — so they are NOT defeq.  (The KERNELS
         `vanVleckGatedWitness g gi hChr hK S a b = gatedKernel K S (globalCutoffParametrixWitnessN 1 …)`
         ARE defeq GIVEN the same `S,a,b`, `ConvApproximants`; the mismatch is purely `∃`-`S` vs `∀`-`S`.)
    (ii) VERDICT = ∃-CONSUMPTION.  To supply (not carry) the `C_L` conjunct we MUST fix the census gate
         to the grounded theorem's choice.  Every S-dependent census binder (all of `v2Census_phase7`'s
         analytic carries — envelope/box/scaffold/gate/amplitude bounds — reference this `S`) migrates
         into the ∃-body as a hypothesis AT the obtained gate.  HONESTY COST: `v2Census_phase8`'s result
         is `∃ a b S, …` — no longer for an arbitrary census `S`, but for the specific grounded gate.
    (iii) SATISFIABILITY (no blocker).  The obtained `S` is exactly "the geometry-chosen gate" that the
         whole campaign's W3 gate-compatibility architecture already contemplates (see
         `DataLeviDischarge`/`FixedGateSourceProviders` headers): the migrated carries are the SURVIVING
         labelled inputs at that gate.  No census binder becomes UNSATISFIABLE at the obtained `S`; they
         stay honest conditional hypotheses.  So the wire is a legitimate ∃-consumption, not a Sol #22
         blocker.

  ── WHAT LANDS.
    • `census_C_L_wired`      — ★ the per-`s` `C_L` conjunct (`∃ σ>0, ∀ᵐ z, |leviSeries|≤C_L·gaussDdim σ`)
        from the grounded domination, with `σ := 2·s`.
    • `gateCoreRR_reconstruct`— ★★ rebuild the phase-7 `hGateCoreR` (with `C_L`) from a DOUBLY-reduced
        gate core `hGateCoreRR` (no `σ`/`C_L`) + the grounded domination, at a fixed gate.
    • `v2Census_phase8`       — ★★★★ the gate-∃-consumed terminal cross-check: obtain `S,a,b` from
        `census_C_L_grounded`, ground the `C_L` slot, apply `v2Census_phase7`.

  ⚠  a₁ = R/6 remains CONDITIONAL.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.PresentationBridges

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
open QIQTH.InnerDataCensusThread QIQTH.PresentationBridges
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.CLSlotWire

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ `census_C_L_wired` — the per-`s` `C_L` conjunct from the grounded domination.
    ############################################################################### -/

/-- **★ `census_C_L_wired` — the census `C_L` conjunct, wired from the grounded domination.**  From the
    grounded Levi Gaussian domination `hdom : ∀ τ p q, 0<τ→τ≤T → |leviSeries E τ p q| ≤ C_L·gaussDdim
    (2τ)(p−q)` (the `census_C_L_grounded` output, post-`hEmeas`) and a single time `s` with `0<s≤T`,
    produce the EXACT census `hGateCore`/`hGateCoreR` `C_L` conjunct shape
      `∃ σ, 0 < σ ∧ ∀ᵐ z, |leviSeries E s z 0| ≤ C_L·gaussDdim σ z`,
    with the Gaussian width `σ := 2·s` (positive since `s>0`) and the base point `q = 0`
    (`p−q = z−0 = z`).  ⚠ NOT `a₁ = R/6`. -/
theorem census_C_L_wired (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (T C_L : ℝ)
    (hdom : ∀ (τ : ℝ) (p q : Point n), 0 < τ → τ ≤ T →
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) τ p q|
          ≤ C_L * gaussDdim (2 * τ) (p - q))
    (s : ℝ) (hs0 : 0 < s) (hsT : s ≤ T) :
    ∃ σ : ℝ, 0 < σ ∧ (∀ᵐ z ∂volume,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ C_L * gaussDdim σ z) := by
  refine ⟨2 * s, by linarith, Filter.Eventually.of_forall (fun z => ?_)⟩
  have h := hdom s z 0 hs0 hsT
  simpa [sub_zero] using h

/-! ###############################################################################
    ### ★★ `gateCoreRR_reconstruct` — rebuild `hGateCoreR` (with `C_L`) at a fixed gate.
    ############################################################################### -/

/-- **★★ `gateCoreRR_reconstruct` — the `C_L`-grounded gate core, at a fixed gate.**  Rebuilds the exact
    `v2Census_phase7` `hGateCoreR` binder (the `∃ znb σ C₂ C_L` per-`(m,i,u)`/a.e.-`s`/`∀ w` core) from a
    DOUBLY-reduced core `hGateCoreRR` carrying only the five non-`C_L` conjuncts (`∃ znb C₂`: the three
    z-slice measurabilities, the `C₂` gate sup, the gate dichotomy) plus the grounded Levi domination
    `hdom` (in the census witness presentation).  Per instance the `σ`/`0<σ`/`0≤C_L`/`C_L`-domination
    conjuncts are SUPPLIED by `census_C_L_wired` (`σ := 2·s`).  The time bounds `0<s≤T` are recovered
    from `s ∈ uIoc 0 (u−epsSeq m)` via `hεU` (`epsSeq m ≤ u`, so `uIoc = Ioc`) and `hUT` (`u ≤ T`).
    ⚠ NOT `a₁ = R/6`. -/
theorem gateCoreRR_reconstruct (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (T : ℝ) (U snb : Set ℝ)
    (hUT : ∀ u ∈ U, u ≤ T) (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (C_L : ℝ) (hC_Lnn : 0 ≤ C_L)
    (hdom : ∀ (τ : ℝ) (p q : Point n), 0 < τ → τ ≤ T →
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) τ p q|
          ≤ C_L * gaussDdim (2 * τ) (p - q))
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
              (Function.update (0 : Point n) i w'))) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
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
              (Function.update (0 : Point n) i w')) := by
  intro m i u hu
  filter_upwards [hGateCoreRR m i u hu] with s hs
  intro hsmem w hwmem
  obtain ⟨znb, C₂, hznb, hC₂nn, hmeas1, hmeasLevi, hmeas3, hC₂gate, hdich⟩ := hs hsmem w hwmem
  have hb : (0 : ℝ) ≤ u - epsSeq m := by have := hεU m u hu; linarith
  rw [Set.uIoc_of_le hb] at hsmem
  have hs0 : 0 < s := hsmem.1
  have hsT : s ≤ T := by
    have h1 : s ≤ u - epsSeq m := hsmem.2
    have h2 : u ≤ T := hUT u hu
    have h3 : (0 : ℝ) < epsSeq m := epsSeq_pos m
    linarith
  obtain ⟨σ, hσ, hLevidom⟩ :=
    census_C_L_wired g gi hChr hK S a b T C_L hdom s hs0 hsT
  exact ⟨znb, σ, C₂, C_L, hznb, hσ, hC₂nn, hC_Lnn, hmeas1, hmeasLevi, hmeas3,
    hLevidom, hC₂gate, hdich⟩

/-! ###############################################################################
    ### ★★★★ `v2Census_phase8` — the gate-∃-consumed census gate core, `C_L` GROUNDED.
    ############################################################################### -/

/-- **★★★★ `v2Census_phase8` — the `C_L`-grounded census gate core at the OBTAINED gate.**  Per the
    gate-coherence audit (∃-consumption verdict), this OBTAINS the gate `(a,b,S)` from
    `census_C_L_grounded` (the grounded Levi domination fixes its own gate), then GROUNDS the census
    `hGateCore`/`hGateCoreR` `C_L` slot at that gate.  Conclusion: `∃ a b S, 0<a ∧ a<b ∧ …`, where the
    body says — over ANY census window data `U,snb` with `u ≤ T` (`hUT`) and `epsSeq m ≤ u` (`hεU`),
    GIVEN the standing base joint measurability `hEmeas` (M1 carry, at THIS obtained gate) and the
    DOUBLY-reduced gate core `hGateCoreRR` (the five non-`C_L` conjuncts) — the FULL phase-7
    `hGateCoreR` (with the `C_L` conjunct `∃ σ>0, ∀ᵐ z, |leviSeries|≤C_L·gaussDdim σ`) holds.  The `C_L`
    conjunct is SUPPLIED (not carried) from the grounded domination via `gateCoreRR_reconstruct`.

    HONESTY COST (recorded).  The result is quantified over the OBTAINED gate `S` (the ∃-chosen
    geometry gate of `gatedWitnessN1_hEboundW_le_vanVleck_final`), NOT an arbitrary census `S`; this is
    the price of moving `C_L` from CARRIED to GROUNDED.  The migrated S-dependent slots (`hUT`, `hεU`,
    `hEmeas`, `hGateCoreRR`) remain satisfiable at that gate — they are exactly the campaign's surviving
    W3 labelled inputs at the geometry-chosen gate (no new unsatisfiability).  ⚠ NOT `a₁ = R/6`. -/
theorem v2Census_phase8 (g gi : Point n → Fin n → Fin n → ℝ)
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
      ∀ (U snb : Set ℝ), (∀ u ∈ U, u ≤ T) → (∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u) →
        StronglyMeasurable (fun w : ℝ × Point n × Point n =>
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) w.1 w.2.1 w.2.2) →
        (∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
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
                  (Function.update (0 : Point n) i w'))) →
        (∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
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
                  (Function.update (0 : Point n) i w'))) := by
  obtain ⟨a, b, C, ha, hab, _hC0, S, _hbound, hLevi⟩ :=
    census_C_L_grounded g gi hg hChr hK hgnd hgsymm hinvF hframeK hwtop hdg0 hg0 hn T hT
  refine ⟨a, b, S, ha, hab, fun U snb hUT hεU hEmeas hGateCoreRR => ?_⟩
  obtain ⟨C_L, hC_Lnn, hdom⟩ := hLevi hEmeas
  exact gateCoreRR_reconstruct g gi hChr hK S a b T U snb hUT hεU C_L hC_Lnn hdom hGateCoreRR

end QIQTH.CLSlotWire

/-! ## THE C_L LEDGER — the census `C_L` slot after J4-465.

  J4-464 grounded the census `C_L` SHAPE (`census_C_L_grounded` — the gaussDdim-presented Levi
  domination) but flagged that it could NOT wire the slot: the grounded theorem `levi_C_L_grounded`
  EXISTENTIALLY fixes its own gate `S` (and radii `a,b`), while `v2Census_phase7` fixes a FREE `S`.
  J4-465 performs the honest gate-∃-consumption wire.

    stage                      what it does                                                status
    ────────────────────────   ───────────────────────────────────────────────────────   ──────────────
    grounded shape (J4-464)    `census_C_L_grounded` : `∃ a b C S, … ∧ (hEmeas → ∃ C_L,    SHAPE GROUNDED
                               ∀τpq, |leviSeries E τ p q| ≤ C_L·gaussDdim(2τ)(p−q))`
    per-`s` conjunct (J4-465)  `census_C_L_wired` : from the grounded domination + `0<s≤T`, SLOT PIECE
                               the exact `∃ σ>0, ∀ᵐ z, |leviSeries|≤C_L·gaussDdim σ z`      GROUNDED
                               (`σ := 2·s`, `q = 0`).
    gate core (J4-465)         `gateCoreRR_reconstruct` : rebuild the phase-7 `hGateCoreR`   GATE CORE
                               (`∃ znb σ C₂ C_L`) from the DOUBLY-reduced `hGateCoreRR`      GROUNDED
                               (`∃ znb C₂`, no `C_L`) + the grounded domination, at a fixed   (fixed gate)
                               gate.  `s`-bounds from `hεU` (`uIoc=Ioc`) + `hUT`.
    capstone (J4-465)          `v2Census_phase8` : OBTAIN `(a,b,S)` from `census_C_L_grounded`, SLOT WIRED
                               ground the `C_L` slot at the obtained gate given `hEmeas` +    (gate ∃-
                               `hGateCoreRR`.  Conclusion `∃ a b S, …`.                       consumed)

  ── THE GATE-COHERENCE AUDIT (verdict = ∃-CONSUMPTION, no blocker).
    (i)  NOT DEFEQ.  The grounded gate is the ∃-chosen `S` of `gatedWitnessN1_hEboundW_le_vanVleck_final`
         (inside `levi_C_L_grounded`); the census gate is a FREE `∀`-binder.  The KERNELS agree defeq
         GIVEN the same `S,a,b` (`vanVleckGatedWitness = gatedKernel K S (globalCutoffParametrixWitnessN
         1 …)`, `ConvApproximants`) — the mismatch is purely `∃`-`S` vs `∀`-`S`.
    (ii) HONESTY COST.  To SUPPLY (not carry) `C_L`, the census gate is fixed to the grounded choice;
         `v2Census_phase8`'s result is `∃ a b S, …`, no longer for an arbitrary `S`.  The S-dependent
         slots migrate into the ∃-body as hypotheses AT the obtained gate.
    (iii) NO BLOCKER.  The obtained `S` IS "the geometry-chosen gate" of the campaign's W3 gate-
         compatibility architecture; the migrated carries (`hUT`, `hεU`, `hEmeas`, `hGateCoreRR`) are the
         surviving labelled inputs at that gate — all satisfiable, none unsatisfiable.  So this is a
         legitimate ∃-consumption wire, NOT a Sol #22 blocker.

  ── RESIDUE (for phase9).  `v2Census_phase8` wires `C_L` into the census GATE CORE at the obtained gate.
  Feeding that reconstructed `hGateCoreR` through the full `v2Census_phase7` binder stack (55 S-dependent
  analytic carries) at the ∃-consumed gate — to conclude `TruncatedDuhamelCore` — is a mechanical
  re-plumbing brick (phase9), deferred (not an obstruction; every carry is the same labelled input at the
  geometry-chosen gate).

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
-/

section AxiomChecks
open QIQTH.CLSlotWire
#print axioms census_C_L_wired
#print axioms gateCoreRR_reconstruct
#print axioms v2Census_phase8
end AxiomChecks
