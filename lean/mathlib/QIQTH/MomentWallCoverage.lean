/-
  MomentWallCoverage — J4-416: THE MOMENT-WALL COVERAGE CHECKS + THREADINGS.

  Closing move for the Duhamel-core threading arc.  `TerminalCoverage.truncatedDuhamelCore_threaded_v2`
  (J4-415) absorbed the two terminal `hdiff`/`hPd2conv` bundles; its own carry list left EXACTLY ONE
  genuinely-open analytic wall — THE MOMENT WALL:
    •  `hslot`          — the per-`τ` slot bound `|∫_z W₂ᵢ(τ)·F(s)| ≤ K₁·τ^{−1/2}+K₀` over all `0<τ≤τc`;
    •  `Cpair`/`hCpair`/`hGpow` — the Hi-leg `m`-uniform `(u−s)^{−1/2}` moment bound on `Set.uIoc`.
  This file checks those against the BANKED wall-A closure chain (J4-401/402/403) and, where the shapes
  match VERBATIM, THREADS them so the moment wall becomes the enumerated, satisfiable slot carries.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE J4-416 DONT-UNDERCREDIT VERDICTS.

  •  (M1) `Cpair`/`hCpair`/`hGpow` vs `GpowBridge.leviSecondPairing_le_invSqrt` (J4-401) +
     `GpowClosure.hGpow_uIoc_of_Ioo_zeroEndpoint` (J4-402).  The v2 core carries `Cpair : ℝ`,
     `hCpair : 0 ≤ Cpair`, and `hGpow` in the shape
       `∀ m i, ∀ u ∈ U, ∀ s ∈ Set.uIoc (u−εₘ) u, |∫_z W₂ᵢ(u−s)·F(s)| ≤ Cpair·(u−s)^{−1/2}`,
     with the SAME pairing (`witnessSecondXDeriv · leviSeries`) and the SAME windows as the banked
     `m`-uniform absorption capstone (whose `Cpair := K₁ + K₀·√(epsSeq 0)` is chosen BEFORE the `m,s`
     binders — the QUANTIFIER TRAP is preserved) followed by the `Ioo → uIoc` endpoint upgrade.
     **VERDICT: COVERED.**  Threading it (`hGpow_covered`) PRODUCES the whole `Cpair`/`hCpair`/`hGpow`
     bundle from the v2 core's own `hslot`/`hcap`/`hEndpoint` + nonnegativities — no residue beyond them.

  •  (M2) `hslot` vs `SlotDischarges.hinner_window_of_slotBound` (J4-403) +
     `GpowClosure.leviSecondPairing_inner_bound_concrete` (J4-402).  The v2 core's `hslot` — quantified
     over ALL `0<τ≤τc`, in the CONCRETE `(2·Lc·(15n/2)+Bcomp+Q)·τ^{−1/2}+Sconst` shape — is VERBATIM the
     `hslot` hypothesis of `hinner_window_of_slotBound` (with `L := Lc`, `τ₀ := τc`), whose per-`(τ,s)`
     supplier is `leviSecondPairing_inner_bound_concrete` (the concrete slot carries).
     **VERDICT: COVERED.**  Threading it (`hslot_covered`) AGGREGATES `hslot`+`hcap` into the exact
     `hinner_window` (open Hi-window) shape the wall-A capstone consumes; the residue = the J4-402 C1
     concrete slot carries (`qc`/`Ichart`/`hoff`/the integrabilities/the Lipschitz+center carries/the
     comparison-leg + gradient/mass dominators — `gpow_closure_carries`) + the J4-403 leftovers
     (`slot_discharge_residuals`), ALL satisfiable and enumerated.

  Both moment-wall residues are therefore DISCHARGEABLE into strictly lower-level, satisfiable slot DATA
  — NOT for free: the threading trades the opaque `Cpair`/`hCpair`/`hGpow` bundle for the (already
  carried) `hslot`/`hcap`/`hEndpoint`, and `hslot` in turn reduces to the enumerated concrete slot
  carries.  After this brick NO genuinely-open analytic wall remains ABOVE the slot-instantiation level.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  binder-coverage / re-plumbing brick: it re-exports the banked wall-A closure chain in the EXACT v2
  moment-wall binder shapes, and (stretch) absorbs the `Cpair`/`hCpair`/`hGpow` trio into a `_v3`
  Duhamel-core carrier deriving them internally from `hslot`/`hcap`/`hEndpoint`.  The capstone
  `a1_R6_from_data_v5` remains the maximally-unconditional **CONDITIONAL** a₁ two-jet; replacing the
  moment-wall binders by their slot carries closes NOTHING deeper.  No `sorry` (header prose excepted),
  no `admit`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to
  (or trivially yielding) the conclusion, no existing file edited, nothing committed, nothing wired into
  `QIQTH.lean` / `AxiomAudit`.  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.TerminalCoverage
import QIQTH.SlotDischarges

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.LeviSeries QIQTH.ExpMap QIQTH.HeatKernelA1
open QIQTH.DuhamelCoreThreaded QIQTH.PerUCensusTuple QIQTH.W2Finish
open QIQTH.HDuhamelExportRethread QIQTH.TruncatedDuhamelData
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData QIQTH.DaLimLUConcreteDischarge
open QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.EveryCeilingFamilies QIQTH.ESLegWidening QIQTH.GlobalRawBoundFacade
open QIQTH.TerminalCoverage
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.MomentWallCoverage

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (M2) `hslot_covered` — the per-`τ` slot bound aggregates to the `hinner_window` shape.
    ############################################################################### -/

/-- **★★★ (M2) `hslot_covered`.**  THE J4-416 M2 LEAN WITNESS.  The v2 Duhamel core's terminal `hslot`
    carry — the per-`τ` matched inner bound quantified over ALL `0 < τ ≤ τc` in the concrete
    `(2·Lc·(15n/2)+Bcomp+Q)·τ^{−1/2}+Sconst` shape — together with the window-cap `hcap`
    (`u−s ≤ τc` on every open Hi window), aggregates VERBATIM into the OPEN Hi-window `hinner_window`
    shape consumed by `GpowClosure.memLapFull_from_gpow_chain`, with the `m`-uniform constants
    `K₁ = 2·Lc·(15n/2)+Bcomp+Q`, `K₀ = Sconst`.  Produced by `SlotDischarges.hinner_window_of_slotBound`
    (J4-403); the per-`(τ,s)` supplier of `hslot` is `GpowClosure.leviSecondPairing_inner_bound_concrete`
    (J4-402), whose residue is the enumerated, satisfiable concrete slot carries (`gpow_closure_carries`
    + `slot_discharge_residuals`).  ⚠ THE QUANTIFIER TRAP: `Lc, Bcomp, Q, Sconst` are TOP-LEVEL
    parameters bound BEFORE the `m, s` binders, and `hslot` is over ALL `τ` — no `εₘ` leakage into
    `K₁`/`K₀`.  ⚠ NOT `a₁ = R/6`. -/
theorem hslot_covered (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (τc Lc Bcomp Q Sconst : ℝ)
    (hslot : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i τ z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ (2 * Lc * (15 / 2 * (n : ℝ)) + Bcomp + Q) * τ ^ (-(1 : ℝ) / 2) + Sconst)
    (hcap : ∀ (m : ℕ), ∀ u ∈ U, ∀ s ∈ Set.Ioo (u - epsSeq m) u, u - s ≤ τc) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ s ∈ Set.Ioo (u - epsSeq m) u,
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ (2 * Lc * (15 / 2 * (n : ℝ)) + Bcomp + Q) * (u - s) ^ (-(1 : ℝ) / 2) + Sconst :=
  QIQTH.SlotDischarges.hinner_window_of_slotBound g gi hChr hK S a b U τc Lc Bcomp Q Sconst hslot hcap

/-! ###############################################################################
    ### (M1) `hGpow_covered` — the whole `Cpair`/`hCpair`/`hGpow` bundle, produced from `hslot`.
    ############################################################################### -/

/-- **★★★ (M1) `hGpow_covered`.**  THE J4-416 M1 LEAN WITNESS.  The v2 Duhamel core's terminal moment
    wall — the `m`-uniform `Cpair : ℝ`, `hCpair : 0 ≤ Cpair`, and the Hi-leg `(u−s)^{−1/2}` bound
      `∀ m i, ∀ u ∈ U, ∀ s ∈ Set.uIoc (u−εₘ) u, |∫_z W₂ᵢ(u−s)·F(s)| ≤ Cpair·(u−s)^{−1/2}`
    — is PRODUCED WHOLESALE from the v2 core's own `hslot`/`hcap`/`hEndpoint` + nonnegativities, via the
    banked wall-A chain:
      `hslot_covered`/`hinner_window_of_slotBound` (M2, ⟹ open-window `K₁·τ^{−1/2}+K₀`)
        → `GpowBridge.leviSecondPairing_le_invSqrt` (⟹ `m`-uniform `Cpair` + OPEN-window `hGpow`)
        → `GpowClosure.hGpow_uIoc_of_Ioo_zeroEndpoint` (⟹ `uIoc` `hGpow`, endpoint carry `hEndpoint`).
    `Cpair := (2·Lc·(15n/2)+Bcomp+Q) + Sconst·√(epsSeq 0)` is chosen BEFORE the `m, s` binders — the
    absorption uses ONLY the fixed upper endpoint `epsSeq 0`, never a per-`m` lower cutoff, so the
    QUANTIFIER TRAP is preserved.  The residue is EXACTLY {`hslot`, `hcap`, `hEndpoint`} — themselves
    already reduced by M2 to the enumerated concrete slot carries.  ⚠ NOT `a₁ = R/6`. -/
theorem hGpow_covered (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (τc Lc Bcomp Q Sconst : ℝ)
    (hLc : 0 ≤ Lc) (hBcomp : 0 ≤ Bcomp) (hQ : 0 ≤ Q) (hSconst : 0 ≤ Sconst)
    (hslot : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i τ z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ (2 * Lc * (15 / 2 * (n : ℝ)) + Bcomp + Q) * τ ^ (-(1 : ℝ) / 2) + Sconst)
    (hcap : ∀ (m : ℕ), ∀ u ∈ U, ∀ s ∈ Set.Ioo (u - epsSeq m) u, u - s ≤ τc)
    (hEndpoint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - u) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) u z 0 = 0) :
    ∃ Cpair : ℝ, 0 ≤ Cpair ∧
      ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ s ∈ Set.uIoc (u - epsSeq m) u,
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ Cpair * (u - s) ^ (-(1 : ℝ) / 2) := by
  have hK₁ : (0 : ℝ) ≤ 2 * Lc * (15 / 2 * (n : ℝ)) + Bcomp + Q := by
    have : (0 : ℝ) ≤ 2 * Lc * (15 / 2 * (n : ℝ)) := by positivity
    linarith
  -- (M2) aggregate `hslot`+`hcap` into the open Hi-window `K₁·(u−s)^{−1/2}+K₀` inner bound.
  have hinner_window := hslot_covered g gi hChr hK S a b U τc Lc Bcomp Q Sconst hslot hcap
  -- (M1a) `m`-uniform `τ^{−1/2}` absorption ⟹ `Cpair` + OPEN-window `hGpow`.
  obtain ⟨Cpair, hCpair, hIoo⟩ :=
    QIQTH.GpowBridge.leviSecondPairing_le_invSqrt (n := n) U
      (2 * Lc * (15 / 2 * (n : ℝ)) + Bcomp + Q) Sconst hK₁ hSconst
      (fun m i u s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      hinner_window
  -- (M1b) `Ioo → uIoc` endpoint upgrade using the `τ = 0` measure-zero carry `hEndpoint`.
  exact ⟨Cpair, hCpair,
    QIQTH.GpowClosure.hGpow_uIoc_of_Ioo_zeroEndpoint (n := n) U Cpair
      (fun m i u s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      hIoo hEndpoint⟩

/-! ###############################################################################
    ### (V3) `truncatedDuhamelCore_threaded_v3` — the Core carrier with the moment wall ROUTED.
    ############################################################################### -/

/-- **★★★★ (V3) `truncatedDuhamelCore_threaded_v3`.**  THE ABSOLUTE-FINAL Duhamel Core carrier.
    Assembled from `TerminalCoverage.truncatedDuhamelCore_threaded_v2` (J4-415) with the MOMENT WALL
    trio `Cpair`/`hCpair`/`hGpow` REMOVED and DISCHARGED internally via `hGpow_covered` (M1) — which
    derives them from the (still carried) `hslot`/`hcap`/`hEndpoint` + nonnegativities, itself routing
    through the banked wall-A chain `hslot_covered`/`leviSecondPairing_le_invSqrt`/
    `hGpow_uIoc_of_Ioo_zeroEndpoint`.  ALL OTHER binders (including the V1/V2-absorbed `hdiff`/`hPd2conv`
    census, and `hslot`/`hcap`/`hEndpoint`) are carried VERBATIM.

    THE RESIDUE, after V1/V2 (J4-415) + V3 (J4-416), is therefore the ABSOLUTE FINAL LIST:
      •  `hslot` (⟶ M2 ⟶ the enumerated concrete slot carries `gpow_closure_carries` +
         `slot_discharge_residuals`), `hcap`, `hEndpoint`  — the moment wall, now slot-level;
      •  `hInnerData`  — the inner-`z` first-derivative census (V2, ← `W2Finish.w2_hdiff`);
      •  `nbP`/…/`hfrozen_pd1`  — the per-`u` `hPd2conv` census (V1, ← `PerUCensusTuple`);
      •  the satisfiable interchange/domination/continuity/gauge/Levi/√ε census carried by v2.
    NO genuinely-open analytic wall remains ABOVE the slot-instantiation level.  Every hypothesis is
    satisfiable and non-vacuous; NONE is the conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem truncatedDuhamelCore_threaded_v3 (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n, F s z y = 0)
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
    -- ── the WALL-A interchange census (as in J4-414/415), ∀ concrete data:
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
    -- ── (V2 absorbed) the inner-`z` `hdiff` census (REPLACING the terminal `hdiff` binder):
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
    -- ── (V1 absorbed) the per-`u` `hPd2conv` census (REPLACING the terminal `hPd2conv` binder):
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
  -- (M1) DISCHARGE the moment wall: derive `Cpair`/`hCpair`/`hGpow` from `hslot`/`hcap`/`hEndpoint`.
  obtain ⟨Cpair, hCpair, hGpow⟩ :=
    hGpow_covered g gi hChr hK S a b U τc Lc Bcomp Q Sconst hLc hBcomp hQ hSconst hslot hcap hEndpoint
  -- re-export the v2 collapsed Core carrier with the moment-wall trio supplied internally.
  exact QIQTH.TerminalCoverage.truncatedDuhamelCore_threaded_v2 g gi hChr hK S a b F hFeq
    t T hT U hUopen htU hUT hn hBoundaryLim hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas
    bnd hbdd hbound D0 D1 hD0 hD1 hbnd E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hEdom hFdom hFzero hIlo hIhi
    hEcomb A₀ A₁ hA₀ hA₁ hAdom hAzero hMeasFII hUfloor hInnerCont
    nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
    ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd
    hWDom hmass hmassone hmod hsup hUsub
    τc wA2 wF CF CA2c hwA2 hCA2c hwF hCF hεU hInter hAdom2cap hFdomW hmeas2Lo hSecCont hBcont
    Lc Bcomp Q Sconst hLc hBcomp hQ hSconst hslot hcap hEndpoint Cpair hCpair hGpow
    hInnerData
    nbP hnbP_open hnbP0 hProvP fderivBulk gderiv C₀ C₁ C₂ hGintP hbulkderiv hsliver hcont hfrozen_pd1

end QIQTH.MomentWallCoverage

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.MomentWallCoverage
#print axioms hslot_covered
#print axioms hGpow_covered
#print axioms truncatedDuhamelCore_threaded_v3
end AxiomChecks
