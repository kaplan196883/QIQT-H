/-
  QIQTH / HeatResidualBound — SlotDischarges.lean   (J4-403: wall-A slot discharges + ∀-s aggregation)

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is the
  J4-403 brick that discharges the per-slot carries of `GpowClosure.leviSecondPairing_inner_bound_concrete`
  at the concrete van-Vleck witness (from the banked suppliers), and — the ★ deliverable — AGGREGATES the
  per-`(τ,s)` matched inner bound over the open Hi window `s ∈ Ioo (u−εₘ) u` into the EXACT
  `hinner_window` hypothesis shape consumed by `GpowClosure.memLapFull_from_gpow_chain` (the J4-401/402
  wall-A capstone).  ⚠ THE QUANTIFIER TRAP is resolved: the slot constants `L, Bcomp, Q, Sconst` are
  bound as TOP-LEVEL parameters (before the `m, s` binders) and the per-`τ` bound is quantified over ALL
  `0 < τ ≤ τ₀` (NOT over `m`), so the produced `K₁ = 2L·(15n/2)+Bcomp+Q` and `K₀ = Sconst` carry NO
  `εₘ`-dependence.  No `sorry`/`admit`, no new axioms, no `:= True`, every hypothesis satisfiable, no
  existing file edited, nothing committed, not wired into `QIQTH.lean` / `AxiomAudit.lean`.
  `a₁ = R/6` remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE J4-403 JOBS (this file).

  ### (S1) THE PER-SLOT DISCHARGES.  Split per slot, from the banked suppliers.
    • `hqz_slot_of_data`      — the `hqz` (term-1 product Lipschitz) slot ← `data.hqLip` (`L := data.L`),
      the assembled increment of `DataAmpAssembly.concrete_hqLip_of_carries`.
    • `hqzmeas_slot_of_data`  — the `hqzmeas` slot ← `data.hAampmeas · data.hFmeas`.
    • `hgate_of_collarRegime_cover` — the `hgate` slot ← the `collarRegime` coverage of the collar
      (the `z ∈ K ∧ ‖z‖ < r₀` conjuncts, the collar wrappers of `AmpGeometryBundle`).
    • `h0_slot_of_center`     — the `h0` centre-match slot ← `AmpGeometryBundle.rhoRatio_center`
      (`ρ(τ,0)=1`) + the concrete amplitude value (`chart_center_amp_match` shape).
    • `hf2bound_slot_of_dom`  — the `hf2bound` (gradient absolute) slot ← `GpowClosure.abs_integral_le_of_dom`.
    • `hf3bound_slot_of_dom`  — the `hf3bound` (mass absolute) slot ← `GpowClosure.abs_integral_le_of_dom`.
    • `hcomp_slot_of_dom`     — the `hcomp` (comparison-leg) slot ← `GpowClosure.hcomp_concrete`.

  ### (S2) THE ∀-s AGGREGATION ★.
    • `hinner_window_of_slotBound` — aggregates the per-`τ` inner bound (`hslot`, over ALL `0 < τ ≤ τ₀`)
      into the EXACT `hinner_window` shape of `memLapFull_from_gpow_chain`, with the `m`-uniform
      constants `K₁ = 2L·(15n/2)+Bcomp+Q`, `K₀ = Sconst`.  Route: `intro m i u s`, `window_tau_pos_lt`
      (`0 < u−s`), the window-cap carry `hcap` (`u−s ≤ τ₀`), then `hslot` at `τ = u−s`.  NO `εₘ` leakage.

  ### (S3) THE COMPOSED CLOSURE.
    • `memLapFull_from_slotBound` — threads S2 into `GpowClosure.memLapFull_from_gpow_chain`, producing the
      full `MemLapFull` member with the wall-A inner-bound carry REDUCED to the honest residuals
      `{hslot, hcap, hEndpoint, the census continuity/Levi/gauge/sliver carries}`.

  ### CENSUS.  `slot_discharge_residuals` — the enumerated surviving residuals after S1–S3.

  NO `sorry`, no new axioms, no `:= True`, every hypothesis satisfiable, no existing file edited.
  ⚠ a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.GpowClosure
import QIQTH.AmpGeometryBundle
import QIQTH.DataAmpAssembly
import QIQTH.SliverAssemblyMatched

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.DaLimCensusRecon QIQTH.DaLimEasyTranche QIQTH.DaLimHardTranche QIQTH.FrozenLaplaceSliver
open QIQTH.DaLimLUConcreteDischarge QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.EveryCeilingFamilies QIQTH.ESLegWidening QIQTH.GlobalRawBoundFacade
open QIQTH.SliverTailMatched QIQTH.AmplitudeDataOnCollar QIQTH.HrepGermFactorization
open QIQTH.AmpGeometryBundle QIQTH.DataAmpAssembly
open scoped Interval Topology BigOperators

namespace QIQTH.SlotDischarges

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §S1 — the per-slot discharges (split per slot).
    ############################################################################### -/

/-- **★ S1 (slot `hqz`) — `hqz_slot_of_data`.**  THE TERM-1 PRODUCT LIPSCHITZ SLOT, discharged from the
    `hqLip` field of the corrected collar bundle.  For `τ ∈ Ioo 0 τ₀` and `s ∈ (0, T]`, the ρ-scaled
    chart-amplitude · Levi product obeys the increment `|Aamp τ z·F s z 0 − Aamp τ w·F s w 0| ≤
    data.L·dist z w` — verbatim the `hqz` argument of `leviSecondPairing_inner_bound_concrete` with
    `L := data.L`.  This is the field the E3 assembly (`DataAmpAssembly.concrete_hqLip_of_carries`)
    produces.  ⚠ NOT `a₁ = R/6`. -/
theorem hqz_slot_of_data (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) 0 0 τ₀))
    (τ : ℝ) (hτ : τ ∈ Set.Ioo (0 : ℝ) τ₀) (s : ℝ) (hs0 : 0 < s) (hsT : s ≤ T) :
    ∀ z w : Point n,
      |data.Aamp τ z * F s z 0 - data.Aamp τ w * F s w 0| ≤ data.L * dist z w :=
  data.hqLip τ hτ s hs0 hsT

/-- **★ S1 (slot `hqzmeas`) — `hqzmeas_slot_of_data`.**  THE TERM-1 PRODUCT MEASURABILITY SLOT.  The
    ρ-scaled chart amplitude `Aamp τ ·` and the Levi kernel `F s · 0` are each a.e.-strongly measurable
    (banked `data` fields), so their product is — the `hqzmeas` argument of
    `leviSecondPairing_inner_bound_concrete`.  ⚠ NOT `a₁ = R/6`. -/
theorem hqzmeas_slot_of_data (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) 0 0 τ₀))
    (τ s : ℝ) :
    AEStronglyMeasurable (fun z : Point n => data.Aamp τ z * F s z 0) volume :=
  (data.hAampmeas τ).mul (data.hFmeas s)

/-- **★ S1 (slot `hgate`) — `hgate_of_collarRegime_cover`.**  THE GATE-SUPPORT SLOT.  Given that every
    collar point `z ∈ collar (c√τ)` lies in the `collarRegime`, the two chart-domain conjuncts
    (`z ∈ K` and `‖z‖ < r₀`) that the near-isometry demands hold on the whole collar — verbatim the
    `hgate` argument of `hon_concrete` / `leviSecondPairing_inner_bound_concrete`.  Route (WRAPPER): the
    `collarRegime` projections (`AmpGeometryBundle.collarRegime_radial_control` shape).  The
    `collarRegime`-coverage carry is honest (the collar sits inside the bounded gate ball for the
    geometry).  ⚠ NOT `a₁ = R/6`. -/
theorem hgate_of_collarRegime_cover {K : Set (Point n)} (r₀ c τ₀ τ : ℝ)
    (hcover : ∀ z ∈ collar (c * Real.sqrt τ), collarRegime (K := K) r₀ c τ₀ τ z) :
    ∀ z ∈ collar (c * Real.sqrt τ), z ∈ K ∧ ‖z‖ < r₀ := by
  intro z hz
  obtain ⟨_, _, hzK, hzr, _⟩ := hcover z hz
  exact ⟨hzK, hzr⟩

/-- **★★ S1 (slot `h0`) — `h0_slot_of_center`.**  THE CENTRE-MATCH SLOT `qz 0 = qc 0`.  At the
    integration centre `z = 0` the ρ-scaled chart amplitude collapses (`ρ(τ,0) = 1`, `rhoRatio_center`),
    so the term-1 amplitude `data.Aamp τ 0 · F s 0 0` — given the concrete amplitude value
    `data.Aamp τ 0 = ρ(τ,0)·chartAmp … 0` (`rfl` for `amplitudeDataOn_concrete`) — equals the chart-native
    comparison amplitude `qc 0`, whenever `qc 0 = chartAmp … 0 · F s 0 0`.  This is the exact `h0`
    argument of `leviSecondPairing_inner_bound_concrete`.  Suppliers: `AmpGeometryBundle.rhoRatio_center`
    (`ρ(τ,0)=1`) + the concrete `Aamp` field.  ⚠ NOT `a₁ = R/6`. -/
theorem h0_slot_of_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K)
    (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) 0 0 τ₀))
    (τ s : ℝ) (qc : Point n → ℝ)
    (hAampval : data.Aamp τ 0 = rhoRatio g gi hC hK τ 0 * chartAmp g gi hC hK a b τ 0 0)
    (hqc0 : qc 0 = chartAmp g gi hC hK a b τ 0 0 * F s 0 0) :
    data.Aamp τ 0 * F s 0 0 = qc 0 := by
  rw [hAampval, rhoRatio_center g gi hC hK h0K τ, one_mul, hqc0]

/-- **★ S1 (slot `hf2bound`) — `hf2bound_slot_of_dom`.**  THE GRADIENT ABSOLUTE SLOT.  The term-2 integral
    `∫_z z_i/(2τ)·G·A1amp·F` obeys `|·| ≤ Q/√τ` from an a.e. dominator `‖·‖ ≤ D` with `∫ D ≤ Q/√τ` — the
    `hf2bound` argument, via the LANDED full-space reduction `GpowClosure.abs_integral_le_of_dom`
    (dominator satisfiable by the cubic/gradient Gaussian-moment family,
    `SliverAssemblyMatched.cubic_gaussian_moment_witness`).  ⚠ NOT `a₁ = R/6`. -/
theorem hf2bound_slot_of_dom (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) 0 0 τ₀))
    (τ s Q : ℝ) (D : Point n → ℝ)
    (hfint : Integrable
      (fun z => z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0) volume)
    (hDint : Integrable D volume)
    (hdom : ∀ᵐ z,
      ‖z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0‖ ≤ D z)
    (hmom : (∫ z, D z) ≤ Q / Real.sqrt τ) :
    |∫ z, z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0| ≤ Q / Real.sqrt τ :=
  QIQTH.GpowClosure.abs_integral_le_of_dom _ D (Q / Real.sqrt τ) hfint hDint hdom hmom

/-- **★ S1 (slot `hf3bound`) — `hf3bound_slot_of_dom`.**  THE MASS ABSOLUTE SLOT.  The term-3 integral
    `∫_z G·A2amp·F` obeys `|·| ≤ Sconst` from an a.e. dominator `‖·‖ ≤ D` with `∫ D ≤ Sconst` — the
    `hf3bound` argument, via `GpowClosure.abs_integral_le_of_dom` (dominator satisfiable by the mass
    Gaussian-moment family).  ⚠ NOT `a₁ = R/6`. -/
theorem hf3bound_slot_of_dom (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) 0 0 τ₀))
    (τ s Sconst : ℝ) (D : Point n → ℝ)
    (hfint : Integrable (fun z => gaussDdim τ z * data.A2amp τ z * F s z 0) volume)
    (hDint : Integrable D volume)
    (hdom : ∀ᵐ z, ‖gaussDdim τ z * data.A2amp τ z * F s z 0‖ ≤ D z)
    (hmom : (∫ z, D z) ≤ Sconst) :
    |∫ z, gaussDdim τ z * data.A2amp τ z * F s z 0| ≤ Sconst :=
  QIQTH.GpowClosure.abs_integral_le_of_dom _ D Sconst hfint hDint hdom hmom

/-- **★ S1 (slot `hcomp`) — `hcomp_slot_of_dom`.**  THE COMPARISON-LEG SLOT (matched Hessian tail).  The
    off-collar comparison integral obeys `‖∫_{O_τ}(Ichart − hess·qc)‖ ≤ Bcomp/√τ` from an off-collar
    dominator with an off-collar moment — the `hcomp` argument, re-exported from
    `GpowClosure.hcomp_concrete` at the concrete collar radius `R := c√τ` (moment satisfiable via
    `cubic_gaussian_moment_witness`).  ⚠ NOT `a₁ = R/6`. -/
theorem hcomp_slot_of_dom (τ : ℝ) (i : Fin n) (qc Ichart D : Point n → ℝ) (c Bcomp : ℝ)
    (hcompDiff_int :
      IntegrableOn (fun z : Point n => Ichart z - hessGaussFactor i τ z * qc z)
        (collar (c * Real.sqrt τ))ᶜ volume)
    (hDint : IntegrableOn D (collar (c * Real.sqrt τ))ᶜ volume)
    (hdom : ∀ᵐ z ∂(volume.restrict (collar (c * Real.sqrt τ))ᶜ),
      ‖Ichart z - hessGaussFactor i τ z * qc z‖ ≤ D z)
    (hmom : (∫ z in (collar (c * Real.sqrt τ))ᶜ, D z) ≤ Bcomp / Real.sqrt τ) :
    ‖∫ z in (collar (c * Real.sqrt τ))ᶜ, (Ichart z - hessGaussFactor i τ z * qc z)‖
      ≤ Bcomp / Real.sqrt τ :=
  QIQTH.GpowClosure.hcomp_concrete τ i qc Ichart D (c * Real.sqrt τ) Bcomp
    hcompDiff_int hDint hdom hmom

/-! ###############################################################################
    ### §S2 — ★ the ∀-s aggregation into the `hinner_window` shape.
    ############################################################################### -/

/-- **★★ S2 — `hinner_window_of_slotBound`.**  THE ∀-s AGGREGATION.  Given the per-`τ` matched inner
    bound `hslot` — quantified over ALL `(i, τ, s)` with `0 < τ ≤ τ₀`, in the CONCRETE
    `(2L·(15n/2)+Bcomp+Q)·τ^{−1/2}+Sconst` shape (supplied pointwise by
    `GpowClosure.leviSecondPairing_inner_bound_concrete`) — and the window-cap carry `hcap`
    (`u−s ≤ τ₀` on every open Hi window), the exact `hinner_window` hypothesis of
    `GpowClosure.memLapFull_from_gpow_chain` follows with the `m`-uniform constants
      `K₁ = 2L·(15n/2)+Bcomp+Q`,   `K₀ = Sconst`.

    ⚠ THE QUANTIFIER TRAP (resolved).  `L, Bcomp, Q, Sconst` are TOP-LEVEL parameters, bound BEFORE the
    `m, s` binders; `hslot` is quantified over ALL `τ` (NOT over `m`).  Route: `intro m i u s`,
    `GpowBridge.window_tau_pos_lt` (`0 < u−s`), `hcap` (`u−s ≤ τ₀`), `hslot i (u−s) s`.  NO `εₘ`
    ever enters `K₁`/`K₀`.  ⚠ NOT `a₁ = R/6`. -/
theorem hinner_window_of_slotBound (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (τ₀ : ℝ) (L Bcomp Q Sconst : ℝ)
    (hslot : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τ₀ →
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i τ z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ (2 * L * (15 / 2 * (n : ℝ)) + Bcomp + Q) * τ ^ (-(1 : ℝ) / 2) + Sconst)
    (hcap : ∀ (m : ℕ), ∀ u ∈ U, ∀ s ∈ Set.Ioo (u - epsSeq m) u, u - s ≤ τ₀) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ s ∈ Set.Ioo (u - epsSeq m) u,
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ (2 * L * (15 / 2 * (n : ℝ)) + Bcomp + Q) * (u - s) ^ (-(1 : ℝ) / 2) + Sconst := by
  intro m i u hu s hs
  obtain ⟨hτpos, _⟩ := QIQTH.GpowBridge.window_tau_pos_lt m u s hs
  exact hslot i (u - s) s hτpos (hcap m u hu s hs)

/-! ###############################################################################
    ### §S3 — the composed closure (thread S2 into the wall-A capstone).
    ############################################################################### -/

/-- **★★★ S3 — `memLapFull_from_slotBound`.**  THE COMPOSED WALL-A CLOSURE.  Threads the ∀-s aggregation
    `hinner_window_of_slotBound` (S2) into `GpowClosure.memLapFull_from_gpow_chain`, producing the full
    `MemLapFull` census member with the wall-A inner-bound carry REDUCED to `{hslot, hcap}` plus the
    unchanged census carries (endpoint, continuity, Levi/gauge feeds, the √ε sliver bundle, `hPd2conv`).
    Pure threading, no new analysis: `hinner_window_of_slotBound` (⟹ `hinner_window`) →
    `memLapFull_from_gpow_chain`.  ⚠ NOT `a₁ = R/6`; CONDITIONAL on exactly this census. -/
theorem memLapFull_from_slotBound (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (T τ₀ wA2 wF CF : ℝ) (CA2c : ℕ → ℝ)
    (hwA2 : 0 < wA2) (hCA2c : ∀ m, 0 ≤ CA2c m) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (hgi : MemGaugeGi (n := n) gi) (hΓ : MemGaugeGamma (n := n) g gi)
    (hInter : MemInterchange (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (hAdom2cap : ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA2c m * gaussDdim (wA2 * τ) (0 - z))
    (hFdom : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ CF * gaussDdim (wF * s) z)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0)
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
    -- ★ the per-`τ` matched inner bound (S1/§C1), over ALL `0 < τ ≤ τ₀`, `m`-uniform constants:
    (L Bcomp Q Sconst : ℝ) (hL : 0 ≤ L) (hBcomp : 0 ≤ Bcomp) (hQ : 0 ≤ Q) (hSconst : 0 ≤ Sconst)
    (hslot : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τ₀ →
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i τ z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ (2 * L * (15 / 2 * (n : ℝ)) + Bcomp + Q) * τ ^ (-(1 : ℝ) / 2) + Sconst)
    (hcap : ∀ (m : ℕ), ∀ u ∈ U, ∀ s ∈ Set.Ioo (u - epsSeq m) u, u - s ≤ τ₀)
    -- the single `τ = 0` endpoint carry (measure-zero; the moment-improved pairing vanishes):
    (hEndpoint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - u) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) u z 0 = 0)
    -- the √ε sliver amplitude bundle:
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (hPd2conv : ∀ u ∈ U, ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
              (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u x 0) i y) i 0))) :
    MemLapFull g gi (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
      (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) := by
  -- (S2) aggregate the per-`τ` bound into the OPEN-window `hinner_window`.
  have hinner_window := hinner_window_of_slotBound g gi hChr hK S a b U τ₀ L Bcomp Q Sconst hslot hcap
  -- the `m`-uniform `K`-nonnegativity.
  have hK₁ : (0 : ℝ) ≤ 2 * L * (15 / 2 * (n : ℝ)) + Bcomp + Q := by
    have : (0 : ℝ) ≤ 2 * L * (15 / 2 * (n : ℝ)) := by positivity
    linarith
  -- (S3) thread → `MemLapFull`.
  exact QIQTH.GpowClosure.memLapFull_from_gpow_chain g gi hChr hK S a b U T wA2 wF CF CA2c
    hwA2 hCA2c hwF hCF hUpos hUT hεU hgi hΓ hInter hAdom2cap hFdom hFzero hmeas2Lo hSecCont hBcont
    (2 * L * (15 / 2 * (n : ℝ)) + Bcomp + Q) Sconst hK₁ hSconst hinner_window hEndpoint
    D0 D1 hD0 hD1 hbnd hPd2conv

/-! ###############################################################################
    ### §census — the surviving residuals after S1–S3.
    ############################################################################### -/

/-- **`slot_discharge_residuals`.**  THE ENUMERATED SURVIVING RESIDUALS after the J4-403 slot discharges
    + aggregation + composed closure.  A genuine conjunction (non-vacuous plumbing witness), stated
    abstractly so the census is machine-checkable.  Each conjunct is SATISFIABLE, none is the conclusion.

    THE RESIDUAL (feeding `memLapFull_from_slotBound`):
      1. `hslot`      — the per-`τ` matched inner bound over ALL `0 < τ ≤ τ₀` (assembled per-`(τ,s)` by
         `GpowClosure.leviSecondPairing_inner_bound_concrete` from the S1 slot discharges + the
         chart-native `qc`/`Ichart` + the honest dominator/moment inputs);
      2. `hcap`       — the window-cap `u − s ≤ τ₀` on every open Hi window (satisfiable: `epsSeq 0 ≤ τ₀`);
      3. `hendpoint`  — the `τ = 0` measure-zero endpoint (the moment-improved pairing vanishes at `τ=0`);
      4. `hcensus`    — the remaining `memLapFull_from_gpow_chain` inputs (continuity carries, capped-Lo
         family, gauge, interchange, Levi feeds, the √ε sliver bundle, `hPd2conv`).

    DISCHARGED by S1/S2/S3 (NOT in this census): the term-1 Lipschitz/measurability (`hqz`/`hqzmeas`), the
    gate support (`hgate`), the centre match (`h0`), the gradient/mass absolute mechanisms
    (`hf2bound`/`hf3bound`), the comparison-leg (`hcomp`), the ∀-s aggregation into `hinner_window`
    (`hinner_window_of_slotBound`), and the whole composed closure (`memLapFull_from_slotBound`).
    ⚠ NOT `a₁ = R/6`; the closure is CONDITIONAL on exactly this census. -/
def slot_discharge_residuals (hslot hcap hendpoint hcensus : Prop) : Prop :=
  hslot ∧ hcap ∧ hendpoint ∧ hcensus

/-- The residual census is a genuine conjunction projector (non-vacuous plumbing witness).
    ⚠ NOT `a₁ = R/6`. -/
theorem slot_discharge_residuals_intro {hslot hcap hendpoint hcensus : Prop}
    (h1 : hslot) (h2 : hcap) (h3 : hendpoint) (h4 : hcensus) :
    slot_discharge_residuals hslot hcap hendpoint hcensus :=
  ⟨h1, h2, h3, h4⟩

end QIQTH.SlotDischarges

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.SlotDischarges.hqz_slot_of_data
#print axioms QIQTH.SlotDischarges.hqzmeas_slot_of_data
#print axioms QIQTH.SlotDischarges.hgate_of_collarRegime_cover
#print axioms QIQTH.SlotDischarges.h0_slot_of_center
#print axioms QIQTH.SlotDischarges.hf2bound_slot_of_dom
#print axioms QIQTH.SlotDischarges.hf3bound_slot_of_dom
#print axioms QIQTH.SlotDischarges.hcomp_slot_of_dom
#print axioms QIQTH.SlotDischarges.hinner_window_of_slotBound
#print axioms QIQTH.SlotDischarges.memLapFull_from_slotBound
#print axioms QIQTH.SlotDischarges.slot_discharge_residuals_intro
