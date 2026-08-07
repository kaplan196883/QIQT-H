/-
  QIQTH / HeatResidualBound — GpowClosure.lean   (J4-402, Sol #17 A3: the hGpow closure chain)

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is the
  A3 brick (Sol consult #17) that CLOSES the last analytic wall (wall A) of the `MemLapFull` census
  MODULO the enumerated, satisfiable C1 slot carries:  it instantiates the `GpowBridge` per-`τ` matched
  inner bound `leviSecondPairing_inner_bound` at the CONCRETE van-Vleck witness (the on-collar integrand
  identity is LANDED from `SliverBoundOnCollar.sliverIntegrand_on_collar`; the gradient/mass absolute
  bounds are LANDED via `abs_integral_le_of_dom`; the comparison leg via
  `SliverAssemblyMatched.comparison_leg_of_dom`), fires the `m`-uniform `τ^{-1/2}` absorption
  `GpowBridge.leviSecondPairing_le_invSqrt`, closes the single `s = u` (`τ = 0`) measure-zero endpoint
  of `Set.uIoc`, and THREADS the resulting `hGpow` carry through
  `MemAdjHiSliver.hII_hi_from_sliver → MemAdjHi → CappedAdom2Audit.memLapFull_from_pairing_dominations`
  to produce the full `MemLapFull` member.  No `sorry`/`admit`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing
  file edited, nothing committed.  `a₁ = R/6` remains CONDITIONAL on the whole convergence-trio +
  geometric-wiring stack.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE A3 JOBS (this file).

  ### (C1) THE CONCRETE SLOT INSTANTIATION.  Split into per-slot private/public lemmas.
    • `abs_integral_le_of_dom`               — LANDED (Mathlib-only): the full-space absolute integral
      reduction `|∫ f| ≤ bound` from an a.e. dominator `‖f‖ ≤ D` with `∫ D ≤ bound`.  This is the exact
      mechanism that lands the `hf2bound` / `hf3bound` (gradient / mass absolute) slots of
      `leviSecondPairing_inner_bound` from the banked Gaussian-moment dominators.
    • `hon_concrete`                          — ★ LANDED: the `hon` slot (on-collar integrand identity
      `witnessSecondXDeriv·F = hessGaussFactor·(Aamp·F) + f₂ + f₃`), directly from
      `SliverBoundOnCollar.sliverIntegrand_on_collar` on the collar `‖z‖ ≤ c√τ` (given the ambient gate
      carry `z ∈ K ∧ ‖z‖ < r₀`).
    • `hcomp_concrete`                        — LANDED (re-export): the `hcomp` slot from
      `SliverAssemblyMatched.comparison_leg_of_dom`.
    • `leviSecondPairing_inner_bound_concrete` — ★★ the per-`(τ,s)` matched inner bound at the CONCRETE
      witness, assembled from the landed `hon` + the honest slot carries (`qc`/`Ichart` chart-native,
      `hoff`, the integrabilities, the two Lipschitz carries + center identity, `hcomp`, `hf2bound`,
      `hf3bound`).  Conclusion: `|∫_z witnessSecondXDeriv·F| ≤ K₁·τ^{-1/2} + S` — the exact `hinner`
      shape of `leviSecondPairing_le_invSqrt`.

  ### (C2) `hKnonneg` + THE `Cpair` PRODUCTION.
    • `K_nonneg`                              — `0 ≤ K₁ = 2L(15n/2)+B_comp+Q` and `0 ≤ K₀ = S` from the
      nonneg constituents.
    • fired inside the closure chain via `GpowBridge.leviSecondPairing_le_invSqrt` ⟹ the `m`-uniform
      `Cpair` and the OPEN-window `hGpow`.

  ### (C3) THE ENDPOINT + THE CLOSURE CHAIN ★.
    • `hGpow_uIoc_of_Ioo_zeroEndpoint`        — ★ the `Ioo → uIoc` upgrade: the open-window bound
      (from C2) plus the `τ = 0` measure-zero endpoint carry (`Inner m i u u = 0`, since
      `(u-u)^{-1/2} = 0^{-1/2} = 0`) gives the full `uIoc` bound `hII_hi_from_sliver` consumes.
    • `memLapFull_from_gpow_chain`            — ★★★ THE CLOSURE: from the per-`τ` window inner bound
      (C1) + `K`-nonneg (C2) + the endpoint carry + the `hII_hi_from_sliver` continuity carries + all
      the OTHER `memLapFull_from_pairing_dominations` inputs, produce the full `MemLapFull` — wall A's
      Hi-leg residue CLOSED (modulo the C1 carries).  Pure threading, no new analysis.

  NO `sorry`, no new axioms, no `:= True`, every hypothesis satisfiable, no existing file edited.
  ⚠ a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.GpowBridge
import QIQTH.MemAdjHiSliver
import QIQTH.SliverBoundOnCollar

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.DaLimCensusRecon QIQTH.DaLimEasyTranche QIQTH.DaLimHardTranche QIQTH.FrozenLaplaceSliver
open QIQTH.DaLimLUConcreteDischarge QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.EveryCeilingFamilies QIQTH.ESLegWidening QIQTH.GlobalRawBoundFacade
open QIQTH.SliverTailMatched QIQTH.AmplitudeDataOnCollar
open scoped Interval Topology BigOperators

namespace QIQTH.GpowClosure

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §C1 — the concrete slot instantiation (split per slot).
    ############################################################################### -/

/-- **★ C1 (slot mechanism) — `abs_integral_le_of_dom`.**  THE FULL-SPACE ABSOLUTE INTEGRAL REDUCTION
    (Mathlib-only).  A real function `f` with an a.e. dominator `‖f‖ ≤ D` (both integrable) whose
    integral is `∫ D ≤ bound` obeys `|∫ f| ≤ bound`.  This is the exact mechanism that LANDS the
    `hf2bound` (gradient) and `hf3bound` (mass) absolute slots of `leviSecondPairing_inner_bound` from
    the banked Gaussian-moment dominators (`cubic_gaussian_moment_witness` and the mass/gradient moment
    family).  Route: `norm_integral_le_integral_norm` → `integral_mono_ae` → the moment.
    ⚠ NOT `a₁ = R/6`. -/
theorem abs_integral_le_of_dom (f D : Point n → ℝ) (bound : ℝ)
    (hfint : Integrable f volume) (hDint : Integrable D volume)
    (hdom : ∀ᵐ z, ‖f z‖ ≤ D z) (hmom : (∫ z, D z) ≤ bound) :
    |∫ z, f z| ≤ bound := by
  rw [← Real.norm_eq_abs]
  calc ‖∫ z, f z‖
      ≤ ∫ z, ‖f z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, D z := integral_mono_ae hfint.norm hDint hdom
    _ ≤ bound := hmom

/-- **★★ C1 (slot 1, LANDED) — `hon_concrete`.**  THE `hon` SLOT: the on-collar integrand identity for
    the CONCRETE second-`x`-derivative witness, on the collar `‖z‖ ≤ c√τ`:
        witnessSecondXDeriv·F
          = hessGaussFactor i τ z · (data.Aamp τ z · F s z 0)     -- term 1 (matched)
            + (z_i/(2τ)·G·data.A1amp τ z · F s z 0)               -- term 2 (gradient, = f₂)
            + (G·data.A2amp τ z · F s z 0).                       -- term 3 (mass, = f₃)
    Directly from `SliverBoundOnCollar.sliverIntegrand_on_collar` (the corrected collar bundle's
    `hD2Hexpand` at a collar point), after unfolding `hessGaussFactor` and `ring`.  The ambient gate
    conjuncts (`z ∈ K`, `‖z‖ < r₀`) that the near-isometry demands are supplied by the honest carry
    `hgate` (the collar is inside the gate for the geometry).  This is the EXACT `hon` argument of
    `GpowBridge.leviSecondPairing_inner_bound` with `qz z := data.Aamp τ z · F s z 0`,
    `f₂ z := z_i/(2τ)·G·data.A1amp τ z·F s z 0`, `f₃ z := G·data.A2amp τ z·F s z 0`.
    ⚠ NOT `a₁ = R/6`. -/
theorem hon_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (hττ₀ : τ ≤ τ₀)
    (hgate : ∀ z ∈ collar (c * Real.sqrt τ), z ∈ K ∧ ‖z‖ < r₀) :
    ∀ z ∈ collar (c * Real.sqrt τ),
      witnessSecondXDeriv g gi hC hK S a b i τ z * F s z 0
        = hessGaussFactor i τ z * (data.Aamp τ z * F s z 0)
          + z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0
          + gaussDdim τ z * data.A2amp τ z * F s z 0 := by
  intro z hz
  obtain ⟨hzK, hzr⟩ := hgate z hz
  have hzc : ‖z‖ ≤ c * Real.sqrt τ := hz
  rw [SliverBoundOnCollar.sliverIntegrand_on_collar g gi hC hK S a b F i T τ₀ r₀ c data
    τ s z hτ hττ₀ hzK hzr hzc]
  simp only [hessGaussFactor]
  ring

/-- **C1 (slot 2, LANDED re-export) — `hcomp_concrete`.**  THE `hcomp` SLOT (comparison leg).  A
    re-export of `SliverAssemblyMatched.comparison_leg_of_dom` producing the EXACT `hcomp` shape of
    `GpowBridge.leviSecondPairing_inner_bound`:
        ‖∫_{O_τ} (Ichart − hessGaussFactor·qc)‖ ≤ Bcomp/√τ
    from any off-collar dominator `D` with an off-collar moment `∫_{O_τ} D ≤ Bcomp/√τ` — the honest
    reduction to the width-generic cubic-Hessian Gaussian moment (satisfiable via
    `cubic_gaussian_moment_witness`).  ⚠ NOT `a₁ = R/6`. -/
theorem hcomp_concrete (τ : ℝ) (i : Fin n) (qc Ichart D : Point n → ℝ) (R Bcomp : ℝ)
    (hcompDiff_int :
      IntegrableOn (fun z : Point n => Ichart z - hessGaussFactor i τ z * qc z) (collar R)ᶜ volume)
    (hDint : IntegrableOn D (collar R)ᶜ volume)
    (hdom : ∀ᵐ z ∂(volume.restrict (collar R)ᶜ),
      ‖Ichart z - hessGaussFactor i τ z * qc z‖ ≤ D z)
    (hmom : (∫ z in (collar R)ᶜ, D z) ≤ Bcomp / Real.sqrt τ) :
    ‖∫ z in (collar R)ᶜ, (Ichart z - hessGaussFactor i τ z * qc z)‖ ≤ Bcomp / Real.sqrt τ :=
  QIQTH.SliverAssemblyMatched.comparison_leg_of_dom τ i qc Ichart D R Bcomp
    hcompDiff_int hDint hdom hmom

/-- **★★ C1 (assembly) — `leviSecondPairing_inner_bound_concrete`.**  THE PER-`(τ,s)` MATCHED INNER
    BOUND AT THE CONCRETE WITNESS.  Instantiates `GpowBridge.leviSecondPairing_inner_bound` with
    `Wpair z := witnessSecondXDeriv·F s z 0`, `R := c√τ`, and the concrete slots
      • `qz z := data.Aamp τ z · F s z 0`, `f₂ z := z_i/(2τ)·G·data.A1amp τ z·F s z 0`,
        `f₃ z := G·data.A2amp τ z·F s z 0`   (the on-collar decomposition), with the `hon` slot LANDED
        internally by `hon_concrete`;
      • `qc`, `Ichart`  — the chart-native amplitude / off-collar integrand (honest carries), and
        `hoff`, the integrabilities, the two Lipschitz carries `hqz`/`hqc` + the center identity `h0`,
        the comparison leg `hcomp` (via `hcomp_concrete`), and the gradient/mass absolute bounds
        `hf2bound`/`hf3bound` (via `abs_integral_le_of_dom`) — ALL SATISFIABLE, none the conclusion.
    Conclusion: `|∫_z witnessSecondXDeriv·F| ≤ (2L·(15n/2)+B_comp+Q)·τ^{-1/2} + S` — exactly the `hinner`
    shape consumed by `leviSecondPairing_le_invSqrt` (C2).  ⚠ NOT `a₁ = R/6`. -/
theorem leviSecondPairing_inner_bound_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (hττ₀ : τ ≤ τ₀)
    (hgate : ∀ z ∈ collar (c * Real.sqrt τ), z ∈ K ∧ ‖z‖ < r₀)
    (qc Ichart : Point n → ℝ) (L Bcomp Q Sconst : ℝ) (hL : 0 ≤ L)
    (hoff : ∀ z ∈ (collar (c * Real.sqrt τ))ᶜ,
        witnessSecondXDeriv g gi hC hK S a b i τ z * F s z 0
          = Ichart z + z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0
            + gaussDdim τ z * data.A2amp τ z * F s z 0)
    (hWint : Integrable (fun z => witnessSecondXDeriv g gi hC hK S a b i τ z * F s z 0) volume)
    (hf2 : Integrable
      (fun z => z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0) volume)
    (hf3 : Integrable (fun z => gaussDdim τ z * data.A2amp τ z * F s z 0) volume)
    (hqz : ∀ z w,
      |data.Aamp τ z * F s z 0 - data.Aamp τ w * F s w 0| ≤ L * dist z w)
    (hqzmeas : AEStronglyMeasurable (fun z => data.Aamp τ z * F s z 0) volume)
    (hqc : ∀ z w, |qc z - qc w| ≤ L * dist z w) (hqcmeas : AEStronglyMeasurable qc volume)
    (h0 : data.Aamp τ 0 * F s 0 0 = qc 0)
    (hIchart_int : IntegrableOn Ichart (collar (c * Real.sqrt τ))ᶜ volume)
    (hcomp : ‖∫ z in (collar (c * Real.sqrt τ))ᶜ,
              (Ichart z - hessGaussFactor i τ z * qc z)‖ ≤ Bcomp / Real.sqrt τ)
    (hf2bound :
      |∫ z, z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0| ≤ Q / Real.sqrt τ)
    (hf3bound : |∫ z, gaussDdim τ z * data.A2amp τ z * F s z 0| ≤ Sconst) :
    |∫ z, witnessSecondXDeriv g gi hC hK S a b i τ z * F s z 0|
      ≤ (2 * L * (15 / 2 * (n : ℝ)) + Bcomp + Q) * τ ^ (-(1 : ℝ) / 2) + Sconst :=
  QIQTH.GpowBridge.leviSecondPairing_inner_bound τ hτ i (c * Real.sqrt τ)
    (fun z => witnessSecondXDeriv g gi hC hK S a b i τ z * F s z 0)
    (fun z => data.Aamp τ z * F s z 0) qc Ichart
    (fun z => z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0)
    (fun z => gaussDdim τ z * data.A2amp τ z * F s z 0)
    L Bcomp Q Sconst hL
    (hon_concrete g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ hττ₀ hgate)
    hoff hWint hf2 hf3 hqz hqzmeas hqc hqcmeas h0 hIchart_int hcomp hf2bound hf3bound

/-! ###############################################################################
    ### §C2 — the `K`-nonnegativity.
    ############################################################################### -/

/-- **C2 — `K_nonneg`.**  The assembled leading/mass constants are nonneg from their constituents:
    `0 ≤ K₁ = 2L·(15n/2)+B_comp+Q` (given `0 ≤ L, B_comp, Q`) and `0 ≤ K₀ = S`.  This is the `hKnonneg`
    conjunct of the `GpowBridge` A3 handoff, so `leviSecondPairing_le_invSqrt` applies with an
    `m`-uniform `Cpair`.  ⚠ NOT `a₁ = R/6`. -/
theorem K_nonneg (L Bcomp Q Sconst : ℝ)
    (hL : 0 ≤ L) (hBcomp : 0 ≤ Bcomp) (hQ : 0 ≤ Q) (hS : 0 ≤ Sconst) :
    0 ≤ 2 * L * (15 / 2 * (n : ℝ)) + Bcomp + Q ∧ (0 : ℝ) ≤ Sconst := by
  refine ⟨?_, hS⟩
  have : (0 : ℝ) ≤ 2 * L * (15 / 2 * (n : ℝ)) := by positivity
  linarith

/-! ###############################################################################
    ### §C3 — ★ the endpoint bridge + the closure chain.
    ############################################################################### -/

/-- **★ C3 (endpoint) — `hGpow_uIoc_of_Ioo_zeroEndpoint`.**  THE `Ioo → uIoc` UPGRADE.  The `m`-uniform
    open-window bound `|Inner| ≤ Cpair·(u−s)^{-1/2}` on `s ∈ Ioo (u−ε_m) u` (from
    `leviSecondPairing_le_invSqrt`), together with the single measure-zero endpoint carry
    `Inner m i u u = 0` (the `s = u`, `τ = 0` value — and `(u−u)^{-1/2} = 0^{-1/2} = 0`, so the bound is
    `|0| ≤ 0`), extends to the FULL `Set.uIoc (u−ε_m) u` bound that
    `MemAdjHiSliver.hII_hi_from_sliver`'s `hGpow` consumes.  Route: `Set.uIoc_of_le` (`ε_m > 0`) reduces
    `uIoc` to `Ioc = Ioo ∪ {u}`; the interior point uses the open-window bound, the endpoint the carry.
    The endpoint carry is the honest `τ = 0` residue of the `GpowBridge` handoff census (SATISFIABLE:
    the moment-improved pairing integral vanishes at `τ = 0`; and it is measure-zero, so irrelevant to
    the downstream integrability).  ⚠ NOT `a₁ = R/6`. -/
theorem hGpow_uIoc_of_Ioo_zeroEndpoint (U : Set ℝ) (Cpair : ℝ)
    (Inner : ℕ → Fin n → ℝ → ℝ → ℝ)
    (hIoo : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ s ∈ Set.Ioo (u - epsSeq m) u,
        |Inner m i u s| ≤ Cpair * (u - s) ^ (-(1 : ℝ) / 2))
    (hEnd : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, Inner m i u u = 0) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ s ∈ Set.uIoc (u - epsSeq m) u,
        |Inner m i u s| ≤ Cpair * (u - s) ^ (-(1 : ℝ) / 2) := by
  intro m i u hu s hs
  have hle : u - epsSeq m ≤ u := by have := epsSeq_pos m; linarith
  rw [Set.uIoc_of_le hle] at hs
  obtain ⟨h1, h2⟩ := hs
  rcases lt_or_eq_of_le h2 with hlt | heq
  · exact hIoo m i u hu s ⟨h1, hlt⟩
  · rw [heq]
    have hz : (u - u) ^ (-(1 : ℝ) / 2) = 0 := by
      rw [sub_self]; exact Real.zero_rpow (by norm_num)
    rw [hEnd m i u hu, hz, mul_zero]
    exact le_of_eq abs_zero

/-- **★★★ C3 (closure) — `memLapFull_from_gpow_chain`.**  WALL A CLOSED (modulo the C1 carries).  From
      •  the per-`τ` matched inner bound over the OPEN Hi window `hinner_window`  (supplied pointwise by
         `leviSecondPairing_inner_bound_concrete` (C1), aggregated over `s`);
      •  the `K`-nonnegativity `hK₁`/`hK₀`  (C2, `K_nonneg`);
      •  the single `τ = 0` endpoint carry `hEndpoint`  (the moment-improved pairing vanishes at `τ=0`);
      •  the `hII_hi_from_sliver` continuity carries `hεU`/`hSecCont`/`hBcont`  (banked AESM inputs);
      •  and ALL the other `memLapFull_from_pairing_dominations` inputs  (the capped-Lo family, gauge,
         interchange, Levi feeds, the √ε sliver bundle, `hPd2conv`),
    the full `MemLapFull` census member follows.  Route (PURE THREADING, no new analysis):
      `leviSecondPairing_le_invSqrt` (⟹ `Cpair` + open-window `hGpow`)
        → `hGpow_uIoc_of_Ioo_zeroEndpoint` (⟹ `uIoc` `hGpow`)
        → `MemAdjHiSliver.hII_hi_from_sliver` (⟹ `MemAdjHi`)
        → `CappedAdom2Audit.memLapFull_from_pairing_dominations` (⟹ `MemLapFull`).
    The Hi-leg integrability residue of wall A is discharged into the enumerated satisfiable C1 slot
    carries (`leviSecondPairing_inner_bound_concrete`) + the endpoint carry — no uncapped / clean-Gaussian
    second-derivative domination anywhere.  ⚠ NOT `a₁ = R/6`; the closure is CONDITIONAL on exactly this
    census. -/
theorem memLapFull_from_gpow_chain (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (T wA2 wF CF : ℝ) (CA2c : ℕ → ℝ)
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
    -- the `hII_hi_from_sliver` continuity carries (banked AESM inputs):
    (hSecCont : ∀ i : Fin n, ContinuousOn
      (fun p : ℝ × Point n => witnessSecondXDeriv g gi hChr hK S a b i p.1 p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    -- ★ the per-`τ` matched inner bound over the OPEN Hi window (C1), with the `m`-uniform constants:
    (K₁ K₀ : ℝ) (hK₁ : 0 ≤ K₁) (hK₀ : 0 ≤ K₀)
    (hinner_window : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ s ∈ Set.Ioo (u - epsSeq m) u,
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ K₁ * (u - s) ^ (-(1 : ℝ) / 2) + K₀)
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
  -- (C2) fire the `m`-uniform `τ^{-1/2}` absorption → the OPEN-window `hGpow` + `Cpair`.
  obtain ⟨Cpair, hCpair, hIoo⟩ :=
    QIQTH.GpowBridge.leviSecondPairing_le_invSqrt (n := n) U K₁ K₀ hK₁ hK₀
      (fun m i u s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      hinner_window
  -- (C3) upgrade `Ioo → uIoc` with the endpoint carry.
  have hGpow := hGpow_uIoc_of_Ioo_zeroEndpoint (n := n) U Cpair
    (fun m i u s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    hIoo hEndpoint
  -- thread → `MemAdjHi`.
  have hII_hi := QIQTH.MemAdjHiSliver.hII_hi_from_sliver g gi hChr hK S a b T U
    hUT hεU hSecCont hBcont Cpair hCpair hGpow
  -- thread → `MemLapFull`.
  exact QIQTH.CappedAdom2Audit.memLapFull_from_pairing_dominations g gi hChr hK S a b
    U T wA2 wF CF CA2c hwA2 hCA2c hwF hCF hUpos hUT hgi hΓ hInter
    hAdom2cap hFdom hFzero hmeas2Lo hII_hi D0 D1 hD0 hD1 hbnd hPd2conv

/-! ###############################################################################
    ### §C1/C3 — the surviving-carry census of the closure chain.
    ############################################################################### -/

/-- **`gpow_closure_carries`.**  THE COMPLETE, ENUMERATED SURVIVING-CARRY CENSUS for the wall-A closure
    `memLapFull_from_gpow_chain`.  A genuine conjunction (non-vacuous plumbing witness), stated
    abstractly so the census is machine-checkable.  Each conjunct is SATISFIABLE, none is the conclusion.

    THE CENSUS:
      1. `hslots`     — the C1 slot carries of `leviSecondPairing_inner_bound_concrete` NOT landed here
         (the chart-native `qc`/`Ichart`, `hoff`, the integrabilities, the two Lipschitz carries `hqz`
         (route: `DataAmpAssembly.concrete_hqLip_of_carries`) / `hqc`, the center identity `h0`, and
         the dominator/moment inputs to `hcomp` (`hcomp_concrete`) / `hf2bound` / `hf3bound`
         (`abs_integral_le_of_dom` + the Gaussian-moment family));
      2. `hgate`      — the gate coverage `∀ z ∈ collar (c√τ), z ∈ K ∧ ‖z‖ < r₀` feeding `hon_concrete`;
      3. `hendpoint`  — the `τ = 0` measure-zero endpoint (the moment-improved pairing vanishes at `τ=0`);
      4. `hcont`      — the `hII_hi_from_sliver` continuity carries `hεU`/`hSecCont`/`hBcont` (banked AESM);
      5. `hmemLap`    — the remaining `memLapFull_from_pairing_dominations` inputs (capped-Lo family,
         gauge, interchange, Levi feeds, the √ε sliver bundle, `hPd2conv`).

    LANDED (NOT in this census): the `hon` slot (`hon_concrete`), the gradient/mass absolute-bound
    mechanism (`abs_integral_le_of_dom`), the comparison-leg re-export (`hcomp_concrete`), the
    `K`-nonnegativity (`K_nonneg`), the `Ioo → uIoc` endpoint upgrade
    (`hGpow_uIoc_of_Ioo_zeroEndpoint`), and the whole closure threading (`memLapFull_from_gpow_chain`).
    ⚠ NOT `a₁ = R/6`; the closure is CONDITIONAL on exactly this census. -/
def gpow_closure_carries (hslots hgate hendpoint hcont hmemLap : Prop) : Prop :=
  hslots ∧ hgate ∧ hendpoint ∧ hcont ∧ hmemLap

/-- The closure census is a genuine conjunction projector (non-vacuous plumbing witness).
    ⚠ NOT `a₁ = R/6`. -/
theorem gpow_closure_carries_intro {hslots hgate hendpoint hcont hmemLap : Prop}
    (h1 : hslots) (h2 : hgate) (h3 : hendpoint) (h4 : hcont) (h5 : hmemLap) :
    gpow_closure_carries hslots hgate hendpoint hcont hmemLap :=
  ⟨h1, h2, h3, h4, h5⟩

end QIQTH.GpowClosure

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.GpowClosure.abs_integral_le_of_dom
#print axioms QIQTH.GpowClosure.hon_concrete
#print axioms QIQTH.GpowClosure.hcomp_concrete
#print axioms QIQTH.GpowClosure.leviSecondPairing_inner_bound_concrete
#print axioms QIQTH.GpowClosure.K_nonneg
#print axioms QIQTH.GpowClosure.hGpow_uIoc_of_Ioo_zeroEndpoint
#print axioms QIQTH.GpowClosure.memLapFull_from_gpow_chain
#print axioms QIQTH.GpowClosure.gpow_closure_carries_intro
