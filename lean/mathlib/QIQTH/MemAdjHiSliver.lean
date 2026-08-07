/-
  MemAdjHiSliver — J4-392: the `MemAdjHi` Hi-leg integrability, the ONE irreducible residual of
  wall A (per the J4-391 decisive audit `CappedAdom2Audit.memLapFull_from_pairing_dominations`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It supplies
  an HONEST integrability reduction for the `MemAdjHi` Hi adjacency leg (`[u−ε_m, u]`, `τ = u−s → 0`)
  from banked AEStronglyMeasurability (`SliceMeasurability.hmeas2Hi_slice`) PLUS one NAMED, SATISFIABLE
  moment-improved carry — the `τ^{-1/2}` pairing bound `hGpow`.  No `sorry`/`admit`, no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the
  conclusion, no existing file edited, nothing committed.  `a₁ = R/6` remains CONDITIONAL on the whole
  convergence-trio + geometric-wiring stack.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE DEMAND MAP (`MemAdjHi`, `DaLimLUWallRecon.MemAdjHi`).

      MemAdjHi F U pdpdH  :=  ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ z, pdpdH i (u − s) z * F s z 0) volume (u − ε_m) u,

  instantiated at `F := leviSeries (heatOp g gi H_G)`, `pdpdH := witnessSecondXDeriv …`, `H_G :=
  vanVleckGatedWitness …`.  On the Hi window `s ∈ (u−ε_m, u)` the first factor is evaluated at
  `τ = u − s ∈ (0, ε_m)` — NOT bounded below (`τ → 0`).

  ## WHY THE NAIVE ROUTES FAIL (the J4-391 verdict, restated).
  The clean `τ`-uniform Gaussian domination `|witnessSecondXDeriv i τ z| ≤ CA·gaussDdim (wA·τ) (0−z)`
  (with a SINGLE `τ`-uniform `CA`) — the hypothesis of `DaLimEasyTranche.hII_hi_concrete` — is GENERALLY
  FALSE for the true second `x`-derivative of a heat kernel (the `τ⁻¹` blow-up at `z = 0`).  The ONLY
  valid pointwise consequence is the crude `C·τ⁻¹·gaussDdim (wA·τ)` bank, which even after the Gaussian
  `z`-pairing leaves an `∫z |…| ≤ C·τ⁻¹` profile, and `∫₀^{ε_m} τ⁻¹ dτ = +∞`.  So `MemAdjHi` is NOT
  dischargeable from any pointwise SECOND-DERIVATIVE domination.

  ## THE HONEST ROUTE (this file — route 2, the moment-improved pairing power).
  The SIGNED `z`-integral of the SECOND-derivative pairing enjoys the standard heat-kernel moment
  cancellation: `∫z ∂²_xG(τ,·) F(·)` stays BOUNDED as `τ → 0` (→ `∂²F(0)`; the leading `τ⁻¹` cancels
  against `∫z ∂²G = 0`).  Hence the moment-improved pointwise profile
      `|∫z witnessSecondXDeriv(u−s)·F(s)| ≤ Cpair · (u−s)^{-1/2}`   (`s ∈ (u−ε_m, u)`)
  holds with a SINGLE `m`-uniform `Cpair` (the true integral is `O(1)`, and `(u−s)^{-1/2} ≥ ε_0^{-1/2}`
  on every Hi window, so `Cpair := (sup |∫z…|)·ε_0^{1/2}` works).  Unlike the false `τ`-uniform clean
  Gaussian bound, this `τ^{-1/2}` carry is SATISFIABLE — it is exactly the moment-aware
  `WideSliverBoundary` target.  And `(u−s)^{-1/2}` IS interval-integrable on `[u−ε_m, u]`
  (`∫₀^{ε_m} τ^{-1/2} dτ = 2√ε_m < ∞`), so the domination closes.

  ## THE `τ = 0` ENDPOINT VERDICT.
  IRRELEVANT to this route.  The reduction uses a.e.-domination on the finite-measure Hi window; the
  single endpoint `s = u` (`τ = 0`) is measure-zero, so whether `witnessSecondXDeriv` is defined / zero
  at `τ ≤ 0` never enters — we never need continuity up to the endpoint, only integrability, which the
  `τ^{-1/2}` dominator supplies.

  BANKABLE OUTCOME.  `hII_hi_from_sliver`: `MemAdjHi` from {banked AESM via `hmeas2Hi_slice` (carries
  `hUT`/`hεU`/`hSecCont`/`hBcont`)} ∪ {the moment-improved `τ^{-1/2}` carry `hGpow` + `Cpair ≥ 0`}.
  No uncapped / clean-Gaussian second-derivative domination anywhere.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CappedAdom2Audit
import QIQTH.SliceMeasurability

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.DaLimCensusRecon QIQTH.DaLimEasyTranche QIQTH.DaLimHardTranche QIQTH.FrozenLaplaceSliver
open QIQTH.DaLimLUConcreteDischarge QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.EveryCeilingFamilies QIQTH.ESLegWidening QIQTH.GlobalRawBoundFacade
open scoped Interval Topology BigOperators

namespace QIQTH.MemAdjHiSliver

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the two Mathlib-only bricks: the domination reduction + the `τ^{-1/2}` dominator.
    ############################################################################### -/

/-- **★ BRICK A1 — `intervalIntegrable_of_aesm_le`.**  The generic honest reduction: a real function
    `f` that is a.e.-strongly-measurable on the `uIoc` window and pointwise `|f| ≤ G` for an
    interval-integrable `G` is itself interval-integrable.  Pure Mathlib (`Integrable.mono'`).  This is
    the honest replacement for "domination by an absolute Gaussian bound" — the dominator `G` may be ANY
    interval-integrable profile, in particular the moment-improved `τ^{-1/2}` one.  NOT `a₁ = R/6`. -/
theorem intervalIntegrable_of_aesm_le {f G : ℝ → ℝ} {a b : ℝ}
    (hG : IntervalIntegrable G volume a b)
    (hf : AEStronglyMeasurable f (volume.restrict (Set.uIoc a b)))
    (hle : ∀ s ∈ Set.uIoc a b, |f s| ≤ G s) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff] at hG ⊢
  refine hG.mono' hf ((ae_restrict_iff' measurableSet_uIoc).mpr (ae_of_all _ ?_))
  intro s hs
  rw [Real.norm_eq_abs]
  exact hle s hs

/-- **★ BRICK A2 — `intervalIntegrable_invSqrt_sub`.**  The moment-improved dominator `(u−s)^{-1/2}` is
    interval-integrable on `[u−ε, u]` — the exact profile the second-derivative pairing needs (better
    than the false `τ⁻¹`).  `∫₀^ε τ^{-1/2} dτ = 2√ε < ∞`.  From `intervalIntegrable_rpow'` (`−1 < −1/2`)
    reflected through `comp_sub_left`.  NOT `a₁ = R/6`. -/
theorem intervalIntegrable_invSqrt_sub (u ε : ℝ) (hε : 0 < ε) :
    IntervalIntegrable (fun s => (u - s) ^ (-(1 : ℝ) / 2)) volume (u - ε) u := by
  have h0 : IntervalIntegrable (fun x : ℝ => x ^ (-(1 : ℝ) / 2)) volume 0 ε :=
    intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := ε) (r := -(1 : ℝ) / 2) (by norm_num)
  have h1 := h0.comp_sub_left u
  rw [sub_zero] at h1
  exact h1.symm

/-! ###############################################################################
    ### §B — ★★★ the capstone: `MemAdjHi` from banked AESM + the moment-improved carry.
    ############################################################################### -/

/-- **★★★ `hII_hi_from_sliver`.**  THE HONEST `MemAdjHi` (Hi adjacency leg, `[u−ε_m, u]`) for the
    endgame gate `H_G := vanVleckGatedWitness …`, `F := leviSeries (heatOp g gi H_G)`,
    `pdpdH := witnessSecondXDeriv …`, derived from
      •  BANKED — the s-slice AEStronglyMeasurability `SliceMeasurability.hmeas2Hi_slice`
         (honest carries `hUT`/`hεU`/`hSecCont`/`hBcont` — joint-continuity of the pairing on
         `Ioc 0 T ×ˢ univ`);
      •  ★ the NAMED, SATISFIABLE moment-improved carry `hGpow` — the `τ^{-1/2}` pointwise bound on the
         SIGNED `z`-integral of the pairing, with a SINGLE `m`-uniform `Cpair ≥ 0`.  This is the
         genuine content the moment-aware `WideSliverBoundary` campaign supplies; it is WEAKER than (and
         does NOT follow from) any pointwise second-derivative Gaussian domination, so no false
         `τ`-uniform / uncapped bound is asserted.
    ⟹ The last residual of wall A is discharged into a labelled satisfiable carry: the crude-`τ⁻¹`
    non-integrability obstruction is bypassed by the moment cancellation `(u−s)^{-1/2}` (integrable),
    dominated via `intervalIntegrable_of_aesm_le`.  Every hypothesis is SATISFIABLE and NON-VACUOUS;
    none is the conclusion.  NOT `a₁ = R/6`. -/
theorem hII_hi_from_sliver (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (U : Set ℝ)
    (hUT : ∀ u ∈ U, u ≤ T)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (hSecCont : ∀ i : Fin n, ContinuousOn
      (fun p : ℝ × Point n => witnessSecondXDeriv g gi hChr hK S a b i p.1 p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (Cpair : ℝ) (hCpair : 0 ≤ Cpair)
    (hGpow : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ s ∈ Set.uIoc (u - epsSeq m) u,
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ Cpair * (u - s) ^ (-(1 : ℝ) / 2)) :
    MemAdjHi (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
      (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) := by
  intro m i u hu
  have hεpos := epsSeq_pos m
  have hG : IntervalIntegrable
      (fun s => Cpair * (u - s) ^ (-(1 : ℝ) / 2)) volume (u - epsSeq m) u :=
    (intervalIntegrable_invSqrt_sub u (epsSeq m) hεpos).const_mul Cpair
  have hAESM := QIQTH.SliceMeasurability.hmeas2Hi_slice g gi hChr hK S a b T U
    hUT hεU hSecCont hBcont m i u hu
  exact intervalIntegrable_of_aesm_le hG hAESM (fun s hs => hGpow m i u hu s hs)

end QIQTH.MemAdjHiSliver

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.MemAdjHiSliver.intervalIntegrable_of_aesm_le
#print axioms QIQTH.MemAdjHiSliver.intervalIntegrable_invSqrt_sub
#print axioms QIQTH.MemAdjHiSliver.hII_hi_from_sliver
