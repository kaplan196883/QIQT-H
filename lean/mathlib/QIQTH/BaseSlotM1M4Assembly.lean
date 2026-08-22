/-
  BaseSlotM1M4Assembly — J4-1008: assembling M1 AND M4 of `ChartGaussianChangeVar`'s (J4-269)
  missing-fact list on a SINGLE genuine open set `S'`, on top of J4-1007's `S`/`V` (M2/M3).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## CONTEXT.  `QIQTH.ChartGaussianChangeVar.chart_gaussian_change_variables` (J4-269) needs four
  data items over a fixed set `S`:
    (M1) `HasFDerivWithinAt W (f' z) S z` for EVERY `z ∈ S` (not just pointwise at `q₀`).
    (M2) `Set.InjOn W S`.
    (M3) a left inverse `V` with `V (W z) = z` on `S`.
    (M4) `0 < |(f' z).det|` on `S` (POINTWISE positivity — the actual Lean statement `hJpos` is
         `∀ z ∈ S, 0 < J z`, NOT a uniform numeric bound; re-checked directly against the source).
  J4-1007 (`BaseSlotIFTLocalHomeomorph`) discharged M2/M3 via Mathlib's own Inverse Function Theorem,
  producing an open set `S ∋ q₀` with `InjOn` and a left inverse `V`, but explicitly left M1/M4 open
  (only a POINTWISE `HasFDerivAt … q₀` and a POINTWISE `−Id` derivative value were banked there).

  ## WHAT LANDS (Sol `gpt-5.6-sol`, high, 2026-08-22, plan reviewed before Lean; sound, no traps).
    • `uniformInverseChart_baseSlot_M1M4_generalK` — ★★★ THE PAYOFF.  Starting from J4-1007's `S`/`V`
      and the ALREADY-BANKED diagonal-tube joint regularity `uniformInverseChart_jointContDiffOn_tube`
      (`QIQTH.ExpMap`, pre-existing), this produces a SINGLE open set
        `S' := S ∩ Uslice ∩ Uinv ∋ q₀`
      (`Uslice` = the base-slot restriction of the open joint-C² tube `T`; `Uinv` = the open
      preimage, under `fderiv ℝ W`, of the open set of UNITS of the endomorphism ring
      `Point n →L[ℝ] Point n`, obtained from continuity of `fderiv ℝ W` at `q₀` — via
      `ContDiffAt.fderiv_right` — combined with `fderiv ℝ W q₀ = −Id` being a unit and `Units.isOpen`)
      on which ALL FOUR of M1–M4 hold SIMULTANEOUSLY, for the base-slot map
      `W p := uniformInverseChart g gi hC hK p q₀`:
        - M1: `HasFDerivWithinAt W (fderiv ℝ W z) S' z` for `z ∈ S'` (from `ContDiffAt ℝ 2 W z`
          restricted from the tube-slice, giving `DifferentiableAt`/`HasFDerivAt`, weakened to
          `HasFDerivWithinAt`).
        - M2/M3: restricted from J4-1007's `S` (since `S' ⊆ S`).
        - M4: `0 < |(fderiv ℝ W z).det|` for `z ∈ S'`, via `IsUnit (fderiv ℝ W z)` (from `z ∈ Uinv`)
          converted through `ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap` and
          `LinearMap.isUnit_iff_isUnit_det` to `(fderiv ℝ W z).det ≠ 0`, hence `|·| > 0`.
    This is the FIRST time all four of `ChartGaussianChangeVar`'s missing-fact-list items are
    simultaneously available, over a common open set, for the concrete base-slot chart map.

  ## WHAT THIS FILE DOES **NOT** DO (honest scope; do NOT over-claim).
    (a) It does NOT instantiate `ChartGaussianChangeVar.chart_gaussian_change_variables` itself — that
        additionally needs `hS : MeasurableSet S'` (open sets are measurable, an easy add-on, not
        wired here) and a concrete `B` (the amplitude factor from Layer A), which is NOT supplied.
        Layer A (the set-integral rewrite onto the gate, factoring `Wit τ 0 z` as
        `gaussDdim τ (W₀ z) · A τ z`) remains a SEPARATE, unstarted brick.
    (b) It does NOT wire into `HCompNearCarryChartSurfaceWired`'s literal `kPrime` shape or
        `VanVleckGatedSpatialSymmetry.hcomp`.  `nb`/`hcomp`/`hCConv` remain OPEN.
    (c) The `f'` produced is `fderiv ℝ W` (a *function*, defined everywhere on `Point n`, junk outside
        `S'`) — this matches `chart_gaussian_change_variables`'s `f' : Point n → (Point n →L[ℝ]
        Point n)` argument shape exactly (only its values ON `S'` are ever used there).
  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.BaseSlotIFTLocalHomeomorph
import QIQTH.UniformFlowCoherentChartReconciliationGeneralK
import QIQTH.HerrHminGeneralQ0GeneralK
import QIQTH.ChartGaussianChangeVar
import QIQTH.FlatHeatEquation

open Filter Set MeasureTheory
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound QIQTH.HerrHminGeneralQ0GeneralK
open QIQTH.FlatHeatEquation
open scoped Topology

namespace QIQTH.BaseSlotM1M4Assembly

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ `uniformInverseChart_baseSlot_M1M4_generalK`.**  THE PAYOFF: a single open set `S' ∋ q₀`
on which the base-slot chart map `W p := uniformInverseChart g gi hC hK p q₀` simultaneously satisfies
M1 (`HasFDerivWithinAt` throughout `S'`), M2 (`InjOn`, restricted from J4-1007's `S`), M3 (left inverse
`V`, restricted from J4-1007's `S`), and M4 (`0 < |det|` throughout `S'`) — `ChartGaussianChangeVar`'s
(J4-269) full missing-fact list, for the FIRST time, over a common open set.  NOT `a₁ = R/6`. -/
theorem uniformInverseChart_baseSlot_M1M4_generalK
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K) :
    ∃ (S' : Set (Point n)) (V : Point n → Point n),
      IsOpen S' ∧ q₀ ∈ S' ∧
      Set.InjOn (fun p => uniformInverseChart g gi hC hK p q₀) S' ∧
      (∀ p ∈ S', V (uniformInverseChart g gi hC hK p q₀) = p) ∧
      (∀ z ∈ S', HasFDerivWithinAt (fun p => uniformInverseChart g gi hC hK p q₀)
          (fderiv ℝ (fun p => uniformInverseChart g gi hC hK p q₀) z) S' z) ∧
      (∀ z ∈ S', 0 < |(fderiv ℝ (fun p => uniformInverseChart g gi hC hK p q₀) z).det|) := by
  set W : Point n → Point n := fun p => uniformInverseChart g gi hC hK p q₀ with hWdef
  -- Step A: J4-1007's IFT data — the open set `S`, `InjOn`, and the left inverse `V` (M2/M3).
  obtain ⟨S, hSopen, hq0S, hinj, V, hV⟩ :=
    QIQTH.BaseSlotIFTLocalHomeomorph.uniformInverseChart_baseSlot_localOpenHomeomorph_generalK
      g gi hC hK hq₀
  -- Step B: the pre-existing diagonal-tube joint `ContDiffOn ℝ 2`, sliced to the base slot.
  obtain ⟨T, hTopen, hTdiag, hTcd⟩ :=
    QIQTH.ExpMap.uniformInverseChart_jointContDiffOn_tube g gi hC hK
  set f : Point n × Point n → Point n :=
    fun ξ => uniformInverseChart g gi hC hK ξ.1 ξ.2 with hfdef
  set Uslice : Set (Point n) := {p : Point n | (p, q₀) ∈ T} with hUdef
  have hUopen : IsOpen Uslice := hTopen.preimage (continuous_id.prodMk continuous_const)
  have hq0U : q₀ ∈ Uslice := by
    show (q₀, q₀) ∈ T
    exact hTdiag q₀ hq₀
  have hWcda : ∀ z ∈ Uslice, ContDiffAt ℝ 2 W z := by
    intro z hz
    have hz' : (z, q₀) ∈ T := hz
    have hfat : ContDiffAt ℝ 2 f (z, q₀) := (hTcd (z, q₀) hz').contDiffAt (hTopen.mem_nhds hz')
    have hemb : ContDiffAt ℝ 2 (fun p : Point n => ((p, q₀) : Point n × Point n)) z :=
      ContDiffAt.prodMk contDiffAt_id contDiffAt_const
    have hcomp := ContDiffAt.comp z hfat hemb
    simpa [hWdef, hfdef] using hcomp
  -- Step C: the base fact at `q₀` itself: `fderiv ℝ W q₀ = −Id`, and its `ContDiffAt` package.
  have hWcda0 : ContDiffAt ℝ 2 W q₀ := hWcda q₀ hq0U
  have hfd0 : HasFDerivAt W (-(ContinuousLinearMap.id ℝ (Point n))) q₀ :=
    QIQTH.HerrHminGeneralQ0GeneralK.uniformInverseChart_baseSlot_fderiv_neg_id_generalK
      g gi hC hK hq₀
  have hfderiv0 : fderiv ℝ W q₀ = -(ContinuousLinearMap.id ℝ (Point n)) := hfd0.fderiv
  -- Step D (M4 machinery): continuity of `fderiv ℝ W` at `q₀`, plus openness of the unit group.
  have hderivCDA : ContDiffAt ℝ 1 (fderiv ℝ W) q₀ := hWcda0.fderiv_right (by norm_num)
  have hderivCont : ContinuousAt (fderiv ℝ W) q₀ := hderivCDA.continuousAt
  have hunit0 : IsUnit (fderiv ℝ W q₀) := by
    rw [hfderiv0, ContinuousLinearMap.isUnit_iff_bijective]
    constructor
    · intro a b hab
      simpa using congrArg (fun x => -x) hab
    · intro y
      exact ⟨-y, by simp⟩
  have hopenUnits : IsOpen {x : Point n →L[ℝ] Point n | IsUnit x} := Units.isOpen
  have hpre : (fun z => fderiv ℝ W z) ⁻¹' {x : Point n →L[ℝ] Point n | IsUnit x} ∈ 𝓝 q₀ :=
    hderivCont.preimage_mem_nhds (hopenUnits.mem_nhds hunit0)
  obtain ⟨Uinv, hUinvSub, hUinvOpen, hq0Uinv⟩ := mem_nhds_iff.mp hpre
  -- Step E: assemble `S' := S ∩ Uslice ∩ Uinv`.
  refine ⟨S ∩ Uslice ∩ Uinv, V, (hSopen.inter hUopen).inter hUinvOpen,
    ⟨⟨hq0S, hq0U⟩, hq0Uinv⟩, hinj.mono (fun p hp => hp.1.1), ?_, ?_, ?_⟩
  · intro p hp
    exact hV p hp.1.1
  · intro z hz
    have hzU : z ∈ Uslice := hz.1.2
    have hcda := hWcda z hzU
    have hdiff : DifferentiableAt ℝ W z := hcda.differentiableAt (by norm_num)
    exact hdiff.hasFDerivAt.hasFDerivWithinAt
  · intro z hz
    have hzInv : z ∈ Uinv := hz.2
    have hUnitZ : IsUnit (fderiv ℝ W z) := hUinvSub hzInv
    have hUnitLM : IsUnit ((fderiv ℝ W z : Point n →L[ℝ] Point n) : Point n →ₗ[ℝ] Point n) :=
      ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mp hUnitZ
    have hUnitDet : IsUnit ((fderiv ℝ W z).det) :=
      (LinearMap.isUnit_iff_isUnit_det (f := (fderiv ℝ W z : Point n →ₗ[ℝ] Point n))).mp hUnitLM
    exact abs_pos.mpr hUnitDet.ne_zero

/-- **★★★★ `uniformInverseChart_baseSlot_gaussian_change_variables_generalK` — THE CoV COROLLARY.**
Feeding M1–M4 (`uniformInverseChart_baseSlot_M1M4_generalK`) directly into
`ChartGaussianChangeVar.chart_gaussian_change_variables`: for ANY amplitude factor `B : Point n → ℝ`
(the concrete Layer-A factor is NOT supplied here — this is the abstract CoV identity, now genuinely
APPLICABLE to the concrete base-slot chart map), the Gaussian gate integral over the open set `S'`
equals the Gaussian integral over the chart image `W '' S'`:
    `∫ z in S', gaussDdim τ (W z) * B z = ∫ w in W '' S', gaussDdim τ w * (B (V w) / J (V w))`
where `J z := |(fderiv ℝ W z).det|`.  This is the FIRST time the full change-of-variables machinery
(Layer B, J4-269) has been triggered on the concrete `uniformInverseChart` base slot.  Layer A (the
set-integral rewrite onto the gate with the concrete amplitude factorization) remains SEPARATE and
unstarted; this corollary is NOT yet wired into `nb`/`hcomp`/`hCConv`.  NOT `a₁ = R/6`. -/
theorem uniformInverseChart_baseSlot_gaussian_change_variables_generalK
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K)
    (τ : ℝ) (B : Point n → ℝ) :
    ∃ (S' : Set (Point n)) (V : Point n → Point n),
      IsOpen S' ∧ q₀ ∈ S' ∧
      (∫ z in S', gaussDdim τ (uniformInverseChart g gi hC hK z q₀) * B z)
        = ∫ w in (fun p => uniformInverseChart g gi hC hK p q₀) '' S',
            gaussDdim τ w *
              (B (V w) / |(fderiv ℝ (fun p => uniformInverseChart g gi hC hK p q₀) (V w)).det|) := by
  obtain ⟨S', V, hS'open, hq0S', hinj, hV, hfd, hJpos⟩ :=
    uniformInverseChart_baseSlot_M1M4_generalK g gi hC hK hq₀
  refine ⟨S', V, hS'open, hq0S', ?_⟩
  have hS'meas : MeasurableSet S' := hS'open.measurableSet
  have := QIQTH.ChartGaussianChangeVar.chart_gaussian_change_variables τ S'
    (fun p => uniformInverseChart g gi hC hK p q₀) V
    (fun z => fderiv ℝ (fun p => uniformInverseChart g gi hC hK p q₀) z)
    (fun z => |(fderiv ℝ (fun p => uniformInverseChart g gi hC hK p q₀) z).det|)
    B hS'meas hfd hinj hV (fun z _ => rfl) hJpos
  simpa using this

end QIQTH.BaseSlotM1M4Assembly

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.BaseSlotM1M4Assembly
#print axioms uniformInverseChart_baseSlot_M1M4_generalK
#print axioms uniformInverseChart_baseSlot_gaussian_change_variables_generalK
end AxiomChecks
