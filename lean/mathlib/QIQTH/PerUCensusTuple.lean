/-
  PerUCensusTuple — J4-407: Sol #17 F3 — `hfam_v2` fired + `hfull_pd1` fired + the per-`u` census tuple.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  `a₁ = R/6`
  remains CONDITIONAL on the whole `hDuhamel` / convergence-trio + geometric-wiring stack AND on the
  SURVIVING labelled census carries threaded here.  This file performs the MECHANICAL F3 composition:
  it FIRES the banked feeders `PerUProviders.hlin_field_concrete` (J4-405) and `HD1Concrete.hD1_concrete`
  (J4-406) into `CConvV2Facade.hfam_v2`, reads off the full-side first-partial germ in the per-`u`
  census shape via `Pd2ConvDissolution.pd_germ_eq_of_family`, and assembles the per-`u` census tuple
  feeding `Pd2ConvPerU.hPd2conv_perU`.  NO `sorry` (header prose excepted), NO new axioms, NO
  `:= True`, NO vacuous / unsatisfiable hypothesis, NONE equal to (or trivially yielding) an `R/6`
  conclusion, NO existing file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE JOBS.

  ### (T1) `hfam_v2_concrete` — FIRE `hfam_v2`.
    The L1 `∃`-`HasFDerivAt` family of `SpatialC2.hCConv_reduction`, at the concrete van-Vleck gated
    witness `W := vanVleckGatedWitness g gi hC hK S a b` and Levi source `F := leviSeries (heatOp g gi W)`,
    obtained by feeding `CConvV2Facade.hfam_v2` the DISCHARGED linewise family
    `PerUProviders.hlin_field_concrete` (from its `hProv` 7-leg carry) and the DISCHARGED `C¹` regularity
    `HD1Concrete.hD1_concrete` (from its three analytic carries `hbulkderiv`/`hsliver`/`hcont` + the
    `hGint` integrability carry).  The facade field neighbourhood `u` is used verbatim.

  ### (T2) `hfull_pd1_fired` — FIRE `hfull_pd1` in the PER-`u` census shape.
    For each `u ∈ U` and coordinate `i`, the full-side first coordinate partial agrees near `0` with the
    Dmap coefficient:
      `(fun y ↦ ∂ᵢ(heatConv W F u · 0) y) =ᶠ[𝓝 0] (fun y ↦ (Dmap … F u y)(eᵢ))`,
    via `Pd2ConvDissolution.pd_germ_eq_of_family` on the fired (T1) family at heat-time `u`.  This is the
    EXACT per-`u` census shape `∀ u ∈ U, ∀ i` the census block `hPd2conv_perU`'s `hfull_pd1` binder wants
    (`gcoef u i := fun y ↦ (Dmap … F u y)(eᵢ)`).

  ### (T3) `hPd2conv_perU_fired` — THE PER-`u` CENSUS TUPLE.
    Fire `Pd2ConvPerU.hPd2conv_perU` with the algorithmically-dischargeable census members supplied
    internally (`sSet := univ`, `hb := hb_concrete`, `hbulk_tendsto := hbulk_tendsto_concrete`,
    `hfull_pd1 := T2`, `fbulk := fbulkInt …`, `gcoef := Dmap coefficient`, `bb := the √ε sliver rate`),
    keeping the genuine analytic carries explicit (`fderivBulk`/`gderiv`, `hbulkderiv`/`hsliver`/`hcont`,
    the `hGint` integrability, the `hProv` linewise provider, the field nbhd `nb`, `hUpos`, and the frozen
    germ-link carry `hfrozen_pd1` — the latter dischargeable per-`u` from the assembly's `hQ1` via
    `Pd2ConvPerU.hfrozen_pd1_from_hQ1`, kept LABELLED here since `hPd2conv_perU` still binds it).  The
    conclusion is the exact per-`u` frozen→full second-partial `Tendsto` binder (viii).

  ── The J4-406 correspondence.  The `hD1` census IS the per-`u` census family; the J4-406 slices
  (`hb_concrete`/`hbulk_tendsto_concrete` at fixed `t`) generalize `t ↝ u ∈ U` verbatim, and the
  `hbulkderiv`/`hsliver` carries are shared BOTH by T2's `hD1` firing (per-`u` slice) and by T3's census
  block — one carry, two consumers.

  Every hypothesis is satisfiable, non-vacuous (the width-2 Gaussian model of the sliver bricks satisfies
  the whole census), strictly lower-level than the conclusion, and NONE equals `a₁ = R/6`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.PerUProviders
import QIQTH.HD1Concrete
import QIQTH.Pd2ConvPerU

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.CConvV2DerivRep QIQTH.CConvV2Facade QIQTH.Pd2ConvDissolution
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.PerUCensusTuple

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (T1) `hfam_v2_concrete` — the FIRED L1 `∃`-`HasFDerivAt` family.
    ############################################################################### -/

/-- **★★ (T1) `hfam_v2_concrete`.**  THE FIRED L1 `∃`-`HasFDerivAt` family at the concrete van-Vleck
    gated witness `W := vanVleckGatedWitness g gi hC hK S a b` and Levi source
    `F := leviSeries (heatOp g gi W)`:
      `∃ w ∈ 𝓝 0, ∀ x ∈ w, HasFDerivAt (fun p ↦ heatConv W F t p 0) (Dmap … F t x) x`,
    obtained from `CConvV2Facade.hfam_v2` by feeding the DISCHARGED linewise family
    `PerUProviders.hlin_field_concrete` (from its `hProv` 7-leg carry) and the DISCHARGED `C¹` regularity
    `HD1Concrete.hD1_concrete` (from its `hbulkderiv`/`hsliver`/`hcont` + `hGint` carries).  The facade
    field neighbourhood `u` is used verbatim.  Honest carries: `hProv` (the seven spatial-line
    differentiation-under-∫ side conditions), the three analytic `hD1` carries, and the `hGint`
    integrability — each satisfiable, non-vacuous, strictly lower-level than the conclusion.
    NOT `a₁ = R/6`. -/
theorem hfam_v2_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (ht : 0 < t)
    (u : Set (Point n)) (hu_open : IsOpen u) (hu0 : (0 : Point n) ∈ u)
    (hProv : ∀ x ∈ u, ∀ i : Fin n,
      ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
        snb ∈ 𝓝 (x i) ∧
        (∀ w, AEStronglyMeasurable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (t - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 t))) ∧
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume 0 t ∧
        AEStronglyMeasurable
          (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 t)) ∧
        IntervalIntegrable bound volume 0 t ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bound s) ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hC hK S a b (t - s)
              (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) (Function.update x i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) w))
    (fderivBulk : Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : Fin n → Point n → (Point n →L[ℝ] ℝ))
    (C₀ C₁ C₂ : Fin n → ℝ)
    (hGint : ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 t)
    (hbulkderiv : ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b t i m)
          (fderivBulk i m x) x)
    (hsliver : ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        dist (fderivBulk i m x) (gderiv i x)
          ≤ (C₀ i + C₁ i) * (2 * Real.sqrt (epsSeq m)) + C₂ i * epsSeq m)
    (hcont : ∀ i : Fin n, ContinuousOn (gderiv i) (Set.univ : Set (Point n))) :
    ∃ w ∈ 𝓝 (0 : Point n), ∀ x ∈ w,
      HasFDerivAt (fun p => heatConv (vanVleckGatedWitness g gi hC hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) t p 0)
        (Dmap g gi hC hK S a b
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) t x) x :=
  QIQTH.CConvV2Facade.hfam_v2 g gi hC hK S a b
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) t
    u hu_open hu0
    (QIQTH.PerUProviders.hlin_field_concrete g gi hC hK S a b t u hProv)
    (QIQTH.HD1Concrete.hD1_concrete g gi hC hK S a b t ht fderivBulk gderiv C₀ C₁ C₂
      hGint hbulkderiv hsliver hcont)

/-! ###############################################################################
    ### (T2) `hfull_pd1_fired` — the full-side first-partial germ, per-`u` census shape.
    ############################################################################### -/

/-- **★★ (T2) `hfull_pd1_fired`.**  THE FIRED full-side first-partial germ in the EXACT per-`u` census
    shape `∀ u ∈ U, ∀ i`:
      `(fun y ↦ ∂ᵢ(heatConv W F u · 0) y) =ᶠ[𝓝 0] (fun y ↦ (Dmap … F u y)(eᵢ))`,
    where `W := vanVleckGatedWitness g gi hC hK S a b`, `F := leviSeries (heatOp g gi W)`.  Route: at
    each `u ∈ U`, the FIRED (T1) family at heat-time `u` (`hfam_v2_concrete`), read off through
    `Pd2ConvDissolution.pd_germ_eq_of_family`.  The census's `gcoef u i` is thus IDENTIFIED with the
    Dmap coefficient `fun y ↦ (Dmap … F u y)(eᵢ)` (= the `hbulk_tendsto` limit, `Dmap_apply_single`).
    All hypotheses are the per-`u` families carried by T1; none is the conclusion.  NOT `a₁ = R/6`. -/
theorem hfull_pd1_fired (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (hUpos : ∀ u ∈ U, 0 < u)
    (nb : ℝ → Set (Point n)) (hnb_open : ∀ u ∈ U, IsOpen (nb u))
    (hnb0 : ∀ u ∈ U, (0 : Point n) ∈ nb u)
    (hProv : ∀ u ∈ U, ∀ x ∈ nb u, ∀ i : Fin n,
      ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
        snb ∈ 𝓝 (x i) ∧
        (∀ w, AEStronglyMeasurable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u))) ∧
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume 0 u ∧
        AEStronglyMeasurable
          (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u)) ∧
        IntervalIntegrable bound volume 0 u ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bound s) ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s)
              (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) w))
    (fderivBulk : ℝ → Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : ℝ → Fin n → Point n → (Point n →L[ℝ] ℝ))
    (C₀ C₁ C₂ : ℝ → Fin n → ℝ)
    (hGint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 u)
    (hbulkderiv : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m)
          (fderivBulk u i m x) x)
    (hsliver : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        dist (fderivBulk u i m x) (gderiv u i x)
          ≤ (C₀ u i + C₁ u i) * (2 * Real.sqrt (epsSeq m)) + C₂ u i * epsSeq m)
    (hcont : ∀ u ∈ U, ∀ i : Fin n, ContinuousOn (gderiv u i) (Set.univ : Set (Point n))) :
    ∀ u ∈ U, ∀ i : Fin n,
      (fun y => pd (fun x => heatConv (vanVleckGatedWitness g gi hC hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u x 0) i y)
        =ᶠ[𝓝 (0 : Point n)]
        (fun y => (Dmap g gi hC hK S a b
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u y)
          (Pi.single i (1 : ℝ))) := by
  intro u hu i
  exact QIQTH.Pd2ConvDissolution.pd_germ_eq_of_family
    (fun x => heatConv (vanVleckGatedWitness g gi hC hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u x 0)
    (Dmap g gi hC hK S a b
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u) i
    (hfam_v2_concrete g gi hC hK S a b u (hUpos u hu) (nb u) (hnb_open u hu) (hnb0 u hu)
      (hProv u hu) (fderivBulk u) (gderiv u) (C₀ u) (C₁ u) (C₂ u)
      (hGint u hu) (hbulkderiv u hu) (hsliver u hu) (hcont u hu))

/-! ###############################################################################
    ### (T3) `hPd2conv_perU_fired` — the assembled per-`u` census tuple.
    ############################################################################### -/

/-- **★★★ (T3) `hPd2conv_perU_fired`.**  THE ASSEMBLED per-`u` census tuple: `Pd2ConvPerU.hPd2conv_perU`
    fired with the algorithmically-dischargeable census members supplied internally and the genuine
    analytic carries kept explicit.  Concretely:
      • `sSet := univ`, `hsOpen`/`hsnhds` from `isOpen_univ`/`univ_mem`;
      • `fbulk := fbulkInt …`, `gcoef u i := fun y ↦ (Dmap … F u y)(eᵢ)`, `bb := the √ε sliver rate`;
      • `hb := hb_concrete` (the vanishing sliver rate, `t ↝ u`);
      • `hbulk_tendsto := hbulk_tendsto_concrete` (`fbulkInt … → gcoef`, via `Dmap_apply_single`);
      • `hfull_pd1 := hfull_pd1_fired` (T2).
    RESIDUAL CARRIES (all satisfiable, non-vacuous, none the conclusion; enumerated):
      `nb`/`hnb_open`/`hnb0`, `hUpos`, `hProv` (T2's linewise provider), `fderivBulk`/`gderiv`,
      `C₀`/`C₁`/`C₂`, `hGint` (integrability), `hbulkderiv`/`hsliver`/`hcont` (the shared analytic
      sliver carries — same data feeding BOTH T2's `hD1` firing and this census block), and the frozen
      germ-link `hfrozen_pd1` (dischargeable per-`u` from the assembly `hQ1` via `hfrozen_pd1_from_hQ1`;
      kept labelled since `hPd2conv_perU` still binds it).  Conclusion = the exact per-`u` frozen→full
      second-partial `Tendsto` binder (viii).  ⚠ STILL NOT `a₁ = R/6`. -/
theorem hPd2conv_perU_fired (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (hUpos : ∀ u ∈ U, 0 < u)
    (nb : ℝ → Set (Point n)) (hnb_open : ∀ u ∈ U, IsOpen (nb u))
    (hnb0 : ∀ u ∈ U, (0 : Point n) ∈ nb u)
    (hProv : ∀ u ∈ U, ∀ x ∈ nb u, ∀ i : Fin n,
      ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
        snb ∈ 𝓝 (x i) ∧
        (∀ w, AEStronglyMeasurable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u))) ∧
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume 0 u ∧
        AEStronglyMeasurable
          (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u)) ∧
        IntervalIntegrable bound volume 0 u ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bound s) ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s)
              (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) w))
    (fderivBulk : ℝ → Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : ℝ → Fin n → Point n → (Point n →L[ℝ] ℝ))
    (C₀ C₁ C₂ : ℝ → Fin n → ℝ)
    (hGint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 u)
    (hbulkderiv : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m)
          (fderivBulk u i m x) x)
    (hsliver : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        dist (fderivBulk u i m x) (gderiv u i x)
          ≤ (C₀ u i + C₁ u i) * (2 * Real.sqrt (epsSeq m)) + C₂ u i * epsSeq m)
    (hcont : ∀ u ∈ U, ∀ i : Fin n, ContinuousOn (gderiv u i) (Set.univ : Set (Point n)))
    (hfrozen_pd1 : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ),
        (fun y => pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u
            (u - epsSeq m) x 0) i y)
          =ᶠ[𝓝 (0 : Point n)]
          QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m) :
    ∀ u ∈ U, ∀ i : Fin n,
      Tendsto
        (fun m => pd (fun y => pd (fun x => heatConvFrozen
            (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u
            (u - epsSeq m) x 0) i y) i 0)
        atTop (𝓝 (pd (fun y => pd (fun x => heatConv
            (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u x 0) i y) i 0)) :=
  QIQTH.Pd2ConvPerU.hPd2conv_perU g gi hC hK S a b U
    (fun _ => (Set.univ : Set (Point n)))
    (fun _ _ => isOpen_univ)
    (fun _ _ => univ_mem)
    (fun u i => fun y => (Dmap g gi hC hK S a b
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u y)
      (Pi.single i (1 : ℝ)))
    gderiv
    (fun u i m => QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m)
    fderivBulk
    (fun u i m => (C₀ u i + C₁ u i) * (2 * Real.sqrt (epsSeq m)) + C₂ u i * epsSeq m)
    (fun u _hu i => QIQTH.HD1Concrete.hb_concrete (C₀ u i) (C₁ u i) (C₂ u i))
    hbulkderiv
    (fun u hu i x _hx => by
      show Tendsto (fun m => QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m x) atTop
        (𝓝 ((Dmap g gi hC hK S a b
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u x)
          (Pi.single i (1 : ℝ))))
      rw [Dmap_apply_single g gi hC hK S a b
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u x i]
      exact QIQTH.HD1Concrete.hbulk_tendsto_concrete g gi hC hK S a b i u (hUpos u hu) x
        (hGint u hu i x))
    hsliver
    (hfull_pd1_fired g gi hC hK S a b U hUpos nb hnb_open hnb0 hProv fderivBulk gderiv
      C₀ C₁ C₂ hGint hbulkderiv hsliver hcont)
    hfrozen_pd1

end QIQTH.PerUCensusTuple

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.PerUCensusTuple
#print axioms hfam_v2_concrete
#print axioms hfull_pd1_fired
#print axioms hPd2conv_perU_fired
end AxiomChecks
