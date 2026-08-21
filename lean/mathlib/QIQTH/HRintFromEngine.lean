/-
  HRintFromEngine — DISCHARGE the c-integrability carrier `hRint` of J4-970's `censusFTC_bridge` /
  `hfar_concrete_of_engine` (and J4-971's `hEnv_window_of_amplitudeAndFdom`), for the CONCRETE frozen
  convolution, from the SAME window-level engine bundle `hEnv` (+ global slice measurability `hFmeasG`)
  that those files already consume — via `measurable_deriv` (measurability of the rate as a derivative)
  + compactness domination (`IsCompact.elim_nhds_subcover` patching the local `hEnv` dominators into a
  single integrable bound on the compact window).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  ANALYSIS-INFRASTRUCTURE / carrier-reduction brick.  No `sorry`, no new axioms, no `:= True`, no vacuous
  / unsatisfiable / conclusion-in-disguise hypothesis, no existing banked file edited.

  ## WHAT J4-970/971 LEFT.  `censusFTC_bridge` / `hfar_concrete_of_engine` reduced the FTC-in-`c` bridge
  to three carriers `{hFmeasG, hEnv, hRint}`, where
      `hRint : ∀ s ∈ Ioo(u−ε)u, IntervalIntegrable (fun c ↦ ∫ z, ∂_τ(witness)(c−s)·F s z 0) volume u (u+h)`
  was flagged (J4-971) as "probably derivable from the full window `hEnv` via `measurable_deriv` +
  compactness".  THIS FILE DISCHARGES IT — `hRint` is NO LONGER a free carrier: it follows from `hEnv`.

  ## THE ROUTE (routine, but genuine).  For fixed `s`, write `R c := ∫ z, ∂_τ(witness)(c−s)·F s z 0` and
  `Φ a := ∫ z, witness(a−s)·F s z 0`.  The engine `censusDeriv_hasDerivAt` (J4-929) gives, at EVERY
  `c ∈ Icc u (u+h)`, `HasDerivAt Φ (R c) c` — so `R c = deriv Φ c` EXACTLY (pointwise, no null-set gap) on
  the window.  Hence:
    • MEASURABILITY: `R` agrees with `deriv Φ` on the interval, and `stronglyMeasurable_deriv Φ` gives
      `StronglyMeasurable (deriv Φ)`, so `R` is `AEStronglyMeasurable` on `volume.restrict (Ι u (u+h))`.
    • UNIFORM BOUND: the local `hEnv` dominators `Dz` (one integrable dominator per point of the compact
      window `Icc u (u+h)`) are patched by `IsCompact.elim_nhds_subcover` into a single integrable
      `Dstar := ∑_{c₀∈t} |D c₀|`, whence `‖R c‖ ≤ ∫ Dstar =: B` for every `c` in the window
      (`norm_integral_le_of_norm_le`).
  A measurable function bounded by a constant on a bounded interval is interval-integrable
  (`IntervalIntegrable.mono_fun'` against `intervalIntegrable_const`).

  ## WHAT THIS DOES — AND DOES NOT — DO.  It reduces the three FTC-bridge carriers from `{hFmeasG, hEnv,
  hRint}` to `{hFmeasG, hEnv}`: `hRint` is supplied internally from the same `hEnv` bundle.  Composed with
  J4-971's `hEnv_window_of_amplitudeAndFdom`, the concrete `H_far` far-envelope's carriers drop to the
  honest F-side data `{hFmeasG, hmeas, hbase, hFdom}` + amplitude sups `{hAmp0, hCfield, hSupp}` + the rate
  `hrate` — with NO separate `hRint`.  It does NOT discharge `hrate`, `hFmeasG`, nor the G3 F-bound; it does
  NOT touch the chart-CoV SCALAR census inequality (the opaque chart wall inside `hrate`).  It discharges
  NONE of `{hballrate, hDuhamel, hDConv, hCConv}` as a top-level τ-carry.  `a₁ = R/6` remains CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HCrossDerivEngineWired
import QIQTH.HFarFTCBridgeFromEngine

open MeasureTheory Set
open QIQTH.Curvature QIQTH.HeatResidualBound
open scoped Interval Topology

namespace QIQTH.HRintFromEngine

variable {n : ℕ}

/-! ###############################################################################
    ### §A — the ABSTRACT lemma: a parametric integral that is a pointwise derivative on a compact
    ###       interval AND locally integrably dominated is interval-integrable.
    ############################################################################### -/

/-- **★★ `intervalIntegrable_paramDeriv_of_localDom` — the abstract measurability+compactness route.**
    For any `Φ : ℝ → ℝ` and integrand family `fp : ℝ → α → ℝ` over a measure space `(α, μ)`, with `0 ≤ h`,
    given
      • `hderiv` — at EVERY `c ∈ Icc u (u+h)`, `HasDerivAt Φ (∫ z, fp c z ∂μ) c` (so the parametric
        integral `R c := ∫ z, fp c z` equals `deriv Φ c` pointwise on the window — no null-set gap), and
      • `hloc` — around each `c ∈ Icc u (u+h)` a neighborhood `V` and an integrable dominator `D` with
        `∀ᵐ z, ∀ c' ∈ V, ‖fp c' z‖ ≤ D z`,
    the parametric integral is interval-integrable:
        `IntervalIntegrable (fun c ↦ ∫ z, fp c z ∂μ) volume u (u+h)`.
    Route: `stronglyMeasurable_deriv` for measurability (via `R = deriv Φ` on the window) +
    `IsCompact.elim_nhds_subcover` domination-patching for a uniform bound.  NOT `a₁ = R/6`. -/
theorem intervalIntegrable_paramDeriv_of_localDom
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (Φ : ℝ → ℝ) (fp : ℝ → α → ℝ) (u h : ℝ) (hh : 0 ≤ h)
    (hderiv : ∀ c ∈ Set.Icc u (u + h), HasDerivAt Φ (∫ z, fp c z ∂μ) c)
    (hloc : ∀ c ∈ Set.Icc u (u + h), ∃ V ∈ 𝓝 c, ∃ D : α → ℝ,
        Integrable D μ ∧ ∀ᵐ z ∂μ, ∀ c' ∈ V, ‖fp c' z‖ ≤ D z) :
    IntervalIntegrable (fun c => ∫ z, fp c z ∂μ) volume u (u + h) := by
  have huv : u ≤ u + h := by linarith
  set R : ℝ → ℝ := fun c => ∫ z, fp c z ∂μ with hRdef
  -- interval ⊆ Icc
  have hIsub : Set.Ioc u (u + h) ⊆ Set.Icc u (u + h) := Set.Ioc_subset_Icc_self
  -- (1) MEASURABILITY of `R` on `volume.restrict (Ι u (u+h))`: `R = deriv Φ` on the interval.
  have hRmeas : AEStronglyMeasurable R (volume.restrict (Ι u (u + h))) := by
    have hEq : deriv Φ =ᵐ[volume.restrict (Ι u (u + h))] R := by
      rw [Set.uIoc_of_le huv]
      refine ae_restrict_of_forall_mem measurableSet_Ioc ?_
      intro c hc
      exact (hderiv c (hIsub hc)).deriv
    exact ((stronglyMeasurable_deriv Φ).aestronglyMeasurable).congr hEq
  -- (2) UNIFORM BOUND on `R` over the compact window via a finite dominator subcover.
  -- choose per-point neighborhood + integrable dominator.
  choose! V hVmem D hDint hDbnd using hloc
  obtain ⟨t, htsub, htcover⟩ :=
    (isCompact_Icc (a := u) (b := u + h)).elim_nhds_subcover V (fun c hc => hVmem c hc)
  -- the single integrable dominator `Dstar := ∑_{c₀∈t} |D c₀|`.
  set Dstar : α → ℝ := fun z => ∑ c₀ ∈ t, |D c₀ z| with hDstardef
  have hDstarInt : Integrable Dstar μ :=
    integrable_finsetSum t (fun c₀ hc₀ => (hDint c₀ (htsub c₀ hc₀)).abs)
  -- a.e. `z`, all points of the finite cover obey their local bound simultaneously.
  have hall : ∀ᵐ z ∂μ, ∀ c₀ ∈ t, ∀ c' ∈ V c₀, ‖fp c' z‖ ≤ D c₀ z := by
    rw [Filter.eventually_all_finset]
    exact fun c₀ hc₀ => hDbnd c₀ (htsub c₀ hc₀)
  set B : ℝ := ∫ z, Dstar z ∂μ with hBdef
  -- for every `c` in the window, `‖R c‖ ≤ B`.
  have hRbound : ∀ c ∈ Set.Icc u (u + h), ‖R c‖ ≤ B := by
    intro c hc
    obtain ⟨c₀, hc₀t, hcV⟩ := Set.mem_iUnion₂.mp (htcover hc)
    have hpt : ∀ᵐ z ∂μ, ‖fp c z‖ ≤ Dstar z := by
      filter_upwards [hall] with z hz
      have h1 : ‖fp c z‖ ≤ D c₀ z := hz c₀ hc₀t c hcV
      have h2 : D c₀ z ≤ Dstar z := by
        rw [hDstardef]
        refine le_trans (le_abs_self _) ?_
        refine Finset.single_le_sum (f := fun c' => |D c' z|) ?_ hc₀t
        intro c' _; exact abs_nonneg _
      exact le_trans h1 h2
    calc ‖R c‖ = ‖∫ z, fp c z ∂μ‖ := rfl
      _ ≤ ∫ z, Dstar z ∂μ := norm_integral_le_of_norm_le hDstarInt hpt
      _ = B := rfl
  -- (3) FINISH: bounded + measurable on a bounded interval ⟹ interval-integrable.
  have hbnd_ae : (fun c => ‖R c‖) ≤ᵐ[volume.restrict (Ι u (u + h))] (fun _ => B) := by
    rw [Set.uIoc_of_le huv]
    refine ae_restrict_of_forall_mem measurableSet_Ioc ?_
    intro c hc
    exact hRbound c (hIsub hc)
  exact (intervalIntegrable_const).mono_fun' hRmeas hbnd_ae

/-! ###############################################################################
    ### §B — THE CONCRETE DISCHARGE: `hRint` for the census convolution from `hEnv` + `hFmeasG`.
    ############################################################################### -/

/-- **★★★ `hRint_of_hEnv` — the c-integrability carrier `hRint` DISCHARGED from the engine bundle.**
    For the concrete gated van-Vleck witness `A := vanVleckGatedWitness g gi hC hK S cutA cutB` and frozen
    field `F`, with `0 ≤ h`, GIVEN
      • `hFmeasG` — the global slice measurability the engine needs, and
      • `hEnv` — the SAME per-`(s,a)` window engine bundle `censusFTC_bridge` / `hfar_concrete_of_engine`
        consume (inhabited by J4-971's `hEnv_window_of_amplitudeAndFdom`),
    the integrated rate `c ↦ ∫ z, ∂_τ(witness)(c−s)·F s z 0` is interval-integrable on `[u, u+h]` for
    every far-window `s`:
        `∀ s ∈ Ioo(u−ε)u,
           IntervalIntegrable (fun c ↦ ∫ z, deriv (fun r ↦ witness r 0 z)(c−s)·F s z 0) volume u (u+h)`.
    This is EXACTLY the `hRint` premise J4-970/971 carry.  Route: §A fed the engine `HasDerivAt`
    (`censusDeriv_hasDerivAt`, J4-929) for `hderiv` and the engine domination clause of `hEnv` for `hloc`.
    So `hRint` is NO LONGER a free carrier.  NOT `a₁ = R/6`. -/
theorem hRint_of_hEnv
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (u ε h : ℝ) (hh : 0 ≤ h)
    (hFmeasG : ∀ s u' : ℝ, AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hC hK S cutA cutB (u' - s) 0 z * F s z 0) volume)
    (hEnv : ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
        ∃ V ∈ 𝓝 a, ∃ Dz : Point n → ℝ,
          Integrable Dz volume ∧
          Integrable
            (fun z => vanVleckGatedWitness g gi hC hK S cutA cutB (a - s) 0 z * F s z 0) volume ∧
          AEStronglyMeasurable
            (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
              * F s z 0) volume ∧
          (∀ᵐ z ∂volume, ∀ a' ∈ V,
            ‖deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a' - s) * F s z 0‖
              ≤ Dz z) ∧
          (∀ᵐ z ∂volume, ∀ a' ∈ V,
            HasDerivAt
              (fun a' => vanVleckGatedWitness g gi hC hK S cutA cutB (a' - s) 0 z * F s z 0)
              (deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a' - s)
                * F s z 0) a')) :
    ∀ s ∈ Set.Ioo (u - ε) u,
      IntervalIntegrable
        (fun c => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (c - s)
          * F s z 0) volume u (u + h) := by
  intro s hs
  refine intervalIntegrable_paramDeriv_of_localDom
    (fun a => ∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (a - s) 0 z * F s z 0)
    (fun c z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (c - s) * F s z 0)
    u h hh ?_ ?_
  · -- `hderiv`: the engine `HasDerivAt` at each `c ∈ Icc u (u+h)`.
    intro c hc
    obtain ⟨V, hV, Dz, hDz, hFint, hF'meas, hbnd, hdiff⟩ := hEnv s hs c hc
    exact censusDeriv_hasDerivAt g gi hC hK S cutA cutB F s c (hFmeasG s) V hV Dz hDz hFint
      hF'meas hbnd hdiff
  · -- `hloc`: the engine local domination clause of `hEnv`.
    intro c hc
    obtain ⟨V, hV, Dz, hDz, _, _, hbnd, _⟩ := hEnv s hs c hc
    exact ⟨V, hV, Dz, hDz, hbnd⟩

/-! ###############################################################################
    ### §C — NON-VACUITY (TEETH).  The abstract lemma is satisfiable at a genuinely non-affine,
    ###       singular-integrand parametric family with the derivative genuinely ACTIVE.
    ############################################################################### -/

/-- **Non-vacuity (TEETH) of `intervalIntegrable_paramDeriv_of_localDom`.**  The `hderiv` and `hloc`
    hypotheses are JOINTLY satisfiable at a GENUINELY non-affine parametric family — a one-point
    (Dirac) measure `μ = Measure.dirac z₀` with `fp c z := Real.cos (c − z₀)`, `Φ a := Real.sin (a − z₀)`,
    on `u = 0, h = 1`, with the resulting integral `R c = cos(c − z₀)` a genuinely NON-CONSTANT rate
    (`R 1 = cos(1 − z₀) ≠ 0` at `z₀ = 0` since `cos 1 > 0` — the derivative is genuinely ACTIVE, NOT
    `0 = 0`).  Confirms the abstract lemma is not vacuously conditioned. -/
theorem intervalIntegrable_paramDeriv_of_localDom_hyp_satisfiable :
    ∃ (α : Type) (_ : MeasurableSpace α) (μ : Measure α) (Φ : ℝ → ℝ) (fp : ℝ → α → ℝ) (u h : ℝ),
      0 ≤ h ∧
      (∀ c ∈ Set.Icc u (u + h), HasDerivAt Φ (∫ z, fp c z ∂μ) c) ∧
      (∀ c ∈ Set.Icc u (u + h), ∃ V ∈ 𝓝 c, ∃ D : α → ℝ,
          Integrable D μ ∧ ∀ᵐ z ∂μ, ∀ c' ∈ V, ‖fp c' z‖ ≤ D z) ∧
      (∫ z, fp (1 : ℝ) z ∂μ) ≠ 0 := by
  refine ⟨Unit, inferInstance, Measure.dirac (), fun a => Real.sin (a - 0),
    fun c _ => Real.cos (c - 0), 0, 1, zero_le_one, ?_, ?_, ?_⟩
  · -- hderiv: `∫ z, cos(c−0) dδ = cos(c−0)`, derivative of `sin(a−0)`.
    intro c _
    have hint : (∫ _z, Real.cos (c - 0) ∂(Measure.dirac ())) = Real.cos (c - 0) := by
      simp
    rw [hint]
    have h1 : HasDerivAt (fun a : ℝ => a - 0) (1 : ℝ) c := by
      simpa using (hasDerivAt_id c).sub_const 0
    simpa using (Real.hasDerivAt_sin (c - 0)).comp c h1
  · -- hloc: constant integrable dominator `D := 1`.
    intro c _
    refine ⟨Set.univ, Filter.univ_mem, fun _ => 1, integrable_const 1,
      Filter.Eventually.of_forall (fun z c' _ => ?_)⟩
    have : ‖Real.cos (c' - 0)‖ ≤ 1 := by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
    simpa using this
  · -- teeth: `∫ z, cos(1−0) dδ = cos 1 ≠ 0`.
    have hint : (∫ _z, Real.cos ((1 : ℝ) - 0) ∂(Measure.dirac ())) = Real.cos 1 := by
      simp
    rw [hint]
    have hpos : 0 < Real.cos 1 :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_gt_three], by nlinarith [Real.pi_gt_three]⟩
    exact ne_of_gt hpos

end QIQTH.HRintFromEngine

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HRintFromEngine
#print axioms intervalIntegrable_paramDeriv_of_localDom
#print axioms hRint_of_hEnv
#print axioms intervalIntegrable_paramDeriv_of_localDom_hyp_satisfiable
end AxiomChecks
