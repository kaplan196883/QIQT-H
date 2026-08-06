/-
  CConvV2LeviSource — J4-324 (facade-v2 brick 10 of 14): the CONCRETE Levi-source adapter.  Derives the
  v2 source contract `CConvV2Contracts.CConvSourceDataV2` for the CONCRETE gate source
      `F s z := leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0`,
  by converting the BANKED Levi-series Gaussian domination into the pairing-input shape and feeding
  `CConvV2GaussianPairing.sourcePair_of_gaussian_bound`.  ONE brick of the `a₁ = R/6` heat-kernel
  campaign (SOL CONSULT #9, docs/qg_roadmap/JET4_TOWER_PLAN.md).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a
  concrete-source ADAPTER: it plugs the banked Levi domination into the v2 pairing analysis.  NO `sorry`
  (header prose excepted), NO new axioms, NO `:= True`, NO vacuous / unsatisfiable hypothesis in this
  file's own theorems, no existing file edited, nothing committed.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (L0) THE BANKED DOMINATION INVENTORY (recon).

  The banked width-2 Levi envelope is the field `LeviSeriesLocalData.hFenv`
  (= `GatedWitnessPackage.leviSeries_dominatedW_le`):
      `∃ C_L ≥ 0, ∀ τ p q, 0 < τ → τ ≤ T → |leviSeries E τ p q| ≤ C_L · baseKernelW 2 0 τ p q`.
  The base kernel at order `0` IS the plain width-2 Gaussian (`ParametrixHEboundWiring.
  baseKernelW_zero_apply`):
      `baseKernelW 2 0 τ p q = gaussDdim (2·τ) (p − q)`.
  Composing at `q = 0` (`sub_zero`) gives, on the window `(0,t]` (`t ≤ T`):
      `|leviSeries E s z 0| ≤ C_L · gaussDdim (2·s) z = C_L · s^0 · gaussDdim (2·s) z`,
  which is EXACTLY the `sourcePair_of_gaussian_bound` input shape `|F s z| ≤ CF·s^γ·gaussDdim (cF·s) z`
  with `CF = C_L`, `γ = 0`, `cF = 2`.  Note `γ = 0 > −1` — even MILDER than Sol's conservative
  `γ = −1/2` estimate (the banked domination carries NO `s`-power at all, only the factorial/Γ-decayed
  constant `C_L`), so the Beta endpoint is comfortably `β(1, 1/2)`-integrable.

  ## WHAT THIS FILE LANDS (L1–L3).
    • (L1) `leviSlice_gaussian_bound_of_dom` — the CONVERSION lemma: from the banked `∀`-form
      domination `|leviSeries E τ p q| ≤ C_L·baseKernelW 2 0 τ p q` (`0<τ≤T`) to the pairing shape
      `|leviSeries E s z 0| ≤ C_L·s^0·gaussDdim (2·s) z` on `Ioc 0 t` (`t ≤ T`).  Pure algebra
      (`baseKernelW_zero_apply` + `sub_zero` + `Real.rpow_zero`).
    • (L2) `leviSource_gaussian_bound` — the concrete `|F s z| ≤ C_L·s^0·gaussDdim (2·s) z`, extracting
      `C_L` from the `LeviSeriesLocalData.hFenv` package (generic in `E`).
    • (L3) `sourceDataV2_concrete` — `CConvSourceDataV2` for the concrete gated Levi source:
      `hFjoint`/`hFmeas` from `FacadeBundleFields.hFjoint_field`/`.hFmeas_field` (J4-319), `hFpair` via
      `sourcePair_of_gaussian_bound ∘ L2`.  Honest satisfiable carries: the `LeviSeriesLocalData`
      package `data`, the `z`-slice summability `hFsum`, and the parametric-integral measurability
      `hgMeas` (the sole `sourcePair` side condition; true for `F ≡ 0`).

  NOT `a₁ = R/6`.
-/
import QIQTH.CConvV2GaussianPairing
import QIQTH.FacadeBundleFields
import QIQTH.ParametrixHEboundWiring

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.TrueHeatKernel QIQTH.LeviSeriesLocalData QIQTH.GaussianWidthTolerant
open QIQTH.CConvV2Contracts QIQTH.CConvV2GaussianPairing QIQTH.FacadeBundleFields
open scoped Topology BigOperators

namespace QIQTH.CConvV2LeviSource

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### §1 — (L1) the CONVERSION: banked `baseKernelW`-domination → pairing shape.
    ############################################################################### -/

/-- **★ (L1) `leviSlice_gaussian_bound_of_dom`.**  Convert the banked width-2 Levi envelope
    `|leviSeries E τ p q| ≤ C_L · baseKernelW 2 0 τ p q` (`0 < τ ≤ T`) into the
    `sourcePair_of_gaussian_bound` input shape, evaluated on the base-point slice `q = 0` and the
    diffusion window `Ioc 0 t` (`t ≤ T`):
        `|leviSeries E s z 0| ≤ C_L · s^0 · gaussDdim (2·s) z`.
    Pure algebra: `baseKernelW_zero_apply` (`baseKernelW 2 0 s z 0 = gaussDdim (2s) (z−0)`), `sub_zero`,
    and `s^(0:ℝ) = 1` (`Real.rpow_zero`).  `γ = 0` here (banked domination has NO `s`-power).
    ⚠ NOT `a₁ = R/6`. -/
theorem leviSlice_gaussian_bound_of_dom (E : ℝ → Point n → Point n → ℝ) (C_L T t : ℝ)
    (htT : t ≤ T)
    (hLdom : ∀ (τ : ℝ) (p q : Point n), 0 < τ → τ ≤ T →
      |leviSeries E τ p q| ≤ C_L * baseKernelW (2 : ℝ) (0 : ℝ) τ p q) :
    ∀ s ∈ Set.Ioc (0 : ℝ) t, ∀ z : Point n,
      |leviSeries E s z 0| ≤ C_L * s ^ (0 : ℝ) * gaussDdim (2 * s) z := by
  intro s hs z
  obtain ⟨hs0, hst⟩ := hs
  have h := hLdom s z 0 hs0 (le_trans hst htT)
  rw [baseKernelW_zero_apply, sub_zero] at h
  rw [Real.rpow_zero, mul_one]
  exact h

/-! ###############################################################################
    ### §2 — (L2) the concrete Gaussian bound from the `LeviSeriesLocalData` package.
    ############################################################################### -/

/-- **★ (L2) `leviSource_gaussian_bound`.**  From a `LeviSeriesLocalData E C T` package (whose `hFenv`
    field IS the banked Levi Gaussian envelope) and `t ≤ T`, the concrete pairing bound
        `∃ C_L ≥ 0, ∀ s ∈ Ioc 0 t, ∀ z, |leviSeries E s z 0| ≤ C_L · s^0 · gaussDdim (2·s) z`.
    Generic in `E`; the gate specialization is `E := heatOp g gi (vanVleckGatedWitness …)` in L3.
    ⚠ NOT `a₁ = R/6`. -/
theorem leviSource_gaussian_bound (E : ℝ → Point n → Point n → ℝ) (C T t : ℝ)
    (htT : t ≤ T) (data : LeviSeriesLocalData E C T) :
    ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ s ∈ Set.Ioc (0 : ℝ) t, ∀ z : Point n,
      |leviSeries E s z 0| ≤ C_L * s ^ (0 : ℝ) * gaussDdim (2 * s) z := by
  obtain ⟨C_L, hCL0, hLdom⟩ := data.hFenv
  exact ⟨C_L, hCL0, leviSlice_gaussian_bound_of_dom E C_L T t htT hLdom⟩

/-! ###############################################################################
    ### §3 — (L3) the concrete `CConvSourceDataV2` at the gated Levi source.
    ############################################################################### -/

/-- **★★★ (L3) `sourceDataV2_concrete`.**  The v2 source contract `CConvSourceDataV2` for the CONCRETE
    gated Levi source `F s z := leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0`,
    on the window `(0,t]` (package ceiling `T = t`):
      • `hFjoint` = `FacadeBundleFields.hFjoint_field` (J4-319, from `data`);
      • `hFmeas`  = `FacadeBundleFields.hFmeas_field` (from `data` + `hFsum`);
      • `hFpair`  = `sourcePair_of_gaussian_bound` at `CF = C_L`, `γ = 0`, `cF = 2` fed by (L2)
                    (`data.hFenv`) + the parametric-integral measurability `hgMeas`.
    Honest satisfiable carries: `data` (the banked `LeviSeriesLocalData`), `hFsum` (`z`-slice
    summability), `hgMeas` (the sole `sourcePair` side condition, true for `F ≡ 0`).  ⚠ NOT
    `a₁ = R/6`. -/
theorem sourceDataV2_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (C t : ℝ) (ht : 0 < t)
    (data : LeviSeriesLocalData (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) C t)
    (hFsum : ∀ s : ℝ, ∀ᵐ z ∂(volume : Measure (Point n)),
        Summable (fun k : ℕ =>
          (-1 : ℝ) ^ (k + 1)
            * iterE (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) (k + 1) s z 0))
    (hgMeas : AEStronglyMeasurable
      (fun s : ℝ => (t - s) ^ (-(1 : ℝ) / 2)
        * ∫ z, gaussDdim (2 * (t - s)) z
            * |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ∂(volume : Measure (Point n)))
      ((volume : Measure ℝ).restrict (Set.Ioc 0 t))) :
    CConvSourceDataV2
      (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) t := by
  obtain ⟨C_L, hCL0, hF⟩ :=
    leviSource_gaussian_bound
      (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) C t t le_rfl data
  exact
    { hFjoint := hFjoint_field g gi hC hK S a b C t data
      hFmeas := fun s => hFmeas_field g gi hC hK S a b C t data hFsum s
      hFpair := sourcePair_of_gaussian_bound
        (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
        t C_L 2 0 ht hCL0 (by norm_num) (by norm_num) hgMeas hF }

end QIQTH.CConvV2LeviSource

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CConvV2LeviSource
#print axioms leviSlice_gaussian_bound_of_dom
#print axioms leviSource_gaussian_bound
#print axioms sourceDataV2_concrete
end AxiomChecks
