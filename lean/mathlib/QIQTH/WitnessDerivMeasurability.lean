/-
  WitnessDerivMeasurability — J4-162: the remaining four L1 G2-slots (`hzmeas`, `hsmeas`, `hsbound`,
  `hBint`) for the CONCRETE first-derivative kernel `dH := witnessFieldDeriv` of the gated `N = 1`
  van-Vleck witness.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about `R/6`.  It discharges — for
  the concrete `dH := witnessFieldDeriv` — the four slots of the per-`(i, x₀)` bundle that
  `QIQTH.GcoefContinuity.gcoef_continuity_discharge` (J4-160) consumes and that J4-161
  (`WitnessDerivDomination`, the `hzcont`/`hzint`/`hzbound` slots) did NOT touch:
      `hzmeas` (inner z-ae-measurability), `hsmeas` (outer s-ae-measurability),
      `hsbound` (outer s-dominator bound), `hBint` (interval-integrability of the s-dominator).
  Together with J4-161 this closes the ENTIRE seven-hypothesis G2 bundle at `witnessFieldDeriv`
  (capstone `g2_bundle_assembled`).  The honest analytic/measurability inputs are carried, never the
  conclusion.

  ── WHAT IS PROVED HERE (axiom-free, no `sorry`).

    SLOT 3 — `hsbound` (DISCHARGED, analytic half).
      • `hsbound_witness` — ★ from a carried x-UNIFORM pointwise z-domination `hdomS` (the `∀ᶠ x`
          OUTSIDE the `∀ᵐ s`, the order `hsbound` needs — satisfiable because the
          `witnessFieldDeriv_gate_envelope` constant is x-FREE, hence the neighbourhood is uniform in
          `s`) plus the EXACT Gaussian mass-one fact `gaussDdim_integral_eq_one`
          (`∫ z, G_σ z = 1`, the NORMALIZED kernel), `MeasureTheory.norm_integral_le_of_norm_le` yields
          `‖∫ z, dH·F ∂volume‖ ≤ (C₀·Cf)·(∫ z, G_{κ(t−s)} z) = (C₀·Cf)·1 = C₀·Cf`,
          the constant s-dominator `B ≡ C₀·Cf`.  (`{t}` is null, so the `s = t` zero-width endpoint is
          excluded a.e.)

    SLOT 4 — `hBint` (DISCHARGED).
      • `hBint_witness` — the constant s-dominator `B ≡ C₀·Cf` is `IntervalIntegrable` on `[0,t]`
          (`intervalIntegrable_const`).

    SLOT 1 — `hzmeas` (REDUCTION, in-shape).
      • `hzmeas_witness` — from a carried BARE-KERNEL z-ae-measurability family `hKmeas`
          (`∀ᶠ x, AEStronglyMeasurable (z ↦ witnessFieldDeriv … x z)`) and a measurable `F`-slice
          `hFmeas`, `AEStronglyMeasurable.mul` gives the EXACT `hzmeas` shape for the product `dH·F`.

    SLOT 2 — `hsmeas` (REDUCTION, in-shape).
      • `hsmeas_witness` — from a carried JOINT `(s,z)`-ae-measurability core `hjoint`
          (measurability of `(s,z) ↦ witnessFieldDeriv … (t−s) x z · F s z` on the product measure),
          `MeasureTheory.AEStronglyMeasurable.integral_prod_right'` produces the EXACT `hsmeas` shape
          (s-ae-measurability of `s ↦ ∫ z, dH·F ∂ν`).

    CAPSTONE — `g2_bundle_assembled` — ★★ assembles ALL SEVEN G2 hypotheses at `witnessFieldDeriv`
      (the three J4-161 slots `hzcont`/`hzint`/`hzbound` + the four here) and feeds them into
      `GcoefContinuity.gcoef_continuity_discharge`, yielding the continuity conclusion
        `∀ x₀ ∈ u, ∀ i, ContinuousAt (x ↦ ∫ s in (0)..t, ∫ z, witnessFieldDeriv … i (t−s) x z · F s z) x₀`
      from the carried G2 cores.  This is the `hcont` slot of `PartialsToFDeriv.hAssembly_reduced`,
      concretely instantiated.  NOT `a₁ = R/6`.

  ── WHAT REMAINS CARRIED (each satisfiable, non-vacuous, NEVER the conclusion).
    • `hKmeas` — bare-kernel z-ae-measurability of `witnessFieldDeriv … x z`.  A genuine measurability
      input (about the `z`/base slot, DIFFERENT from the integral-continuity conclusion); satisfiable
      because the kernel is `G_τ(W z x)·(amplitude)` on the measurable base-gate `K` and `0` off it —
      a measurable-set-glued product of measurable functions.
    • `hFmeas` — measurability of each `F`-slice `z ↦ F s z` (a property of the source term `F`).
    • `hjoint` — joint `(s,z)`-ae-measurability of `(s,z) ↦ dH·F`.  Genuine joint-measurability input
      (about the product measure), satisfiable from the same gate/Gaussian/amplitude structure as
      `hKmeas` measured jointly; NOT the (fibrewise-integrated) conclusion.
    • `hdomS` — the x-UNIFORM pointwise z-domination in the `hsbound` order (`∀ᶠ x` outside `∀ᵐ s`).
      Satisfiable from `WitnessDerivDomination.witnessFieldDeriv_gate_envelope` (whose bound is x-free,
      hence the neighbourhood is uniform in `s`); a POINTWISE bound, strictly weaker than / different
      from the INTEGRAL bound it feeds.
    • The J4-161 carries (`hC2fam`, `henv`) thread through unchanged.

  NO `sorry`.  NO new axioms.  NO `expRho`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WitnessDerivDomination
import QIQTH.GcoefContinuity

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap QIQTH.HeatParametrixAnsatz
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound
open QIQTH.WitnessDerivDomination
open scoped Interval Topology BigOperators

namespace QIQTH.WitnessDerivMeasurability

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### SLOT 3 — `hsbound`: the outer s-dominator bound (analytic half).
    ############################################################################### -/

/-- **★ SLOT 3 — `hsbound_witness`.**  THE EXACT `hsbound` SHAPE for `dH := witnessFieldDeriv`, with
    the CONSTANT s-dominator `B ≡ C₀·Cf`.  From a carried x-UNIFORM pointwise z-domination `hdomS`
    (the `∀ᶠ x` OUTSIDE the `∀ᵐ s` — the order `hsbound` needs; satisfiable from the x-FREE envelope
    `witnessFieldDeriv_gate_envelope`) plus the EXACT Gaussian mass-one identity
    `gaussDdim_integral_eq_one` (`∫ z, G_σ z = 1`), `MeasureTheory.norm_integral_le_of_norm_le` gives
      `‖∫ z, dH·F ∂volume‖ ≤ ∫ z, (C₀·Cf)·G_{κ(t−s)} z ∂volume = (C₀·Cf)·1 = C₀·Cf`.
    The zero-width endpoint `s = t` is excluded a.e. (`{t}` is null).  NOT `a₁ = R/6`. -/
theorem hsbound_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (F : ℝ → Point n → ℝ) (u : Set (Point n))
    (κ C₀ Cf : ℝ) (hκ : 0 < κ) (ht : 0 < t)
    (hdomS : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᵐ z ∂(volume : Measure (Point n)),
          ‖witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z‖
            ≤ (C₀ * Cf) * gaussDdim (κ * (t - s)) z) :
    ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
      ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z ∂(volume : Measure (Point n))‖
        ≤ (C₀ * Cf) := by
  intro x₀ hx₀ i
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    rw [ae_iff]
    have hset : {a : ℝ | ¬ a ≠ t} = {t} := by ext a; simp
    rw [hset]; exact Real.volume_singleton
  filter_upwards [hdomS x₀ hx₀ i] with x hx
  filter_upwards [hx, hae] with s hsb hsne hmem
  have hmem' := hmem
  rw [Set.uIoc_of_le ht.le] at hmem'
  have hst : s < t := lt_of_le_of_ne hmem'.2 hsne
  have hσ : 0 < κ * (t - s) := mul_pos hκ (by linarith)
  have hgint : Integrable (fun z : Point n => (C₀ * Cf) * gaussDdim (κ * (t - s)) z) volume :=
    envelope_integrable (κ * (t - s)) hσ (C₀ * Cf)
  have hbz : ∀ᵐ z ∂(volume : Measure (Point n)),
      ‖witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z‖
        ≤ (C₀ * Cf) * gaussDdim (κ * (t - s)) z := hsb hmem
  calc ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z
            ∂(volume : Measure (Point n))‖
      ≤ ∫ z, (C₀ * Cf) * gaussDdim (κ * (t - s)) z ∂(volume : Measure (Point n)) :=
        MeasureTheory.norm_integral_le_of_norm_le hgint hbz
    _ = (C₀ * Cf) * ∫ z : Point n, gaussDdim (κ * (t - s)) z :=
        integral_const_mul (C₀ * Cf) _
    _ = (C₀ * Cf) * 1 := by rw [gaussDdim_integral_eq_one (κ * (t - s)) hσ]
    _ = (C₀ * Cf) := mul_one _

/-! ###############################################################################
    ### SLOT 4 — `hBint`: interval-integrability of the (constant) s-dominator.
    ############################################################################### -/

/-- **SLOT 4 — `hBint_witness`.**  The constant s-dominator `B ≡ C₀·Cf` is interval-integrable on
    `[0,t]` (`intervalIntegrable_const`).  Matches the `hBint` slot with `B i x₀ s = C₀·Cf` (the
    mass-one collapse of `(C₀·Cf)·∫ z G_{κ(t−s)} z`).  NOT `a₁ = R/6`. -/
theorem hBint_witness (t C₀ Cf : ℝ) :
    IntervalIntegrable (fun _ : ℝ => C₀ * Cf) volume 0 t :=
  intervalIntegrable_const

/-! ###############################################################################
    ### SLOT 1 — `hzmeas`: inner z-ae-measurability of `dH·F` (reduction).
    ############################################################################### -/

/-- **SLOT 1 — `hzmeas_witness`.**  THE EXACT `hzmeas` SHAPE for `dH := witnessFieldDeriv`, reduced to
    a carried BARE-KERNEL z-ae-measurability family `hKmeas` (`∀ᶠ x, AEStronglyMeasurable (z ↦
    witnessFieldDeriv … x z) ν`) and a measurable `F`-slice `hFmeas` via `AEStronglyMeasurable.mul`.
    NOT `a₁ = R/6`. -/
theorem hzmeas_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (F : ℝ → Point n → ℝ) (ν : Measure (Point n)) (u : Set (Point n))
    (hKmeas : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀,
          AEStronglyMeasurable (fun z => witnessFieldDeriv g gi hC hK S a b i (t - s) x z) ν)
    (hFmeas : ∀ s : ℝ, AEStronglyMeasurable (fun z => F s z) ν) :
    ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
      ∀ᶠ x in 𝓝 x₀,
        AEStronglyMeasurable (fun z => witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z) ν := by
  intro x₀ hx₀ i
  filter_upwards [hKmeas x₀ hx₀ i] with s hs hmem
  filter_upwards [hs hmem] with x hx
  exact hx.mul (hFmeas s)

/-! ###############################################################################
    ### SLOT 2 — `hsmeas`: outer s-ae-measurability of `s ↦ ∫ z, dH·F ∂ν` (reduction).
    ############################################################################### -/

/-- **SLOT 2 — `hsmeas_witness`.**  THE EXACT `hsmeas` SHAPE for `dH := witnessFieldDeriv`, reduced to
    a carried JOINT `(s,z)`-ae-measurability core `hjoint` (measurability of
    `(s,z) ↦ witnessFieldDeriv … (t−s) x z · F s z` on the product measure) via
    `MeasureTheory.AEStronglyMeasurable.integral_prod_right'`.  NOT `a₁ = R/6`. -/
theorem hsmeas_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (F : ℝ → Point n → ℝ) (ν : Measure (Point n)) [SFinite ν] (u : Set (Point n))
    (hjoint : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        AEStronglyMeasurable
          (fun p : ℝ × Point n =>
            witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2 * F p.1 p.2)
          ((volume.restrict (Set.uIoc 0 t)).prod ν)) :
    ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z ∂ν)
        (volume.restrict (Set.uIoc 0 t)) := by
  intro x₀ hx₀ i
  filter_upwards [hjoint x₀ hx₀ i] with x hx
  exact hx.integral_prod_right'

/-! ###############################################################################
    ### CAPSTONE — the full seven-slot G2 bundle at `witnessFieldDeriv`.
    ############################################################################### -/

/-- **★★ CAPSTONE — `g2_bundle_assembled`.**  Assembles ALL SEVEN G2 hypotheses at the concrete
    `dH := witnessFieldDeriv` — the three J4-161 slots (`hzcont` via `hzcont_witness`, `hzbound` via
    `hzbound_witness`, `hzint` via `hzint_witness`) and the four slots proved here (`hzmeas`,
    `hsmeas`, `hsbound`, `hBint`) — and feeds them into
    `GcoefContinuity.gcoef_continuity_discharge`, producing the continuity conclusion
      `∀ x₀ ∈ u, ∀ i, ContinuousAt (x ↦ ∫ s in (0)..t, ∫ z, witnessFieldDeriv … i (t−s) x z · F s z) x₀`.
    The dominators are `boundz i x₀ s z = (C₀·Cf)·G_{κ(t−s)} z` and `B i x₀ s = C₀·Cf` (mass-one).
    All inputs are the carried G2 cores (`hC2fam`, `henv`, `hKmeas`, `hFmeas`, `hjoint`, `hdomS`,
    `hFbd`) + banked facts; NONE is the conclusion.  NOT `a₁ = R/6`. -/
theorem g2_bundle_assembled (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (F : ℝ → Point n → ℝ) (u : Set (Point n))
    (κ C₀ Cf : ℝ) (hκ : 0 < κ) (ht : 0 < t) (hC₀ : 0 ≤ C₀)
    (hFbd : ∀ s z, |F s z| ≤ Cf)
    -- J4-161 STEP-1 carry (field-slot `C²` regularity family) for `hzcont`:
    (hC2fam : ∀ x₀ ∈ u, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᵐ z ∂(volume : Measure (Point n)),
        ContDiffAt ℝ 2 (fun x' => vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) x₀)
    -- J4-161 STEP-2 carry (bare-kernel x-free Gaussian envelope, `∀ᵐ s → ∀ᶠ x` order) for `hzbound`:
    (henv : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀, ∀ᵐ z ∂(volume : Measure (Point n)),
          |witnessFieldDeriv g gi hC hK S a b i (t - s) x z| ≤ C₀ * gaussDdim (κ * (t - s)) z)
    -- SLOT-1 carries (bare z-ae-measurability + measurable `F`-slice) for `hzmeas`:
    (hKmeas : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀,
          AEStronglyMeasurable (fun z => witnessFieldDeriv g gi hC hK S a b i (t - s) x z)
            (volume : Measure (Point n)))
    (hFmeas : ∀ s : ℝ, AEStronglyMeasurable (fun z => F s z) (volume : Measure (Point n)))
    -- SLOT-2 carry (joint `(s,z)`-ae-measurability) for `hsmeas`:
    (hjoint : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        AEStronglyMeasurable
          (fun p : ℝ × Point n =>
            witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2 * F p.1 p.2)
          ((volume.restrict (Set.uIoc 0 t)).prod (volume : Measure (Point n))))
    -- SLOT-3 carry (x-uniform pointwise z-domination, `∀ᶠ x → ∀ᵐ s` order) for `hsbound`:
    (hdomS : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᵐ z ∂(volume : Measure (Point n)),
          ‖witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z‖
            ≤ (C₀ * Cf) * gaussDdim (κ * (t - s)) z) :
    ∀ x₀ ∈ u, ∀ i : Fin n,
      ContinuousAt
        (fun x => ∫ s in (0)..t, ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z
          ∂(volume : Measure (Point n))) x₀ := by
  refine QIQTH.GcoefContinuity.gcoef_continuity_discharge t
    (fun i τ x z => witnessFieldDeriv g gi hC hK S a b i τ x z) F u
    (fun _ _ _ => C₀ * Cf)
    (fun _ _ s z => (C₀ * Cf) * gaussDdim (κ * (t - s)) z)
    ?hzmeas ?hzbound ?hzint ?hzcont ?hsmeas ?hsbound ?hBint
  case hzmeas =>
    exact hzmeas_witness g gi hC hK S a b t F volume u hKmeas hFmeas
  case hzbound =>
    exact hzbound_witness g gi hC hK S a b t F volume u κ C₀ Cf hC₀ hFbd henv
  case hzint =>
    intro x₀ _ i
    exact hzint_witness κ t hκ ht (C₀ * Cf)
  case hzcont =>
    exact hzcont_witness g gi hC hK S a b t F volume u hC2fam
  case hsmeas =>
    exact hsmeas_witness g gi hC hK S a b t F volume u hjoint
  case hsbound =>
    exact hsbound_witness g gi hC hK S a b t F u κ C₀ Cf hκ ht hdomS
  case hBint =>
    intro x₀ _ i
    exact hBint_witness t C₀ Cf

end QIQTH.WitnessDerivMeasurability

section AxiomChecks
open QIQTH.WitnessDerivMeasurability
#print axioms hsbound_witness
#print axioms hBint_witness
#print axioms hzmeas_witness
#print axioms hsmeas_witness
#print axioms g2_bundle_assembled
end AxiomChecks
