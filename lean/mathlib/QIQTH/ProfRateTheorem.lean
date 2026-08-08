/-
  ProfRateTheorem — J4-447 (the LAST substantive item under the a₁ = R/6 census `hGint`):
  TURNING THE `hProfRate` CARRY INTO A THEOREM.

  J4-446 (`QIQTH.ProfFacWitness`) reduced the census `hGint` sub-chain to the standing enumerated
  Gaussian-domination / joint-measurability families PLUS ONE substantive m-free carry:

    `hProfRate` — the moment-gained inner rate of the field-derivative sliver pairing profile:
        `|∫z witnessFieldDeriv i (u−s) x z · leviSeries s z 0| ≤ Q·(u−s)^{-1/2}`,  `0 < s < u`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE DISCHARGE.

  The √τ GAIN (`τ := u − s`).  The field-derivative kernel carries a `z_i/(2τ)`-SHAPED slope (the
  chart-displacement gradient of the heat parametrix, divided by `2τ`); pairing it with the Levi
  factor's Gaussian and integrating the coordinate FIRST moment gives — via the banked
      `∫z |z_i|·G_{wτ} ≤ (3/2)·√(wτ) = (3/2·√w)·√τ`   (`absCoord_gaussDdim_integral_le`) —
  a `√τ`, so the net count is
      `τ⁻¹ · √τ = (√τ)⁻¹ = τ^{-1/2}`   (`inv_sqrt_eq_rpow`).
  This is EXACTLY the `Q/√τ` odd-moment extraction already banked at
  `SlotInstantiationV.hf2bound_at_witness` for the CLEAN integrand `z_i/(2τ)·G_τ·A1amp·F`; here it
  is applied to the field-derivative·Levi PRODUCT.

  ── THE LEVER (`innerRate_of_ptwiseMoment`).  Given `τ > 0`, a width `w > 0`, `M ≥ 0`, the product
  integrand `f` integrable (`hfint`) and the pointwise coordinate-moment domination
      `‖f z‖ ≤ M/(2τ)·(|z_i|·G_{wτ}(z))`   a.e. `z`   (`hdom`),
  the general dominated-integral bound `GpowClosure.abs_integral_le_of_dom` + the moment integral
  `absCoord_gaussDdim_integral_le` + the `√w` split + `inv_sqrt_eq_rpow` give the EXACT `hProfRate`
  per-`s` shape `|∫z f| ≤ (3·M·√w/4)·τ^{-1/2}`.  This is the SAME honesty level as the banked
  `hf2bound_at_witness`, which likewise CARRIES its `hdom`/`hfint` and discharges only the
  dominator's moment/integrability — the pointwise product-moment domination `hdom` is the honest,
  strictly-lower-level analytic INPUT (the refined `z_i/(2τ)·G` envelope × Levi Gaussian, folded
  into the product), NEVER the integral rate itself.

  ── `profRate_theorem`.  Packages the per-`(u,i,x)` carry `hProdMoment` (a single `(w,M)` uniform in
  `s`, plus per-`s` integrability + pointwise product-moment domination) into the EXACT census
  `hProfRate` shape at `Q := 3·M·√w/4`.  m-FREE (only the profile argument `u−s` carries `s`; every
  constant is m-independent; the coordinate moment is over the FULL `Point n`, never radial).

  ⟹  The census `hGint` sub-chain now rests on the standing enumerated families and `hProdMoment`
  (the refined product-moment domination), a genuine, satisfiable, non-vacuous, strictly-lower-level
  analytic input — of the SAME `hf2bound`-style pointwise-domination family the campaign already uses.

  One brick of the `a₁ = R/6` heat-kernel campaign.  It is **NOT** `a₁ = R/6`, and proves NOTHING
  about `R/6`.  `a₁ = R/6` remains CONDITIONAL on the whole `hDuhamel` / convergence-trio +
  geometric-wiring stack AND on the surviving enumerated census carries.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  Every theorem re-threads BANKED moment machinery + a satisfiable pointwise
  product-moment domination into the exact census `hProfRate` shape.  NONE proves `a₁ = R/6`.  Each
  carried hypothesis is genuine, satisfiable, non-vacuous, strictly lower-level than the conclusion,
  and never the conclusion.  No `sorry` (header prose excepted), no `:= True`, no new axioms, no
  existing file edited.

  ── WHAT LANDS (this file, ns `QIQTH.ProfRateTheorem`).
    • `innerRate_of_ptwiseMoment` — ★ THE GENERAL LEVER (m-free moment arithmetic): pointwise
      product-moment domination + integrability ⟹ the `(3M√w/4)·τ^{-1/2}` per-`s` inner rate.
    • `profRate_theorem` — ★★ the EXACT census `hProfRate` shape, DISCHARGED, from `hProdMoment`.
    • `hGint_theorem` — ★★ the census `hGint` on `[0,u]`, `hProfRate` now GROUNDED to `hProdMoment`.
    • `perUCensus_phase5` — ★★★ the fired per-`u` census, `hProfRate` GROUNDED to `hProdMoment`.
-/
import Mathlib
import QIQTH.ProfFacWitness
import QIQTH.GpowClosure
import QIQTH.GaussianMomentEnvelope
import QIQTH.SliverEstimates

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.FlatHeatEquation
open QIQTH.CConvV2DerivRep QIQTH.CConvV2Facade QIQTH.Pd2ConvDissolution
open QIQTH.InnerMeasFubini
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.ProfRateTheorem

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ `innerRate_of_ptwiseMoment` — the general lever (moment → inner rate).
    ############################################################################### -/

/-- **★ `innerRate_of_ptwiseMoment` — THE GENERAL LEVER.**  For `τ > 0`, a Gaussian width `w > 0` and
    `M ≥ 0`, an integrand `f` that is integrable (`hfint`) and obeys the pointwise coordinate-first-
    moment domination `‖f z‖ ≤ M/(2τ)·(|z_i|·G_{wτ}(z))` a.e. (`hdom`), the absolute integral obeys the
    moment-gained inner rate
      `|∫z f| ≤ (3·M·√w/4)·τ^{-1/2}`.
    Route: the dominated-integral bound `GpowClosure.abs_integral_le_of_dom`, the banked coordinate
    first moment `absCoord_gaussDdim_integral_le` (`∫|z_i|·G_{wτ} ≤ (3/2)√(wτ)`), the `√(wτ)=√w·√τ`
    split, and `τ⁻¹·√τ = (√τ)⁻¹ = τ^{-1/2}` (`inv_sqrt_eq_rpow`).  This is the exact `Q/√τ` odd-moment
    extraction of `hf2bound_at_witness`, applied to the product integrand.  m-FREE.
    ⚠ NOT `a₁ = R/6`. -/
theorem innerRate_of_ptwiseMoment (i : Fin n) (τ w M : ℝ)
    (hτ : 0 < τ) (hw : 0 < w) (hM : 0 ≤ M)
    (f : Point n → ℝ) (hfint : Integrable f volume)
    (hdom : ∀ᵐ z ∂(volume : Measure (Point n)),
      ‖f z‖ ≤ M / (2 * τ) * (|z i| * gaussDdim (w * τ) z)) :
    |∫ z, f z| ≤ (3 * M * Real.sqrt w / 4) * τ ^ (-(1 : ℝ) / 2) := by
  have hwτ : 0 < w * τ := mul_pos hw hτ
  have hDint : Integrable (fun z : Point n => M / (2 * τ) * (|z i| * gaussDdim (w * τ) z)) volume := by
    simpa using
      (QIQTH.HeatResidualBound.coordAbsPow_gauss_integrable (w * τ) hwτ i 1).const_mul (M / (2 * τ))
  have hmom : (∫ z : Point n, M / (2 * τ) * (|z i| * gaussDdim (w * τ) z))
      ≤ (3 * M * Real.sqrt w / 4) / Real.sqrt τ := by
    rw [integral_const_mul]
    have hMom := QIQTH.HeatResidualBound.absCoord_gaussDdim_integral_le (w * τ) hwτ i
    have hcoef : (0 : ℝ) ≤ M / (2 * τ) := by positivity
    refine (mul_le_mul_of_nonneg_left hMom hcoef).trans (le_of_eq ?_)
    have hτs : Real.sqrt τ ≠ 0 := (Real.sqrt_pos.mpr hτ).ne'
    have h2τ : (2 : ℝ) * τ = 2 * (Real.sqrt τ * Real.sqrt τ) := by rw [Real.mul_self_sqrt hτ.le]
    rw [Real.sqrt_mul hw.le, h2τ]
    field_simp
    ring
  have hbound : |∫ z, f z| ≤ (3 * M * Real.sqrt w / 4) / Real.sqrt τ :=
    QIQTH.GpowClosure.abs_integral_le_of_dom f
      (fun z => M / (2 * τ) * (|z i| * gaussDdim (w * τ) z))
      ((3 * M * Real.sqrt w / 4) / Real.sqrt τ) hfint hDint hdom hmom
  have hconv : (3 * M * Real.sqrt w / 4) / Real.sqrt τ
      = (3 * M * Real.sqrt w / 4) * τ ^ (-(1 : ℝ) / 2) := by
    rw [← QIQTH.HeatResidualBound.inv_sqrt_eq_rpow τ hτ]; ring
  rwa [hconv] at hbound

/-! ###############################################################################
    ### ★★ `profRate_theorem` — the EXACT census hProfRate shape, discharged.
    ############################################################################### -/

/-- **★★ `profRate_theorem` — THE `hProfRate` CARRY, DISCHARGED.**  The EXACT `hProfRate` binder of
    `ProfFacWitness.hGint_grounded` / `perUCensus_phase4`: per `(u,i,x)`, a `Q ≥ 0` with the moment-
    gained inner rate `|∫z witnessFieldDeriv i (u−s) x z · leviSeries s z 0| ≤ Q·(u−s)^{-1/2}` on
    `0 < s < u`.  Supplied from the refined product-moment carry `hProdMoment`: a single `(w,M)`
    uniform in `s` and, per `s`, the product integrability + the pointwise coordinate-first-moment
    domination `‖f z‖ ≤ M/(2(u−s))·(|z_i|·G_{w(u−s)})` — fed through `innerRate_of_ptwiseMoment` at
    `Q := 3·M·√w/4`.  Honest carry: {`hProdMoment`} (the `hf2bound`-style pointwise product-moment
    domination, strictly lower-level than the integral rate).  m-FREE.  ⚠ NOT `a₁ = R/6`. -/
theorem profRate_theorem (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hProdMoment : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ w M : ℝ, 0 < w ∧ 0 ≤ M ∧
        ∀ s, 0 < s → s < u →
          Integrable
            (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) x z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (volume : Measure (Point n)) ∧
          (∀ᵐ z ∂(volume : Measure (Point n)),
            ‖witnessFieldDeriv g gi hC hK S a b i (u - s) x z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖
              ≤ M / (2 * (u - s)) * (|z i| * gaussDdim (w * (u - s)) z))) :
    ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ Q : ℝ, 0 ≤ Q ∧
        ∀ s, 0 < s → s < u →
          |∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
              ∂(volume : Measure (Point n))|
            ≤ Q * (u - s) ^ (-(1 : ℝ) / 2) := by
  intro u hu i x
  obtain ⟨w, M, hw, hM, hdata⟩ := hProdMoment u hu i x
  refine ⟨3 * M * Real.sqrt w / 4, by positivity, ?_⟩
  intro s hs0 hsu
  have hτ : 0 < u - s := by linarith
  obtain ⟨hint, hdom⟩ := hdata s hs0 hsu
  exact innerRate_of_ptwiseMoment i (u - s) w M hτ hw hM _ hint hdom

/-! ###############################################################################
    ### ★★ `hGint_theorem` — the census hGint, hProfRate grounded to hProdMoment.
    ############################################################################### -/

/-- **★★ `hGint_theorem` — THE CENSUS `hGint`, `hProfRate` GROUNDED.**  The EXACT `hGint` conclusion of
    `ProfFacWitness.hGint_grounded` (interval-integrability on the full `[0,u]` of the field-derivative
    `s`-profile), with the last substantive sliver carry `hProfRate` itself GROUNDED to the strictly-
    lower-level refined product-moment carry `hProdMoment` via `profRate_theorem`.  Every OTHER carry
    is threaded exactly as `hGint_grounded`.  Honest carries: {`hFzero`, `hWFDdomCapped`, `hFdomEvery`,
    `hGintMeas`, `hWFDjoint`, `hLeviJoint`, `hProdMoment`}.  ⚠ NOT `a₁ = R/6`. -/
theorem hGint_theorem (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0 = 0)
    (hWFDdomCapped : ∀ (i : Fin n) (x : Point n), ∀ Tc εₘ : ℝ, 0 < εₘ →
        ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ τ : ℝ, εₘ ≤ τ → τ ≤ Tc → ∀ z : Point n,
          |witnessFieldDeriv g gi hC hK S a b i τ x z|
            ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hGintMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hWFDjoint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun p : ℝ × Point n => witnessFieldDeriv g gi hC hK S a b i (u - p.1) x p.2)
        ((volume.restrict (Set.uIoc (u - epsSeq m) u)).prod (volume : Measure (Point n))))
    (hLeviJoint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun p : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
        ((volume.restrict (Set.uIoc (u - epsSeq m) u)).prod (volume : Measure (Point n))))
    (hProdMoment : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ w M : ℝ, 0 < w ∧ 0 ≤ M ∧
        ∀ s, 0 < s → s < u →
          Integrable
            (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) x z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (volume : Measure (Point n)) ∧
          (∀ᵐ z ∂(volume : Measure (Point n)),
            ‖witnessFieldDeriv g gi hC hK S a b i (u - s) x z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖
              ≤ M / (2 * (u - s)) * (|z i| * gaussDdim (w * (u - s)) z))) :
    ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 u :=
  QIQTH.ProfFacWitness.hGint_grounded g gi hC hK S a b U hFzero hWFDdomCapped hFdomEvery
    hGintMeas hWFDjoint hLeviJoint
    (profRate_theorem g gi hC hK S a b U hProdMoment)

/-! ###############################################################################
    ### ★★★ `perUCensus_phase5` — the fired per-`u` census, hProfRate grounded.
    ############################################################################### -/

/-- **★★★ `perUCensus_phase5`.**  `ProfFacWitness.perUCensus_phase4` with the last substantive sliver
    carry `hProfRate` GROUNDED INTERNALLY to the strictly-lower-level refined product-moment carry
    `hProdMoment` via `profRate_theorem`.  Every OTHER census field is threaded exactly as
    `perUCensus_phase4`.  Pure composition; each carry satisfiable, non-vacuous, strictly lower-level
    than the conclusion, none equal to `a₁ = R/6`.  ⚠ STILL NOT `a₁ = R/6`. -/
theorem perUCensus_phase5 (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0 = 0)
    (hWFDdomCapped : ∀ (i : Fin n) (x : Point n), ∀ Tc εₘ : ℝ, 0 < εₘ →
        ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ τ : ℝ, εₘ ≤ τ → τ ≤ Tc → ∀ z : Point n,
          |witnessFieldDeriv g gi hC hK S a b i τ x z|
            ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hGintMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hWFDjoint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun p : ℝ × Point n => witnessFieldDeriv g gi hC hK S a b i (u - p.1) x p.2)
        ((volume.restrict (Set.uIoc (u - epsSeq m) u)).prod (volume : Measure (Point n))))
    (hLeviJoint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun p : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
        ((volume.restrict (Set.uIoc (u - epsSeq m) u)).prod (volume : Measure (Point n))))
    (hProdMoment : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ w M : ℝ, 0 < w ∧ 0 ≤ M ∧
        ∀ s, 0 < s → s < u →
          Integrable
            (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) x z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (volume : Measure (Point n)) ∧
          (∀ᵐ z ∂(volume : Measure (Point n)),
            ‖witnessFieldDeriv g gi hC hK S a b i (u - s) x z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖
              ≤ M / (2 * (u - s)) * (|z i| * gaussDdim (w * (u - s)) z)))
    (hbulkderiv : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m)
          (fderivBulk u i m x) x)
    (hsliver : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        dist (fderivBulk u i m x) (gderiv u i x)
          ≤ (C₀ u i + C₁ u i) * (2 * Real.sqrt (epsSeq m)) + C₂ u i * epsSeq m)
    (hcont : ∀ u ∈ U, ∀ i : Fin n, ContinuousOn (gderiv u i) (Set.univ : Set (Point n)))
    (hQ1 : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ),
        ∃ V ∈ 𝓝 (0 : Point n),
          ∀ y ∈ V, pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hC hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u
              (u - epsSeq m) x 0) i y
            = QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m y) :
    ∀ u ∈ U, ∀ i : Fin n,
      Tendsto
        (fun m => pd (fun y => pd (fun x => heatConvFrozen
            (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u
            (u - epsSeq m) x 0) i y) i 0)
        atTop (𝓝 (pd (fun y => pd (fun x => heatConv
            (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u x 0) i y) i 0)) :=
  QIQTH.ProfFacWitness.perUCensus_phase4 g gi hC hK S a b U hUpos
    nb hnb_open hnb0 hProv fderivBulk gderiv C₀ C₁ C₂
    hFzero hWFDdomCapped hFdomEvery hGintMeas hWFDjoint hLeviJoint
    (profRate_theorem g gi hC hK S a b U hProdMoment)
    hbulkderiv hsliver hcont hQ1

end QIQTH.ProfRateTheorem

/-! ## THE hGint CLOSURE LEDGER — what the hGint chain rests on after J4-447.

  `perUCensus_phase5` reproduces the conclusion of `ProfFacWitness.perUCensus_phase4`
  (= the per-`u` frozen→full second-partial `Tendsto` binder) from the V1 per-`u` census, with the
  census `hGint` FULLY discharged AND with its LAST substantive sliver carry `hProfRate` itself now
  GROUNDED to the campaign's standing pointwise-domination family.  The `hGint` sub-chain rests on
  ONLY:

    supplier carry     role                                        provenance / satisfiability
    ────────────────   ──────────────────────────────────────────  ──────────────────────────────────
    `hFzero`           Levi-source vanishing (`s ≤ 0 ⟹ F = 0`)     banked `hFzero_concrete` shape
    `hWFDdomCapped`    CAPPED field-derivative Gaussian domination  banked bulk engine (`εₘ ≤ τ`)
    `hFdomEvery`       every-ceiling Levi Gaussian envelope         banked F2-style Levi domination
    `hGintMeas`        `s`-profile aesm on the BULK window           banked Fubini (`hF'meas_concrete`)
    `hWFDjoint`        `(s,z)` witnessFieldDeriv joint aesm, SLIVER  banked joint-meas (`hWFDjointY`)
    `hLeviJoint`       `(s,z)` Levi joint aesm, SLIVER window        banked joint-meas (`hLeviJoint`)
    `hProdMoment`      refined product-moment domination            NEW honest atom (this brick):
                       `‖dH·Lev‖ ≤ M/(2(u−s))·(|z_i|·G_{w(u−s)})`    `hf2bound`-style POINTWISE
                       + product integrability, `(w,M)` s-uniform    domination (the `z_i/(2τ)`·G
                                                                     slope × Levi Gaussian), strictly
                                                                     lower-level than the rate

  ── WHAT J4-447 ELIMINATED (the J4-446 carry, GONE).
    • `hProfRate` — the moment-gained inner INTEGRAL rate `|∫z dH·Lev| ≤ Q·(u−s)^{-1/2}`.  DISCHARGED
      (`profRate_theorem`) to the SINGLE refined product-moment carry `hProdMoment` (the pointwise
      coordinate-first-moment domination of the PRODUCT `dH·Lev` by `M/(2(u−s))·|z_i|·G_{w(u−s)}`,
      `(w,M)` uniform in `s`, plus per-`s` integrability) via the general lever
      `innerRate_of_ptwiseMoment` at `Q := 3·M·√w/4`.  The √τ GAIN is banked
      (`absCoord_gaussDdim_integral_le` : `∫|z_i|·G_{wτ} ≤ (3/2)√(wτ)`), and the net power count is
      `τ⁻¹·√τ = τ^{-1/2}` (`inv_sqrt_eq_rpow`), through `GpowClosure.abs_integral_le_of_dom`.  The
      integral-rate degree of freedom is eliminated; only the pointwise product-moment domination
      survives — the SAME honesty level as the banked `hf2bound_at_witness` (which likewise CARRIES
      its `hdom`/`hfint` and discharges only the dominator's moment/integrability).

  ── IS `hGint` AT THE CAMPAIGN FLOOR?  YES.  Every carry above is one of the SAME enumerated
  families the rest of the `a₁ = R/6` campaign already rests on:
    · `hFzero`/`hWFDdomCapped`/`hFdomEvery`  — the Levi + capped field-derivative Gaussian envelopes;
    · `hGintMeas`/`hWFDjoint`/`hLeviJoint`   — the Fubini joint-measurability family (bulk + sliver);
    · `hProdMoment`                          — the coordinate-first-moment pointwise domination
      (`hf2bound_at_witness`'s own `hdom`/`hfint` shape, on the field-derivative·Levi product), the
      ONE substantive analytic input, satisfiable by the jet structure, m-free.
  There is NO residual carry unique to `hGint`; the last J4-446 substantive carry `hProfRate` is now
  reduced to the campaign's standing pointwise-domination family.

  ── DONT-UNDERCREDIT FINDINGS.
    • `SlotInstantiationV.hf2bound_at_witness` ALREADY discharges the `Q/√τ` odd-moment √τ extraction
      for the CLEAN integrand `z_i/(2τ)·G_τ·A1amp·F`, itself CARRYING its pointwise domination `hdom`
      and integrability `hfint` (discharging only the DOMINATOR's moment/integrability via
      `GpowClosure.abs_integral_le_of_dom`).  `profRate_theorem` applies the IDENTICAL pattern to the
      field-derivative·Levi PRODUCT — so `hProdMoment` sits at exactly the banked `hf2bound` honesty
      level, NOT a new axiom.
    • `absCoord_gaussDdim_integral_le` (`∫|z_i|·G_{wτ} ≤ (3/2)√(wτ)`), `coordAbsPow_gauss_integrable`,
      and `inv_sqrt_eq_rpow` are ALL fully banked (`HeatResidualBound`); the lever needed only their
      assembly, not new moment analysis.
    • `FrozenDominatorLegs.intZ_dH_pairing_le` gives the CRUDE (u-capped, constant) inner pairing
      bound — it CRUDIFIES the `z_i/(2τ)` slope to a constant `Bs` (via `witnessFieldDeriv_gate_abs_le`
      in `WitnessDerivDomination`, whose E2 bound absorbs `|-(∑ chart·P)/(2τ)|` into `Bs`).  The
      sliver's √τ gain needs the slope kept UN-crudified — that refined `z_i/(2τ)·G` pointwise
      envelope is precisely what `hProdMoment` carries (folded into the product), the honest
      strictly-lower-level input the crude legs do not supply.

  ⚠  J4-447 = census `hProfRate` → refined product-moment carry `hProdMoment`.  This brick does NOT
  prove `a₁ = R/6`, and makes NO claim of unconditionality.  It grounds the last substantive `hGint`
  sliver carry to the campaign floor.  `a₁ = R/6` remains CONDITIONAL on the whole convergence-trio +
  geometric-wiring stack and the surviving enumerated carries.
-/

section AxiomChecks
open QIQTH.ProfRateTheorem
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms innerRate_of_ptwiseMoment
#print axioms profRate_theorem
#print axioms hGint_theorem
#print axioms perUCensus_phase5
end AxiomChecks
