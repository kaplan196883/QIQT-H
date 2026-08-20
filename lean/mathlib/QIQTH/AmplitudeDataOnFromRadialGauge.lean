/-
  AmplitudeDataOnFromRadialGauge — threading the J4-893 named `RadialNormalCoordinateGauge` interface
  into the ACTUAL constructible collar amplitude bundle and the named collar-sliver census.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  No `sorry`
  (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no
  hypothesis equal to (or trivially yielding) the conclusion, no existing banked file edited.

  ## CONTEXT — the correct target for the radial-gauge center identities.
  The `hDConv` center-identity wall was NAMED and REDUCED in J4-893 (`RadialGaugeInterface`,
  `HDConvReducedToRadialGauge`): the `HjetsShape` center identities `hVP`/`hPsq`/`hVQ` follow from the
  clean, curved-satisfiable `RadialNormalCoordinateGauge g gi` + a base-point pullback bridge.  A fresh
  audit of the discharge chain establishes the ARCHITECTURAL FACT that the UNRESTRICTED
  `AmplitudePackage.AmplitudeDerivativeData` (whose `hD2Hexpand` holds for ALL `τ ∈ Ioo 0 τ₀, ∀ z`) is
  NOT constructible for the curved witness — the Leibniz–Gaussian identity relies on the near-isometry
  ratio `rhoRatio`, bounded only ON THE COLLAR (`AmplitudeDerivativeDataConcrete` header §; the memory's
  chain `hbnd_concrete ← AmplitudeDerivativeData` therefore routes through a NON-constructible
  intermediate).  The ACTUAL constructible object is the collar-restricted
  `AmplitudeDataOnCollar.AmplitudeDerivativeDataOn` via `amplitudeDataOn_concrete`, whose ONE center-
  identity-bearing field is `hjets` (verbatim `AmpGeometryBundle.HjetsShape`), and whose sliver bound
  is `SliverAssemblyMatched.amplitudePackageOn_sliver_bound` with the enumerated 5-carry census
  `hbnd_concrete_v2_carries {hcubic, hgate, hdisp, hjets, hcenter}`.

  ## WHAT THIS FILE LANDS — the radial gauge threaded into the CONSTRUCTIBLE collar route.
    • `amplitudeDataOn_from_radialGauge` — the collar bundle `AmplitudeDerivativeDataOn` CONSTRUCTED
      with its `hjets` field supplied by `HjetsShape_of_radialGauge_at_gate` (from
      `RadialNormalCoordinateGauge g gi` + the collar-quantified mechanical jet suppliers + the pullback
      bridge), all other carries of `amplitudeDataOn_concrete` passed through verbatim.  This
      MATERIALISES the collar amplitude bundle with the center-identity leg reduced to the single clean
      named `RadialNormalCoordinateGauge` — i.e. the constructor census with its geometric field
      radial-gauge-threaded.
    • `radialGauge_discharges_hjets_carry` — the `hjets` carry (item 4) of the NAMED collar-sliver
      census `SliverAssemblyMatched.hbnd_concrete_v2_carries` is DISCHARGED by
      `RadialNormalCoordinateGauge` + the mechanical jet suppliers + the pullback bridge.
    • `hbnd_v2_census_of_radialGauge` — the full 5-carry sliver census assembled with its `hjets` slot
      filled from the radial gauge, given the OTHER four carries (`hcubic`/`hgate`/`hdisp`/`hcenter`) as
      hypotheses.  Places `RadialNormalCoordinateGauge` explicitly INTO the named census.

  ## HOW FAR THIS REACHES (honest scope).  This threads `RadialNormalCoordinateGauge` into exactly the
  `hjets` (center-identity) slot of the constructible collar route — the ONE slot the gauge governs.
  The full `hbnd` binder of `HDConvGateThreading.hDConvSlot_AT_GATE` additionally needs the OTHER four
  sliver carries (`hcubic`/`hgate`/`hdisp`/`hcenter`), the pointwise `hinner` matched-pair inner
  estimate, and — beyond `hbnd` — the ~60 further genuine analytic hypotheses of the `hDConvSlot_AT_GATE`
  census (F2 differentiation-under-∫∫ pile, `hFII` tail-integrability, the Gaussian dominations
  `hEdom`/`hAdom`/`hWDom`, `MemLapFull`/`MemAdjLo`/`MemAdjHi`/`MemECombine`, and the boundary loc-unif
  frozen/moving lists).  `hDConv` does NOT reduce to just `RadialNormalCoordinateGauge`.  ⚠ a₁ = R/6
  remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HDConvReducedToRadialGauge
import QIQTH.AmplitudeDataOnCollar
import QIQTH.SliverAssemblyMatched

open Finset MeasureTheory
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.AmpGeometryBundle QIQTH.AmplitudeDataOnCollar
open QIQTH.HrepGermFactorization
open QIQTH.RadialGaugeInterface QIQTH.HDConvReducedToRadialGauge QIQTH.SliverAssemblyMatched
open scoped BigOperators

namespace QIQTH.AmplitudeDataOnFromRadialGauge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — the collar amplitude bundle constructed from the named radial gauge.
    ############################################################################### -/

/-- **★ `amplitudeDataOn_from_radialGauge`.**  The constructible collar amplitude bundle
    `AmplitudeDerivativeDataOn` for the true van-Vleck chart, over `collarRegime (K := K) r₀ c τ₀`,
    with its ONE center-identity-bearing field `hjets` supplied by `HjetsShape_of_radialGauge_at_gate`
    (from the clean named `RadialNormalCoordinateGauge g gi` + the collar-quantified mechanical jet
    suppliers `hSopen`/`h0`/`hV1`/`hP1`/`hA1`/`hA2` + the geodesic pullback bridge `hpull`).  Every
    other carry of `AmplitudeDataOnCollar.amplitudeDataOn_concrete` (`hiso`, the chart-amplitude sup-
    bounds, the Levi width-2 domination `hFdom`, the four measurabilities, `hqLip`) is passed through
    verbatim.  This materialises the collar derivative-layer bundle with the center-identity leg
    reduced to the single named radial-gauge hypothesis.  ⚠ NOT `a₁ = R/6`. -/
noncomputable def amplitudeDataOn_from_radialGauge (g gi : Point n → Fin n → Fin n → ℝ)
    (hgauge : RadialNormalCoordinateGauge g gi)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ : ℝ)
    (Liso c r₀ : ℝ) (hLiso : 0 ≤ Liso)
    (hiso : ∀ z ∈ K, ‖z‖ < r₀ →
      rncRadialSq z - Liso * ‖z‖ * rncRadialSq z
        ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0))
    (M₀chart M₁chart M₂chart Lq C_L : ℝ)
    (hM₀chart_nn : 0 ≤ M₀chart) (hM₁chart_nn : 0 ≤ M₁chart) (hM₂chart_nn : 0 ≤ M₂chart)
    (hLq : 0 ≤ Lq) (hC_L : 0 ≤ C_L)
    (hM₀chart : ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
      |chartAmp g gi hC hK a b τ z 0| ≤ M₀chart)
    (hM₁chart : ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
      |(-2 * pd (chartAmp g gi hC hK a b τ z) i 0)| ≤ M₁chart)
    (hM₂chart : ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
      |pd (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i 0| ≤ M₂chart)
    -- ── the radial-gauge center identities + mechanical jet suppliers (feeding `hjets`) ────────────
    (P : Point n → Point n → Fin n → ℝ) (Q : Point n → Fin n → ℝ)
    (hSopen : ∀ z, IsOpen (S z)) (h0 : ∀ z, (0 : Point n) ∈ S z)
    (hV1 : ∀ z x k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k) (P z x k) (x i))
    (hP1 : ∀ z k, HasDerivAt
      (fun s : ℝ => P z (Function.update (0 : Point n) i s) k) (Q z k) ((0 : Point n) i))
    (hA1 : ∀ τ z x, PdiffAt (chartAmp g gi hC hK a b τ z) i x)
    (hA2 : ∀ τ z, PdiffAt (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i (0 : Point n))
    (hpull : ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
      ((∑ k, uniformInverseChart g gi hC hK z 0 k * P z 0 k) = ∑ j, g z i j * z j) ∧
      ((∑ k, P z 0 k ^ 2) = g (0 : Point n) i i) ∧
      ((∑ k, uniformInverseChart g gi hC hK z 0 k * Q z k)
          = (∑ j, g z i j * z j) - (∑ j, gi z i j * z j)))
    -- ── the unchanged Levi / measurability / Lipschitz feeds ──────────────────────────────────────
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hAampmeas : ∀ τ, AEStronglyMeasurable
      (fun z : Point n => rhoRatio g gi hC hK τ z * chartAmp g gi hC hK a b τ z 0) volume)
    (hA1ampmeas : ∀ τ, AEStronglyMeasurable
      (fun z : Point n =>
        rhoRatio g gi hC hK τ z * (-2 * pd (chartAmp g gi hC hK a b τ z) i 0)) volume)
    (hA2ampmeas : ∀ τ, AEStronglyMeasurable
      (fun z : Point n =>
        rhoRatio g gi hC hK τ z * pd (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i 0) volume)
    (hFmeas : ∀ s, AEStronglyMeasurable (fun z : Point n => F s z 0) volume)
    (hqLip : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ s, 0 < s → s ≤ T → ∀ z w : Point n,
      |(rhoRatio g gi hC hK τ z * chartAmp g gi hC hK a b τ z 0) * F s z 0
          - (rhoRatio g gi hC hK τ w * chartAmp g gi hC hK a b τ w 0) * F s w 0|
        ≤ Lq * dist z w) :
    AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀) :=
  amplitudeDataOn_concrete g gi hC hK S a b F i T τ₀ Liso c r₀ hLiso hiso
    M₀chart M₁chart M₂chart Lq C_L hM₀chart_nn hM₁chart_nn hM₂chart_nn hLq hC_L
    hM₀chart hM₁chart hM₂chart
    (fun τ z hreg =>
      HjetsShape_of_radialGauge_at_gate g gi hgauge hC hK S a b i c r₀ τ₀
        P Q hSopen h0 hV1 hP1 hA1 hA2 hpull τ z hreg)
    hFdom hAampmeas hA1ampmeas hA2ampmeas hFmeas hqLip

/-! ###############################################################################
    ### §2 — the radial gauge threaded into the named collar-sliver census.
    ############################################################################### -/

/-- **`radialGauge_discharges_hjets_carry`.**  The `hjets` carry (item 4) of the named collar-sliver
    census `SliverAssemblyMatched.hbnd_concrete_v2_carries` — the collar-quantified chart jet supply +
    center identities feeding `hD2HexpandOn_concrete` — is DISCHARGED by `RadialNormalCoordinateGauge`
    + the mechanical jet suppliers + the pullback bridge, via `HjetsShape_of_radialGauge_at_gate`.
    ⚠ NOT `a₁ = R/6`. -/
theorem radialGauge_discharges_hjets_carry (g gi : Point n → Fin n → Fin n → ℝ)
    (hgauge : RadialNormalCoordinateGauge g gi)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (c r₀ τ₀ : ℝ)
    (P : Point n → Point n → Fin n → ℝ) (Q : Point n → Fin n → ℝ)
    (hSopen : ∀ z, IsOpen (S z)) (h0 : ∀ z, (0 : Point n) ∈ S z)
    (hV1 : ∀ z x k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k) (P z x k) (x i))
    (hP1 : ∀ z k, HasDerivAt
      (fun s : ℝ => P z (Function.update (0 : Point n) i s) k) (Q z k) ((0 : Point n) i))
    (hA1 : ∀ τ z x, PdiffAt (chartAmp g gi hC hK a b τ z) i x)
    (hA2 : ∀ τ z, PdiffAt (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i (0 : Point n))
    (hpull : ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
      ((∑ k, uniformInverseChart g gi hC hK z 0 k * P z 0 k) = ∑ j, g z i j * z j) ∧
      ((∑ k, P z 0 k ^ 2) = g (0 : Point n) i i) ∧
      ((∑ k, uniformInverseChart g gi hC hK z 0 k * Q z k)
          = (∑ j, g z i j * z j) - (∑ j, gi z i j * z j))) :
    ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z → HjetsShape g gi hC hK S a b i τ z :=
  HjetsShape_of_radialGauge_at_gate g gi hgauge hC hK S a b i c r₀ τ₀
    P Q hSopen h0 hV1 hP1 hA1 hA2 hpull

/-- **`hbnd_v2_census_of_radialGauge`.**  The full 5-carry collar-sliver census
    `SliverAssemblyMatched.hbnd_concrete_v2_carries` assembled with its `hjets` slot FILLED from the
    named `RadialNormalCoordinateGauge` (via `radialGauge_discharges_hjets_carry`), given the OTHER four
    carries (`hcubic`/`hgate`/`hdisp`/`hcenter`) as explicit hypotheses.  This places
    `RadialNormalCoordinateGauge` explicitly into the named census, isolating the genuine residue as
    exactly the four remaining sliver carries.  ⚠ NOT `a₁ = R/6`. -/
theorem hbnd_v2_census_of_radialGauge (g gi : Point n → Fin n → Fin n → ℝ)
    (hgauge : RadialNormalCoordinateGauge g gi)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (c r₀ τ₀ : ℝ)
    (P : Point n → Point n → Fin n → ℝ) (Q : Point n → Fin n → ℝ)
    (hSopen : ∀ z, IsOpen (S z)) (h0 : ∀ z, (0 : Point n) ∈ S z)
    (hV1 : ∀ z x k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k) (P z x k) (x i))
    (hP1 : ∀ z k, HasDerivAt
      (fun s : ℝ => P z (Function.update (0 : Point n) i s) k) (Q z k) ((0 : Point n) i))
    (hA1 : ∀ τ z x, PdiffAt (chartAmp g gi hC hK a b τ z) i x)
    (hA2 : ∀ τ z, PdiffAt (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i (0 : Point n))
    (hpull : ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
      ((∑ k, uniformInverseChart g gi hC hK z 0 k * P z 0 k) = ∑ j, g z i j * z j) ∧
      ((∑ k, P z 0 k ^ 2) = g (0 : Point n) i i) ∧
      ((∑ k, uniformInverseChart g gi hC hK z 0 k * Q z k)
          = (∑ j, g z i j * z j) - (∑ j, gi z i j * z j)))
    (hcubic hgate hdisp hcenter : Prop)
    (h1 : hcubic) (h2 : hgate) (h3 : hdisp) (h5 : hcenter) :
    hbnd_concrete_v2_carries hcubic hgate hdisp
      (∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z → HjetsShape g gi hC hK S a b i τ z) hcenter :=
  hbnd_concrete_v2_carries_intro h1 h2 h3
    (radialGauge_discharges_hjets_carry g gi hgauge hC hK S a b i c r₀ τ₀
      P Q hSopen h0 hV1 hP1 hA1 hA2 hpull) h5

end QIQTH.AmplitudeDataOnFromRadialGauge

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.AmplitudeDataOnFromRadialGauge.amplitudeDataOn_from_radialGauge
#print axioms QIQTH.AmplitudeDataOnFromRadialGauge.radialGauge_discharges_hjets_carry
#print axioms QIQTH.AmplitudeDataOnFromRadialGauge.hbnd_v2_census_of_radialGauge
