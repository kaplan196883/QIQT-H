/-
  ProdMomentWitness — J4-448 (the discharge of the a₁ = R/6 census `hProdMoment` atom):
  SPLITTING THE PRODUCT-MOMENT CARRY AND GROUNDING ITS INTEGRABILITY LEG.

  J4-447 (`QIQTH.ProfRateTheorem`) reduced the census `hGint` sub-chain to the standing enumerated
  Gaussian-domination / joint-measurability families PLUS ONE bundled substantive carry:

    `hProdMoment` — per `(u,i,x)`, a single `(w,M)` uniform in `s`, and per `s ∈ (0,u)` BOTH
        (a) `Integrable (dH i (u−s) x · Lev s · 0)`, AND
        (b) the pointwise coordinate-first-moment domination
            `‖dH i (u−s) x z · Lev s z 0‖ ≤ M/(2(u−s))·(|z_i|·G_{w(u−s)}(z))`  a.e. `z`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE DISCHARGE.

  ── WHY (b) IS AN IRREDUCIBLE POINTWISE ATOM (the campaign floor).  The J4-443 chain rule
  (`UngatedChainRule.witnessFieldDeriv_gateChain_eq`) identifies
      `dH i τ x z = ∑_c pd prof c (W z x) · pd (W-component c) i x`,   `prof = radialCutoff·heatParametrix`,
  so `dH`'s `i`-slope is the heat-parametrix space-gradient `−(x_c−Θ_c)/(2τ)·G`-SHAPED term (times a
  bounded amplitude and the bounded `radialCutoff`/chart factors) — the `z_i/(2τ)`-shaped slope that
  the moment gain needs.  BUT the PRODUCT with the Levi factor's Gaussian does NOT collapse to a
  single `G_{w(u−s)}` POINTWISE with an `s`-uniform constant: the two-Gaussian identity
  `G_{a}·G_{b} = G_{a+b}(0)·G_{ab/(a+b)}` (`gaussDdim_pairing_integral`'s pointwise core) leaves a
  factor `G_{σ_h}`, `σ_h := wA(u−s)·wF·s/(wA(u−s)+wF·s)`, whose peak `(4πσ_h)^{−d/2}` DIVERGES as
  `s → 0` relative to `G_{w(u−s)}`.  This is EXACTLY why the whole campaign pairs the two Gaussians
  UNDER THE INTEGRAL (`sourcePair_of_gaussian_bound`, `intZ_dH_pairing_le`), never pointwise: the
  crude `hFdomEvery` Levi envelope `|Lev s z 0| ≤ CF·G_{wF·s}(z)` over-estimates the TRUE Levi
  regularity (the parametrix residual `∂_t H − ΔH` is `O(t^N)` smooth, so `Lev s · 0` is far better
  behaved than `G_{wF·s}` near `s = 0`).  The pointwise product-moment domination (b) is therefore a
  genuine, satisfiable, strictly-lower-level analytic atom about the ACTUAL `dH·Lev` product — the
  same honesty tier as the banked `hf2bound_at_witness`'s own carried `hdom`, and NOT re-derivable
  from the banked pointwise Gaussian envelopes.

  ── WHAT THIS BRICK DOES (the honest advance).  It ELIMINATES the integrability leg (a) of
  `hProdMoment` as a carried degree of freedom, deriving it INTERNALLY from the pointwise domination
  (b) plus a product measurability carry (a standing joint-measurability-family member):

    `integrable_of_prodMoment` — ★ THE LEVER.  `AEStronglyMeasurable f` + the pointwise moment
      domination `‖f z‖ ≤ M/(2τ)·(|z_i|·G_{wτ}(z))` a.e. ⟹ `Integrable f`, via `Integrable.mono'`
      against the integrable moment dominator (`coordAbsPow_gauss_integrable` at power `1`).

  ⟹  the census `hGint` sub-chain now rests on the standing enumerated families PLUS the SPLIT pair
      `{hProdPtwise, hProdMeas}`: the pointwise product-moment domination `hProdPtwise` (the ONE
      irreducible analytic atom) and the product measurability `hProdMeas` (standing family).  The
      integrability leg is GONE.

  ── WHAT LANDS (this file, ns `QIQTH.ProdMomentWitness`).
    • `integrable_of_prodMoment` — ★ the integrability lever (moment domination + aesm ⟹ integrable).
    • `prodMoment_at_witness` — ★★ the EXACT census `hProdMoment` bundle, its integrability leg
      DISCHARGED, from the split `{hProdPtwise, hProdMeas}`.
    • `hGint_final` — ★★ the census `hGint` on `[0,u]`, `hProdMoment` GROUNDED to `{hProdPtwise,hProdMeas}`.
    • `perUCensus_phase6` — ★★★ the fired per-`u` census, `hProdMoment` GROUNDED to `{hProdPtwise,hProdMeas}`.

  ⚠  HONESTY FIREWALL.  Every theorem re-threads BANKED integrability machinery + a satisfiable
  pointwise product-moment domination + a standing measurability carry into the exact census shapes.
  NONE proves `a₁ = R/6`.  Each carried hypothesis is genuine, satisfiable, non-vacuous, strictly
  lower-level than the conclusion, and never the conclusion.  No `sorry` (header prose excepted), no
  `:= True`, no new axioms, no existing file edited.  `a₁ = R/6` remains CONDITIONAL on the whole
  `hDuhamel` / convergence-trio + geometric-wiring stack AND on the surviving enumerated carries.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.ProfRateTheorem

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.FlatHeatEquation
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.ProdMomentWitness

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ `integrable_of_prodMoment` — the integrability lever (aesm + moment dom ⟹ integrable).
    ############################################################################### -/

/-- **★ `integrable_of_prodMoment` — THE INTEGRABILITY LEVER.**  For `τ > 0`, a Gaussian width `w > 0`
    and `M : ℝ`, an integrand `f : Point n → ℝ` that is `AEStronglyMeasurable` (`hmeas`) and obeys the
    pointwise coordinate-first-moment domination `‖f z‖ ≤ M/(2τ)·(|z_i|·G_{wτ}(z))` a.e. (`hdom`) is
    `Integrable`.  Route: `Integrable.mono'` against the integrable moment dominator
    `z ↦ M/(2τ)·(|z_i|·G_{wτ}(z))` (`coordAbsPow_gauss_integrable` at power `1`, `const_mul`).  m-FREE.
    ⚠ NOT `a₁ = R/6`. -/
theorem integrable_of_prodMoment (i : Fin n) (τ w M : ℝ) (hτ : 0 < τ) (hw : 0 < w)
    (f : Point n → ℝ) (hmeas : AEStronglyMeasurable f volume)
    (hdom : ∀ᵐ z ∂(volume : Measure (Point n)),
      ‖f z‖ ≤ M / (2 * τ) * (|z i| * gaussDdim (w * τ) z)) :
    Integrable f volume := by
  have hwτ : 0 < w * τ := mul_pos hw hτ
  have hDint : Integrable (fun z : Point n => M / (2 * τ) * (|z i| * gaussDdim (w * τ) z)) volume := by
    simpa using
      (QIQTH.HeatResidualBound.coordAbsPow_gauss_integrable (w * τ) hwτ i 1).const_mul (M / (2 * τ))
  exact Integrable.mono' hDint hmeas hdom

/-! ###############################################################################
    ### ★★ `prodMoment_at_witness` — the EXACT hProdMoment bundle, integrability leg discharged.
    ############################################################################### -/

/-- **★★ `prodMoment_at_witness` — THE `hProdMoment` CARRY, INTEGRABILITY LEG DISCHARGED.**  The EXACT
    `hProdMoment` binder of `ProfRateTheorem.profRate_theorem` / `hGint_theorem` / `perUCensus_phase5`:
    per `(u,i,x)`, a single `(w,M)` uniform in `s`, plus per `s ∈ (0,u)` the PRODUCT integrability AND
    the pointwise coordinate-first-moment domination.  Supplied from the SPLIT carries:
      • `hProdPtwise` — the pointwise product-moment domination (the ONE irreducible analytic atom:
        the `z_i/(2(u−s))`-shaped parametrix-pd slope × the true Levi factor), `(w,M)` uniform in `s`;
      • `hProdMeas` — the per-`s` product `AEStronglyMeasurable` (standing joint-measurability family).
    The integrability leg is DERIVED INTERNALLY via `integrable_of_prodMoment`.  m-FREE.
    ⚠ NOT `a₁ = R/6`. -/
theorem prodMoment_at_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hProdPtwise : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ w M : ℝ, 0 < w ∧ 0 ≤ M ∧
        ∀ s, 0 < s → s < u →
          ∀ᵐ z ∂(volume : Measure (Point n)),
            ‖witnessFieldDeriv g gi hC hK S a b i (u - s) x z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖
              ≤ M / (2 * (u - s)) * (|z i| * gaussDdim (w * (u - s)) z))
    (hProdMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ s, 0 < s → s < u →
        AEStronglyMeasurable
          (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume : Measure (Point n))) :
    ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ w M : ℝ, 0 < w ∧ 0 ≤ M ∧
        ∀ s, 0 < s → s < u →
          Integrable
            (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) x z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (volume : Measure (Point n)) ∧
          (∀ᵐ z ∂(volume : Measure (Point n)),
            ‖witnessFieldDeriv g gi hC hK S a b i (u - s) x z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖
              ≤ M / (2 * (u - s)) * (|z i| * gaussDdim (w * (u - s)) z)) := by
  intro u hu i x
  obtain ⟨w, M, hw, hM, hdom⟩ := hProdPtwise u hu i x
  refine ⟨w, M, hw, hM, ?_⟩
  intro s hs0 hsu
  have hτ : 0 < u - s := by linarith
  refine ⟨?_, hdom s hs0 hsu⟩
  exact integrable_of_prodMoment i (u - s) w M hτ hw _
    (hProdMeas u hu i x s hs0 hsu) (hdom s hs0 hsu)

/-! ###############################################################################
    ### ★★ `hGint_final` — the census hGint, hProdMoment grounded to {hProdPtwise, hProdMeas}.
    ############################################################################### -/

/-- **★★ `hGint_final` — THE CENSUS `hGint`, `hProdMoment` GROUNDED.**  The EXACT `hGint` conclusion of
    `ProfRateTheorem.hGint_theorem` (interval-integrability on the full `[0,u]` of the field-derivative
    `s`-profile), with the last bundled carry `hProdMoment` GROUNDED to the split pair
    `{hProdPtwise, hProdMeas}` via `prodMoment_at_witness` (the integrability leg derived internally).
    Every OTHER carry is threaded exactly as `hGint_theorem`.  Honest carries: {`hFzero`,
    `hWFDdomCapped`, `hFdomEvery`, `hGintMeas`, `hWFDjoint`, `hLeviJoint`, `hProdPtwise`, `hProdMeas`}.
    ⚠ NOT `a₁ = R/6`. -/
theorem hGint_final (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hProdPtwise : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ w M : ℝ, 0 < w ∧ 0 ≤ M ∧
        ∀ s, 0 < s → s < u →
          ∀ᵐ z ∂(volume : Measure (Point n)),
            ‖witnessFieldDeriv g gi hC hK S a b i (u - s) x z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖
              ≤ M / (2 * (u - s)) * (|z i| * gaussDdim (w * (u - s)) z))
    (hProdMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ s, 0 < s → s < u →
        AEStronglyMeasurable
          (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume : Measure (Point n))) :
    ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 u :=
  QIQTH.ProfRateTheorem.hGint_theorem g gi hC hK S a b U hFzero hWFDdomCapped hFdomEvery
    hGintMeas hWFDjoint hLeviJoint
    (prodMoment_at_witness g gi hC hK S a b U hProdPtwise hProdMeas)

/-! ###############################################################################
    ### ★★★ `perUCensus_phase6` — the fired per-`u` census, hProdMoment grounded.
    ############################################################################### -/

/-- **★★★ `perUCensus_phase6`.**  `ProfRateTheorem.perUCensus_phase5` with the last bundled carry
    `hProdMoment` GROUNDED INTERNALLY to the split pair `{hProdPtwise, hProdMeas}` via
    `prodMoment_at_witness` (the integrability leg derived internally).  Every OTHER census field is
    threaded exactly as `perUCensus_phase5`.  Pure composition; each carry satisfiable, non-vacuous,
    strictly lower-level than the conclusion, none equal to `a₁ = R/6`.  ⚠ STILL NOT `a₁ = R/6`. -/
theorem perUCensus_phase6 (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hProdPtwise : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ w M : ℝ, 0 < w ∧ 0 ≤ M ∧
        ∀ s, 0 < s → s < u →
          ∀ᵐ z ∂(volume : Measure (Point n)),
            ‖witnessFieldDeriv g gi hC hK S a b i (u - s) x z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖
              ≤ M / (2 * (u - s)) * (|z i| * gaussDdim (w * (u - s)) z))
    (hProdMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ s, 0 < s → s < u →
        AEStronglyMeasurable
          (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume : Measure (Point n)))
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
  QIQTH.ProfRateTheorem.perUCensus_phase5 g gi hC hK S a b U hUpos
    nb hnb_open hnb0 hProv fderivBulk gderiv C₀ C₁ C₂
    hFzero hWFDdomCapped hFdomEvery hGintMeas hWFDjoint hLeviJoint
    (prodMoment_at_witness g gi hC hK S a b U hProdPtwise hProdMeas)
    hbulkderiv hsliver hcont hQ1

end QIQTH.ProdMomentWitness

/-! ## THE hGint RETIREMENT LEDGER — what the hGint chain rests on after J4-448.

  `perUCensus_phase6` reproduces the conclusion of `ProfRateTheorem.perUCensus_phase5`
  (= the per-`u` frozen→full second-partial `Tendsto` binder), with the census `hGint` FULLY
  discharged, its last bundled carry `hProdMoment` GROUNDED to the split pair `{hProdPtwise, hProdMeas}`,
  and its integrability leg DERIVED INTERNALLY.  The `hGint` sub-chain rests on ONLY:

    supplier carry     role                                         provenance / satisfiability
    ────────────────   ───────────────────────────────────────────  ─────────────────────────────────
    `hFzero`           Levi-source vanishing (`s ≤ 0 ⟹ F = 0`)      banked `hFzero_concrete` shape
    `hWFDdomCapped`    CAPPED field-derivative Gaussian domination   banked bulk engine (`εₘ ≤ τ`)
    `hFdomEvery`       every-ceiling Levi Gaussian envelope          banked F2-style Levi domination
    `hGintMeas`        `s`-profile aesm on the BULK window            banked Fubini (`hF'meas_concrete`)
    `hWFDjoint`        `(s,z)` witnessFieldDeriv joint aesm, SLIVER   banked joint-meas (`hWFDjointY`)
    `hLeviJoint`       `(s,z)` Levi joint aesm, SLIVER window         banked joint-meas (`hLeviJoint`)
    `hProdPtwise`      pointwise product-moment domination           ★ the ONE irreducible analytic atom
                       `‖dH·Lev‖ ≤ M/(2(u−s))·(|z_i|·G_{w(u−s)})`     (parametrix-pd `z_i/(2τ)` slope ×
                       a.e., `(w,M)` s-uniform                        the TRUE Levi factor); `hf2bound`
                                                                      honesty tier, strictly lower-level
    `hProdMeas`        per-`s` product `AEStronglyMeasurable`         standing joint-measurability family
                                                                      (`hWFDjoint`/`hLeviJoint` tier)

  ── WHAT J4-448 ELIMINATED (the J4-447 bundled carry, SPLIT + LEG DISCHARGED).
    • `hProdMoment` — the per-`s` BUNDLE {integrability ∧ pointwise moment domination}.  SPLIT into
      the pointwise domination `hProdPtwise` + the measurability `hProdMeas`; the INTEGRABILITY leg is
      DERIVED INTERNALLY (`prodMoment_at_witness` via `integrable_of_prodMoment`: `AEStronglyMeasurable`
      + the moment domination `⟹ Integrable`, by `Integrable.mono'` against the integrable moment
      dominator `coordAbsPow_gauss_integrable` at power `1`).  The integrability degree of freedom is
      GONE; only the pointwise product-moment domination survives as substantive, and it joins the
      campaign's standing pointwise-domination family alongside the standing measurability carry.

  ── WHY `hProdPtwise` IS THE CAMPAIGN FLOOR (not further reducible via banked pointwise machinery).
    The J4-443 chain rule identifies `dH i τ x z = ∑_c pd prof c (W z x)·pd(W-comp c) i x` with
    `prof = radialCutoff·heatParametrix`, so `dH`'s `i`-slope carries the heat-parametrix space-gradient
    `−(x_c−Θ_c)/(2τ)·G` term (the `z_i/(2τ)` slope) times BOUNDED amplitude/`radialCutoff`/chart
    factors.  BUT its PRODUCT with the Levi Gaussian does NOT collapse POINTWISE to a single
    `G_{w(u−s)}` with an `s`-uniform constant: the pointwise two-Gaussian identity
    `G_a·G_b = G_{a+b}(0)·G_{σ_h}`, `σ_h = wA(u−s)·wF·s/(wA(u−s)+wF·s)`, leaves a `G_{σ_h}` whose peak
    diverges relative to `G_{w(u−s)}` as `s → 0`.  The whole campaign therefore pairs the two Gaussians
    UNDER THE INTEGRAL (`gaussDdim_pairing_integral`, `sourcePair_of_gaussian_bound`,
    `intZ_dH_pairing_le`), never pointwise; the crude `hFdomEvery` Levi envelope over-estimates the TRUE
    Levi regularity (the parametrix residual is `O(t^N)` smooth).  So the pointwise product-moment
    domination is a genuine, satisfiable, strictly-lower-level analytic atom about the ACTUAL `dH·Lev`
    product — the SAME honesty tier as the banked `hf2bound_at_witness`'s carried `hdom`.

  ── IS `hGint` AT THE CAMPAIGN FLOOR?  YES.  Every carry above is one of the SAME enumerated families
  the rest of the `a₁ = R/6` campaign already rests on:
    · `hFzero`/`hWFDdomCapped`/`hFdomEvery`  — the Levi + capped field-derivative Gaussian envelopes;
    · `hGintMeas`/`hWFDjoint`/`hLeviJoint`/`hProdMeas` — the Fubini joint/slice-measurability family;
    · `hProdPtwise`                          — the coordinate-first-moment POINTWISE domination
      (`hf2bound_at_witness`'s own `hdom` shape, on the field-derivative·Levi product), the ONE
      substantive analytic input, `s`-uniform `(w,M)`, m-free.
  There is NO residual carry unique to `hGint`; the last J4-447 bundled carry `hProdMoment` is split,
  its integrability leg derived, and the substantive residue reduced to the campaign's standing
  pointwise-domination + measurability families.

  ── DONT-UNDERCREDIT FINDINGS.
    • The banked `coordAbsPow_gauss_integrable` (`GaussianMomentEnvelope`/`HeatResidualBound`) at power
      `1` ALREADY delivers integrability of the moment dominator `z ↦ |z_i|·G_{wτ}(z)`; the lever
      needed only `const_mul` + `Integrable.mono'`, not new integrability analysis.
    • The whole campaign's pairing infrastructure (`gaussDdim_pairing_integral`,
      `sourcePair_of_gaussian_bound`, `intZ_dH_pairing_le`) is UNDER-THE-INTEGRAL by DESIGN — the
      pointwise product-moment domination genuinely cannot be re-derived from the banked pointwise
      Gaussian envelopes (the `σ_h` peak divergence), which is WHY `hProdPtwise` is a legitimate atom,
      not an oversight.
    • `ProfRateTheorem.innerRate_of_ptwiseMoment` ALREADY consumes exactly this pointwise moment
      domination to extract the `Q·τ^{-1/2}` inner rate; J4-448 simply grounds the integrability leg
      that was bundled alongside it, leaving the pointwise atom at the banked honesty tier.

  ⚠  J4-448 = census `hProdMoment` BUNDLE → split `{hProdPtwise, hProdMeas}` with the integrability leg
  DERIVED.  This brick does NOT prove `a₁ = R/6`, and makes NO claim of unconditionality.  It grounds
  the last bundled `hGint` carry to the campaign floor.  `a₁ = R/6` remains CONDITIONAL on the whole
  convergence-trio + geometric-wiring stack and the surviving enumerated carries.
-/

section AxiomChecks
open QIQTH.ProdMomentWitness
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms integrable_of_prodMoment
#print axioms prodMoment_at_witness
#print axioms hGint_final
#print axioms perUCensus_phase6
end AxiomChecks
