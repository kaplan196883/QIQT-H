/-
  MassChartBridge — J4-511: the `hmassone` CHART-BRIDGE (decoupling the mass hypothesis from
  `hframeK`), the SECOND fix piece of the J4-509 flat-only obstruction.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (J4-509 flat-only obstruction; J4-510 first fix piece).  The a₁ mainline
  `A1R6FromLabelled.a1_R6_from_labelled` is CONDITIONAL and J4-509 exhibited a demonstrated
  FLAT-ONLY obstruction: the pair
    • `hframeK : ∀ q∈K, g q = δ`  (the metric flat on ALL of the witness gate — forces `Ric(0)=0`);
    • `hmassone : Tendsto (fun m => ∫ z, Wit (epsSeq m) 0 z) atTop (𝓝 1)`  (the gated witness carries
      unit heat mass as `τ ↓ 0`)
  is jointly satisfiable only for `Ric(0)=0`.  J4-510 (`CurvedParametrixMass`) proved the CHART-variable
  content — `heatParametrix_setMass_tendsto_one` — that the curved parametrix mass → 1 over a fixed
  chart neighbourhood `Ω`, INDEPENDENT of `hframeK`, via the Gaussian approximate identity, with a
  genuinely-curved certificate.

  ⚠ WHAT THIS FILE DOES (J4-511).  Bridges J4-510's chart-variable (`w`) content to the repo's
  z-variable `hmassone` shape (`∫_z`), WITHOUT `hframeK`.  The bridge is Route B (confirmed by Sol):
  after the on-gate factorisation `Wit τ 0 z = gaussDdim τ (W₀ z)·chartFieldAmp τ z` and the chart
  change of variables `w = W₀ z`, the z-integral becomes
      `∫ z, Wit τ 0 z = ∫ w in Ω, gaussDdim τ w · (parametrixAmp N Θ u τ w · φ w)`,
  where `φ w = radialCutoff a b w / J(V w)` is a FIXED (`τ`-independent) chart weight with
      `φ(0) = radialCutoff(0)/J(0) = 1/J(0)`     (`radialCutoff ≡ 1` near `0` since `0 < a`),
  so `φ(0) = 1 ⟺ J(0) = 1` — the FIRST-ORDER chart Jacobian normalisation (NOT flatness on a
  neighbourhood; compatible with curved normal coordinates; Sol's `V(z)=2z` shows the Jacobian is
  genuinely necessary).  We take this change of variables as an ABSTRACT eventual equality hypothesis
  `hcov` (the concrete base-varying CoV bundle for `W₀` — M1–M4 — is the acknowledged MISSING brick,
  see `ChartImageAIConcrete`'s orientation verdict) and expose `φ(0)=1` as the sole curved-satisfiable
  carried input.  The limit is then delivered by the general MOVING approximate identity
  `ChartImageApproxIdentity.gaussDdim_set_approx_identity_moving`, reusing J4-510's amplitude lemmas
  `parametrixAmp_continuousAt_zero` / `parametrixAmp_zero_zero` (the guts of
  `heatParametrix_setMass_tendsto_one`) for the joint-local approach to `1`.

  WHAT LANDS.
    • `weightedParametrix_setMass_tendsto_one` — ★ the WEIGHTED chart mass → 1: for a fixed weight `φ`
      continuous at `0` with `φ(0)=1`, `∫ w in Ω, gaussDdim τ w · (parametrixAmp N Θ u τ w · φ w) → 1`
      over `𝓝[>]0`.  `hlocal` (joint approach to `1`) is PROVED — not assumed — from J4-510's amplitude
      joint-continuity × `φ`-continuity, value `1·1=1`.  Independent of flatness.
    • `chartMass_tendsto_one_of_weightedCovar` — ★ the CHART BRIDGE (`𝓝[>]0` form): transports the
      weighted limit across the abstract eventual change-of-variables equality `hcov` to the z-variable
      `∫_z` integral.  `Tendsto (fun τ => ∫ z, Wit τ 0 z) (𝓝[>]0) (𝓝 1)`.  NO `hframeK`.
    • `gatedKernel_mass_tendsto_one_of_localChart` — ★★ the exact `hmassone` shape (`atTop`/`epsSeq`):
      composes with `epsSeq → 𝓝[>]0` to produce `Tendsto (fun m => ∫ z, Wit (epsSeq m) 0 z) atTop (𝓝 1)`.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`.  This is the SECOND brick decoupling `hmassone` from `hframeK`
  (J4-510 = first).  It shows the z-variable mass → 1 follows from J4-510's curved parametrix content +
  a `J(0)=1` change of variables, WITHOUT flatness.  It does NOT by itself make `a1_R6_from_labelled`
  curved-satisfiable: (i) the concrete `hcov` for the base-varying chart `W₀` (the M1–M4 CoV bundle) is
  still MISSING; (ii) `hframeK` is ALSO consumed elsewhere (`hDaLimLU_from_labelled`), which must be
  weakened separately.  The carried inputs — `hcov` (abstract CoV), `φ` continuity + `φ(0)=1`
  (= `J(0)=1`), `hmeas`/`hbound` (genuine eventual a.e./bound carries), and J4-510's `Θ(0)=1`/`u₀(0)=1`
  — are curved-inhabited and none is the conclusion.  No `sorry`, no new axioms, no `:= True`.
-/
import Mathlib
import QIQTH.CurvedParametrixMass
import QIQTH.ConvApproximants

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.CurvedParametrixMass QIQTH.ChartImageApproxIdentity
open scoped Topology BigOperators

namespace QIQTH.MassChartBridge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### The weighted chart mass → 1 (Route B: general moving approximate identity + fixed weight). -/

/-- **★ J4-511 — THE WEIGHTED CHART MASS → 1.**  For `Ω` a measurable neighbourhood of the origin,
    the amplitude satisfying the diagonal DeWitt normalisation `Θ(0)=1`, `u₀(0)=1` (with `Θ`, `u_k`
    continuous at `0`), and a FIXED (`τ`-independent) chart weight `φ` continuous at `0` with `φ(0)=1`,
    the WEIGHTED curved-parametrix mass → 1:
        `∫ w in Ω, gaussDdim τ w · (parametrixAmp N Θ u τ w · φ w)  →  1`   in `𝓝[>]0`.
    ROUTE (Sol-confirmed Route B): apply the banked general MOVING approximate identity
    `gaussDdim_set_approx_identity_moving` with `g τ w := parametrixAmp N Θ u τ w · φ w` and `L := 1`;
    the `hlocal` (joint approach to `1`) is PROVED — not assumed — from J4-510's
    `parametrixAmp_continuousAt_zero` × the continuity of `φ`, valued
    `parametrixAmp(0,0)·φ(0) = 1·1 = 1` (`parametrixAmp_zero_zero`).  The weight carries the chart
    Jacobian and radial cutoff, and `φ(0)=1` is exactly the first-order `J(0)=1` normalisation
    (curved-satisfiable, NOT flatness).  `hmeas`/`hbound` are genuine eventual a.e./bound carries for
    the weighted integrand.  NOT `a₁ = R/6`. -/
theorem weightedParametrix_setMass_tendsto_one (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (φ : Point n → ℝ) {Ω : Set (Point n)} (hΩmeas : MeasurableSet Ω) (hΩnhds : Ω ∈ 𝓝 (0 : Point n))
    (hΘ0 : Θ (0 : Point n) = 1) (hu0 : u 0 (0 : Point n) = 1)
    (hΘcont : ContinuousAt Θ (0 : Point n)) (hucont : ∀ k, ContinuousAt (u k) (0 : Point n))
    (hφcont : ContinuousAt φ (0 : Point n)) (hφ0 : φ (0 : Point n) = 1)
    (hmeas : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
        AEStronglyMeasurable (fun w => parametrixAmp N Θ u τ w * φ w) (volume.restrict Ω))
    (hbound : ∃ C, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
        ∀ᵐ w ∂(volume.restrict Ω), ‖parametrixAmp N Θ u τ w * φ w‖ ≤ C) :
    Tendsto (fun τ => ∫ w in Ω, gaussDdim τ w * (parametrixAmp N Θ u τ w * φ w))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  -- joint continuity of the WEIGHTED amplitude at `(0,0)`, valued `1`
  have hA : ContinuousAt (fun p : ℝ × Point n => parametrixAmp N Θ u p.1 p.2) (0, 0) :=
    parametrixAmp_continuousAt_zero N Θ u hΘ0 hΘcont hucont
  have hφ2 : ContinuousAt (fun p : ℝ × Point n => φ p.2) ((0 : ℝ), (0 : Point n)) :=
    ContinuousAt.comp_of_eq hφcont continuousAt_snd rfl
  have hcont : ContinuousAt (fun p : ℝ × Point n => parametrixAmp N Θ u p.1 p.2 * φ p.2) (0, 0) :=
    hA.mul hφ2
  have hval : parametrixAmp N Θ u 0 (0 : Point n) * φ (0 : Point n) = 1 := by
    rw [parametrixAmp_zero_zero N Θ u hΘ0 hu0, hφ0]; ring
  -- derive `hlocal` (joint approach to `L = 1`) from continuity (mirrors J4-510)
  have hlocal : ∀ ε > 0, ∃ r > 0, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      ∀ᵐ w ∂(volume.restrict Ω), ‖w‖ < r → ‖parametrixAmp N Θ u τ w * φ w - 1‖ < ε := by
    intro ε εpos
    have hkey : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : Point n)),
        dist (parametrixAmp N Θ u p.1 p.2 * φ p.2)
          (parametrixAmp N Θ u 0 (0 : Point n) * φ (0 : Point n)) < ε :=
      Metric.tendsto_nhds.mp hcont.tendsto ε εpos
    rw [nhds_prod_eq, Filter.eventually_prod_iff] at hkey
    obtain ⟨pa, hpa, pb, hpb, hP⟩ := hkey
    obtain ⟨r, rpos, hr⟩ := Metric.eventually_nhds_iff.1 hpb
    refine ⟨r, rpos, ?_⟩
    filter_upwards [nhdsWithin_le_nhds hpa] with τ hτ
    refine Filter.Eventually.of_forall (fun w hw => ?_)
    have hwpb : pb w := hr (by simpa [dist_zero_right] using hw)
    have hd := hP hτ hwpb
    rw [Real.dist_eq, hval] at hd
    rw [Real.norm_eq_abs]; exact hd
  -- apply the banked general moving approximate identity at `L = 1`
  exact gaussDdim_set_approx_identity_moving hΩmeas hΩnhds hmeas hbound hlocal

/-! ### The chart bridge — z-variable mass → 1 on `𝓝[>]0`, WITHOUT `hframeK`. -/

/-- **★ J4-511 — THE CHART BRIDGE (`𝓝[>]0` form).**  For an ABSTRACT z-variable witness
    `Wit : ℝ → Point n → Point n → ℝ`, given the eventual change-of-variables equality `hcov` (the
    on-gate factorisation + chart change of variables output, carried abstractly because the concrete
    base-varying CoV bundle for `W₀` is the acknowledged MISSING brick) together with the DeWitt
    normalisation, the chart weight normalisation `φ(0)=1` (= the first-order Jacobian `J(0)=1`), and
    the genuine eventual carries `hmeas`/`hbound`, the z-variable heat mass → 1:
        `Tendsto (fun τ => ∫ z, Wit τ 0 z) (𝓝[>]0) (𝓝 1)`.
    Route: `weightedParametrix_setMass_tendsto_one` (the weighted chart mass) transported across `hcov`
    by `Tendsto.congr'`.  ⚠ NO `hframeK` / NO `g=δ` on any neighbourhood: the ONLY normalisation used is
    `φ(0)=1 ⟺ J(0)=1`, a first-order chart fact compatible with curved normal coordinates.  NOT
    `a₁ = R/6`. -/
theorem chartMass_tendsto_one_of_weightedCovar (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (φ : Point n → ℝ) (Wit : ℝ → Point n → Point n → ℝ)
    {Ω : Set (Point n)} (hΩmeas : MeasurableSet Ω) (hΩnhds : Ω ∈ 𝓝 (0 : Point n))
    (hΘ0 : Θ (0 : Point n) = 1) (hu0 : u 0 (0 : Point n) = 1)
    (hΘcont : ContinuousAt Θ (0 : Point n)) (hucont : ∀ k, ContinuousAt (u k) (0 : Point n))
    (hφcont : ContinuousAt φ (0 : Point n)) (hφ0 : φ (0 : Point n) = 1)
    (hmeas : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
        AEStronglyMeasurable (fun w => parametrixAmp N Θ u τ w * φ w) (volume.restrict Ω))
    (hbound : ∃ C, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
        ∀ᵐ w ∂(volume.restrict Ω), ‖parametrixAmp N Θ u τ w * φ w‖ ≤ C)
    (hcov : (fun τ => ∫ z, Wit τ (0 : Point n) z)
        =ᶠ[𝓝[>] (0 : ℝ)]
        (fun τ => ∫ w in Ω, gaussDdim τ w * (parametrixAmp N Θ u τ w * φ w))) :
    Tendsto (fun τ => ∫ z, Wit τ (0 : Point n) z) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hbase := weightedParametrix_setMass_tendsto_one N Θ u φ hΩmeas hΩnhds hΘ0 hu0 hΘcont hucont
    hφcont hφ0 hmeas hbound
  exact hbase.congr' hcov.symm

/-! ### The exact `hmassone` shape — `atTop` / `epsSeq`. -/

/-- **★★ J4-511 — THE `hmassone` CHART-BRIDGE (exact `atTop`/`epsSeq` shape).**  Composes
    `chartMass_tendsto_one_of_weightedCovar` with `epsSeq m = 1/(m+1) → 𝓝[>]0` to produce EXACTLY the
    repo's z-variable `hmassone` shape:
        `Tendsto (fun m => ∫ z, Wit (epsSeq m) 0 z) atTop (𝓝 1)`,
    from J4-510's curved parametrix content + a `J(0)=1` change of variables (`hcov` + `φ(0)=1`),
    WITHOUT `hframeK`.  This is the second piece decoupling `hmassone` from the flat-only obstruction.
    ⚠ CONDITIONAL on the abstract `hcov` (whose concrete base-varying CoV bundle for `W₀` is the
    acknowledged MISSING brick) and on `φ(0)=1` (= `J(0)=1`, curved-satisfiable).  NOT `a₁ = R/6`. -/
theorem gatedKernel_mass_tendsto_one_of_localChart (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (φ : Point n → ℝ) (Wit : ℝ → Point n → Point n → ℝ)
    {Ω : Set (Point n)} (hΩmeas : MeasurableSet Ω) (hΩnhds : Ω ∈ 𝓝 (0 : Point n))
    (hΘ0 : Θ (0 : Point n) = 1) (hu0 : u 0 (0 : Point n) = 1)
    (hΘcont : ContinuousAt Θ (0 : Point n)) (hucont : ∀ k, ContinuousAt (u k) (0 : Point n))
    (hφcont : ContinuousAt φ (0 : Point n)) (hφ0 : φ (0 : Point n) = 1)
    (hmeas : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
        AEStronglyMeasurable (fun w => parametrixAmp N Θ u τ w * φ w) (volume.restrict Ω))
    (hbound : ∃ C, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
        ∀ᵐ w ∂(volume.restrict Ω), ‖parametrixAmp N Θ u τ w * φ w‖ ≤ C)
    (hcov : (fun τ => ∫ z, Wit τ (0 : Point n) z)
        =ᶠ[𝓝[>] (0 : ℝ)]
        (fun τ => ∫ w in Ω, gaussDdim τ w * (parametrixAmp N Θ u τ w * φ w))) :
    Tendsto (fun m => ∫ z, Wit (QIQTH.HeatResidualBound.epsSeq m) (0 : Point n) z) atTop (𝓝 1) := by
  have hchart := chartMass_tendsto_one_of_weightedCovar N Θ u φ Wit hΩmeas hΩnhds hΘ0 hu0
    hΘcont hucont hφcont hφ0 hmeas hbound hcov
  -- `epsSeq → 𝓝[>]0` (positive and → 0)
  have heps : Tendsto QIQTH.HeatResidualBound.epsSeq atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      QIQTH.HeatResidualBound.epsSeq_tendsto
      (Filter.Eventually.of_forall (fun m => QIQTH.HeatResidualBound.epsSeq_pos m))
  exact hchart.comp heps

/-! ### Satisfiability gate — a CONCRETE genuinely-curved instance (no flatness). -/

/-- **A concrete CURVED chart weight** `φ_curved w = (1 + ‖w‖²)⁻¹ = (curvedTheta w)⁻¹`.  Continuous,
    `∈ (0,1]`, `φ_curved(0)=1`, but `φ_curved ≢ 1` — a genuinely-curved (`J(0)=1` but `J ≢ 1`) weight. -/
noncomputable def curvedPhi (w : Point n) : ℝ := (curvedTheta w)⁻¹

theorem curvedPhi_zero : curvedPhi (0 : Point n) = 1 := by
  simp [curvedPhi, curvedTheta_zero]

theorem curvedPhi_continuous : Continuous (curvedPhi : Point n → ℝ) :=
  curvedTheta_continuous.inv₀
    (fun w => (lt_of_lt_of_le one_pos (curvedTheta_ge_one w)).ne')

theorem curvedPhi_abs_le_one (w : Point n) : ‖curvedPhi w‖ ≤ 1 := by
  have hpos : (0 : ℝ) < curvedTheta w := lt_of_lt_of_le one_pos (curvedTheta_ge_one w)
  rw [curvedPhi, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos)]
  exact inv_le_one_of_one_le₀ (curvedTheta_ge_one w)

/-- `φ_curved ≢ 1` at the all-ones point (`n ≥ 1`): `φ_curved (1,…,1) = (1+n)⁻¹ ≠ 1`. -/
theorem curvedPhi_ne_one (hn : 1 ≤ n) : curvedPhi (fun _ : Fin n => (1 : ℝ)) ≠ 1 := by
  have hval : curvedPhi (fun _ : Fin n => (1 : ℝ)) = (1 + (n : ℝ))⁻¹ := by
    simp [curvedPhi, curvedTheta, Finset.card_univ]
  rw [hval]
  have hnpos : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  intro h
  have : (1 : ℝ) + (n : ℝ) = 1 := by
    field_simp at h ⊢
    linarith [h]
  linarith

/-- **★ SATISFIABILITY GATE — a curved instance of the chart bridge.**  The full hypothesis bundle of
    `gatedKernel_mass_tendsto_one_of_localChart` is JOINTLY inhabited by a GENUINELY-CURVED instance
    (`Θ = curvedTheta ≢ 1`, `φ = curvedPhi ≢ 1`, both with value `1` only at the origin, over `Ω = univ`),
    with the abstract `Wit` chosen so `hcov` holds by `setIntegral_univ`.  This certifies the bridge does
    NOT secretly re-introduce `g = δ` on a neighbourhood: the mass → 1 conclusion holds for a curved
    amplitude AND a curved chart weight, the ONLY normalisation used being `Θ(0)=1`, `u₀(0)=1`, `φ(0)=1`
    (= `J(0)=1`) — all first-order facts.  NOT `a₁ = R/6`. -/
theorem chartBridge_curved_certificate (N : ℕ) :
    Tendsto (fun m => ∫ z : Point n,
        gaussDdim (QIQTH.HeatResidualBound.epsSeq m) z
          * (parametrixAmp N curvedTheta flatU (QIQTH.HeatResidualBound.epsSeq m) z * curvedPhi z))
      atTop (𝓝 1) := by
  have hac : Continuous (fun w : Point n => (curvedTheta w) ^ (-(1 : ℝ) / 2)) :=
    curvedTheta_continuous.rpow_const
      (fun w => Or.inl (lt_of_lt_of_le one_pos (curvedTheta_ge_one w)).ne')
  have hmeas : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable
        (fun w => parametrixAmp N curvedTheta flatU τ w * curvedPhi w)
        (volume.restrict (Set.univ : Set (Point n))) := by
    refine Filter.Eventually.of_forall (fun τ => ?_)
    have heq : (fun w : Point n => parametrixAmp N curvedTheta flatU τ w * curvedPhi w)
        = fun w : Point n => (curvedTheta w) ^ (-(1 : ℝ) / 2) * curvedPhi w :=
      funext (fun w => by rw [parametrixAmp_curved_eq])
    rw [heq]
    exact ((hac.mul curvedPhi_continuous).aestronglyMeasurable).restrict
  have hbound : ∃ C, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      ∀ᵐ w ∂(volume.restrict (Set.univ : Set (Point n))),
        ‖parametrixAmp N curvedTheta flatU τ w * curvedPhi w‖ ≤ C :=
    ⟨1, Filter.Eventually.of_forall (fun τ => Filter.Eventually.of_forall (fun w => by
      rw [norm_mul]
      calc ‖parametrixAmp N curvedTheta flatU τ w‖ * ‖curvedPhi w‖
          ≤ 1 * 1 := mul_le_mul (parametrixAmp_curved_abs_le_one N τ w) (curvedPhi_abs_le_one w)
            (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1))⟩
  have hcov :
      (fun τ => ∫ z : Point n,
          gaussDdim τ z * (parametrixAmp N curvedTheta flatU τ z * curvedPhi z))
        =ᶠ[𝓝[>] (0 : ℝ)]
        (fun τ => ∫ w in (Set.univ : Set (Point n)),
          gaussDdim τ w * (parametrixAmp N curvedTheta flatU τ w * curvedPhi w)) :=
    Filter.Eventually.of_forall (fun τ => setIntegral_univ.symm)
  exact gatedKernel_mass_tendsto_one_of_localChart N curvedTheta flatU curvedPhi
    (fun τ _ z => gaussDdim τ z * (parametrixAmp N curvedTheta flatU τ z * curvedPhi z))
    MeasurableSet.univ Filter.univ_mem
    curvedTheta_zero flatU_zero curvedTheta_continuous.continuousAt flatU_continuousAt
    curvedPhi_continuous.continuousAt curvedPhi_zero hmeas hbound hcov

end QIQTH.MassChartBridge

/-! ### Axiom audit. -/

section AxiomChecks

open QIQTH.MassChartBridge

#print axioms weightedParametrix_setMass_tendsto_one
#print axioms chartMass_tendsto_one_of_weightedCovar
#print axioms gatedKernel_mass_tendsto_one_of_localChart
#print axioms curvedPhi_ne_one
#print axioms chartBridge_curved_certificate

end AxiomChecks
