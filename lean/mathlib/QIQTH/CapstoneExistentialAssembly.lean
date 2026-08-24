/-
QIQTH/CapstoneExistentialAssembly.lean

  Phase 5 of the capstone-signature redesign plan
  (`docs/qg_roadmap/CAPSTONE_SIGNATURE_REDESIGN_PLAN.md`, J4-1168, Sol's 38th consult), per the phase
  table's Phase 5 line: "Build the `a1_R6_assembled_v3` existential signature (Layer C), instantiate `CT`
  internally → D7/D8 green".

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS.

    • `a1_R6_assembled_v3` (Layer C) — the destructed-existential capstone signature Sol's plan
      specifies: destruct `GateOpennessExport.gatedWitnessN1_package_open`'s existential FIRST (via
      `PackageHorizonBound.gatedWitnessN1_horizon_bound`, J4-1170, which already performs exactly this
      single opening and re-exposes the package's local bound at the caller-fixed horizon `t`, stated at
      `vanVleckGatedWitness` rather than the raw `gatedKernel …` unfold), set the internal effective
      constant `CT := C * (1 + t)` (the package's own `C`, threaded through `a1_R6_assembled_local`'s
      already-built `CT*(1+t)` assembly, Phase 3/J4-1172), and re-expose ALL ~50 other independent
      hypotheses of `a1_R6_assembled_v2'`/`a1_R6_assembled_local` (`htriple, core, hCH, uu, hu_open, hu0,
      Bs, Ba, Bd, Cf, Dmap, metric, chart, source, derivData, env, hgD1, T, hT, U, hUopen, htU, hUpos,
      hUT, r₀, τ₀, hr₀, hτ₀, u₀, u₁, hAnear, hu₀cont, hu₀one, C₀, C₁, hu₀bdd, hu₁bdd, A₀, A₁, C_L, hA₀,
      hA₁, hC_L, hAdom, hAzero, hBdom, hBcont, hAmeas, hBmeas, hu₀meas, hu₁meas, hMeasFII, hUfloor,
      hInnerCont, nb, hnb, hFmeas, hFint, hF'meas, boundD, hbdd, hbound, hpardiff, L, hLnn, hCross,
      pdpdH, hInterchange, hLapFull, hII_lo, hII_hi, D0, D1, hD0, hD1nn, hbnd, E₀, E₁, hE₀, hE₁, hEdom,
      hEzeroE, hFzero, hIlo, hIhi, hEcomb`) as caller-supplied inputs UNDER the existential — i.e. as a
      `∀`-quantified tail bound to the SAME `(a, b, S)` the package selects, exactly the shape Sol's
      classification (a)(i)/(a)(ii) demands.  `hK0`/`hS0` discharge exactly as Phase 0/1 established:
      `hS0` is `hmemS0 hK0` (no longer a free binder), `K`/`hK`/`hK0` remain genuine external inputs.

    • The proof body is a SINGLE opening of the package (via `gatedWitnessN1_horizon_bound`, which itself
      performs exactly one `obtain` on `gatedWitnessN1_package_open` — Canary D6 discipline, re-verified
      here transitively) followed by direct application of `CapstoneLocalAssembly.a1_R6_assembled_local`
      (Layer A, J4-1172) at the package's selected `(a, b, S, C)`.  Zero new analytic content: this file
      introduces no new estimate, only re-plumbs Phase 1's `gatedWitnessN1_horizon_bound` and Phase 3's
      `a1_R6_assembled_local` together at the shape Sol's Layer C calls for.

  `a₁=R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
  Per the plan's own explicit scoping (and Sol's J4-1168 caution, reiterated in the plan's "Honest
  worth-doing assessment"), Phase 6 — migrating a REAL consumer through all ~50 tuple-dependent
  hypotheses at the package's chosen tuple — is NOT attempted here and remains withheld pending a named
  concrete consumer.  This file is signature/existential-destructuring plumbing only.
-/
import QIQTH.CapstoneLocalAssembly
import QIQTH.PackageHorizonBound

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound QIQTH.ChartRepConstruction
open QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel QIQTH.VanVleck
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.GaussianConvolution QIQTH.HeatParametrixAnsatz QIQTH.ResidueBound
open QIQTH.HeatKernelA1 QIQTH.LaplaceBeltrami
open QIQTH.CConvFacade QIQTH.LeviSeries
open QIQTH.CConvConcreteThreading
open QIQTH.HDConvThreading QIQTH.TruncatedDuhamelData
open QIQTH.DaLimLUWallRecon QIQTH.ETailRateBound QIQTH.HD1CLMLift
open QIQTH.GrandAssemblyRecon QIQTH.ChartJetHessianMixed
open QIQTH.LocalizedBankedData
open QIQTH.CapstoneLocalAssembly
open QIQTH.GateOpennessExport QIQTH.PackageHorizonBound QIQTH.PullbackMetric
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.CapstoneExistentialAssembly

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ (Layer C, J4-1174, Phase 5) `a1_R6_assembled_v3`.**  The destructed-existential capstone
    signature: `(a, b, S)` and the local affine constant `C` are NOT free external binders — they are
    obtained by opening `gatedWitnessN1_package_open` exactly once (via
    `PackageHorizonBound.gatedWitnessN1_horizon_bound`), exposed to the caller as `∃ a b, 0 < a ∧ a < b ∧
    ∃ S, (0:Point n) ∈ S 0 ∧ (all ~50 other hypotheses → conclusion)`.  All ~50 other independent
    hypotheses of `a1_R6_assembled_local`/`a1_R6_assembled_v2'` are copied verbatim and re-exposed as
    caller-supplied inputs UNDER the existential (they are NOT discharged by opening the package — the
    package never touches them, per the plan's hypothesis classification (a)(ii)).  NOT `a₁ = R/6`. -/
theorem a1_R6_assembled_v3 (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    -- ★ the five geometric inputs needed ONLY to open the package (dropped once opened, matching J4-1173):
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    -- (i) RNC / Ricci geometric data (flat), unchanged from `v2'`/`a1_R6_assembled_local`:
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0))) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∃ S : Point n → Set (Point n), (0 : Point n) ∈ S 0 ∧
      -- ★ (Layer C) : the ~50 independent hypotheses, re-exposed UNDER the existential, at the
      -- package-selected `(a, b, S)`.  NONE of these are supplied by `gatedWitnessN1_package_open`.
      (QIQTH.HEmeasBorelAudit.tripleHEmeas g gi (vanVleckGatedWitness g gi hChr hK S a b) →
       TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t →
       ContDiffAt ℝ 2 (fun p => vanVleckGatedWitness g gi hChr hK S a b t p 0) (0 : Point n) →
       ∀ (uu : Set (Point n)), IsOpen uu → (0 : Point n) ∈ uu →
       ∀ (Bs Ba Bd Cf : ℝ) (Dmap : Point n → (Point n →L[ℝ] ℝ)),
       CConvMetricData g gi →
       CConvChartGateData g gi hChr hK S a b t uu →
       CConvSourceData
         (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) t Cf →
       CConvDerivativeData g gi hChr hK S a b t uu
         (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
         (vanVleckGatedWitness g gi hChr hK S a b)
         (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
         Dmap →
       CConvEnvelopeData g gi hChr hK S a b t uu Bs Ba Bd →
       (∀ i : Fin n, ContDiffAt ℝ 1
           (fun x => ∫ s in (0:ℝ)..t, ∫ z, witnessFieldDeriv g gi hChr hK S a b i (t - s) x z
               * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
               ∂(volume : Measure (Point n))) (0 : Point n)) →
       ∀ (T : ℝ), 0 < T →
       ∀ (U : Set ℝ), IsOpen U → t ∈ U →
       (∀ u ∈ U, 0 < u) → (∀ u ∈ U, u ≤ T) →
       ∀ (r₀ τ₀ : ℝ), 0 < r₀ → 0 < τ₀ →
       ∀ (u₀ u₁ : Point n → ℝ),
       (∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z ∈ Metric.ball (0 : Point n) r₀,
           vanVleckGatedWitness g gi hChr hK S a b τ 0 z = gaussDdim τ z * (u₀ z + τ * u₁ z)) →
       ContinuousAt u₀ 0 → u₀ 0 = 1 →
       ∀ (C₀ C₁ : ℝ), (∀ z ∈ Metric.ball (0 : Point n) r₀, |u₀ z| ≤ C₀) →
       (∀ z ∈ Metric.ball (0 : Point n) r₀, |u₁ z| ≤ C₁) →
       ∀ (A₀ A₁ C_L : ℝ), 0 ≤ A₀ → 0 ≤ A₁ → 0 ≤ C_L →
       (∀ τ, 0 < τ → ∀ p q : Point n,
           |vanVleckGatedWitness g gi hChr hK S a b τ p q|
             ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q)) →
       (∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness g gi hChr hK S a b τ p q = 0) →
       (∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
           |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z y|
             ≤ C_L * gaussDdim (2 * s) (z - y)) →
       ContinuousOn
           (fun x : ℝ × Point n =>
             leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) x.1 x.2 0)
           (Set.Ioc 0 T ×ˢ Set.univ) →
       (∀ τ, AEStronglyMeasurable
           (fun z : Point n => vanVleckGatedWitness g gi hChr hK S a b τ 0 z) volume) →
       (∀ s, AEStronglyMeasurable
           (fun z : Point n => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
           volume) →
       AEStronglyMeasurable u₀ volume → AEStronglyMeasurable u₁ volume →
       (∀ u ∈ U, AEStronglyMeasurable
           (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
             * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
           (volume.restrict (Set.uIoc 0 u))) →
       (∃ c : ℝ, 0 < c ∧ ∀ u ∈ U, c ≤ u) →
       (∀ u ∈ U, ContinuousOn
           (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
             * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
           (Set.Ioo 0 u)) →
       ∀ (nb : ℕ → ℝ → Set ℝ), (∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u) →
       (∀ (m : ℕ), ∀ u ∈ U, ∀ a', AEStronglyMeasurable
         (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (a' - s) 0 z
           * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
         (volume.restrict (Set.uIoc 0 (u - epsSeq m)))) →
       (∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
         (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
           * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
         volume 0 (u - epsSeq m)) →
       (∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
         (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s)
           * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
         (volume.restrict (Set.uIoc 0 (u - epsSeq m)))) →
       ∀ (boundD : ℕ → ℝ → ℝ → ℝ),
       (∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m)) →
       (∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a' ∈ nb m u,
         ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (a' - s)
           * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ boundD m u s) →
       (∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a' ∈ nb m u,
         HasDerivAt (fun a' => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (a' - s) 0 z
             * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
           (∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (a' - s)
             * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) a') →
       ∀ (L : ℕ → ℝ → ℝ), (∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u) →
       (∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
         |heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
               (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
               (u + h) (u - epsSeq m + k) 0 0
             - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
               (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
               (u + h) (u - epsSeq m) 0 0
             - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
               (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
               u (u - epsSeq m + k) 0 0
             + heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
               (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
               u (u - epsSeq m) 0 0|
           ≤ L m u * (|h| * |k|)) →
       ∀ (pdpdH : Fin n → ℝ → Point n → ℝ),
       MemInterchange (vanVleckGatedWitness g gi hChr hK S a b)
           (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U pdpdH →
       MemLapFull g gi (vanVleckGatedWitness g gi hChr hK S a b)
           (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U pdpdH →
       MemAdjLo (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U pdpdH →
       MemAdjHi (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U pdpdH →
       ∀ (D0 D1 : Fin n → ℝ), (∀ i, 0 ≤ D0 i) → (∀ i, 0 ≤ D1 i) →
       (∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
           |∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z
               * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
             ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m) →
       ∀ (E₀ E₁ : ℝ), 0 ≤ E₀ → 0 ≤ E₁ →
       (∀ τ, 0 < τ → ∀ p q : Point n,
           |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
             ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q)) →
       (∀ τ, τ ≤ 0 → ∀ p q : Point n,
           heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q = 0) →
       (∀ s, s ≤ 0 → ∀ z y : Point n,
           leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z y = 0) →
       (∀ (m : ℕ), ∀ u ∈ U,
           IntervalIntegrable (fun s => ∫ (z : Point n),
               heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
                 * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
             volume 0 (u - epsSeq m)) →
       (∀ (m : ℕ), ∀ u ∈ U,
           IntervalIntegrable (fun s => ∫ (z : Point n),
               heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
                 * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
             volume (u - epsSeq m) u) →
       MemECombine g gi (vanVleckGatedWitness g gi hChr hK S a b)
           (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) →
       heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hK S a b)
           (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) ) t 0 0 = 0
       ∧ trueHeatKernel (vanVleckGatedWitness g gi hChr hK S a b)
           (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0
           = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
             * (1 + ((∑ i, Ric i i) / 6) * t
                 + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                             transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                               * t ^ (k - 2))
                           + heatConv (vanVleckGatedWitness g gi hChr hK S a b)
                               (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
                               t 0 0
                               / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2)))) := by
  -- ★ single opening of the package existential (D6 discipline) — the RAW every-ceiling `hbound`
  -- family is kept (not specialized to `t`), since `a1_R6_assembled_local`'s `hEbound_t` slot needs the
  -- full `∀ t' τ p q, …` shape, exactly what `gatedWitnessN1_package_open` itself already produces.
  obtain ⟨a, b, C, ha, hab, hC0, S, hbound, hmemS0, hopenS0⟩ :=
    gatedWitnessN1_package_open g gi hg hChr hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
  refine ⟨a, b, ha, hab, S, hmemS0 hK0, ?_⟩
  intro htriple core hCH uu hu_open hu0 Bs Ba Bd Cf Dmap metric chart source derivData env hgD1
    T hT U hUopen htU hUpos hUT r₀ τ₀ hr₀ hτ₀ u₀ u₁ hAnear hu₀cont hu₀one C₀ C₁ hu₀bdd hu₁bdd
    A₀ A₁ C_L hA₀ hA₁ hC_L hAdom hAzero hBdom hBcont hAmeas hBmeas hu₀meas hu₁meas
    hMeasFII hUfloor hInnerCont nb hnb hFmeas hFint hF'meas boundD hbdd hboundBnd hpardiff
    L hLnn hCross
    pdpdH hInterchange hLapFull hII_lo hII_hi D0 D1 hD0 hD1nn hbnd
    E₀ E₁ hE₀ hE₁ hEdom hEzeroE hFzero hIlo hIhi hEcomb
  exact a1_R6_assembled_local g gi Ric t ht C hC0 hChr hK S a b ha hab hK0 (hmemS0 hK0)
    hg hg0 hgi hΓ hdg0 htr hsrc htriple hbound core hCH
    uu hu_open hu0 Bs Ba Bd Cf Dmap metric chart source derivData env hgD1
    T hT U hUopen htU hUpos hUT r₀ τ₀ hr₀ hτ₀ u₀ u₁ hAnear hu₀cont hu₀one C₀ C₁ hu₀bdd hu₁bdd
    A₀ A₁ C_L hA₀ hA₁ hC_L hAdom hAzero hBdom hBcont hAmeas hBmeas hu₀meas hu₁meas
    hMeasFII hUfloor hInnerCont nb hnb hFmeas hFint hF'meas boundD hbdd hboundBnd hpardiff
    L hLnn hCross
    pdpdH hInterchange hLapFull hII_lo hII_hi D0 D1 hD0 hD1nn hbnd
    E₀ E₁ hE₀ hE₁ hEdom hEzeroE hFzero hIlo hIhi hEcomb

end QIQTH.CapstoneExistentialAssembly

section AxiomChecks
open QIQTH.CapstoneExistentialAssembly
#print axioms a1_R6_assembled_v3
end AxiomChecks
