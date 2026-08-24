/-
QIQTH/A1R6PublicClaim.lean

  J4-1178 — the FIRST real consumer of the capstone-signature tower (Sol's 41st consult
  recommendation, `docs/qg_roadmap/WITNESS_UNIFICATION_PLAN.md`): a stable, publication-facing
  theorem APPLICATION (not a `#check`) of `CapstoneExistentialAssembly.a1_R6_assembled_v3`, wired
  into `verify/config.json` / `claim_card.md` as a second capstone entry, giving the tower a genuine
  external citation outside its own internal plumbing for the first time.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS FILE IS AND IS NOT.

  `a1_R6_public_claim` is DEFINITIONALLY IDENTICAL to `CapstoneExistentialAssembly.a1_R6_assembled_v3`
  — same statement, same hypotheses, same conclusion — with exactly two outer binders renamed
  (`hK` → `hCptK`, `hK0` → `hMemZeroK`) to avoid an unrelated name COLLISION in the shared
  verify-capsule claim-card annotation table (`verify/config.json`'s `input_notes`, which does
  PREFIX matching, not just exact-name matching): its existing key `"hK"` is a physical-input
  annotation for the UNRELATED `gr` track's Bisognano–Wichmann heat-functional `hK`, not this
  theorem's `hK : IsCompact K` geometric-chart hypothesis. Because the annotation lookup is
  longest-PREFIX, not just exact-name, candidate renames must avoid starting with the substring
  `"hK"` entirely (an earlier draft renamed to `hKcpt`/`hK0mem`, which still collided and was
  corrected before banking). Reusing any `hK`-prefixed name here would have made the auto-generated
  claim card MISDESCRIBE a routine compactness hypothesis as a load-bearing physical input. The
  proof is a single one-line application of `a1_R6_assembled_v3` — zero new analytic content, zero
  new estimate, pure re-exposure so the verify capsule can probe a name outside the
  `CapstoneExistentialAssembly` internal chain.

  This does NOT discharge, weaken, or touch any hypothesis of the underlying tower. `a₁=R/6` remains
  STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}` (re-exposed here as the `core`/`chart, source,
  derivData, env` bundles under the existential, exactly as in `a1_R6_assembled_v3`), UNCHANGED, PLUS
  the ~15 outer RNC/geometric-chart hypotheses (`hg, hChr, hCptK, hMemZeroK, hgnd, hgsymm, hinvF,
  hframeK, hw, hg0, hgi, hΓ, hdg0, htr, hsrc`). NOT a proof of `a₁ = R/6`.
-/
import QIQTH.CapstoneExistentialAssembly

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
open QIQTH.CapstoneExistentialAssembly
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.A1R6PublicClaim

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ (J4-1178, first real consumer) `a1_R6_public_claim`.** A stable, non-internal application of
    `CapstoneExistentialAssembly.a1_R6_assembled_v3`, published as the verify-capsule's second capstone
    target. Definitionally the SAME statement as `a1_R6_assembled_v3` (two outer binders renamed only to
    avoid a claim-card annotation prefix collision, see the file docstring); the proof is a one-line
    application, zero new analytic content. NOT `a₁ = R/6` — STRICTLY CONDITIONAL on the full hypothesis
    list. -/
theorem a1_R6_public_claim (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hCptK : IsCompact K) (hMemZeroK : (0 : Point n) ∈ K)
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
      (QIQTH.HEmeasBorelAudit.tripleHEmeas g gi (vanVleckGatedWitness g gi hChr hCptK S a b) →
       TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hCptK S a b) t →
       ContDiffAt ℝ 2 (fun p => vanVleckGatedWitness g gi hChr hCptK S a b t p 0) (0 : Point n) →
       ∀ (uu : Set (Point n)), IsOpen uu → (0 : Point n) ∈ uu →
       ∀ (Bs Ba Bd Cf : ℝ) (Dmap : Point n → (Point n →L[ℝ] ℝ)),
       CConvMetricData g gi →
       CConvChartGateData g gi hChr hCptK S a b t uu →
       CConvSourceData
         (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b)) s z 0) t Cf →
       CConvDerivativeData g gi hChr hCptK S a b t uu
         (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b)) s z 0)
         (vanVleckGatedWitness g gi hChr hCptK S a b)
         (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b)))
         Dmap →
       CConvEnvelopeData g gi hChr hCptK S a b t uu Bs Ba Bd →
       (∀ i : Fin n, ContDiffAt ℝ 1
           (fun x => ∫ s in (0:ℝ)..t, ∫ z, witnessFieldDeriv g gi hChr hCptK S a b i (t - s) x z
               * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b)) s z 0
               ∂(volume : Measure (Point n))) (0 : Point n)) →
       ∀ (T : ℝ), 0 < T →
       ∀ (U : Set ℝ), IsOpen U → t ∈ U →
       (∀ u ∈ U, 0 < u) → (∀ u ∈ U, u ≤ T) →
       ∀ (r₀ τ₀ : ℝ), 0 < r₀ → 0 < τ₀ →
       ∀ (u₀ u₁ : Point n → ℝ),
       (∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z ∈ Metric.ball (0 : Point n) r₀,
           vanVleckGatedWitness g gi hChr hCptK S a b τ 0 z = gaussDdim τ z * (u₀ z + τ * u₁ z)) →
       ContinuousAt u₀ 0 → u₀ 0 = 1 →
       ∀ (C₀ C₁ : ℝ), (∀ z ∈ Metric.ball (0 : Point n) r₀, |u₀ z| ≤ C₀) →
       (∀ z ∈ Metric.ball (0 : Point n) r₀, |u₁ z| ≤ C₁) →
       ∀ (A₀ A₁ C_L : ℝ), 0 ≤ A₀ → 0 ≤ A₁ → 0 ≤ C_L →
       (∀ τ, 0 < τ → ∀ p q : Point n,
           |vanVleckGatedWitness g gi hChr hCptK S a b τ p q|
             ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q)) →
       (∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness g gi hChr hCptK S a b τ p q = 0) →
       (∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
           |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b)) s z y|
             ≤ C_L * gaussDdim (2 * s) (z - y)) →
       ContinuousOn
           (fun x : ℝ × Point n =>
             leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b)) x.1 x.2 0)
           (Set.Ioc 0 T ×ˢ Set.univ) →
       (∀ τ, AEStronglyMeasurable
           (fun z : Point n => vanVleckGatedWitness g gi hChr hCptK S a b τ 0 z) volume) →
       (∀ s, AEStronglyMeasurable
           (fun z : Point n => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b)) s z 0)
           volume) →
       AEStronglyMeasurable u₀ volume → AEStronglyMeasurable u₁ volume →
       (∀ u ∈ U, AEStronglyMeasurable
           (fun s => ∫ z, vanVleckGatedWitness g gi hChr hCptK S a b (u - s) 0 z
             * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b)) s z 0)
           (volume.restrict (Set.uIoc 0 u))) →
       (∃ c : ℝ, 0 < c ∧ ∀ u ∈ U, c ≤ u) →
       (∀ u ∈ U, ContinuousOn
           (fun s => ∫ z, vanVleckGatedWitness g gi hChr hCptK S a b (u - s) 0 z
             * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b)) s z 0)
           (Set.Ioo 0 u)) →
       ∀ (nb : ℕ → ℝ → Set ℝ), (∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u) →
       (∀ (m : ℕ), ∀ u ∈ U, ∀ a', AEStronglyMeasurable
         (fun s => ∫ z, vanVleckGatedWitness g gi hChr hCptK S a b (a' - s) 0 z
           * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b)) s z 0)
         (volume.restrict (Set.uIoc 0 (u - epsSeq m)))) →
       (∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
         (fun s => ∫ z, vanVleckGatedWitness g gi hChr hCptK S a b (u - s) 0 z
           * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b)) s z 0)
         volume 0 (u - epsSeq m)) →
       (∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
         (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hCptK S a b r 0 z) (u - s)
           * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b)) s z 0)
         (volume.restrict (Set.uIoc 0 (u - epsSeq m)))) →
       ∀ (boundD : ℕ → ℝ → ℝ → ℝ),
       (∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m)) →
       (∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a' ∈ nb m u,
         ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hCptK S a b r 0 z) (a' - s)
           * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b)) s z 0‖ ≤ boundD m u s) →
       (∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a' ∈ nb m u,
         HasDerivAt (fun a' => ∫ z, vanVleckGatedWitness g gi hChr hCptK S a b (a' - s) 0 z
             * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b)) s z 0)
           (∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hCptK S a b r 0 z) (a' - s)
             * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b)) s z 0) a') →
       ∀ (L : ℕ → ℝ → ℝ), (∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u) →
       (∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
         |heatConvFrozen (vanVleckGatedWitness g gi hChr hCptK S a b)
               (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b)))
               (u + h) (u - epsSeq m + k) 0 0
             - heatConvFrozen (vanVleckGatedWitness g gi hChr hCptK S a b)
               (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b)))
               (u + h) (u - epsSeq m) 0 0
             - heatConvFrozen (vanVleckGatedWitness g gi hChr hCptK S a b)
               (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b)))
               u (u - epsSeq m + k) 0 0
             + heatConvFrozen (vanVleckGatedWitness g gi hChr hCptK S a b)
               (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b)))
               u (u - epsSeq m) 0 0|
           ≤ L m u * (|h| * |k|)) →
       ∀ (pdpdH : Fin n → ℝ → Point n → ℝ),
       MemInterchange (vanVleckGatedWitness g gi hChr hCptK S a b)
           (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b))) U pdpdH →
       MemLapFull g gi (vanVleckGatedWitness g gi hChr hCptK S a b)
           (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b))) U pdpdH →
       MemAdjLo (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b))) U pdpdH →
       MemAdjHi (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b))) U pdpdH →
       ∀ (D0 D1 : Fin n → ℝ), (∀ i, 0 ≤ D0 i) → (∀ i, 0 ≤ D1 i) →
       (∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
           |∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z
               * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b)) s z 0|
             ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m) →
       ∀ (E₀ E₁ : ℝ), 0 ≤ E₀ → 0 ≤ E₁ →
       (∀ τ, 0 < τ → ∀ p q : Point n,
           |heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b) τ p q|
             ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q)) →
       (∀ τ, τ ≤ 0 → ∀ p q : Point n,
           heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b) τ p q = 0) →
       (∀ s, s ≤ 0 → ∀ z y : Point n,
           leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b)) s z y = 0) →
       (∀ (m : ℕ), ∀ u ∈ U,
           IntervalIntegrable (fun s => ∫ (z : Point n),
               heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b) (u - s) 0 z
                 * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b)) s z 0)
             volume 0 (u - epsSeq m)) →
       (∀ (m : ℕ), ∀ u ∈ U,
           IntervalIntegrable (fun s => ∫ (z : Point n),
               heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b) (u - s) 0 z
                 * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b)) s z 0)
             volume (u - epsSeq m) u) →
       MemECombine g gi (vanVleckGatedWitness g gi hChr hCptK S a b)
           (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b))) →
       heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hCptK S a b)
           (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b))) ) t 0 0 = 0
       ∧ trueHeatKernel (vanVleckGatedWitness g gi hChr hCptK S a b)
           (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b))) t 0 0
           = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
             * (1 + ((∑ i, Ric i i) / 6) * t
                 + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                             transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                               * t ^ (k - 2))
                           + heatConv (vanVleckGatedWitness g gi hChr hCptK S a b)
                               (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hCptK S a b)))
                               t 0 0
                               / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2)))) :=
  a1_R6_assembled_v3 g gi Ric t ht hg hChr hCptK hMemZeroK hgnd hgsymm hinvF hframeK hw
    hg0 hgi hΓ hdg0 htr hsrc


end QIQTH.A1R6PublicClaim

section AxiomChecks
open QIQTH.A1R6PublicClaim
#print axioms a1_R6_public_claim
end AxiomChecks
