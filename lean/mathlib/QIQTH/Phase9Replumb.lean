/-
  Phase9Replumb — J4-466: THE FULL ANALYTIC STACK AT THE ∃-CONSUMED GATE.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  completes the J4-465 residue: `v2Census_phase8` (CLSlotWire.lean) wired the census `C_L` slot by
  ∃-consuming the gate — it OBTAINS `(a,b,S)` from `census_C_L_grounded` and, at that gate, GROUNDS
  the `C_L` conjunct of the reduced gate core, delivering the phase-7 `hGateCoreR` from the doubly-
  reduced `hGateCoreRR` + the standing joint measurability `hEmeas`.  Phase8's ∃-body stops at
  `hGateCoreR`; it does NOT yet reach the actual `TruncatedDuhamelCore`.  This brick performs the
  remaining MECHANICAL step (the J4-465 rec): feed the reconstructed `hGateCoreR` through the FULL
  `v2Census_phase7` analytic stack AT the obtained gate, so the conclusion is the genuine
  `TruncatedDuhamelCore` — ∃-quantified over the geometry-chosen gate.  `a₁ = R/6` remains
  CONDITIONAL on the whole convergence-trio + geometric-wiring stack AND on the surviving
  envelope/box/scaffold/gate/amplitude inputs.  NO `sorry` (header prose excepted), NO `:= True`,
  NO new axioms; std-3 only.  No existing file is edited.

  ── THE ∃-CONSUMPTION SHAPE (inherited from J4-465, mandatory audit).
    (i)   PHASE8'S BODY REACHES ONLY `hGateCoreR`.  `v2Census_phase8` concludes
          `∃ a b S, 0<a ∧ a<b ∧ ∀ U snb, hUT → hεU → hEmeas → hGateCoreRR → hGateCoreR` — i.e. its
          ∃-body delivers the C_L-grounded REDUCED GATE CORE at the obtained gate, not the core.
    (ii)  THE PHASE-7 STACK IS S-DEPENDENT.  Every analytic carry of `v2Census_phase7` (envelope
          `hEdom`/`hFdom`, boxes `hSecBoxes`/`hBBoxes`, scaffold `hQ1`/`hProvP`/`hbulkderiv`/…,
          amplitude `hAdom`, gate `hGateCoreR`, …) references the gate `S` (via the witness
          `vanVleckGatedWitness g gi hChr hK S a b`).  With `S` ∃-obtained, these cannot be
          signature binders quantified over a free census `S`; the honest supply is AT the obtained
          gate — they migrate into the ∃-body implication exactly as in phase8's own design.
    (iii) THE S-INDEPENDENT geometry (`g,gi,hg,hChr,hK,hgnd,hgsymm,hinvF,hframeK,hwtop,hdg0,hg0,hn`)
          and the horizon `T,hT` pass through VERBATIM as `v2Census_phase9`'s signature — they are
          exactly `v2Census_phase8`'s signature, feeding the gate-obtaining call.

  ── WHAT LANDS.
    • `v2Census_phase9`  — ★★★★★ THE CAPSTONE.  Obtain `(a,b,S)` + the C_L-grounding closure from
        `v2Census_phase8`; at that gate, given the full phase-7 analytic stack (with `C_L` GROUNDED,
        i.e. `hGateCoreR` replaced by `hEmeas` + `hGateCoreRR`), conclude the genuine
        `TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t`.  Conclusion:
        `∃ a b S, 0<a ∧ a<b ∧ (full stack at the gate → TruncatedDuhamelCore)`.

  ⚠  a₁ = R/6 remains CONDITIONAL.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.CLSlotWire

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.LeviSeries QIQTH.ExpMap QIQTH.HeatKernelA1
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.WitnessMeasDeriv QIQTH.SupConstantFamily QIQTH.UngatedChainRule QIQTH.PullbackMetric
open QIQTH.DuhamelCoreThreaded QIQTH.PerUCensusTuple QIQTH.W2Finish
open QIQTH.HDuhamelExportRethread QIQTH.TruncatedDuhamelData
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.V2CensusInstantiation QIQTH.WallAInstantiation QIQTH.WallAThreading
open QIQTH.HInterGrounding QIQTH.HAdom2capGrounding
open QIQTH.InnerDataInstantiation QIQTH.InnerDataEnvelope QIQTH.HdiffGrounding
open QIQTH.InnerDataCensusThread QIQTH.PresentationBridges QIQTH.CLSlotWire
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.Phase9Replumb

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★★★★★ `v2Census_phase9` — the full analytic stack at the ∃-consumed gate.
    ############################################################################### -/

/-- **★★★★★ `v2Census_phase9` — THE CAPSTONE: the genuine `TruncatedDuhamelCore` at the ∃-consumed
    gate.**  This closes the J4-465 residue.  `v2Census_phase8` (CLSlotWire) delivered the C_L-grounded
    reduced gate core `hGateCoreR` at the OBTAINED gate `(a,b,S)` (from `census_C_L_grounded`); this
    brick feeds that reconstructed `hGateCoreR` through the FULL `v2Census_phase7` analytic stack at the
    same gate, concluding the actual v3-core `TruncatedDuhamelCore`.

    STRUCTURE.  The signature is EXACTLY `v2Census_phase8`'s (the S-INDEPENDENT geometry + horizon
    `T,hT`), which obtains the gate.  The conclusion `∃ a b S, 0<a ∧ a<b ∧ (⋯)` migrates ALL the
    S-DEPENDENT phase-7 carries into the ∃-body implication (they reference the ∃-obtained `S`), with
    the `C_L`-carrying `hGateCoreR` REPLACED by the phase8 inputs `hEmeas` (standing joint
    measurability) + `hGateCoreRR` (the doubly-reduced, C_L-free core).  Internally `hcore8`
    (from `v2Census_phase8`) grounds `C_L` to rebuild `hGateCoreR`, then `v2Census_phase7` produces the
    core.

    HONESTY COST (recorded).  The result is quantified over the OBTAINED gate `S`, NOT an arbitrary
    census `S`; the migrated S-dependent carries are the campaign's surviving W3 labelled inputs at the
    geometry-chosen gate — all satisfiable, none newly unsatisfiable.  This is a legitimate
    ∃-consumption re-plumb, not a Sol #22 blocker.  ⚠ Pure surface re-plumbing; closes NOTHING deeper.
    NOT `a₁ = R/6`. -/
theorem v2Census_phase9 (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hwtop : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hn : 1 ≤ n) (T : ℝ) (hT : 0 < T) :
    ∃ (a b : ℝ) (S : Point n → Set (Point n)), 0 < a ∧ a < b ∧
      ∀ (F : ℝ → Point n → Point n → ℝ)
        (_hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
        (t : ℝ) (U : Set ℝ) (_hUopen : IsOpen U) (_htU : t ∈ U)
        (_hUT : ∀ u ∈ U, u ≤ T)
        (_hBoundaryLim : Tendsto
            (fun m => BoundaryTrunc (vanVleckGatedWitness g gi hChr hK S a b) F m t) atTop
            (𝓝 (F t 0 0)))
        (_hgi : MemGaugeGi (n := n) gi) (_hΓ : MemGaugeGamma (n := n) g gi)
        (V : Set (Point n)) (_hVopen : IsOpen V) (_hV0 : (0 : Point n) ∈ V)
        (snb : Set ℝ) (_hsnb : snb ∈ 𝓝 (0 : ℝ))
        (_hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
            pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u
                (u - epsSeq m) x 0) i y
              = ∫ s in (0)..(u - epsSeq m),
                  ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) y z * F s z 0)
        (_hFmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
            (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w) z * F s z 0)
            (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
        (_hFint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
            (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (0 : Point n) z * F s z 0)
            volume 0 (u - epsSeq m))
        (_hF'meas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
            (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s) (0 : Point n) z * F s z 0)
            (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
        (bnd : ℕ → Fin n → ℝ → ℝ)
        (_hbdd : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
            IntervalIntegrable (bnd m i) volume 0 (u - epsSeq m))
        (_hbound : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
            s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
              ‖∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                  (Function.update (0 : Point n) i w) z * F s z 0‖ ≤ bnd m i s)
        (D0 D1 : Fin n → ℝ) (_hD0 : ∀ i, 0 ≤ D0 i) (_hD1 : ∀ i, 0 ≤ D1 i)
        (_hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
            |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
                witnessSecondXDeriv g gi hChr hK S a b i (u - s) z * F s z 0|
              ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
        (E₀ E₁ C_L aT : ℝ) (_hE₀ : 0 ≤ E₀) (_hE₁ : 0 ≤ E₁) (_hC_L : 0 ≤ C_L) (_haT : 0 < aT)
        (_hUlb : ∀ u ∈ U, aT ≤ u)
        (_hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
            |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
              ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
        (_hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
        (_hIlo : ∀ (m : ℕ), ∀ u ∈ U,
            IntervalIntegrable (fun s => ∫ (z : Point n),
                heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z * F s z 0)
              volume 0 (u - epsSeq m))
        (_hIhi : ∀ (m : ℕ), ∀ u ∈ U,
            IntervalIntegrable (fun s => ∫ (z : Point n),
                heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z * F s z 0)
              volume (u - epsSeq m) u)
        (_hEcomb : MemECombine g gi (vanVleckGatedWitness g gi hChr hK S a b) F)
        (A₀ A₁ : ℝ) (_hA₀ : 0 ≤ A₀) (_hA₁ : 0 ≤ A₁)
        (_hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
            |vanVleckGatedWitness g gi hChr hK S a b τ p q|
              ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
        (_hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness g gi hChr hK S a b τ p q = 0)
        (_hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
            (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
            (volume.restrict (Set.uIoc 0 u)))
        (_hUfloor : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ U, c ≤ u)
        (_hInnerCont : ∀ u ∈ U,
            ContinuousOn (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
              (Set.Ioo 0 u))
        (nb : ℕ → ℝ → Set ℝ) (_hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
        (_hFmeas_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ c, AEStronglyMeasurable
          (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (c - s) 0 z * F s z 0)
          (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
        (_hFint_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
          volume 0 (u - epsSeq m))
        (_hF'meas_d : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
          (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s) * F s z 0)
          (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
        (boundD : ℕ → ℝ → ℝ → ℝ)
        (_hbdd_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
        (_hbound_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb m u,
          ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (c - s) * F s z 0‖
            ≤ boundD m u s)
        (_hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb m u,
          HasDerivAt (fun c => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (c - s) 0 z * F s z 0)
            (∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (c - s) * F s z 0) c)
        (L : ℕ → ℝ → ℝ) (_hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
        (_hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
          |heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F (u + h) (u - epsSeq m + k) 0 0
              - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F (u + h) (u - epsSeq m) 0 0
              - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u (u - epsSeq m + k) 0 0
              + heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u (u - epsSeq m) 0 0|
            ≤ L m u * (|h| * |k|))
        (ρ lam CW Cf τ₀ : ℝ) (ta tb : ℝ)
        (_hρ : 0 < ρ) (_hlam : 0 < lam) (_hCW : 0 ≤ CW) (_hτ₀ : 0 < τ₀)
        (_hWmeas : ∀ τ, AEStronglyMeasurable
            (fun z => vanVleckGatedWitness g gi hChr hK S a b τ (0 : Point n) z) volume)
        (_hffro_meas : ∀ u, AEStronglyMeasurable (fun z => F u z (0 : Point n)) volume)
        (_hfmov_meas : ∀ m u, AEStronglyMeasurable (fun z => F (u - epsSeq m) z (0 : Point n)) volume)
        (_hffro_bdd : ∀ u z, |F u z (0 : Point n)| ≤ Cf)
        (_hfmov_bdd : ∀ m u z, |F (u - epsSeq m) z (0 : Point n)| ≤ Cf)
        (_hWDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z,
          |vanVleckGatedWitness g gi hChr hK S a b τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z)
        (_hmass : ∀ᶠ m in atTop,
          ∫ z, |vanVleckGatedWitness g gi hChr hK S a b (epsSeq m) (0 : Point n) z| ≤ CW)
        (_hmassone : Tendsto
            (fun m => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (epsSeq m) (0 : Point n) z) atTop (𝓝 1))
        (_hmod : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ u ∈ Set.Icc ta tb,
            ∀ z ∈ Metric.ball (0 : Point n) δ,
              |F u z (0 : Point n) - F u (0 : Point n) (0 : Point n)| < ε)
        (_hsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ u ∈ Set.Icc ta tb,
            ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
              |F (u - epsSeq m) z (0 : Point n) - F u z (0 : Point n)| < ε)
        (_hUsub : U ⊆ Set.Icc ta tb)
        (τc wA2 : ℝ)
        (_hwA2 : 0 < wA2)
        (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
        (Cdata : ℝ)
        (_data : LeviSeriesLocalData
            (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) Cdata T)
        (_hSecBoxes : ∀ i : Fin n, ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
          ContinuousOn
            (fun p : ℝ × Point n => witnessSecondXDeriv g gi hChr hK S a b i p.1 p.2)
            (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
        (_hBBoxes : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
          ContinuousOn
            (fun p : ℝ × Point n =>
              leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
            (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
        (Ccrude : ℝ) (_hCcrude : 0 ≤ Ccrude)
        (_hcrude : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
            |witnessSecondXDeriv g gi hChr hK S a b i τ z|
              ≤ Ccrude * τ⁻¹ * gaussDdim (wA2 * τ) (0 - z))
        (Lc Bcomp Q Sconst : ℝ)
        (_hLc : 0 ≤ Lc) (_hBcomp : 0 ≤ Bcomp) (_hQ : 0 ≤ Q) (_hSconst : 0 ≤ Sconst)
        (_hslot : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
            |∫ z, witnessSecondXDeriv g gi hChr hK S a b i τ z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
              ≤ (2 * Lc * (15 / 2 * (n : ℝ)) + Bcomp + Q) * τ ^ (-(1 : ℝ) / 2) + Sconst)
        (_hcap : ∀ (m : ℕ), ∀ u ∈ U, ∀ s ∈ Set.Ioo (u - epsSeq m) u, u - s ≤ τc)
        (_hEndpoint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
            ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - u) z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) u z 0 = 0)
        (ρc : ℝ) (_hρc : 0 < ρc)
        (_hwInf : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
          (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
        (_hC1geom : ∀ (i : Fin n), ∀ w ∈ snb,
          ContinuousOn
            (fun q : ℝ × Point n =>
              uniformInverseChart g gi hChr hK q.2 (Function.update (0 : Point n) i q.1))
            (Set.Icc (w - ρc) (w + ρc) ×ˢ K)
          ∧ Set.MapsTo
            (fun q : ℝ × Point n =>
              (q.2, uniformInverseChart g gi hChr hK q.2 (Function.update (0 : Point n) i q.1)))
            (Set.Icc (w - ρc) (w + ρc) ×ˢ K)
            (K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hChr hK))
          ∧ (∀ q ∈ Set.Icc (w - ρc) (w + ρc) ×ˢ K,
              IsUnit (fderiv ℝ (uniformFlowExp g gi hChr hK q.2)
                (uniformInverseChart g gi hChr hK q.2 (Function.update (0 : Point n) i q.1))))
          ∧ (∀ q ∈ Set.Icc (w - ρc) (w + ρc) ×ˢ K,
              fderiv ℝ (uniformInverseChart g gi hChr hK q.2) (Function.update (0 : Point n) i q.1)
                = Ring.inverse (fderiv ℝ (uniformFlowExp g gi hChr hK q.2)
                    (uniformInverseChart g gi hChr hK q.2 (Function.update (0 : Point n) i q.1))))
          ∧ (∀ q ∈ Set.Icc (w - ρc) (w + ρc) ×ˢ K,
              DifferentiableAt ℝ (uniformInverseChart g gi hChr hK q.2)
                (Function.update (0 : Point n) i q.1))
          ∧ (∀ q ∈ Set.Icc (w - ρc) (w + ρc) ×ˢ K,
              S q.2 ∈ nhds (Function.update (0 : Point n) i q.1)))
        -- ★ `C_L` GROUNDED: the phase-7 `hGateCoreR` is REPLACED by the phase8 inputs.
        (hEmeas : StronglyMeasurable (fun w : ℝ × Point n × Point n =>
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) w.1 w.2.1 w.2.2))
        (hGateCoreRR : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
            s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
            ∃ (znb : Set ℝ) (C₂ : ℝ),
              znb ∈ 𝓝 w ∧ 0 ≤ C₂ ∧
              (∀ w' : ℝ, AEStronglyMeasurable
                (fun z => witnessFieldDeriv g gi hChr hK S a b i (u - s)
                    (Function.update (0 : Point n) i w') z) volume) ∧
              AEStronglyMeasurable
                (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
                volume ∧
              AEStronglyMeasurable
                (fun z => witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                    (Function.update (0 : Point n) i w) z) volume ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ znb, z ∈ K →
                |witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                    (Function.update (0 : Point n) i w') z| ≤ C₂) ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ znb,
                z ∉ K ∨ PdiffAt (fun x' : Point n =>
                    witnessFieldDeriv g gi hChr hK S a b i (u - s) x' z) i
                  (Function.update (0 : Point n) i w')))
        (nbP : ℝ → Set (Point n)) (_hnbP_open : ∀ u ∈ U, IsOpen (nbP u))
        (_hnbP0 : ∀ u ∈ U, (0 : Point n) ∈ nbP u)
        (_hProvP : ∀ u ∈ U, ∀ x ∈ nbP u, ∀ i : Fin n,
          ∃ (snbx : Set ℝ) (bound : ℝ → ℝ),
            snbx ∈ 𝓝 (x i) ∧
            (∀ w, AEStronglyMeasurable
              (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) (Function.update x i w) z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
              (volume.restrict (Set.uIoc 0 u))) ∧
            IntervalIntegrable
              (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) x z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume 0 u ∧
            AEStronglyMeasurable
              (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) x z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
              (volume.restrict (Set.uIoc 0 u)) ∧
            IntervalIntegrable bound volume 0 u ∧
            (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snbx,
              ‖∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (Function.update x i w) z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ bound s) ∧
            (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snbx,
              HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s)
                  (Function.update x i w) z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
                (∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (Function.update x i w) z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) w))
        (fderivBulk : ℝ → Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
        (gderiv : ℝ → Fin n → Point n → (Point n →L[ℝ] ℝ))
        (C₀ C₁ C₂ : ℝ → Fin n → ℝ)
        (_hGintP : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), IntervalIntegrable
            (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) x z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
                ∂(volume : Measure (Point n)))
            volume 0 u)
        (_hbulkderiv : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
            HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK S a b u i m)
              (fderivBulk u i m x) x)
        (_hsliver : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
            dist (fderivBulk u i m x) (gderiv u i x)
              ≤ (C₀ u i + C₁ u i) * (2 * Real.sqrt (epsSeq m)) + C₂ u i * epsSeq m)
        (_hcont : ∀ u ∈ U, ∀ i : Fin n, ContinuousOn (gderiv u i) (Set.univ : Set (Point n)))
        (_hfrozen_pd1 : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ),
            (fun y => pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
                (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
                (u - epsSeq m) x 0) i y)
              =ᶠ[𝓝 (0 : Point n)]
              QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK S a b u i m),
        TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t := by
  obtain ⟨a, b, S, ha, hab, hcore8⟩ :=
    v2Census_phase8 g gi hg hChr hK hgnd hgsymm hinvF hframeK hwtop hdg0 hg0 hn T hT
  refine ⟨a, b, S, ha, hab, fun F hFeq t U hUopen htU hUT hBoundaryLim hgi hΓ V hVopen hV0
    snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound D0 D1 hD0 hD1 hbnd
    E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hEdom hFdom hIlo hIhi hEcomb A₀ A₁ hA₀ hA₁ hAdom hAzero
    hMeasFII hUfloor hInnerCont nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff
    L hLnn hCross ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd
    hfmov_bdd hWDom hmass hmassone hmod hsup hUsub τc wA2 hwA2 hεU Cdata data hSecBoxes hBBoxes
    Ccrude hCcrude hcrude Lc Bcomp Q Sconst hLc hBcomp hQ hSconst hslot hcap hEndpoint ρc hρc
    hwInf hC1geom hEmeas hGateCoreRR nbP hnbP_open hnbP0 hProvP fderivBulk gderiv C₀ C₁ C₂
    hGintP hbulkderiv hsliver hcont hfrozen_pd1 => ?_⟩
  -- ★ GROUND `C_L`: rebuild the phase-7 `hGateCoreR` from `hEmeas` + `hGateCoreRR` via phase8.
  have hGateCoreR := hcore8 U snb hUT hεU hEmeas hGateCoreRR
  -- ★ RE-PLUMB: feed the reconstructed gate core through the full phase-7 analytic stack.
  exact v2Census_phase7 g gi hChr hK S a b F hFeq t T hT U hUopen htU hUT hn hBoundaryLim
    hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound D0 D1 hD0 hD1 hbnd
    E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hEdom hFdom hIlo hIhi hEcomb A₀ A₁ hA₀ hA₁ hAdom hAzero
    hMeasFII hUfloor hInnerCont nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff
    L hLnn hCross ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd
    hfmov_bdd hWDom hmass hmassone hmod hsup hUsub τc wA2 hwA2 hεU Cdata data hSecBoxes hBBoxes
    Ccrude hCcrude hcrude Lc Bcomp Q Sconst hLc hBcomp hQ hSconst hslot hcap hEndpoint ρc hρc
    hwInf hC1geom hGateCoreR nbP hnbP_open hnbP0 hProvP fderivBulk gderiv C₀ C₁ C₂
    hGintP hbulkderiv hsliver hcont hfrozen_pd1

end QIQTH.Phase9Replumb

/-! ## THE PHASE-9 LEDGER — the final census surface after the full slot-grounding chain (phases 2–9).

  The slot-grounding chain runs `v2Census_phase2 … phase9`.  Phase9 is the CAPSTONE: it reaches the
  genuine `TruncatedDuhamelCore` at the ∃-consumed (geometry-chosen) gate, with the `C₁` slot
  (phase7) and the `C_L` slot (phase8) both GROUNDED rather than carried.

    phase   what it grounds / does                                                        status
    ─────   ──────────────────────────────────────────────────────────────────────────   ─────────────
    2–6     the census tuple assembly → `TruncatedDuhamelCore` for a FREE census gate      CARRIED STACK
            `S,a,b`, all analytic carries as signature binders.
    7       C₁ slot GROUNDED: `hGateCore` → reduced `hGateCoreR` + `hC1geom` + `hwInf`;     C₁ GROUNDED
            C₁ nonneg/on-gate-sup supplied by `census_C1_grounded` (BRIDGE 2).  Still a
            FREE census gate; `C_L` still carried inside `hGateCoreR`.
    8       C_L slot GROUNDED, gate ∃-CONSUMED: OBTAIN `(a,b,S)` from                       C_L GROUNDED
            `census_C_L_grounded`; at that gate rebuild `hGateCoreR` from the doubly-        (gate ∃-
            reduced `hGateCoreRR` + `hEmeas`.  Body STOPS at `hGateCoreR`.                   consumed)
    9       FULL STACK at the ∃-consumed gate: feed the reconstructed `hGateCoreR` through   CORE REACHED
            `v2Census_phase7` at the obtained gate → genuine `TruncatedDuhamelCore`.         (∃ over gate)

  ── THE FINAL CENSUS SURFACE (what remains CARRIED at the geometry-chosen gate).  Both slot bridges
  (C₁, C_L) are grounded.  The `v2Census_phase9` ∃-body still carries the following labelled analytic
  inputs AT the obtained gate — each is a surviving W3 labelled input, each satisfiable (no new
  unsatisfiability introduced by the ∃-consumption):

    block         carried binders                                              satisfiable via
    ───────────   ──────────────────────────────────────────────────────────  ───────────────────────
    envelope      `hEdom`, `hFdom`, `hWDom`, `hffro_bdd`/`hfmov_bdd`, `hmass`   Gaussian domination
                  `hmassone`                                                    of the gated witness /
                                                                                Levi series (banked).
    amplitude     `hAdom`, `hAzero`                                             `vanVleckGatedWitness`
                                                                                Gaussian bounds (banked).
    boxes         `hSecBoxes`, `hBBoxes`, `hInnerCont`, `hmod`, `hsup`          joint continuity of the
                                                                                witness derivatives on
                                                                                compact boxes (J4-443).
    scaffold      `hQ1`, `hProvP`, `hbulkderiv`, `hsliver`, `hcont`,            frozen-germ differ-
                  `hfrozen_pd1`, `hGintP`, `hbnd`, `hCross`, `hpardiff`         entiation + Duhamel
                                                                                interchange (banked).
    measurability `hFmeas`/`hFint`/`hF'meas`(_d), `hMeasFII`, `hWmeas`,         Fubini-Tonelli /
                  `hffro_meas`/`hfmov_meas`, `hbdd`(_d), `hbound`(_d),          strong-meas of the
                  `hIlo`/`hIhi`, `hbdd`                                         integrands (banked).
    gate          `hEmeas` + `hGateCoreRR` (C_L GROUNDED here) + `hC1geom`      standing joint meas +
                  + `hwInf`                                                     C_L domination (phase8)
                                                                                + BRIDGE 2 geometry.
    slot          `hslot`, `hcrude`, `hcap`, `hEndpoint`, `data`               second-x-deriv slot
                                                                                bounds + LocalData
                                                                                (banked).
    boundary      `hBoundaryLim`, `hUfloor`, `hUlb`, `hUsub`, `hUT`, `hεU`     window geometry
                  `htU`, `hUopen`, `hV0`/`hVopen`, `hsnb`                       (elementary).
    gauge         `hgi`, `hΓ`                                                   `MemGaugeGi/Gamma`
                                                                                (banked).

  ── HONEST STATUS.  `v2Census_phase9` is a PURE SURFACE re-plumb: it moves `C_L` from carried to
  grounded (via phase8) and threads the phase-7 stack to the actual `TruncatedDuhamelCore`, ALL at the
  ∃-obtained gate.  It closes NOTHING deeper — the surviving carries above remain the honest
  conditional inputs of the a₁-endgame.  The `∃ a b S` quantification is the recorded HONESTY COST of
  the C_L ∃-consumption (the result is for the geometry-chosen gate, not an arbitrary census `S`).

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL on the whole convergence-trio + geometric-wiring
  stack AND on the surviving envelope/box/scaffold/gate/amplitude carries above.
-/

section AxiomChecks
open QIQTH.Phase9Replumb
#print axioms v2Census_phase9
end AxiomChecks
