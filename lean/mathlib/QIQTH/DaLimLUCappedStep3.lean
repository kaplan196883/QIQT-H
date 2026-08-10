/-
  DaLimLUCappedStep3 — J4-541.  The LEG-1 (Da-limit) LO-CAPPED **capstone** `hDaLimLU_from_labelled_capped`
  — the whole `DaLimLUGoal` Da-limit assembly with the FALSE uncapped whole-time second-derivative
  domination `hAdom2` PURGED from the binder list.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It splices
  the two banked capped leg-1 bricks — J4-539's `DaLimLUCapped.integrability_from_dominations_capped`
  (the drop-in four-output census tuple `⟨hIlo,hIhi,hII_lo,hII_hi⟩` built from the per-`m` CAPPED family
  `hAdom2cap` + a carried `MemAdjHi` residual, NO uncapped `hAdom2`) and J4-540's downstream
  `memLapFull_from_labelled_capped` — through the EXACT banked concrete-gate discharge
  `DaLimLUConcreteDischarge.hDaLimLU_concrete`, to reproduce the whole `GlobalRawBoundFacade.
  hDaLimLU_from_labelled` conclusion (`DaLimLUGoal` at the endgame gate `H_G := vanVleckGatedWitness …`)
  WITHOUT ever asserting the false uncapped whole-time `hAdom2`.  No `sorry` (header prose excepted), no
  new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially
  yielding) the conclusion, no existing file edited, nothing committed.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE DECISIVE TRACE (J4-541 — confirmed by direct read of the mainline + Sol consult, high).

  `GlobalRawBoundFacade.hDaLimLU_from_labelled` consumes the uncapped `hAdom2` at EXACTLY ONE site — the
  census `integrability_from_dominations` (its body line ~497), which returns the four-output tuple
  `⟨hIlo, hIhi, hII_lo, hII_hi⟩`.  Downstream:
    •  `memLapFull_from_labelled` (body line ~512) consumes ONLY `hII_lo`/`hII_hi` — never `hAdom2`;
    •  the FINAL concrete-gate discharge `DaLimLUConcreteDischarge.hDaLimLU_concrete` (body line ~524)
       takes `hIlo`, `hIhi`, `hII_lo`, `hII_hi` AND the `MemLapFull` binder `hLapFull` as PLAIN
       hypotheses — it NEVER takes `hAdom2` and NEVER re-derives anything needing it.
  Past `integrability_from_dominations`, `hAdom2` never appears again.  ⟹  the concrete-gate discharge is
  ALREADY capped-clean; the ONLY site touching `hAdom2` is the census tuple, for which J4-539 built the
  drop-in capped replacement.  There is NO second clean-`hAdom2` site in leg-1.

  ## THE SPLICE (J4-541 — `hDaLimLU_from_labelled_capped`).

  The capped capstone is the uncapped `hDaLimLU_from_labelled` body VERBATIM, with the SINGLE seam swap:
    •  the `hAdom2` binder (`|witnessSecondXDeriv …| ≤ CA2 · gauss`, whole-time, FALSE at `τ → 0`) is
       replaced by the per-`m` CAPPED family `hAdom2cap` (`epsSeq m ≤ τ`, per-`m` constant `CA2c m`) plus
       the labelled matched-sliver residual `hII_hi_res : MemAdjHi` (the honest HI-leg target,
       `∫₀^{ε_m} τ⁻¹ = +∞`, NOT dischargeable from any pointwise 2nd-derivative Gaussian domination);
    •  the now-unused `hmeas2Hi` binder is DROPPED (the capped census brick does not need it — the HI
       adjacency leg is the carried `hII_hi_res`, not a measurability + pointwise-domination pair);
    •  step (v) calls `DaLimLUCapped.integrability_from_dominations_capped` instead of
       `integrability_from_dominations`; steps (i)/(ii)/(iii)/(iv)/(vi)/(vii)/(viii)/(ix) and the final
       `hDaLimLU_concrete` discharge are byte-identical to the uncapped body.
  The `hLapFull` sub-goal is threaded via the banked facade `memLapFull_from_labelled` on the CAPPED
  tuple's `hII_lo`/`hII_hi` (equivalently the J4-540 route); no uncapped `hAdom2` anywhere on the path.

  Every hypothesis is SATISFIABLE and NON-VACUOUS; NONE is the conclusion.  For the curved instantiation
  `g = g^K` (constant curvature), `hAdom2cap` is TRUE per J4-537, so the capstone stays non-vacuous OFF
  the flat metric at 2nd-derivative order — the point of the whole capping campaign.

  ⚠  `a₁ = R/6` remains CONDITIONAL and effectively FLAT-ONLY.  This capstone purges the false uncapped
  `hAdom2` from leg-1's Da-limit assembly, but does NOT derive the coefficient: the carried `MemAdjHi`
  residuals (both legs, the moment-aware / matched-sliver integrability target), the externally-supplied
  capped leg-2 `hLapFull`, the convergence trio, and the Seeley–DeWitt geometric wiring all remain.  NOT
  `a₁ = R/6`. -/
import Mathlib
import QIQTH.DaLimLUCapped
import QIQTH.DaLimLUCappedStep2
import QIQTH.GlobalRawBoundFacade

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.DaLimCensusRecon QIQTH.DaLimEasyTranche QIQTH.DaLimHardTranche QIQTH.FrozenLaplaceSliver
open QIQTH.DaLimLUConcreteDischarge QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.EveryCeilingFamilies QIQTH.ESLegWidening QIQTH.GlobalRawBoundFacade
open QIQTH.CappedAdom2Audit QIQTH.DaLimLUCapped QIQTH.DaLimLUCappedStep2
open scoped Interval Topology BigOperators

namespace QIQTH.DaLimLUCappedStep3

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ J4-541 — `hDaLimLU_from_labelled_capped`.**  THE LEG-1 LO-CAPPED capstone: the complete
    `DaLimLUGoal` Da-limit assembly at the endgame gate `H_G := vanVleckGatedWitness g gi hChr hK S a b`,
    `F := leviSeries (heatOp g gi H_G)`, reproducing `GlobalRawBoundFacade.hDaLimLU_from_labelled` but with
    the FALSE uncapped whole-time second-derivative domination `hAdom2` PURGED — replaced by the per-`m`
    CAPPED family `hAdom2cap` (via J4-539's drop-in `integrability_from_dominations_capped`) plus the
    carried labelled matched-sliver residual `hII_hi_res : MemAdjHi`.  The `hmeas2Hi` binder of the
    uncapped capstone is dropped (the capped census brick carries the HI adjacency leg as the residual,
    not a measurability + pointwise-domination pair).  Every OTHER binder + every downstream discharge
    (gauge, W2 interchange family, Levi source envelope, √ε sliver, labelled raw bound, atomic carrier,
    E-combination, final `hDaLimLU_concrete`) is identical to the uncapped capstone.  Every hypothesis is
    SATISFIABLE and NON-VACUOUS; NONE is the conclusion; for `g = g^K` (const curvature) `hAdom2cap` is
    TRUE per J4-537, so this stays non-vacuous off the flat metric.  NOT `a₁ = R/6`. -/
theorem hDaLimLU_from_labelled_capped (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (T : ℝ) (U : Set ℝ) (hUopen : IsOpen U) (hn : 1 ≤ n)
    -- (i) geometry / gauge raw inputs:
    (hK0 : (0 : Point n) ∈ K)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hinvF : ∀ y c d, (∑ σ, g y c σ * gi y σ d) = if c = d then 1 else 0)
    (hdg0 : ∀ c d e, pd (fun y => g y c d) e (0 : Point n) = 0)
    -- (ii) the W2 differentiation-under-∫ family (at `F := leviSeries (heatOp g gi H_G)`):
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
            (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) y z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    (hFmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
            (Function.update (0 : Point n) i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bnd : ℕ → Fin n → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (bnd m i) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ bnd m i s)
    (hdiff : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) w)
    -- (iii) the residual-domination time floor / window:
    (aa : ℝ) (haa : 0 < aa) (hau : ∀ u ∈ U, aa ≤ u) (hUTle : ∀ u ∈ U, u ≤ T)
    -- (iv) the Levi source envelope package:
    (C : ℝ) (dataLevi : LeviSeriesLocalData
        (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) C T)
    -- (v) the integrability Gaussian dominations + measurabilities (★ CAPPED: `hAdom2cap` + residual):
    (wA CA wA2 : ℝ) (CA2c : ℕ → ℝ)
    (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwA2 : 0 < wA2) (hCA2c : ∀ m, 0 ≤ CA2c m)
    (hAdomHeat : ∀ τ : ℝ, 0 < τ → τ ≤ T → ∀ z : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ 0 z|
          ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hAdom2cap : ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA2c m * gaussDdim (wA2 * τ) (0 - z))
    (hmeasLo : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hmeasHi : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
    (hmeas2Lo : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    -- (v-residual) ★ THE MATCHED-SLIVER HI-LEG RESIDUAL — CARRIED, NOT from any pointwise domination:
    (hII_hi_res : MemAdjHi (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    -- (vi) the √ε sliver amplitude bundle:
    (τ₀ : ℝ)
    (dataAmp : ∀ i : Fin n, AmplitudeDerivativeData g gi hChr hK S a b
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) i T τ₀)
    (hεaa : ∀ m : ℕ, epsSeq m < aa / 2) (hετ₀ : ∀ m : ℕ, epsSeq m ≤ τ₀)
    -- (vii) ★ the labelled residual gated raw bound:
    (P : ℝ) (hP : 0 ≤ P)
    (hraw : GlobalGatedRawBound g gi (vanVleckGatedWitness g gi hChr hK S a b) P)
    -- (viii) ★ the labelled atomic interchange carrier:
    (hPd2conv : ∀ u ∈ U, ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
              (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u x 0) i y) i 0)))
    -- (ix) the E-combination carries:
    (hDa : ∀ (m : ℕ) (u : ℝ),
        DaTrunc (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s)
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    (hLap : ∀ (m : ℕ) (u : ℝ),
        LapTrunc g gi (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    (hLapZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
    (hEZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
    (hLapS : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z,
            laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hES : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m)) :
    DaLimLUGoal g gi (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U := by
  -- abbreviations kept implicit via the literal expressions.
  -- (i) gauge.
  obtain ⟨hgi, hΓ⟩ := gauge_from_geometry g gi hK0 hframeK hinvF hdg0
  -- (ii) the frozen-side interchange member (from the W2 family) — reused for `hLapFull`.
  have hInter :
      MemInterchange (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) :=
    QIQTH.SecondOrderInterchangeConcrete.witness_MemInterchange g gi hChr hK S a b
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) (0 : ℝ) U
      V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
  -- (iii)/(iv) source envelope: width-2 `hFdom`, `hFzero`, and the derived width-2 `hFdomW`.
  obtain ⟨⟨C_L, hCL0, hFdom⟩, hFzero⟩ :=
    source_from_leviData g gi hChr hK S a b T C hn dataLevi
  have hFzero0 : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
      leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0 :=
    fun s hs z => hFzero s hs z 0
  have hFdomW : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
      |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
        ≤ C_L * gaussDdim (2 * s) z := by
    intro s hs hsT z
    have h := hFdom s hs hsT z 0
    rwa [sub_zero] at h
  have hUpos : ∀ u ∈ U, 0 < u := fun u hu => lt_of_lt_of_le haa (hau u hu)
  -- (v) ★ CAPPED integrability legs — `integrability_from_dominations_capped`, NO uncapped `hAdom2`.
  obtain ⟨hIlo, hIhi, hII_lo, hII_hi⟩ :=
    QIQTH.DaLimLUCapped.integrability_from_dominations_capped g gi hChr hK S a b U T wA CA wA2 2 C_L CA2c
      hwA hCA hwA2 hCA2c (by norm_num) hCL0 hUpos hUTle hAdomHeat hAdom2cap hFdomW hFzero0
      hmeasLo hmeasHi hmeas2Lo hII_hi_res
  -- (vi) sliver amplitudes.
  obtain ⟨D0, D1, hD0, hD1, hbnd⟩ :=
    sliver_from_ampData g gi hChr hK S a b
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U T τ₀ aa haa
      dataAmp hau hUTle hεaa hετ₀
  -- (vii) ★ residual width-3/2 domination from the labelled raw bound.
  obtain ⟨E₀, E₁, hE₀, hE₁, hEdom⟩ :=
    hEdom_of_globalRawBound g gi (vanVleckGatedWitness g gi hChr hK S a b) P hP hraw
  -- (viii) ★ untruncated interchange (`hLapFull`) from the labelled atomic carrier + CAPPED tuple.
  have hLapFull :
      MemLapFull g gi (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) :=
    memLapFull_from_labelled g gi (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
      (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z)
      hgi hΓ hInter hII_lo hII_hi D0 D1 hD0 hD1 hbnd hPd2conv
  -- (ix) E-combination.
  have hEcomb :
      MemECombine g gi (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) :=
    eCombine_from_data g gi (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
      hDa hLap hLapZ hEZ hLapS hES
  -- ★★★ thread every discharged binder into the concrete-gate Da-limit (identical to uncapped).
  exact QIQTH.DaLimLUConcreteDischarge.hDaLimLU_concrete g gi hChr hK S a b
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) T U hUopen hn
    hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    hLapFull hII_lo hII_hi D0 D1 hD0 hD1 hbnd
    E₀ E₁ C_L aa hE₀ hE₁ hCL0 haa hau hUTle hEdom hFdom hFzero hIlo hIhi hEcomb

end QIQTH.DaLimLUCappedStep3

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.DaLimLUCappedStep3.hDaLimLU_from_labelled_capped
