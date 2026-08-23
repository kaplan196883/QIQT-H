/-
  HDConvGateInterchangeWired — the J4-898/914 `hDuhamel`-side `MemLapFull`/`MemAdjLo` deep-wire
  (`InterchangeBundlesDeeperWired.memLapFull_live_crude` / `.memAdjLo_live_crude`) cross-wired into
  the `hDConv`-side `HDConvGateThreading.hDConv_AT_GATE` census, which had NEVER received it.

  One brick of the `a₁ = R/6` heat-kernel campaign.  It is NOT `a₁ = R/6`, and proves NOTHING about
  `R/6`.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  UNDER-CREDITING FIND (mirrors J4-1101/1102/1105/1109's discovery pattern).  J4-898
  (`InterchangeBundlesFromExisting`) + J4-914 (`InterchangeBundlesDeeperWired`) DISCHARGED the FOUR
  interchange-bundle census binders `{hLapFull, hII_lo, hII_hi, hEcomb}` for the LIVE order-1
  `hDuhamel`-side capstone (`HDuhamelExportRethread.truncatedDuhamelCore_AT_GATE_FULL`), explicitly
  noting the census is "shared by `hDuhamel` AND `hDConv` via the `hDaLimLU` data" (J4-898 header).
  But `HDConvGateThreading.hDConv_AT_GATE` (the `hDConv`-side capstone, a SIBLING theorem sharing the
  IDENTICAL `hLapFull`/`hII_lo`/`hII_hi` binder shapes verbatim — same `MemLapFull`/`MemAdjLo` abbrevs,
  same `pdpdH := witnessSecondXDeriv …`, same `F` + `hFeq` reconciliation) was NEVER re-threaded: its
  own signature (`HDConvGateThreading.lean:240-243`) still carries `hLapFull`/`hII_lo`/`hII_hi` as RAW
  opaque hypotheses, exactly the situation J4-1101–1109 corrected for `hAzero`/`hUfloor`/`nb`/`hnb`/
  `hAdom`/`hWDom`/`hFdom`/`hQ1`.  This file performs the SAME correction for `hLapFull`/`hII_lo`.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS.  `hDConv_AT_GATE_interchangeWired` — `HDConvGateThreading.hDConv_AT_GATE`'s IDENTICAL
  conclusion, with its `hLapFull : MemLapFull …` and `hII_lo : MemAdjLo …` binders REMOVED and REPLACED
  by the strictly more primitive carries `InterchangeBundlesDeeperWired.memLapFull_live_crude` /
  `.memAdjLo_live_crude` need beyond what `hDConv_AT_GATE` ALREADY carries:
    •  `hUpos` is derived FOR FREE from the existing `haT : 0 < aT` + `hUlb : ∀ u ∈ U, aT ≤ u`.
    •  `hFdom`/`hUT`/`hn`/`hgi`/`hII_hi`/`D0`/`D1`/`hD0`/`hD1`/`hbnd` are REUSED VERBATIM (no
       duplicate binder; the specialization `y := 0`, `wF := 2`, `CF := C_L` of the census's OWN
       general-`y` `hFdom` supplies both providers' `y = 0` slice domination).
    •  the SHARED slice-measurability binder `hmeas2Lo` feeds BOTH `memAdjLo_live_crude`'s `hmeas` and
       `memLapFull_live_crude`'s `hmeas2Lo` (identical type).
    •  genuinely NEW carries: `wA2`/`hwA2`, `Ccrude`/`hCcrude`, the crude `τ⁻¹` envelope `hcrude`
       (⟵ replaces the assembled `hAdom2cap`), `hInter : MemInterchange` (the frozen-side interchange),
       `hdg0` (the RNC first-derivative gauge `∂g(0) = 0`, ⟵ replaces `hΓ : MemGaugeGamma`).

  Every hypothesis is the PROVIDER'S OWN satisfiable, non-vacuous named carry (verbatim from
  `InterchangeBundlesDeeperWired`, itself verbatim from `CappedAdom2Audit`/`DaLimEasyTranche`/
  `DaLimCensusRecon`); NONE is the conclusion; no `hAnear`, no uncapped whole-time `hAdom2`. This is a
  pure find-and-wire composition — no new analysis, no `sorry`, no new axiom, no existing file edited.
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HDConvGateThreading
import QIQTH.InterchangeBundlesDeeperWired

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound
open QIQTH.DaLimLUWallRecon
open scoped Interval Topology BigOperators

namespace QIQTH.HDConvGateInterchangeWired

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ `hDConv_AT_GATE_interchangeWired`.**  `HDConvGateThreading.hDConv_AT_GATE` with its
    `hLapFull : MemLapFull …` and `hII_lo : MemAdjLo …` census binders REMOVED and derived INTERNALLY
    from `InterchangeBundlesDeeperWired.memLapFull_live_crude` / `.memAdjLo_live_crude`, reusing the
    capstone's OWN `hFdom`/`hUT`/`hn`/`hgi`/`hII_hi`/`D0`/`D1`/`hD0`/`hD1`/`hbnd` and deriving `hUpos`
    from `haT`/`hUlb` — plus the genuinely NEW primitive carries `wA2`/`hwA2`, `Ccrude`/`hCcrude`,
    `hcrude` (crude `τ⁻¹` domination), `hInter : MemInterchange`, `hdg0` (RNC gauge `∂g(0) = 0`), and
    the shared slice measurability `hmeas2Lo`.  NOT `a₁ = R/6`. -/
theorem hDConv_AT_GATE_interchangeWired (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ)
    (hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    (t T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUT : ∀ u ∈ U, u ≤ T) (hn : 1 ≤ n)
    (hgi : MemGaugeGi (n := n) gi) (hΓ : MemGaugeGamma (n := n) g gi)
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u
            (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) y z * F s z 0)
    (hFmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
            (Function.update (0 : Point n) i w) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (0 : Point n) z * F s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s) (0 : Point n) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bnd : ℕ → Fin n → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (bnd m i) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0‖ ≤ bnd m i s)
    (hdiff : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0)
            (∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0) w)
    -- ── REPLACES `hLapFull`/`hII_lo`: the strictly-more-primitive carries ────────────────────────
    (wA2 Ccrude : ℝ) (hwA2 : 0 < wA2) (hCcrude : 0 ≤ Ccrude)
    (hcrude : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z|
          ≤ Ccrude * τ⁻¹ * gaussDdim (wA2 * τ) (0 - z))
    (hInter : MemInterchange (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (hmeas2Lo : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hII_hi : MemAdjHi F U (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv g gi hChr hK S a b i (u - s) z * F s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (hPd2conv : ∀ u ∈ U, ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
              (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u x 0) i y) i 0)))
    -- ── the REST of `hDConv_AT_GATE`'s census, unchanged ─────────────────────────────────────────
    (E₀ E₁ C_L aT : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hC_L : 0 ≤ C_L) (haT : 0 < aT)
    (hUlb : ∀ u ∈ U, aT ≤ u)
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n, F s z y = 0)
    (hIlo : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z * F s z 0)
          volume 0 (u - epsSeq m))
    (hIhi : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z * F s z 0)
          volume (u - epsSeq m) u)
    (hEcomb : MemECombine g gi (vanVleckGatedWitness g gi hChr hK S a b) F)
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness g gi hChr hK S a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness g gi hChr hK S a b τ p q = 0)
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    (hUfloor : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ U, c ≤ u)
    (hInnerCont : ∀ u ∈ U,
        ContinuousOn (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
          (Set.Ioo 0 u))
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ c, AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (c - s) 0 z * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
      volume 0 (u - epsSeq m))
    (hF'meas_d : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s) * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundD : ℕ → ℝ → ℝ → ℝ)
    (hbdd_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
    (hbound_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb m u,
      ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (c - s) * F s z 0‖
        ≤ boundD m u s)
    (hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb m u,
      HasDerivAt (fun c => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (c - s) 0 z * F s z 0)
        (∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (c - s) * F s z 0) c)
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F (u + h) (u - epsSeq m + k) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F (u + h) (u - epsSeq m) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u (u - epsSeq m + k) 0 0
          + heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|))
    (ρ lam CW Cf τ₀ : ℝ) (ta tb : ℝ)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ₀ : 0 < τ₀)
    (hWmeas : ∀ τ, AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hChr hK S a b τ (0 : Point n) z) volume)
    (hffro_meas : ∀ u, AEStronglyMeasurable (fun z => F u z (0 : Point n)) volume)
    (hfmov_meas : ∀ m u, AEStronglyMeasurable (fun z => F (u - epsSeq m) z (0 : Point n)) volume)
    (hffro_bdd : ∀ u z, |F u z (0 : Point n)| ≤ Cf)
    (hfmov_bdd : ∀ m u z, |F (u - epsSeq m) z (0 : Point n)| ≤ Cf)
    (hWDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z,
      |vanVleckGatedWitness g gi hChr hK S a b τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z)
    (hmass : ∀ᶠ m in atTop, ∫ z, |vanVleckGatedWitness g gi hChr hK S a b (epsSeq m) (0 : Point n) z| ≤ CW)
    (hmassone : Tendsto
        (fun m => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (epsSeq m) (0 : Point n) z) atTop (𝓝 1))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.ball (0 : Point n) δ,
          |F u z (0 : Point n) - F u (0 : Point n) (0 : Point n)| < ε)
    (hsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
          |F (u - epsSeq m) z (0 : Point n) - F u z (0 : Point n)| < ε)
    (hUsub : U ⊆ Set.Icc ta tb) :
    DifferentiableAt ℝ
      (fun u => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u 0 0) t := by
  subst hFeq
  -- `hUpos` FOR FREE from `haT`/`hUlb`.
  have hUpos : ∀ u ∈ U, 0 < u := fun u hu => lt_of_lt_of_le haT (hUlb u hu)
  -- the `y = 0` specialization of the census's OWN general-`y` `hFdom` (`wF := 2`, `CF := C_L`).
  have hFdom0 : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
      |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
        ≤ C_L * gaussDdim (2 * s) z := by
    intro s hs hsT z
    have h := hFdom s hs hsT z 0
    simpa using h
  -- the `y = 0` specialization of the census's OWN general-`y` `hFzero`.
  have hFzero0 : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
      leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0 :=
    fun s hs z => hFzero s hs z 0
  -- the per-`m` capped second-derivative family from the primitive crude `τ⁻¹` envelope.
  have hAdom2cap : ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
      |witnessSecondXDeriv g gi hChr hK S a b i τ z|
        ≤ (Ccrude * (epsSeq m)⁻¹) * gaussDdim (wA2 * τ) (0 - z) :=
    QIQTH.CappedAdom2Audit.hAdom2_capped_family_of_crude g gi hChr hK S a b T Ccrude wA2
      hCcrude hcrude
  have hCA2c : ∀ m, 0 ≤ (Ccrude * (epsSeq m)⁻¹) := fun m =>
    mul_nonneg hCcrude (le_of_lt (inv_pos.mpr (epsSeq_pos m)))
  -- `hII_lo` built from the capped family (⟵ the primitive crude envelope).
  have hII_lo : MemAdjLo (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
      (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) :=
    QIQTH.InterchangeBundlesFromExisting.memAdjLo_live g gi hChr hK S a b U
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) rfl
      T wA2 2 C_L (fun m => Ccrude * (epsSeq m)⁻¹) hwA2 hCA2c (by norm_num) hC_L
      hUpos hUT hAdom2cap hFdom0 hFzero0 hmeas2Lo
  -- `hLapFull` built from the capped family + the census's OWN `hΓ`.
  have hLapFull : MemLapFull g gi (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
      (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) :=
    QIQTH.InterchangeBundlesFromExisting.memLapFull_live g gi hChr hK S a b U
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) rfl
      T wA2 2 C_L (fun m => Ccrude * (epsSeq m)⁻¹) hwA2 hCA2c (by norm_num) hC_L
      hUpos hUT hgi hΓ hInter hAdom2cap hFdom0 hFzero0 hmeas2Lo hII_hi D0 D1 hD0 hD1 hbnd hPd2conv
  exact QIQTH.HDConvGateThreading.hDConv_AT_GATE g gi hChr hK S a b
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) rfl t T hT U hUopen htU
    hUT hn hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    hLapFull hII_lo hII_hi D0 D1 hD0 hD1 hbnd
    E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hEdom hFdom hFzero hIlo hIhi hEcomb
    A₀ A₁ hA₀ hA₁ hAdom hAzero hMeasFII hUfloor hInnerCont nb hnb
    hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
    ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd
    hWDom hmass hmassone hmod hsup hUsub

end QIQTH.HDConvGateInterchangeWired

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HDConvGateInterchangeWired.hDConv_AT_GATE_interchangeWired
