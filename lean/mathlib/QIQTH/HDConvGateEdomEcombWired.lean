/-
  HDConvGateEdomEcombWired — the J4-897 `hEdom` and J4-898 `hEcomb` `hDuhamel`-side dischargers
  cross-wired into the `hDConv`-side `HDConvGateThreading.hDConv_AT_GATE` census, which had NEVER
  received either.

  One brick of the `a₁ = R/6` heat-kernel campaign.  It is NOT `a₁ = R/6`, and proves NOTHING about
  `R/6`.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  UNDER-CREDITING FIND (mirrors J4-1101/1102/1105/1109/1110's discovery pattern).  Both
  `HEdomFromHrawPreCollapse.hEdom_from_hrawPreCollapse` (J4-897) and
  `InterchangeBundlesFromExisting.memECombine_live` (J4-898) already produce the EXACT census-binder
  shapes `HDConvGateThreading.hDConv_AT_GATE` carries for `hEdom` (lines 251-253) and `hEcomb`
  (line 264) — J4-897's own header explicitly states its target is "shared by `hDuhamel`
  (`HDuhamelExportRethread.truncatedDuhamelCore_AT_GATE_FULL`) AND `hDConv` (the same `hDaLimLU`
  data)", and J4-898's header makes the identical claim for `hEcomb`.  But neither was ever
  re-threaded into `hDConv_AT_GATE`'s own signature: character-checking confirms it STILL carries
  `hEdom` (at fixed external `E₀ E₁ hE₀ hE₁`, unused anywhere else in the signature) and `hEcomb` as
  two raw opaque binders — the documentation-not-execution gap J4-1110 diagnosed for
  `hLapFull`/`hII_lo`, now closed for `hEdom`/`hEcomb`.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS.  `hDConv_AT_GATE_edomEcombWired` — `HDConvGateThreading.hDConv_AT_GATE`'s IDENTICAL
  binder list with `{E₀, E₁, hE₀, hE₁, hEdom}` REMOVED and derived INTERNALLY (via an `obtain` on
  `HEdomFromHrawPreCollapse.hEdom_from_hrawPreCollapse`'s `∃ E₀ E₁, …` conclusion) from the single new
  named carry `{P, hP, hgate}` (the on-gate width-4/3 quadratic parametrix bound), and `hEcomb`
  REMOVED and derived INTERNALLY (via `InterchangeBundlesFromExisting.memECombine_live`) from the six
  new named carries `{hDa, hLap, hLapZ, hEZ, hLapS, hES}` (per-`(m,u)` Fubini/representation/
  integrability facts).  Every hypothesis is the PROVIDER'S OWN satisfiable, non-vacuous named carry;
  NONE is the conclusion.  This is a pure find-and-wire composition — no new analysis, no `sorry`, no
  new axiom, no existing file edited.  Consulted `gpt-5.6-sol` (high) before construction: confirmed
  the composition is sound/non-circular (neither discharger depends on `hDConv_AT_GATE` or reuses
  `hEdom`/`hEcomb` as an input), confirmed `E₀ E₁ hE₀ hE₁` are genuinely unused elsewhere in
  `hDConv_AT_GATE`'s signature so dropping them for an internal `obtain` is the correct interface
  reduction (mirroring J4-1109's `hFrozenData` trade), and flagged the implicit/explicit `K`-binder
  character-check (confirmed: `{K : Set (Point n)} (hK : IsCompact K)` identically in all three
  theorems) as the one thing to verify directly rather than assume.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HDConvGateThreading
import QIQTH.HEdomFromHrawPreCollapse
import QIQTH.InterchangeBundlesFromExisting

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound
open QIQTH.DaLimLUWallRecon
open QIQTH.RadialDistance
open scoped Interval Topology BigOperators

namespace QIQTH.HDConvGateEdomEcombWired

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ `hDConv_AT_GATE_edomEcombWired`.**  `HDConvGateThreading.hDConv_AT_GATE` with its
    `{E₀, E₁, hE₀, hE₁, hEdom}` and `hEcomb : MemECombine …` census binders REMOVED and derived
    INTERNALLY from the banked `HEdomFromHrawPreCollapse.hEdom_from_hrawPreCollapse` (J4-897) and
    `InterchangeBundlesFromExisting.memECombine_live` (J4-898) `hDuhamel`-side dischargers, at the new
    primitive carries `{P, hP, hgate}` (for `hEdom`) and `{hDa, hLap, hLapZ, hEZ, hLapS, hES}` (for
    `hEcomb`).  NOT `a₁ = R/6`. -/
theorem hDConv_AT_GATE_edomEcombWired (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hLapFull : MemLapFull g gi (vanVleckGatedWitness g gi hChr hK S a b) F U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (hII_lo : MemAdjLo F U (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (hII_hi : MemAdjHi F U (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv g gi hChr hK S a b i (u - s) z * F s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (C_L aT : ℝ) (hC_L : 0 ≤ C_L) (haT : 0 < aT)
    (hUlb : ∀ u ∈ U, aT ≤ u)
    -- ── REPLACES `E₀,E₁,hE₀,hE₁,hEdom`: the on-gate width-4/3 quadratic parametrix carry ──────────
    (P : ℝ) (hP : 0 ≤ P)
    (hgate : ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n, p ∈ closure (S q) →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ P * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (p - q)))
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
    -- ── REPLACES `hEcomb`: the six per-`(m,u)` Fubini/representation/integrability carries ───────
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
        (fun z => laplaceBeltrami g gi
            (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
    (hEZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
    (hLapS : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, laplaceBeltrami g gi
            (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hES : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m))
    -- ── the REST of `hDConv_AT_GATE`'s census, unchanged ─────────────────────────────────────────
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
  -- `hEdom` derived internally from the on-gate width-4/3 quadratic carry `hgate` (J4-897).
  obtain ⟨E₀, E₁, hE₀, hE₁, hEdom⟩ :=
    QIQTH.HEdomFromHrawPreCollapse.hEdom_from_hrawPreCollapse g gi hChr hK S a b P hP hgate
  -- `hEcomb` derived internally from the six per-`(m,u)` carries (J4-898).
  have hEcomb : MemECombine g gi (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) :=
    QIQTH.InterchangeBundlesFromExisting.memECombine_live g gi hChr hK S a b
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) rfl
      hDa hLap hLapZ hEZ hLapS hES
  exact QIQTH.HDConvGateThreading.hDConv_AT_GATE g gi hChr hK S a b
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) rfl t T hT U hUopen htU
    hUT hn hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    hLapFull hII_lo hII_hi D0 D1 hD0 hD1 hbnd
    E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hEdom hFdom hFzero hIlo hIhi hEcomb
    A₀ A₁ hA₀ hA₁ hAdom hAzero hMeasFII hUfloor hInnerCont nb hnb
    hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
    ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd
    hWDom hmass hmassone hmod hsup hUsub

end QIQTH.HDConvGateEdomEcombWired

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HDConvGateEdomEcombWired.hDConv_AT_GATE_edomEcombWired
