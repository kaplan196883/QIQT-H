/-
  HDConvGateHQ1Discharged — eliminate the frozen first-order interchange EQUALITY carry `hQ1`
  from the live `hDConv_AT_GATE` census, in favour of the SEVEN-leg frozen diff-under-∫ provider
  `hFrozenData` (the raw measurability / interval-integrability / dominator / `HasDerivAt` inputs)
  ALREADY sufficient to PROVE that equality via the banked `W2Finish.w2_hQ1` (J4-378).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure COMPOSITION / dependency-normalization brick — the `hDConv`-side sibling of
  `HDuhamelHQ1Discharged.hDuhamelSlot_hQ1_discharged` (J4-982), which performed the IDENTICAL
  reduction for the `hDuhamel` slot.  This is precisely the "under-crediting" pattern this campaign
  has flagged repeatedly (e.g. J4-1102): `W2Finish.w2_hQ1` was built at an EARLIER stage of this same
  tower and simply never re-wired into `HDConvGateThreading.hDConv_AT_GATE`'s live census, even though
  `hDConv_AT_GATE`'s `hQ1` binder is LITERALLY the same shape (same `W := vanVleckGatedWitness g gi
  hChr hK S a b`, same `F := leviSeries (heatOp g gi W)` after `hFeq`-substitution) that
  `HDuhamelHQ1Discharged` already reduced for the sibling `hDuhamel` theorem.

  `HDConvGateThreading.hDConv_AT_GATE`'s `hQ1` binder:
      `hQ1 : ∀ m i, ∀ u ∈ U, ∀ y ∈ V,
         pd (fun x => heatConvFrozen W F u (u−ε_m) x 0) i y
           = ∫ s in (0)..(u−ε_m), ∫ z, witnessFieldDeriv … i (u−s) y z · F s z 0`
  on the SHARED field neighborhood `V ∋ 0` (a SINGLE, m-INDEPENDENT nbhd — the exact shape the gate
  binds; NO per-`(u,i,m)` existential, NO m-collapse trap) — is SYNTACTICALLY IDENTICAL, after
  `hFeq`-substitution, to `HDuhamel`'s original `hQ1` (both instantiate the SAME banked
  `W2Finish.w2_hQ1`, whose conclusion is baked to the composite
  `F := leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))`, not a generic `F`).

  `W2Finish.w2_hQ1` (J4-378, F3): DERIVES EXACTLY that shared-`V` equality — threading
  `SecondOrderInterchange.pd_heatConvFrozen_interchange` per `(m,i,u,y)` — FROM the seven-leg frozen
  first-order diff-under-∫ provider `hFrozenData` on the SAME shared `V`: a real-line nbhd
  `snb ∈ 𝓝 (y i)`, the witness / field-derivative pairing measurabilities and interval-integrabilities,
  an interval-integrable `s`-dominator, and the outer `s`-level `HasDerivAt` family.

  This file COMPOSES them: it derives the shared-`V` interchange equality `hQ1` from `hFrozenData`
  via `W2Finish.w2_hQ1`, and feeds it into `HDConvGateThreading.hDConv_AT_GATE`'s census, whose
  remaining surface (INCLUDING `hFmeas`/`hFint`/`hF'meas`, which are SEPARATE hypotheses from `hQ1`
  and are NOT touched by this trade) is reproduced verbatim.  Net effect: the frozen first-order
  interchange EQUALITY `hQ1` is GONE from the live `hDConv` surface, traded for its raw diff-under-∫
  INPUTS `hFrozenData` — a genuine dependency-frontier reduction (a cooked interchange identity
  replaced by the elementary satisfiable measurability / integrability / dominator / `HasDerivAt`
  side conditions that PROVE it), NOT a new analytic result and NOT a logical weakening, and NOT a
  claim that `hFmeas`/`hFint`/`hF'meas` (still fully separately open) are discharged.

  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE LANDS.
    • `hDConv_AT_GATE_hQ1_discharged` — the EXACT `hDConv_AT_GATE` `DifferentiableAt` conclusion at
      the (abstract) van-Vleck gate `S`, with the frozen first-order interchange EQUALITY carry `hQ1`
      ELIMINATED from the antecedent surface, DERIVED internally from `W2Finish.w2_hQ1` (J4-378) fed
      the seven-leg frozen first-order diff-under-∫ provider `hFrozenData`.  Every remaining binder is
      verbatim from `HDConvGateThreading.hDConv_AT_GATE`.  Pure composition; NONE of the hypotheses is
      the conclusion.

  ⚠  STILL NOT `a₁ = R/6`.  `hFmeas`/`hFint`/`hF'meas` and the ~20 remaining Section-G census members
  (`hLapFull`, `hII_lo/hi`, `hFdom`/`hEdom`/`hEcomb`, `boundD`/`hpardiff` family, `L`/`hLnn`/`hCross`,
  etc.) are NOT discharged here.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv,
  hCConv}`, UNCHANGED.
-/
import QIQTH.HDConvGateThreading
import QIQTH.W2Finish

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel
open QIQTH.HeatKernelA1 QIQTH.LaplaceBeltrami
open QIQTH.HeatResidualBound QIQTH.LeviSeries
open QIQTH.TruncatedDuhamelData QIQTH.DaLimLUWallRecon
open QIQTH.ETailRateBound QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped Interval Topology BigOperators

namespace QIQTH.HDConvGateHQ1Discharged

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ `hDConv_AT_GATE_hQ1_discharged`.**  The EXACT `hDConv_AT_GATE` `DifferentiableAt`
    conclusion at the concrete van-Vleck gated witness, with the frozen first-order interchange
    EQUALITY carry `hQ1` ELIMINATED from the antecedent surface.  The `hQ1` equality (shared-`V`
    shape, single `V ∈ 𝓝 0`) is DERIVED internally from `W2Finish.w2_hQ1` (J4-378), fed the seven-leg
    frozen first-order diff-under-∫ provider `hFrozenData` on the SAME shared `V`.  Every remaining
    binder is verbatim from `HDConvGateThreading.hDConv_AT_GATE` (J4-312) — in particular
    `hFmeas`/`hFint`/`hF'meas` remain fully separate, explicit, undischarged hypotheses.  Pure
    composition; NONE of the hypotheses is the conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem hDConv_AT_GATE_hQ1_discharged (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ)
    (hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    (t T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUT : ∀ u ∈ U, u ≤ T) (hn : 1 ≤ n)
    -- ── the `hDaLimLU` data census (from `hDaLimLU_concrete`), `hQ1` REPLACED by `hFrozenData` ──────
    (hgi : MemGaugeGi (n := n) gi) (hΓ : MemGaugeGamma (n := n) g gi)
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hFrozenData : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
          snb ∈ 𝓝 (y i) ∧
          (∀ w : ℝ, AEStronglyMeasurable
            (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s)
                (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            (volume.restrict (Set.uIoc 0 (u - epsSeq m)))) ∧
          IntervalIntegrable
            (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) y z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            volume 0 (u - epsSeq m) ∧
          AEStronglyMeasurable
            (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) y z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            (volume.restrict (Set.uIoc 0 (u - epsSeq m))) ∧
          IntervalIntegrable bound volume 0 (u - epsSeq m) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
            ‖∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖
              ≤ bound s) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
            HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s)
                (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
              (∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) w))
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
    -- ── the F2 pile + `hFII` pile (for `hDConv_W1free`) ──────────────────────────────────────────
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
    -- ── the frozen/moving satisfiable lists (for `hbdryLU_CONCRETE`) ─────────────────────────────
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
  -- Derive the shared-`V` frozen first-order interchange EQUALITY `hQ1` from its raw diff-under-∫
  -- inputs `hFrozenData`, via the banked `W2Finish.w2_hQ1` (J4-378).  The shared `V` is passed
  -- through unchanged — no per-`(u,i,m)` existential, no m-uniformity gap.
  have hQ1 := QIQTH.W2Finish.w2_hQ1 g gi hChr hK S a b U V hFrozenData
  -- Feed the derived interchange equality into `hDConv_AT_GATE`; every other binder is verbatim.
  exact QIQTH.HDConvGateThreading.hDConv_AT_GATE g gi hChr hK S a b _ rfl t T hT U hUopen htU hUT hn
    hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    hLapFull hII_lo hII_hi D0 D1 hD0 hD1 hbnd
    E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hEdom hFdom hFzero hIlo hIhi hEcomb
    A₀ A₁ hA₀ hA₁ hAdom hAzero hMeasFII hUfloor hInnerCont
    nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
    ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd
    hWDom hmass hmassone hmod hsup hUsub

end QIQTH.HDConvGateHQ1Discharged

section AxiomChecks
open QIQTH.HDConvGateHQ1Discharged
#print axioms hDConv_AT_GATE_hQ1_discharged
end AxiomChecks
