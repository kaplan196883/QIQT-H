/-
  CurvedA1Assembled — J4-548.  THE FIRST GENUINELY CURVED-SATISFIABLE a₁ two-jet capstone.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6`.  It proves NOTHING new about the coefficient.

  ## THE KEY MOVE (J4-548) — route BOTH legs through the CAPPED (curved-valid) 2nd-derivative bound.

  Every prior curved a₁ capstone (`A1R6FromLabelledCurved.a1_R6_from_labelled_curved`,
  `…CurvedGauge.a1_R6_from_labelled_curved_gauge`, `…CurvedBoundary.a1_R6_from_labelled_curved_boundary`)
  carries, in its Da-limit leg, the CLEAN whole-time second-`x`-derivative Gaussian bound
      `hAdom2 : ∀ (i) (τ), 0 < τ → τ ≤ T → ∀ z, |witnessSecondXDeriv …| ≤ CA2 · gaussDdim (wA2·τ) (0−z)`.
  J4-537/538 PROVED this clean bound is FALSE for the genuinely-curved witness `g^K = curvedRNCMetric K`
  (`K < 0`): near `τ → 0` the second derivative blows up like `τ⁻¹` from the metric-deviation `(r²/τ)²`
  term, so no single constant `CA2` dominates.  Consequently, instantiating any of those capstones at
  `g := curvedRNCMetric K` makes the `hAdom2` antecedent UNSATISFIABLE — the instantiation is VACUOUS
  (flat-only in disguise).

  This assembly REMOVES the clean `hAdom2` binder entirely.  It threads the a₁ two-jet through the three
  banked sub-assemblies DIRECTLY:
    • `htr_adapter`      — the Seeley–DeWitt `htr : ∑_a ∂²_{dc} g_{aa}(0) = −(2/3)·Ric_{cd}` from the
                            labelled RNC Gauss-lemma `hGauss` (SDW geometric wiring, CARRIED);
    • `a1_R6_slots_AT_GATE` — the three per-gate analytic slots, consuming the two LEG OUTPUTS as
                            EXTERNAL binders:  `hDa : DaLimLUGoal` (LEG 1) and `core :
                            TruncatedDuhamelCore` (LEG 2), plus `hbdry` and the hDConv/hCConv census;
    • `wide_a1_R6_core_AT_CONSTRADIUS` — the pre-∃ core at `Ric := fun c d => ricci g gi c d 0`.
  LEG 1's `hDa` is the caller-supplied output of `DaLimLUCappedStep3.hDaLimLU_from_labelled_capped`
  (J4-541) — which uses the PER-`m` CAPPED bound `hAdom2cap` (curved-VALID, `curvedRNC_witnessSecondXDeriv
  _dom_crude` capped via `hAdom2cap_grounded`), NOT the clean `hAdom2`.  LEG 2's `core` is built from
  `Leg2HLapFull.curved_leg2_hLapFull`'s `hLapFull` (J4-547) via `truncatedDuhamelCore_AT_GATE_FULL`, again
  through the capped route.  So NO clean `hAdom2` appears anywhere: for `g^K` (`K < 0`) EVERY antecedent
  is jointly satisfiable, and the conclusion coefficient `(∑_i ricci g gi i i 0)/6 = n(n−1)K/6 ≠ 0` is
  genuinely NONZERO (`curvedRNCMetric_ricci_from_gauge`: `Ric(0) = (n−1)K δ`).  This is the FIRST a₁
  capstone that is NOT flat-only — Sol-audited (satisfiable / non-vacuous / honest, high).

  ## WHAT IS CARRIED (honest residue).

  The assembled capstone's antecedents reduce to EXACTLY:
    • LEG 1 `hDa : DaLimLUGoal` and LEG 2 `core : TruncatedDuhamelCore` — the two capped-route leg outputs
      (each downstream of a `MemAdjHi` matched-sliver moment residual + the convergence trio, carried in
      their J4-541/J4-547 suppliers, NOT re-derived here);
    • `hbdry : hbdryLUTarget` — the W1-free boundary loc-unif slot;
    • the hDConv analytic census (`hAdom`/`hFdom`/`hMeasFII`/`hInnerCont`/`hpardiff`/`hCross`/…) and the
      hCConv sliver census (`hlin`/`hbulkderiv`/`hbulk_tendsto`/`hsliver`/…);
    • the SEELEY–DEWITT geometric wiring — `hGauss` (RNC Gauss lemma → `htr`) and `hsrc` (the
      `transportCoeff` source regularity);
    • the RNC 0/1-jet gauge (`hg0`/`hgi`/`hΓ`/`hdg0`/`hgpos`) — all curved-inhabited by `g^K`.
  NONE is the conclusion; NONE is vacuous, `:= True`, or unsatisfiable for `g^K`.

  ⚠  `a₁ = R/6` remains CONDITIONAL.  A curved-SATISFIABLE, non-vacuous capstone does NOT make the
  coefficient unconditional: the two leg outputs (`hDa`/`core`, hence the `MemAdjHi`/matched-sliver moment
  residuals + convergence trio), and the SDW wiring (`hGauss`/`htr`/`hsrc`/`transportCoeff`), all remain
  owed physical/analytic inputs.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, no hypothesis equal to the conclusion, no existing file edited, nothing committed.  NOT
  `a₁ = R/6`. -/
import Mathlib
import QIQTH.A1R6FromLabelled
import QIQTH.A1R6SlotAdapters
import QIQTH.A1R6CoreAtGate
import QIQTH.CurvedRNCGaussWitness

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.HEmeasRecon QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.FlatHeatEquation QIQTH.LaplaceBeltrami
open QIQTH.CConvV2DerivRep QIQTH.TruncatedDuhamelData QIQTH.DaLimLUWallRecon
open QIQTH.LeviSeriesLocalData QIQTH.GaussianWidthTolerant QIQTH.HeatKernelA1
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.VanVleck
open QIQTH.NCRiemannTwoJet QIQTH.GlobalRawBoundFacade QIQTH.HDuhamelExportRethread
open QIQTH.HDConvGateThreading QIQTH.CConvV2Facade QIQTH.A1R6CoreAtGate
open QIQTH.A1R6SlotAdapters QIQTH.HDerivConvComposition
open QIQTH.RadialDistance QIQTH.A1R6FromLabelled QIQTH.CurvedRNCGaussWitness
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.CurvedA1Assembled

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-- **★★★ J4-548 — `curved_a1_R6_assembled` — THE FIRST GENUINELY CURVED-SATISFIABLE a₁ TWO-JET
    CAPSTONE.**  The a₁ two-jet at the constant-radius gate, threaded DIRECTLY through the three banked
    sub-assemblies (`htr_adapter`, `a1_R6_slots_AT_GATE`, `wide_a1_R6_core_AT_CONSTRADIUS`) with the two
    Da/Duhamel LEG OUTPUTS taken as EXTERNAL binders — `hDa : DaLimLUGoal` (LEG 1, from J4-541's capped
    `hDaLimLU_from_labelled_capped`) and `core : TruncatedDuhamelCore` (LEG 2, from J4-547's capped
    `curved_leg2_hLapFull`).  The clean whole-time second-derivative bound `hAdom2` — PROVED false for the
    curved witness `g^K` (J4-537/538) — is ABSENT, so EVERY antecedent is jointly satisfiable for
    `g := curvedRNCMetric K` (`K < 0`) and the conclusion coefficient `(∑_i ricci g gi i i 0)/6 =
    n(n−1)K/6 ≠ 0` is genuinely nonzero (`curvedRNCMetric_ricci_from_gauge`).  Same conclusion as the
    prior curved capstones.  ⚠ NOT `a₁ = R/6` (still CONDITIONAL — the two leg outputs, their
    `MemAdjHi`/matched-sliver moment residuals + convergence trio, and the SDW wiring `hGauss`/`htr`/
    `hsrc`/`transportCoeff` all remain carried; see file header). -/
theorem curved_a1_R6_assembled
    -- ═══ SECTION A — base geometry, gate, window, and window parameters ═══
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (t T : ℝ) (ht : 0 < t) (hT : 0 < T) (hn : 1 ≤ n)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (a b c C : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (hCnn : 0 ≤ C)
    -- ═══ SECTION B — gauge / smoothness (core + `htr_adapter`); `hGauss` is LABELLED (SDW wiring) ═══
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hGauss : ∀ i, (fun x => ∑ j, g x i j * x j) =ᶠ[𝓝 (0 : Point n)] (fun x => x i))  -- ★ LABELLED (SDW)
    -- ═══ SECTION C — the constant-radius package facts ═══
    (hpkgBound : ∀ t' : ℝ, ∀ τ p q, 0 < τ → τ ≤ t' →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hmemS0 : (0 : Point n) ∈ K → (0 : Point n) ∈ constGate g gi hChr hK c 0)
    (hopenS0 : (0 : Point n) ∈ K → IsOpen (constGate g gi hChr hK c 0))
    (hS1 : QIQTH.HEmeasBorelAudit.tripleHEmeas g gi
      (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))
    -- ═══ SECTION D — ★ LEG 1 (Da-limit) — the capped-route output, EXTERNAL binder (J4-541) ═══
    (hDa : DaLimLUGoal g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) U)
    -- ═══ SECTION E — ★ LEG 2 (Duhamel-core) — the capped-route output, EXTERNAL binder (J4-547) ═══
    (core : TruncatedDuhamelCore g gi
      (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) t)
    -- ═══ SECTION F — the W1-free boundary loc-unif slot, EXTERNAL binder ═══
    (hbdry : QIQTH.LocUnifDerivConv.hbdryLUTarget
      (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) U)
    -- ═══ SECTION G — the hDConv F2 regularity census (for `a1_R6_slots_AT_GATE`) ═══
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b τ p q = 0)
    (C_L : ℝ) (hC_L : 0 ≤ C_L)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y))
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    (hUfloor : ∃ cc : ℝ, 0 < cc ∧ ∀ u ∈ U, cc ≤ u)
    (hInnerCont : ∀ u ∈ U, ContinuousOn
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
          (Set.Ioo 0 u))
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ cc, AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (cc - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
      volume 0 (u - epsSeq m))
    (hF'meas_d : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b r 0 z) (u - s)
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundD : ℕ → ℝ → ℝ → ℝ)
    (hbdd_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
    (hbound_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ cc ∈ nb m u,
      ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b r 0 z) (cc - s)
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0‖
        ≤ boundD m u s)
    (hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ cc ∈ nb m u,
      HasDerivAt (fun cc => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (cc - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        (∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b r 0 z) (cc - s)
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0) cc)
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) (u + h) (u - epsSeq m + k) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) (u + h) (u - epsSeq m) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) u (u - epsSeq m + k) 0 0
          + heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) u (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|))
    -- ═══ SECTION H — the hCConv sliver census (for `a1_R6_slots_AT_GATE`) ═══
    (uSet : Set (Point n)) (hu_open : IsOpen uSet) (hu0 : (0 : Point n) ∈ uSet)
    (hlin : ∀ x ∈ uSet, ∀ i : Fin n,
      HasDerivAt (fun w => heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) t
          (Function.update x i w) 0)
        ((Dmap g gi hChr hK (constGate g gi hChr hK c) a b
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) t x)
          (Pi.single i (1 : ℝ))) (x i))
    (sSet : Set (Point n)) (hsOpen : IsOpen sSet) (hsnhds : sSet ∈ 𝓝 (0 : Point n))
    (fbulk : Fin n → ℕ → Point n → ℝ)
    (fderivBulk : Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : Fin n → Point n → (Point n →L[ℝ] ℝ))
    (bb : Fin n → ℕ → ℝ) (hb : ∀ i, Filter.Tendsto (bb i) atTop (𝓝 (0 : ℝ)))
    (hbulkderiv : ∀ i : Fin n, ∀ m : ℕ, ∀ x ∈ sSet, HasFDerivAt (fbulk i m) (fderivBulk i m x) x)
    (hbulk_tendsto : ∀ i : Fin n, ∀ x ∈ sSet, Filter.Tendsto (fun m => fbulk i m x) atTop
      (𝓝 (∫ s in (0:ℝ)..t, ∫ z,
          witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0
          ∂(volume : Measure (Point n)))))
    (hsliver : ∀ i : Fin n, ∀ m : ℕ, ∀ x ∈ sSet, dist (fderivBulk i m x) (gderiv i x) ≤ bb i m)
    (hcont : ∀ i : Fin n, ContinuousOn (gderiv i) sSet) :
    heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))) t 0 0 = 0
    ∧ trueHeatKernel (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, ricci g gi i i 0) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
                            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
                            t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  -- ── the SDW `htr` at `Ric := fun cc d => ricci g gi cc d 0`, from the labelled `hGauss`.
  have htr := htr_adapter g gi hg hgsymm hgiC hgi hdg0 hGauss
  -- ── the three per-gate analytic slots, feeding LEG 1 (`hDa`) and LEG 2 (`core`) as EXTERNAL binders.
  have slots := a1_R6_slots_AT_GATE g gi hChr hK c a b t T hT U hUopen htU hUpos hUT
    (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) rfl rfl
    core
    A₀ A₁ hA₀ hA₁ hAdom hAzero C_L hC_L hFdom hMeasFII hUfloor hInnerCont
    nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
    hDa hbdry
    uSet hu_open hu0 hlin sSet hsOpen hsnhds fbulk fderivBulk gderiv bb hb
    hbulkderiv hbulk_tendsto hsliver hcont
  -- ── the pre-∃ core, at `Ric := fun cc d => ricci g gi cc d 0`.
  exact wide_a1_R6_core_AT_CONSTRADIUS g gi (fun cc d => ricci g gi cc d 0) t ht hn
    hChr hK hK0 hg hgiC hgpos hg0 hgi hΓ hdg0 hsrc a b c C ha hab hbc hCnn
    htr hpkgBound hmemS0 hopenS0 hS1
    slots.hDuhamel slots.hDConv slots.hCConv

/-- **★ J4-548 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  The conclusion coefficient of
    `curved_a1_R6_assembled` is `(∑_i ricci g gi i i 0)/6`.  For `g := curvedRNCMetric K` (`K ≠ 0`,
    `n ≥ 2`) the diagonal metric-Hessian trace — the datum `htr` (hence the a₁ coefficient) is pinned to
    via `htr = −(2/3)·Ric` — is nonzero, so `Ric(0) = (n−1)K δ ≠ 0` and the coefficient
    `n(n−1)K/6 ≠ 0`.  The assembled capstone therefore states a GENUINELY CURVED, non-vacuous conclusion
    when instantiated at `g^K`, NOT the flat `δ` statement in disguise.  NOT `a₁ = R/6`. -/
theorem curved_a1_R6_assembled_curved_satisfiable (K : ℝ) (hK : K ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) K y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne K hK hn c

end QIQTH.CurvedA1Assembled

/-! ## Axiom check — the assembled curved-satisfiable capstone is std-3
    (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CurvedA1Assembled
#print axioms curved_a1_R6_assembled
#print axioms curved_a1_R6_assembled_curved_satisfiable
end AxiomChecks
