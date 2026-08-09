/-
  HAdom2capGrounding — J4-461: GROUND `hAdom2cap`, THE LAST BLOCK-B GENUINE CARRY.

  `HInterGrounding.v2Census_phase3` (J4-460) grounded `hInter`, leaving `hAdom2cap` — the clean
  second-`x`-derivative Gaussian cap — as the SOLE remaining block-B genuine carry.  This brick attacks
  `hAdom2cap`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE GATE  (which supplier + the bridge, before building).

  DEMANDED SHAPE (verbatim from `WallAThreading.v2Census_phase2` / `HInterGrounding.v2Census_phase3`,
  the `hAdom2cap` binder):
      `hAdom2cap : ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,`
      `    |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA2c m · gaussDdim (wA2 · τ) (0 − z)`.
  READING OF THE SHAPE:
    • GAUSSIAN-SHAPED cap `CA2c m · gaussDdim (wA2·τ) (0−z)` — a Gaussian envelope, NOT a constant cap;
    • PER-`m` constant: `CA2c : ℕ → ℝ`, and the cap uses `CA2c m` (constant chosen AFTER `m`);
    • the range `epsSeq m ≤ τ ≤ T` is LOWER-CAPPED (bounded below by `εₘ`), never `τ → 0`;
    • the kernel is `witnessSecondXDeriv` (the second BASE-`x`-derivative), width `wA2·τ`, arg `0 − z`.

  ── CANDIDATE SUPPLIER 1 — `CappedAdom2Audit.hAdom2_capped_family_of_crude` (the per-`m` capped family).
     OUTPUT SHAPE (`CappedAdom2Audit.lean` lines 110-121):
       `∀ (m) (i) (τ), epsSeq m ≤ τ → τ ≤ T → ∀ z,`
       `    |witnessSecondXDeriv … i τ z| ≤ (Ccrude · (epsSeq m)⁻¹) · gaussDdim (wA2·τ) (0−z)`.
     This is the demanded shape VERBATIM under `CA2c := fun m => Ccrude · (epsSeq m)⁻¹`:  same kernel
     `witnessSecondXDeriv`, same Gaussian factor `gaussDdim (wA2·τ) (0−z)` (SAME width `wA2` — no
     width-arithmetic conversion needed), same lower-capped range `epsSeq m ≤ τ ≤ T`, same quantifier
     order, per-`m` constant.  Its ONE input is the CRUDE `τ⁻¹` envelope
       `hcrude : ∀ i τ, 0 < τ → τ ≤ T → ∀ z, |witnessSecondXDeriv … i τ z| ≤ Ccrude·τ⁻¹·gaussDdim (wA2·τ) (0−z)`
     — the banked wide crude bound (`WideWitnessAmplitude.WideAmplitudePackage.hSecond`, lifted to ALL
     `z` by `FixedGateDichotomy.second_global_of_package`; the clean `τ⁻¹` shape).  ✔ MATCH.

  ── CANDIDATE SUPPLIER 2 — `SecondDerivEnvelope.witnessFieldDeriv2_envelope_coercive` (coercive E2).
     OUTPUT `|witnessFieldDeriv2 … i τ p z| ≤ (√2)ⁿ · gaussDdim (2·τ) z · (Bs2·Ba + 2·Bs1·Bd + Bdd)`.
     REJECTED as the `hAdom2cap` supplier: (a) WRONG KERNEL — it bounds `witnessFieldDeriv2` (the second
     FIELD-derivative), not `witnessSecondXDeriv` (the second BASE-`x`-derivative); (b) it needs
     per-point ON-GATE jet data (`hz`, `hSopen`, `hp`, `P`/`Q`, coercivity `hco`), so it is NOT a clean
     pointwise bound over ALL `z`; (c) WIDTH `2·τ` (would force `wA2 := 2`, and there is still the
     `1/τ²`/`1/τ` blow-up buried inside `Bs2`/`Bs1`, so it is NOT a `τ`-lower-capped clean cap).  It is
     the E2 gate envelope, a DIFFERENT object.

  m-UNIFORMITY STATUS.  The demanded `hAdom2cap` is PER-`m` (`CA2c : ℕ → ℝ`, cap `CA2c m`).  The per-`m`
  capped supplier is therefore ADMISSIBLE precisely because `hAdom2cap` is per-`m` — the `τ`-uniform
  whole-time `hAdom2` (a SINGLE `CA2` outside `∀ m`) is GENERALLY FALSE (the `τ⁻¹` blow-up at `z = 0` as
  `τ → 0`; see `CappedAdom2Audit` verdict), but the census only ever consumes the per-`m` capped form.

  WIDTH MISMATCH.  NONE.  The crude bank and the demanded cap share the SAME width `wA2·τ`; the capping
  lemma preserves width (`hAdom2_capped_of_crude` does no width-monotonicity algebra).  So the width-2τ
  machinery (`gaussDdim_zero_antitone` etc.) is NOT invoked.

  VERDICT.  `hAdom2cap` is GROUNDED (shape-bridged), NOT walled.  Supplier =
  `CappedAdom2Audit.hAdom2_capped_family_of_crude`; bridge = the banked crude `τ⁻¹` envelope `hcrude`
  (`WideAmplitudePackage.hSecond` → `second_global_of_package`), with `CA2c := fun m => Ccrude·(epsSeq
  m)⁻¹`.  It is the EXACT hFdomW-pattern shape bridge (the clean per-`m` capped Gaussian cap is not
  directly banked, but the crude `τ⁻¹` envelope IS, and the capping lemma bridges it).  ⟹ block-B's
  last genuine carry collapses onto the crude ENVELOPE input.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It grounds
  the last block-B genuine carry by exhibiting the banked capping lemma that produces it from the crude
  envelope; `a₁ = R/6` remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack AND on
  the surviving labelled envelope/box/scaffold inputs (the crude envelope `hcrude`, the `LeviSeriesLocalData`
  package `data`, the two box families, `hUT`/`hεU`).  Each is genuine, satisfiable, non-vacuous, strictly
  lower-level than its target, and never the conclusion.  NO `sorry` (header prose excepted), NO
  `:= True`, NO new axioms, NO existing file edited, nothing wired into `AxiomAudit`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HInterGrounding
import QIQTH.CappedAdom2Audit

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.LeviSeries QIQTH.ExpMap QIQTH.HeatKernelA1
open QIQTH.DuhamelCoreThreaded QIQTH.PerUCensusTuple QIQTH.W2Finish
open QIQTH.HDuhamelExportRethread QIQTH.TruncatedDuhamelData
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.CappedAdom2Audit
open QIQTH.V2CensusInstantiation QIQTH.WallAInstantiation QIQTH.WallAThreading
open QIQTH.HInterGrounding
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.HAdom2capGrounding

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★★★ `hAdom2cap_grounded` — the per-`m` capped Gaussian cap from the crude `τ⁻¹` envelope.
    ############################################################################### -/

/-- **★★★ `hAdom2cap_grounded`.**  THE `hAdom2cap` MEMBER, GROUNDED.  From the banked crude `τ⁻¹`
    second-`x`-derivative Gaussian envelope
      `hcrude : ∀ i τ, 0 < τ → τ ≤ T → ∀ z, |witnessSecondXDeriv … i τ z| ≤ Ccrude·τ⁻¹·gaussDdim (wA2·τ) (0−z)`
    (the wide crude bound `WideAmplitudePackage.hSecond` lifted to all `z` by
    `FixedGateDichotomy.second_global_of_package`), the capping lemma
    `CappedAdom2Audit.hAdom2_capped_family_of_crude` produces the EXACT demanded per-`m` capped Gaussian
    cap with `CA2c := fun m => Ccrude·(epsSeq m)⁻¹` (width `wA2` unchanged) — the block-B `hAdom2cap`
    member verbatim — together with its non-negativity.  Pure shape bridge (the hFdomW pattern).  ⚠ NOT
    `a₁ = R/6`. -/
theorem hAdom2cap_grounded (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (T Ccrude wA2 : ℝ) (hCcrude : 0 ≤ Ccrude)
    (hcrude : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z|
          ≤ Ccrude * τ⁻¹ * gaussDdim (wA2 * τ) (0 - z)) :
    (∀ m : ℕ, 0 ≤ Ccrude * (epsSeq m)⁻¹) ∧
    (∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z|
          ≤ (Ccrude * (epsSeq m)⁻¹) * gaussDdim (wA2 * τ) (0 - z)) :=
  ⟨fun m => mul_nonneg hCcrude (inv_nonneg.mpr (epsSeq_pos m).le),
   hAdom2_capped_family_of_crude g gi hChr hK S a b T Ccrude wA2 hCcrude hcrude⟩

/-! ###############################################################################
    ### ★★★★ `v2Census_phase4` — `v2Census_phase3` with `hAdom2cap` GROUNDED from the crude envelope.
    ###                          BLOCK-B: ZERO GENUINE ATOMS REMAIN.
    ############################################################################### -/

/-- **★★★★ `v2Census_phase4`.**  THE hAdom2cap-GROUNDED TERMINAL CROSS-CHECK.  It is `v2Census_phase3`
    with the LAST block-B genuine carry `hAdom2cap` REMOVED from the carried surface and supplied
    INTERNALLY from `hAdom2cap_grounded` — which consumes the banked crude `τ⁻¹` second-`x`-derivative
    Gaussian ENVELOPE `hcrude` (`WideAmplitudePackage.hSecond` → `second_global_of_package`) and the
    capping lemma.  So its binder list is `v2Census_phase3`'s MINUS `{CA2c, hCA2c, hAdom2cap}` PLUS the
    crude envelope `{Ccrude, hCcrude, hcrude}`.  The conclusion is the SAME v3-core
    `TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t`.

    THAT THIS TYPECHECKS certifies `hAdom2cap` is no longer an independent block-B carry — it collapses
    onto the crude Gaussian envelope input, leaving the wall-A block-B surface with ZERO genuine atoms:
    only the satisfiable envelope/box inputs `{hcrude, data, hSecBoxes, hBBoxes}` and the group-(A)
    scaffolding `{hUT, hεU}`.  ⚠ Pure grounding at the domination leg; closes NOTHING deeper.  Every
    remaining input is satisfiable, non-vacuous, strictly lower-level, and NONE is `a₁ = R/6`. -/
theorem v2Census_phase4 (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ)
    (hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    (t T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUT : ∀ u ∈ U, u ≤ T) (hn : 1 ≤ n)
    (hBoundaryLim : Tendsto
        (fun m => BoundaryTrunc (vanVleckGatedWitness g gi hChr hK S a b) F m t) atTop
        (𝓝 (F t 0 0)))
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
    (hUsub : U ⊆ Set.Icc ta tb)
    (τc wA2 : ℝ)
    (hwA2 : 0 < wA2)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (Cdata : ℝ)
    (data : LeviSeriesLocalData
        (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) Cdata T)
    (hSecBoxes : ∀ i : Fin n, ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n => witnessSecondXDeriv g gi hChr hK S a b i p.1 p.2)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hBBoxes : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    -- ★ the crude `τ⁻¹` ENVELOPE replacing the `hAdom2cap` carry (`WideAmplitudePackage.hSecond` route):
    (Ccrude : ℝ) (hCcrude : 0 ≤ Ccrude)
    (hcrude : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z|
          ≤ Ccrude * τ⁻¹ * gaussDdim (wA2 * τ) (0 - z))
    (Lc Bcomp Q Sconst : ℝ) (hLc : 0 ≤ Lc) (hBcomp : 0 ≤ Bcomp) (hQ : 0 ≤ Q) (hSconst : 0 ≤ Sconst)
    (hslot : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i τ z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ (2 * Lc * (15 / 2 * (n : ℝ)) + Bcomp + Q) * τ ^ (-(1 : ℝ) / 2) + Sconst)
    (hcap : ∀ (m : ℕ), ∀ u ∈ U, ∀ s ∈ Set.Ioo (u - epsSeq m) u, u - s ≤ τc)
    (hEndpoint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - u) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) u z 0 = 0)
    (hInnerData : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
        ∃ (znb : Set ℝ) (bnd : Point n → ℝ),
          znb ∈ 𝓝 w ∧
          (∀ w' : ℝ, AEStronglyMeasurable
            (fun z => witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume) ∧
          Integrable
            (fun z => witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume ∧
          AEStronglyMeasurable
            (fun z => witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume ∧
          Integrable bnd volume ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb,
            ‖witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ bnd z) ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb,
            HasDerivAt (fun w' => witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
              (witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) w'))
    (nbP : ℝ → Set (Point n)) (hnbP_open : ∀ u ∈ U, IsOpen (nbP u))
    (hnbP0 : ∀ u ∈ U, (0 : Point n) ∈ nbP u)
    (hProvP : ∀ u ∈ U, ∀ x ∈ nbP u, ∀ i : Fin n,
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
    (hGintP : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 u)
    (hbulkderiv : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK S a b u i m)
          (fderivBulk u i m x) x)
    (hsliver : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        dist (fderivBulk u i m x) (gderiv u i x)
          ≤ (C₀ u i + C₁ u i) * (2 * Real.sqrt (epsSeq m)) + C₂ u i * epsSeq m)
    (hcont : ∀ u ∈ U, ∀ i : Fin n, ContinuousOn (gderiv u i) (Set.univ : Set (Point n)))
    (hfrozen_pd1 : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ),
        (fun y => pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
            (u - epsSeq m) x 0) i y)
          =ᶠ[𝓝 (0 : Point n)]
          QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK S a b u i m) :
    TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t := by
  -- ★ GROUND `hAdom2cap` from the crude `τ⁻¹` envelope via the capping lemma.
  obtain ⟨hCA2c, hAdom2cap⟩ := hAdom2cap_grounded g gi hChr hK S a b T Ccrude wA2 hCcrude hcrude
  -- re-supply the `v2Census_phase3` surface with `hAdom2cap` (and its `CA2c`) now internal.
  exact QIQTH.HInterGrounding.v2Census_phase3 g gi hChr hK S a b F hFeq
    t T hT U hUopen htU hUT hn hBoundaryLim hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas
    bnd hbdd hbound hdiff D0 D1 hD0 hD1 hbnd E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hEdom hFdom hIlo hIhi
    hEcomb A₀ A₁ hA₀ hA₁ hAdom hAzero hMeasFII hUfloor hInnerCont
    nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
    ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd
    hWDom hmass hmassone hmod hsup hUsub
    τc wA2 (fun m => Ccrude * (epsSeq m)⁻¹) hwA2 hCA2c hεU Cdata data hSecBoxes hBBoxes
    hAdom2cap
    Lc Bcomp Q Sconst hLc hBcomp hQ hSconst hslot hcap hEndpoint
    hInnerData
    nbP hnbP_open hnbP0 hProvP fderivBulk gderiv C₀ C₁ C₂ hGintP hbulkderiv hsliver hcont hfrozen_pd1

/-! ###############################################################################
    ### `hAdom2capGrounded_core` — the block-B-closed terminal cross-check (alias of `v2Census_phase4`).
    ############################################################################### -/

/-- **★★★★★ `hAdom2capGrounded_core`.**  THE BLOCK-B-CLOSED TERMINAL CROSS-CHECK, made machine-checked:
    `v2Census_phase4` under its audit name.  Its statement — consuming the group-(1)-(4) carry surface
    with BOTH block-B genuine carries now grounded (`hInter` in J4-460, `hAdom2cap` here from the crude
    envelope) and producing the v3-core conclusion — certifies the wall-A block-B carried surface has
    closed to ZERO genuine atoms: only satisfiable envelope/box/scaffold inputs remain.  ⚠ NOT
    `a₁ = R/6`. -/
def hAdom2capGrounded_core := @v2Census_phase4

end QIQTH.HAdom2capGrounding

/-! ## THE BLOCK-B CLOSURE LEDGER — the wall-A leg rests on envelope/box/scaffold inputs ONLY.

  With `v2Census_phase4` / `hAdom2capGrounded_core` grounding `hAdom2cap` (from the crude `τ⁻¹`
  envelope via the capping lemma) on top of J4-460's `hInter` grounding, the v3-core WALL-A BLOCK-B
  conditional surface is now, in full:

    surface member                       verdict              satisfied by
    ──────────────────────────────────   ──────────────────   ─────────────────────────────────────────
    `hInter`  (grounded J4-460)          NO LONGER A CARRY    `HInterGrounding.hInter_grounded` — the
                                                              banked W2 diff-under-∫ engine
                                                              `witness_MemInterchange`.
    `hAdom2cap`  (grounded HERE)         NO LONGER A CARRY    `hAdom2cap_grounded` — the capping lemma
                                                              `hAdom2_capped_family_of_crude` on the
                                                              crude envelope `hcrude`.
    `hcrude`                             SATISFIABLE INPUT    the crude `τ⁻¹` second-`x`-derivative
      (`≤ Ccrude·τ⁻¹·G_{wA2·τ}`)         (ENVELOPE)           Gaussian bound, banked as
                                                              `WideAmplitudePackage.hSecond` → all-`z`
                                                              `FixedGateDichotomy.second_global_of_package`.
    `data`                               SATISFIABLE INPUT    the `LeviSeriesLocalData` envelope package;
      (`LeviSeriesLocalData … Cdata T`)   (ENVELOPE)           ⇒ `hFdomW` (`wF:=2`).
    `hSecBoxes`, `hBBoxes`               SATISFIABLE INPUT    the two positive-time-compact box families;
                                          (BOX)                ⇒ `hSecCont`/`hBcont`/`hmeas2Lo`.
    `hUT`, `hεU`                         GROUP-(A) SCAFFOLD   domain floor/ceiling (already present).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ★★★  BLOCK-B FULLY GROUNDED.  The wall-A leg of the v3 core rests on satisfiable
  ENVELOPE / BOX / SCAFFOLD inputs ONLY — ZERO genuine atoms remain.  Both former block-B genuine
  carries (`hInter`, `hAdom2cap`) are grounded to banked suppliers; the residual surface is
  `{hcrude, data, hSecBoxes, hBBoxes}` (envelope/box) + `{hUT, hεU}` (scaffold), each of which is a
  pointwise Gaussian domination / joint-continuity box / domain bound — NOT a diff-under-∫ interchange
  atom or an unprovable uniform cap.  ⚠ NEVER `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════

  ── WHAT MOVED.  `hAdom2cap` is no longer an independent block-B carry — it is supplied internally by
  `hAdom2cap_grounded` from the crude envelope `hcrude`, with `CA2c := fun m => Ccrude·(epsSeq m)⁻¹`
  (width `wA2` unchanged, no width-arithmetic conversion).  This is the EXACT hFdomW-pattern shape
  bridge: the clean per-`m` capped Gaussian cap is not directly banked, but the crude `τ⁻¹` envelope IS.

  ⚠  THIS IS **NOT** `a₁ = R/6`, AND MAKES NO CLAIM OF UNCONDITIONALITY.  `a₁ = R/6` remains CONDITIONAL
  on: (i) the enumerated envelope/box/scaffold inputs themselves (`hcrude`, `data`, the box families are
  INPUTS here, not theorems), and (ii) the DEEP convergence-trio + geometric-wiring content that lives
  OUTSIDE block B (true-kernel existence / Levi convergence / Seeley-DeWitt geometric identification),
  which is NEVER claimed closed.  Closing block-B to zero genuine atoms closes NOTHING deeper.
-/

section AxiomChecks
open QIQTH.HAdom2capGrounding
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms hAdom2cap_grounded
#print axioms v2Census_phase4
#print axioms hAdom2capGrounded_core
end AxiomChecks
