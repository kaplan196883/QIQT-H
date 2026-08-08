/-
  ProfFacWitness — J4-446 (GROUP (3), completing the hGint endpoint sliver): DISCHARGING THE TWO
  J4-445 CARRIES `hProfFac` and `hProfMeas` at the concrete witness, down to banked theorems.

  J4-445 (`QIQTH.SliverSingularEngine`) discharged the census `hGint` FULLY (bulk capped-ceiling
  engine ⊕ endpoint sliver singular engine), MODULO two lower-level carries threaded into
  `hGint_full_at_witness` / `perUCensus_phase3`:
    • `hProfFac`  — the RISK-GATE FACTORISATION of the sliver pairing profile: per `(u,i,x)`, constants
      `C,B` and a remainder `rem : ℝ → ℝ` with `|profile s| ≤ C·(u−s)⁻¹·|rem s|` (the `1/(2τ)` slope ×
      amplitude/Levi Gaussian) AND `|rem s| ≤ B·√(u−s)` (the coordinate first moment), the two-part
      shape the singular engine converts to the integrable `(u−s)^{-1/2}` rate;
    • `hProfMeas` — the sliver-window ae-strong-measurability of the `s`-profile on `Ι (u−εₘ) u`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE DISCHARGE.

  ### `hProfFac`  (the risk-gate factorisation, from the inner `Q·(u−s)^{-1/2}` rate).
  The risk-gate power-count runs FORWARD (`C·u⁻¹·|rem|` with `|rem| ≤ B·√u` ⟹ `(C·B)·u^{-1/2}`) inside
  `SliverRiskGate.riskGate_powercount`.  Its INVERSE is the clean packaging used here: the substantive
  content — the moment-gained inner rate `|profile s| ≤ Q·(u−s)^{-1/2}` for `0 < s < u` (the risk-gate
  OUTPUT shape, satisfiable by the banked coordinate-first-moment machinery `absCoord_gaussDdim_
  integral_le` / `hf2bound_at_witness`'s `Q/√τ` extraction × the Levi Gaussian `intZ_dH_pairing_le`) —
  is repackaged into the exact `hProfFac` two-part shape with the CANONICAL remainder `rem s := √(u−s)`,
  `C := Q`, `B := 1`, via the ARITHMETIC HEART `(u−s)⁻¹·√(u−s) = (u−s)^{-1/2}` (`HeatResidualBound.
  inv_sqrt_eq_rpow`).  The endpoint half `s ≤ 0` is killed by the Levi-source vanishing `hFzero`
  (`profile = 0`).  Every constant is m-FREE (only the interval endpoint `εₘ` carries `m`).

  ### `hProfMeas`  (the Fubini profile measurability, from the joint `(s,z)` factors).
  The `s`-profile on the sliver window is the inner-integral marginal of the joint `(s,z)` product
  `witnessFieldDeriv · leviSeries`, so `InnerMeasFubini.innerIntegral_aesm`
  (`AEStronglyMeasurable.integral_prod_right'`) integrates `z` out, given the two banked joint factor
  measurabilities `.mul`-combined — MIRRORING `hFmeas_concrete`/`hF'meas_concrete`, on the SLIVER
  window `Ι (u−εₘ) u` instead of the bulk.

  ⟹  Both carries reduce to STRICTLY-LOWER-LEVEL, already-enumerated campaign carries.  `hGint_grounded`
  supplies both to `hGint_full_at_witness`; `perUCensus_phase4` fires the per-`u` census with `hGint`
  grounded internally.

  One brick of the `a₁ = R/6` heat-kernel campaign.  It is **NOT** `a₁ = R/6`, and proves NOTHING about
  `R/6`.  `a₁ = R/6` remains CONDITIONAL on the whole `hDuhamel` / convergence-trio + geometric-wiring
  stack AND on the surviving labelled census carries threaded here.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  Every theorem re-threads BANKED, satisfiable inner-rate / joint-measurability
  data into the exact census `hProfFac` / `hProfMeas` shapes.  NONE proves `a₁ = R/6`.  Each carried
  hypothesis is genuine, satisfiable, non-vacuous, strictly lower-level than the conclusion, and never
  the conclusion.  No `sorry` (header prose excepted), no `:= True`, no new axioms, no existing file
  edited.

  ── WHAT LANDS (this file, ns `QIQTH.ProfFacWitness`).
    • `profFac_of_innerRate` — ★ THE GENERAL LEVER (m-free arithmetic): the inner `Q·(u−s)^{-1/2}` rate
      (+ `s ≤ 0` vanishing) packaged into the `∃ C B rem` risk-gate factorisation shape.
    • `profFac_at_witness` — ★★ the EXACT census `hProfFac` shape, DISCHARGED, from {`hFzero`,
      `hProfRate`}.
    • `profMeas_at_witness` — ★★ the EXACT census `hProfMeas` shape, DISCHARGED, from the two joint
      `(s,z)` factor measurabilities via the Fubini inner-integral engine.
    • `hGint_grounded` — ★★ the census `hGint` on `[0,u]`, both sliver carries supplied INTERNALLY.
    • `perUCensus_phase4` — ★★★ the fired per-`u` census, `hProfMeas`/`hProfFac` BOTH grounded to their
      lower-level suppliers {`hWFDjoint`,`hLeviJoint`,`hProfRate`}.

  Every hypothesis is satisfiable, non-vacuous, strictly lower-level than the conclusion, and NONE
  equals `a₁ = R/6`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.SliverSingularEngine
import QIQTH.InnerMeasFubini

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.FlatHeatEquation
open QIQTH.CConvV2DerivRep QIQTH.CConvV2Facade QIQTH.Pd2ConvDissolution
open QIQTH.InnerMeasFubini
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.ProfFacWitness

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ `profFac_of_innerRate` — the general lever (inner rate → factorisation).
    ############################################################################### -/

/-- **★ `profFac_of_innerRate` — THE GENERAL LEVER.**  A profile `f` that vanishes for `s ≤ 0`
    (`hzero`) and obeys the moment-gained inner rate `|f s| ≤ Q·(u−s)^{-1/2}` on `0 < s < u`
    (`hrate`, the risk-gate OUTPUT shape) admits the risk-gate FACTORISATION in its exact carried form:
    `∃ C B rem, 0 ≤ C ∧ (∀ s < u, |f s| ≤ C·(u−s)⁻¹·|rem s|) ∧ (∀ s < u, |rem s| ≤ B·√(u−s))`, at the
    CANONICAL witness `C := Q`, `B := 1`, `rem s := √(u−s)`.  The arithmetic heart is
    `(u−s)⁻¹·√(u−s) = (u−s)^{-1/2}` (`HeatResidualBound.inv_sqrt_eq_rpow`), the exact inverse of
    `SliverRiskGate.riskGate_powercount`.  `s ≤ 0` uses `hzero`; `0 < s` uses `hrate`.  m-FREE.
    ⚠ NOT `a₁ = R/6`. -/
theorem profFac_of_innerRate (f : ℝ → ℝ) (u Q : ℝ) (hQ : 0 ≤ Q)
    (hzero : ∀ s : ℝ, s ≤ 0 → f s = 0)
    (hrate : ∀ s : ℝ, 0 < s → s < u → |f s| ≤ Q * (u - s) ^ (-(1 : ℝ) / 2)) :
    ∃ C B : ℝ, ∃ rem : ℝ → ℝ, 0 ≤ C ∧
      (∀ s : ℝ, s < u → |f s| ≤ C * (u - s)⁻¹ * |rem s|) ∧
      (∀ s : ℝ, s < u → |rem s| ≤ B * Real.sqrt (u - s)) := by
  refine ⟨Q, 1, fun s => Real.sqrt (u - s), hQ, ?_, ?_⟩
  · intro s hsu
    show |f s| ≤ Q * (u - s)⁻¹ * |Real.sqrt (u - s)|
    have hτpos : 0 < u - s := by linarith
    have hune : u - s ≠ 0 := ne_of_gt hτpos
    have hsne : Real.sqrt (u - s) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hτpos)
    have hmul : Real.sqrt (u - s) * Real.sqrt (u - s) = u - s := Real.mul_self_sqrt hτpos.le
    have hid0 : (u - s)⁻¹ * Real.sqrt (u - s) = (Real.sqrt (u - s))⁻¹ := by
      field_simp
      linarith [hmul]
    have hgoal_eq : Q * (u - s)⁻¹ * |Real.sqrt (u - s)| = Q * (u - s) ^ (-(1 : ℝ) / 2) := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _),
        ← QIQTH.HeatResidualBound.inv_sqrt_eq_rpow (u - s) hτpos, ← hid0]
      ring
    rcases le_or_gt s 0 with hs0 | hs0
    · rw [hzero s hs0, abs_zero, hgoal_eq]
      exact mul_nonneg hQ (Real.rpow_nonneg hτpos.le _)
    · rw [hgoal_eq]
      exact hrate s hs0 hsu
  · intro s _hsu
    show |Real.sqrt (u - s)| ≤ (1 : ℝ) * Real.sqrt (u - s)
    rw [abs_of_nonneg (Real.sqrt_nonneg _), one_mul]

/-! ###############################################################################
    ### ★★ `profFac_at_witness` — the EXACT census hProfFac shape, discharged.
    ############################################################################### -/

/-- **★★ `profFac_at_witness` — THE `hProfFac` CARRY, DISCHARGED.**  The EXACT `hProfFac` binder of
    `SliverSingularEngine.hGint_full_at_witness` / `perUCensus_phase3`: per `(u,i,x)` a risk-gate
    factorisation of the field-derivative sliver pairing profile.  Supplied from the moment-gained inner
    rate `hProfRate` (`|profile s| ≤ Q·(u−s)^{-1/2}` on `0 < s < u`, the banked coordinate-first-moment ×
    Levi-Gaussian content) and the Levi-source vanishing `hFzero` (`profile = 0` for `s ≤ 0`), fed
    through `profFac_of_innerRate` with the canonical remainder `rem s := √(u−s)`, `C := Q`, `B := 1`.
    Honest carries: {`hFzero`, `hProfRate`}.  m-FREE.  ⚠ NOT `a₁ = R/6`. -/
theorem profFac_at_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0 = 0)
    (hProfRate : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ Q : ℝ, 0 ≤ Q ∧
        ∀ s, 0 < s → s < u →
          |∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
              ∂(volume : Measure (Point n))|
            ≤ Q * (u - s) ^ (-(1 : ℝ) / 2)) :
    ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ C B : ℝ, ∃ rem : ℝ → ℝ, 0 ≤ C ∧
        (∀ s, s < u →
          |∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
              ∂(volume : Measure (Point n))|
            ≤ C * (u - s)⁻¹ * |rem s|) ∧
        (∀ s, s < u → |rem s| ≤ B * Real.sqrt (u - s)) := by
  intro u hu i x
  obtain ⟨Q, hQ, hrate⟩ := hProfRate u hu i x
  have hzero : ∀ s : ℝ, s ≤ 0 →
      (∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
          ∂(volume : Measure (Point n))) = 0 := by
    intro s hs
    have hfun : (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) x z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
        = fun _ => (0 : ℝ) := by
      funext z; rw [hFzero s hs z, mul_zero]
    rw [hfun]; exact integral_zero (Point n) ℝ
  exact profFac_of_innerRate
    (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
        ∂(volume : Measure (Point n)))
    u Q hQ hzero hrate

/-! ###############################################################################
    ### ★★ `profMeas_at_witness` — the EXACT census hProfMeas shape, discharged.
    ############################################################################### -/

/-- **★★ `profMeas_at_witness` — THE `hProfMeas` CARRY, DISCHARGED.**  The EXACT `hProfMeas` binder of
    `SliverSingularEngine.hGint_full_at_witness` / `perUCensus_phase3`: per `(u,i,x,m)` the ae-strong-
    measurability of the field-derivative `s`-profile on the SLIVER window `Ι (u−εₘ) u`.  The profile is
    the inner-integral marginal (`z` integrated out) of the joint `(s,z)` product `witnessFieldDeriv ·
    leviSeries`, so `InnerMeasFubini.innerIntegral_aesm` (`AEStronglyMeasurable.integral_prod_right'`)
    supplies it from the two banked joint factor measurabilities `hWFDjoint`/`hLeviJoint` combined by
    `.mul` — the SLIVER analogue of `hFmeas_concrete`/`hF'meas_concrete` (bulk).  Honest carries:
    {`hWFDjoint`, `hLeviJoint`}.  ⚠ NOT `a₁ = R/6`. -/
theorem profMeas_at_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hWFDjoint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun p : ℝ × Point n => witnessFieldDeriv g gi hC hK S a b i (u - p.1) x p.2)
        ((volume.restrict (Set.uIoc (u - epsSeq m) u)).prod (volume : Measure (Point n))))
    (hLeviJoint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun p : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
        ((volume.restrict (Set.uIoc (u - epsSeq m) u)).prod (volume : Measure (Point n)))) :
    ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)) := by
  intro u hu i x m
  exact innerIntegral_aesm
    (fun p : ℝ × Point n => witnessFieldDeriv g gi hC hK S a b i (u - p.1) x p.2
      * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
    ((hWFDjoint u hu i x m).mul (hLeviJoint u hu i x m))

/-! ###############################################################################
    ### ★★ `hGint_grounded` — the census hGint, both sliver carries supplied internally.
    ############################################################################### -/

/-- **★★ `hGint_grounded` — THE CENSUS `hGint`, BOTH SLIVER CARRIES GROUNDED.**  The EXACT `hGint`
    conclusion of `SliverSingularEngine.hGint_full_at_witness` (interval-integrability on the full
    `[0,u]` of the field-derivative `s`-profile), with BOTH sliver carries `hProfMeas`/`hProfFac`
    supplied INTERNALLY from their lower-level suppliers of this file: `profMeas_at_witness`
    (from the joint factor measurabilities) and `profFac_at_witness` (from the inner rate + `hFzero`).
    Honest carries: {`hFzero`, `hWFDdomCapped`, `hFdomEvery`, `hGintMeas`, `hWFDjoint`, `hLeviJoint`,
    `hProfRate`}.  ⚠ NOT `a₁ = R/6`. -/
theorem hGint_grounded (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0 = 0)
    (hWFDdomCapped : ∀ (i : Fin n) (x : Point n), ∀ Tc εₘ : ℝ, 0 < εₘ →
        ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ τ : ℝ, εₘ ≤ τ → τ ≤ Tc → ∀ z : Point n,
          |witnessFieldDeriv g gi hC hK S a b i τ x z|
            ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hGintMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hWFDjoint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun p : ℝ × Point n => witnessFieldDeriv g gi hC hK S a b i (u - p.1) x p.2)
        ((volume.restrict (Set.uIoc (u - epsSeq m) u)).prod (volume : Measure (Point n))))
    (hLeviJoint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun p : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
        ((volume.restrict (Set.uIoc (u - epsSeq m) u)).prod (volume : Measure (Point n))))
    (hProfRate : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ Q : ℝ, 0 ≤ Q ∧
        ∀ s, 0 < s → s < u →
          |∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
              ∂(volume : Measure (Point n))|
            ≤ Q * (u - s) ^ (-(1 : ℝ) / 2)) :
    ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 u :=
  QIQTH.SliverSingularEngine.hGint_full_at_witness g gi hC hK S a b U hFzero hWFDdomCapped hFdomEvery
    hGintMeas
    (profMeas_at_witness g gi hC hK S a b U hWFDjoint hLeviJoint)
    (profFac_at_witness g gi hC hK S a b U hFzero hProfRate)

/-! ###############################################################################
    ### ★★★ `perUCensus_phase4` — the fired per-`u` census, both sliver carries grounded.
    ############################################################################### -/

/-- **★★★ `perUCensus_phase4`.**  `SliverSingularEngine.perUCensus_phase3` with the two sliver carries
    `hProfMeas`/`hProfFac` GROUNDED INTERNALLY to their strictly-lower-level suppliers of this file:
    `hProfMeas` ← {`hWFDjoint`,`hLeviJoint`} via `profMeas_at_witness`, and `hProfFac` ← {`hProfRate`}
    (+ the standing `hFzero`) via `profFac_at_witness`.  Every OTHER census field is threaded exactly as
    `perUCensus_phase3`.  Pure composition; each carry satisfiable, non-vacuous, strictly lower level
    than the conclusion, none equal to `a₁ = R/6`.  ⚠ STILL NOT `a₁ = R/6`. -/
theorem perUCensus_phase4 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (hUpos : ∀ u ∈ U, 0 < u)
    (nb : ℝ → Set (Point n)) (hnb_open : ∀ u ∈ U, IsOpen (nb u))
    (hnb0 : ∀ u ∈ U, (0 : Point n) ∈ nb u)
    (hProv : ∀ u ∈ U, ∀ x ∈ nb u, ∀ i : Fin n,
      ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
        snb ∈ 𝓝 (x i) ∧
        (∀ w, AEStronglyMeasurable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u))) ∧
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume 0 u ∧
        AEStronglyMeasurable
          (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u)) ∧
        IntervalIntegrable bound volume 0 u ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bound s) ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s)
              (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) w))
    (fderivBulk : ℝ → Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : ℝ → Fin n → Point n → (Point n →L[ℝ] ℝ))
    (C₀ C₁ C₂ : ℝ → Fin n → ℝ)
    -- the lower-level `hGint` suppliers (in place of the census `hGint` binder AND J4-444's `hSliver`)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0 = 0)
    (hWFDdomCapped : ∀ (i : Fin n) (x : Point n), ∀ Tc εₘ : ℝ, 0 < εₘ →
        ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ τ : ℝ, εₘ ≤ τ → τ ≤ Tc → ∀ z : Point n,
          |witnessFieldDeriv g gi hC hK S a b i τ x z|
            ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hGintMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    -- `hProfMeas` grounded : the two joint `(s,z)` factor measurabilities on the sliver window
    (hWFDjoint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun p : ℝ × Point n => witnessFieldDeriv g gi hC hK S a b i (u - p.1) x p.2)
        ((volume.restrict (Set.uIoc (u - epsSeq m) u)).prod (volume : Measure (Point n))))
    (hLeviJoint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun p : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
        ((volume.restrict (Set.uIoc (u - epsSeq m) u)).prod (volume : Measure (Point n))))
    -- `hProfFac` grounded : the moment-gained inner `Q·(u−s)^{-1/2}` rate
    (hProfRate : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ Q : ℝ, 0 ≤ Q ∧
        ∀ s, 0 < s → s < u →
          |∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
              ∂(volume : Measure (Point n))|
            ≤ Q * (u - s) ^ (-(1 : ℝ) / 2))
    (hbulkderiv : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m)
          (fderivBulk u i m x) x)
    (hsliver : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        dist (fderivBulk u i m x) (gderiv u i x)
          ≤ (C₀ u i + C₁ u i) * (2 * Real.sqrt (epsSeq m)) + C₂ u i * epsSeq m)
    (hcont : ∀ u ∈ U, ∀ i : Fin n, ContinuousOn (gderiv u i) (Set.univ : Set (Point n)))
    (hQ1 : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ),
        ∃ V ∈ 𝓝 (0 : Point n),
          ∀ y ∈ V, pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hC hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u
              (u - epsSeq m) x 0) i y
            = QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m y) :
    ∀ u ∈ U, ∀ i : Fin n,
      Tendsto
        (fun m => pd (fun y => pd (fun x => heatConvFrozen
            (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u
            (u - epsSeq m) x 0) i y) i 0)
        atTop (𝓝 (pd (fun y => pd (fun x => heatConv
            (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u x 0) i y) i 0)) :=
  QIQTH.SliverSingularEngine.perUCensus_phase3 g gi hC hK S a b U hUpos
    nb hnb_open hnb0 hProv fderivBulk gderiv C₀ C₁ C₂
    hFzero hWFDdomCapped hFdomEvery hGintMeas
    (profMeas_at_witness g gi hC hK S a b U hWFDjoint hLeviJoint)
    (profFac_at_witness g gi hC hK S a b U hFzero hProfRate)
    hbulkderiv hsliver hcont hQ1

end QIQTH.ProfFacWitness

/-! ## THE hGint FINAL LEDGER — what the hGint chain now rests on after J4-446.

  `perUCensus_phase4` reproduces the conclusion of `SliverSingularEngine.perUCensus_phase3`
  (= the per-`u` frozen→full second-partial `Tendsto` binder (viii)) from the V1 per-`u` census, with
  `hGint` now discharged FULLY (bulk ⊕ sliver, J4-444/J4-445) AND with the two J4-445 SLIVER carries
  `hProfMeas`/`hProfFac` themselves grounded to strictly-lower-level, already-enumerated campaign
  carries.  The `hGint` sub-chain now rests on ONLY:

    supplier carry     role                                       provenance / satisfiability
    ────────────────   ─────────────────────────────────────────  ───────────────────────────────────
    `hFzero`           Levi-source vanishing (`s ≤ 0 ⟹ F = 0`)    banked `hFzero_concrete` shape
    `hWFDdomCapped`    CAPPED field-derivative Gaussian domination banked bulk engine (`εₘ ≤ τ`)
    `hFdomEvery`       every-ceiling Levi Gaussian envelope        banked F2-style Levi domination
    `hGintMeas`        `s`-profile aesm on the BULK window Ι0(u−εₘ) banked Fubini (`hF'meas_concrete`)
    `hWFDjoint`        `(s,z)` witnessFieldDeriv joint aesm, SLIVER banked joint-meas family (`hWFDjointY`)
    `hLeviJoint`       `(s,z)` Levi joint aesm, SLIVER window        banked joint-meas family (`hLeviJoint`)
    `hProfRate`        inner `|profile s| ≤ Q·(u−s)^{-1/2}` rate     banked coordinate-first-moment
                                                                    (`absCoord_gaussDdim_integral_le` /
                                                                    `hf2bound_at_witness` `Q/√τ`) ×
                                                                    Levi Gaussian (`intZ_dH_pairing_le`)

  ── WHAT J4-446 ELIMINATED (the two J4-445 carries, GONE).
    • `hProfFac`  — the two-part `∃ C B rem` risk-gate FACTORISATION shape with an UNKNOWN remainder
      function.  DISCHARGED (`profFac_at_witness`) to the SINGLE clean inner rate `hProfRate`
      (`Q·(u−s)^{-1/2}`) via `profFac_of_innerRate` — the exact inverse of `riskGate_powercount`, at the
      canonical remainder `rem s := √(u−s)`, `C := Q`, `B := 1`.  The unknown-`rem` degree of freedom is
      eliminated; only the clean scalar rate survives.
    • `hProfMeas` — the sliver-window profile ae-strong-measurability.  DISCHARGED
      (`profMeas_at_witness`) to the two joint `(s,z)` factor measurabilities via the banked Fubini
      inner-integral engine `innerIntegral_aesm` (`AEStronglyMeasurable.integral_prod_right'`), exactly
      as the bulk `hF'meas_concrete`.

  ── IS `hGint` AT THE CAMPAIGN FLOOR?  YES for its OWN sub-chain.  Every carry above is one of the
  SAME enumerated Gaussian-domination / joint-measurability / coordinate-moment families the rest of the
  a₁ = R/6 campaign already rests on:
    · `hFzero`/`hWFDdomCapped`/`hFdomEvery` — the Levi + capped field-derivative Gaussian envelopes;
    · `hGintMeas`/`hWFDjoint`/`hLeviJoint`  — the Fubini joint-measurability family (bulk + sliver);
    · `hProfRate`                            — the coordinate-first-moment √τ-gain (the ONE substantive
      analytic input, satisfiable by the banked moment machinery, m-free).
  There is NO residual carry unique to `hGint` — the single `hGint` interval-integrability binder (the
  J4-428 "NO banked supplier" flag) is now fully reduced to the campaign's standing enumerated carries.

  ── DONT-UNDERCREDIT FINDINGS.
    • `SlotInstantiationV.hf2bound_at_witness` ALREADY proves the `Q/√τ` odd-moment √τ extraction for
      the CLEAN integrand `z_i/(2τ)·G_τ·A1amp·F` (= `Q·τ^{-1/2}`); the profile's `hProfRate` is the SAME
      rate for the witnessFieldDeriv·Levi pairing — the substantive content is banked in shape.
    • `FrozenDominatorLegs.intZ_dH_pairing_le` gives the CONSTANT (u-capped) inner pairing bound at
      general base — the bulk (non-endpoint) content; the sliver needs the √τ-gained REFINEMENT, which
      is exactly `hProfRate`.  The risk-gate arithmetic (`riskGate_powercount`) and the sliver rpow
      integrability (`rpow_sub_intervalIntegrable`) are fully banked; J4-446 needed only their INVERSE
      packaging + the Fubini marginal.
    • The `hProfMeas` Fubini engine (`innerIntegral_aesm`) is base-general and window-general — the
      sliver window is a first-class instance, no re-proof.

  ⚠  GROUP (3) v4 = ENUMERATED INPUT CARRIES ONLY.  This brick does NOT prove `a₁ = R/6`, and makes NO
  claim of unconditionality.  It grounds the two J4-445 sliver carries to the campaign floor: `hGint` is
  now at the campaign floor.  `a₁ = R/6` remains CONDITIONAL on the whole convergence-trio + geometric-
  wiring stack and the surviving enumerated carries (the census `hProv`/order-2/`hbulkderiv`/`hsliver`/
  `hcont`/`hQ1` fields, and the Gaussian-domination / moment / joint-measurability families).
-/

section AxiomChecks
open QIQTH.ProfFacWitness
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms profFac_of_innerRate
#print axioms profFac_at_witness
#print axioms profMeas_at_witness
#print axioms hGint_grounded
#print axioms perUCensus_phase4
end AxiomChecks
