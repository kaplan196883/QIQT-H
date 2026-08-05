/-
  SecondOrderInterchangeConcrete — J4-256 (wide-route brick 10): FIRING THE W2 ENGINE.

  One brick of the `a₁ = R/6` heat-kernel campaign.  It is NOT `a₁ = R/6`, and proves NOTHING about
  `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT.  Bricks 1–3,5,6,7,9 banked the two engines and the global center-field domination:
    • `SecondOrderInterchange.pd_pd_heatConvFrozen_interchange` / `.hInterchange_discharge` — the
      ABSTRACT second-order differentiation-under-∫∫ engine;
    • `EngineInstantiation.witness_secondOrder_interchange` — that engine THREADED to the concrete
      `N = 1` van-Vleck gated witness `H_G := vanVleckGatedWitness`, delivering, at any gap `b`,
        `pd (fun y => pd (fun x => heatConvFrozen H_G F u b x 0) i y) i 0
           = ∫ s in (0)..b, ∫ z, witnessSecondXDeriv … i (u−s) z · F s z 0`;
    • `SecondOrderMajorants.secondOrder_inner_bound_slot` — the W2 MAJORANT (`hbound`) slot: the
      truncated-window inner `z`-pairing is bounded u/w-uniformly by the single constant
      `secondBoundConst`, GIVEN the second-order Gaussian domination `hD2`
        `|D2 (u−s) w z| ≤ Csec·(u−s)⁻¹·gaussDdim(α(u−s)) z`   (uniform over `w ∈ snb`);
    • `FixedGateDichotomy.second_global_of_package` — the GLOBAL center-field second domination
      (the `witnessSecondXDeriv` shape, `p = 0`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS (this file, ns `QIQTH.SecondOrderInterchangeConcrete`).

    (1)  `witnessFieldDeriv2_shifted_hD2` — ★ THE snb-UNIFORM SECOND-ORDER DOMINATION (the field-point-
         shifted `hD2` the W2 majorant consumes), GLOBALISED off-gate.  For the shifted second-derivative
         kernel `D2 τ w z := witnessFieldDeriv2 … i τ (update 0 i w) z` (the engine's second `∫z`-kernel
         at the coordinate-shifted field point), from the ON-GATE shifted domination `hOn` (`z ∈ K` leg)
         the FULL `hD2` shape holds for ALL `z`: off the base gate (`z ∉ K`) the shifted second kernel
         VANISHES (`witnessFieldDeriv2_offGate_eq_zero`) and the Gaussian RHS is `≥ 0`.  The off-gate leg
         COMPOSES (new content); the on-gate shifted leg is CARRIED — the field-shifted near-isometry /
         general-`p` chart-jet estimate (the width-gap argument at the shifted field point), the honest
         second-order analogue of `second_global_of_package`'s `hSupp`+on-ball carry.

    (2)  `witness_secondOrder_hbound_slot` — the CONCRETE W2 `hbound` SLOT.  Composes (1) into
         `SecondOrderMajorants.secondOrder_inner_bound_slot`: on the truncated window the concrete
         shifted inner `z`-pairing is bounded u/w-uniformly by `secondBoundConst n Csec C_L α m`, given
         the on-gate shifted domination + the Levi source bound `hF`.  This IS the `bound`/`hbdd`/`hbound`
         triple the engine's second-order member needs, discharged for the concrete witness.

    (3)  ★★★ `witness_MemInterchange` — THE ENGINE FIRING (pure threading form).  Threading
         `EngineInstantiation.witness_secondOrder_interchange` over `(m, i, u ∈ U)` produces the VERBATIM
         `DaLimLUWallRecon.MemInterchange` member for the concrete witness, with
         `pdpdH i τ z := witnessSecondXDeriv … i τ z`:
             `∀ m i, ∀ u ∈ U,
                pd (fun y => pd (fun x => heatConvFrozen H_G F u (u−epsSeq m) x 0) i y) i 0
                  = ∫ s in (0)..(u−epsSeq m), ∫ z, witnessSecondXDeriv … i (u−s) z · F s z 0`.
         The analytic family (`hQ1`, `hFmeas`/`hFint`/`hF'meas`, `bound`/`hbdd`/`hbound`, `hdiff`) is
         carried per `(m,i,u)` — each a genuine differentiation-under-∫ fact, NONE the conclusion.

    (4)  ★★★ `witness_MemInterchange_majorant` — THE ENGINE FIRING WITH THE W2 BOUND SLOT DISCHARGED.
         The same MemInterchange member, but the `bound`/`hbdd`/`hbound` triple is SUPPLIED INTERNALLY by
         (2) + `secondBoundConst_intervalIntegrable` from the on-gate shifted domination `hOn` and the
         Levi source bound `hF` — so ONLY the `hQ1`/`hFmeas`/`hFint`/`hF'meas`/`hdiff` diff-under-∫ carries
         remain.  Fires on the eventual window (`epsSeq m ≤ u`, where the truncation is non-singular);
         the `ε → 0` limit is the downstream `DaLim` machinery.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST FIREWALL — the carries (each a genuine differentiation-under-∫ / on-gate-domination fact,
  NONE the conclusion, none vacuous / unsatisfiable).

    hOn        the ON-GATE shifted second-order Gaussian domination (`z ∈ K` leg) — the field-shifted
               near-isometry chart-jet estimate at the coordinate-shifted field point `update 0 i w`;
               the honest second-order analogue of `second_global_of_package`'s on-ball carry, NOT the
               conclusion.  The OFF-gate leg is DISCHARGED here (composes).
    hF         the Levi source width-2 Gaussian bound `|F s z 0| ≤ C_L·gaussDdim(2s) z` — the landed
               Levi-series envelope.
    hQ1        the FIRST-ORDER interchange on the open field nbhd `V ∋ 0` at the concrete `dH`
               (= `SecondOrderInterchange.pd_heatConvFrozen_interchange` for the witness); genuine,
               dischargeable, NOT the (second-order) conclusion.
    hFmeas/hF'meas   the `∫z`-object / its `∫z`-derivative `s`-measurabilities (the closed
               `ChartJointBorel` Borel machinery route).
    hFint      base interval-integrability of the `∫z`-object (the `ConvCarriesDischarge.
               heatConvInner_intervalIntegrable_gaussianDom` route at the first-derivative kernel).
    hdiff      the `∫z`-derivative `HasDerivAt` family (each an
               `SecondOrderInterchange.innerZ_line_hasDerivAt`).

    NO `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
    hypotheses, no conclusion-in-disguise.  No existing file is edited.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.EngineInstantiation
import QIQTH.SecondOrderMajorants

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.ResidueBound
open QIQTH.HeatResidualBound QIQTH.HeatDuhamel QIQTH.SecondOrderMajorants
open scoped Interval Topology

namespace QIQTH.SecondOrderInterchangeConcrete

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (1) — the snb-uniform second-order domination, globalised off-gate.
    ############################################################################### -/

/-- **★ (1) `witnessFieldDeriv2_shifted_hD2` — THE snb-UNIFORM SECOND-ORDER DOMINATION.**  For the
    field-point-shifted second-derivative kernel `D2 τ w z := witnessFieldDeriv2 … i τ (update 0 i w) z`
    (the second `∫z`-kernel the W2 engine differentiates, at the coordinate-shifted field point), from
    the ON-GATE shifted Gaussian domination `hOn` (valid on the base gate `z ∈ K`) the FULL `hD2` shape
    holds for ALL `z`:
        `|witnessFieldDeriv2 … i (u−s) (update 0 i w) z| ≤ Csec·(u−s)⁻¹·gaussDdim(α(u−s)) z`
    uniformly over `w ∈ snb`.  OFF the base gate (`z ∉ K`) the shifted second kernel VANISHES
    (`witnessFieldDeriv2_offGate_eq_zero`) and the Gaussian RHS is `≥ 0` (`Csec ≥ 0`, `(u−s)⁻¹ ≥ 0`,
    Gaussian peak `≥ 0`).  The off-gate leg COMPOSES here (new content); `hOn` is CARRIED — the honest
    second-order analogue of `second_global_of_package`'s support+on-ball carry.  This is exactly the
    `hD2` slot of `SecondOrderMajorants.secondOrder_inner_bound_slot`.  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv2_shifted_hD2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (acut bcut : ℝ)
    (i : Fin n) (u T α Csec : ℝ) (snb : Set ℝ) (hCsec : 0 ≤ Csec)
    (hOn : ∀ (s w : ℝ) (z : Point n), 0 < u - s → s ≤ T → w ∈ snb → z ∈ K →
        |witnessFieldDeriv2 g gi hC hK S acut bcut i (u - s) (Function.update (0 : Point n) i w) z|
          ≤ Csec * (u - s)⁻¹ * gaussDdim (α * (u - s)) z) :
    ∀ (s w : ℝ) (z : Point n), 0 < u - s → s ≤ T → w ∈ snb →
      |witnessFieldDeriv2 g gi hC hK S acut bcut i (u - s) (Function.update (0 : Point n) i w) z|
        ≤ Csec * (u - s)⁻¹ * gaussDdim (α * (u - s)) z := by
  intro s w z hτ hsT hw
  by_cases hz : z ∈ K
  · exact hOn s w z hτ hsT hw hz
  · rw [witnessFieldDeriv2_offGate_eq_zero g gi hC hK S acut bcut i (u - s)
        (Function.update (0 : Point n) i w) z hz, abs_zero]
    exact mul_nonneg (mul_nonneg hCsec (inv_nonneg.mpr hτ.le)) (gaussDdim_nonneg _ _)

/-! ###############################################################################
    ### (2) — the concrete W2 `hbound` slot.
    ############################################################################### -/

/-- **★★ (2) `witness_secondOrder_hbound_slot` — THE CONCRETE W2 `hbound` SLOT.**  Composing the
    globalised shifted domination (1) into `SecondOrderMajorants.secondOrder_inner_bound_slot`, the
    concrete shifted inner `z`-pairing is bounded on the TRUNCATED window
    `s ∈ uIoc 0 (u − epsSeq m)` by the single u/w-uniform constant `secondBoundConst n Csec C_L α m`,
    uniformly in `w ∈ snb`:
        `‖∫ z, witnessFieldDeriv2 … i (u−s) (update 0 i w) z · F s z 0‖
           ≤ secondBoundConst n Csec C_L α m`.
    Inputs: the ON-GATE shifted domination `hOn` (the `hD2` half, off-gate discharged by (1)) and the
    Levi source width-2 bound `hF`; the singular `(u−s)⁻¹` endpoint is tamed by the truncation
    (`epsSeq m ≤ u`).  This IS the `hbound` slot the concrete engine member needs.  NOT `a₁ = R/6`. -/
theorem witness_secondOrder_hbound_slot (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (acut bcut : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (u T α Csec C_L : ℝ) (m : ℕ) (snb : Set ℝ)
    (hu : 0 < u) (huT : u ≤ T) (hα : 0 < α) (hεu : epsSeq m ≤ u)
    (hCsec : 0 ≤ Csec) (hC_L : 0 ≤ C_L)
    (hOn : ∀ (s w : ℝ) (z : Point n), 0 < u - s → s ≤ T → w ∈ snb → z ∈ K →
        |witnessFieldDeriv2 g gi hC hK S acut bcut i (u - s) (Function.update (0 : Point n) i w) z|
          ≤ Csec * (u - s)⁻¹ * gaussDdim (α * (u - s)) z)
    (hF : ∀ (s : ℝ) (z : Point n), 0 < s → s ≤ T → |F s z 0| ≤ C_L * gaussDdim (2 * s) z) :
    ∀ s ∈ Set.uIoc 0 (u - epsSeq m), ∀ w ∈ snb,
      ‖∫ z, witnessFieldDeriv2 g gi hC hK S acut bcut i (u - s)
          (Function.update (0 : Point n) i w) z * F s z 0‖
        ≤ secondBoundConst n Csec C_L α m := by
  have hD2 := witnessFieldDeriv2_shifted_hD2 g gi hC hK S acut bcut i u T α Csec snb hCsec hOn
  exact secondOrder_inner_bound_slot
    (fun τ w z => witnessFieldDeriv2 g gi hC hK S acut bcut i τ (Function.update (0 : Point n) i w) z)
    F u T α Csec C_L m snb hu huT hα hεu hCsec hC_L hD2 hF

/-! ###############################################################################
    ### (3) — ★★★ the engine firing (pure threading form).
    ############################################################################### -/

/-- **★★★ (3) `witness_MemInterchange` — THE ENGINE FIRING (pure threading form).**  Threading
    `EngineInstantiation.witness_secondOrder_interchange` over `(m, i, u ∈ U)` (each at gap
    `b := u − epsSeq m`) produces the VERBATIM `DaLimLUWallRecon.MemInterchange` member for the concrete
    `N = 1` van-Vleck gated witness `H_G := vanVleckGatedWitness g gi hC hK S acut bcut`, with
    `pdpdH i τ z := witnessSecondXDeriv … i τ z`:
        `∀ m i, ∀ u ∈ U,
           pd (fun y => pd (fun x => heatConvFrozen H_G F u (u−epsSeq m) x 0) i y) i 0
             = ∫ s in (0)..(u−epsSeq m), ∫ z, witnessSecondXDeriv … i (u−s) z · F s z 0`.
    The whole analytic family is carried per `(m,i,u)` — the first-order interchange `hQ1` on the open
    field nbhd `V ∋ 0`, the `∫z`/`∫s` measurabilities `hFmeas`/`hFint`/`hF'meas`, the interval-integrable
    `s`-dominator `bound`/`hbdd`/`hbound`, and the `∫z`-derivative `HasDerivAt` family `hdiff` — each a
    genuine differentiation-under-∫ fact about the concrete witness (satisfiable via the E1/E2 on-gate
    formulas + the C4b Gaussian-derivative bounds and the strictly-positive gap), NONE the conclusion.
    Pure threading through `witness_secondOrder_interchange`.  NOT `a₁ = R/6`. -/
theorem witness_MemInterchange (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (acut bcut : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (u : ℝ) (U : Set ℝ)
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hC hK S acut bcut) F u
            (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv g gi hC hK S acut bcut i (u - s) y z * F s z 0)
    (hFmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S acut bcut i (u - s)
            (Function.update (0 : Point n) i w) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S acut bcut i (u - s) (0 : Point n) z * F s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 g gi hC hK S acut bcut i (u - s) (0 : Point n) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bound : ℕ → Fin n → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (bound m i) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv2 g gi hC hK S acut bcut i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0‖ ≤ bound m i s)
    (hdiff : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, witnessFieldDeriv g gi hC hK S acut bcut i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0)
            (∫ z, witnessFieldDeriv2 g gi hC hK S acut bcut i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0) w) :
    ∀ (m : ℕ) (i : Fin n), ∀ u' ∈ U,
      pd (fun y => pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hC hK S acut bcut) F u'
          (u' - epsSeq m) x 0) i y) i 0
        = ∫ s in (0)..(u' - epsSeq m),
            ∫ z, witnessSecondXDeriv g gi hC hK S acut bcut i (u' - s) z * F s z 0 := by
  intro m i u' hu'
  have hsnb' : snb ∈ 𝓝 ((0 : Point n) i) := by
    have hz : ((0 : Point n) i) = (0 : ℝ) := by simp
    rw [hz]; exact hsnb
  exact witness_secondOrder_interchange g gi hC hK S acut bcut F u' (u' - epsSeq m) i
    V hVopen hV0 (hQ1 m i u' hu') snb hsnb'
    (hFmeas m i u' hu') (hFint m i u' hu') (hF'meas m i u' hu')
    (bound m i) (hbdd m i u' hu') (hbound m i u' hu') (hdiff m i u' hu')

/-! ###############################################################################
    ### (4) — ★★★ the engine firing with the W2 bound slot discharged.
    ############################################################################### -/

/-- **★★★ (4) `witness_MemInterchange_majorant` — THE ENGINE FIRING WITH THE W2 BOUND SLOT
    DISCHARGED.**  The same `MemInterchange` member as (3), but the `bound`/`hbdd`/`hbound` triple is
    SUPPLIED INTERNALLY by the W2 majorant: `bound := secondBoundConst n Csec C_L α m`, `hbdd` from
    `secondBoundConst_intervalIntegrable`, and `hbound` from (2) `witness_secondOrder_hbound_slot`
    (built from the on-gate shifted domination `hOn` and the Levi source bound `hF`).  So ONLY the
    `hQ1`/`hFmeas`/`hFint`/`hF'meas`/`hdiff` differentiation-under-∫ carries remain.  Fires on the
    EVENTUAL WINDOW (the antecedent `epsSeq m ≤ u`, where the truncation `u − epsSeq m ≥ 0` and the
    `(u−s)⁻¹` endpoint is bounded — `SecondOrderMajorants.window_inv_le`); the `ε → 0` limit is the
    downstream `DaLim` machinery.  Each carry is a genuine differentiation-under-∫ / on-gate-domination
    fact, NONE the conclusion.  NOT `a₁ = R/6`. -/
theorem witness_MemInterchange_majorant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (acut bcut : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (U : Set ℝ) (T α Csec C_L : ℝ)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (hα : 0 < α) (hCsec : 0 ≤ Csec) (hC_L : 0 ≤ C_L)
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hOn : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ (s w : ℝ) (z : Point n),
        0 < u - s → s ≤ T → w ∈ snb → z ∈ K →
        |witnessFieldDeriv2 g gi hC hK S acut bcut i (u - s) (Function.update (0 : Point n) i w) z|
          ≤ Csec * (u - s)⁻¹ * gaussDdim (α * (u - s)) z)
    (hF : ∀ (s : ℝ) (z : Point n), 0 < s → s ≤ T → |F s z 0| ≤ C_L * gaussDdim (2 * s) z)
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hC hK S acut bcut) F u
            (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv g gi hC hK S acut bcut i (u - s) y z * F s z 0)
    (hFmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S acut bcut i (u - s)
            (Function.update (0 : Point n) i w) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S acut bcut i (u - s) (0 : Point n) z * F s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 g gi hC hK S acut bcut i (u - s) (0 : Point n) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hdiff : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, witnessFieldDeriv g gi hC hK S acut bcut i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0)
            (∫ z, witnessFieldDeriv2 g gi hC hK S acut bcut i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0) w) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, epsSeq m ≤ u →
      pd (fun y => pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hC hK S acut bcut) F u
          (u - epsSeq m) x 0) i y) i 0
        = ∫ s in (0)..(u - epsSeq m),
            ∫ z, witnessSecondXDeriv g gi hC hK S acut bcut i (u - s) z * F s z 0 := by
  intro m i u hu hεu
  have hsnb' : snb ∈ 𝓝 ((0 : Point n) i) := by
    have hz : ((0 : Point n) i) = (0 : ℝ) := by simp
    rw [hz]; exact hsnb
  -- W2 majorant supplies the bound slot.
  have hbdd : IntervalIntegrable (fun _ : ℝ => secondBoundConst n Csec C_L α m)
      volume 0 (u - epsSeq m) := secondBoundConst_intervalIntegrable Csec C_L α m u
  have hbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
      ‖∫ z, witnessFieldDeriv2 g gi hC hK S acut bcut i (u - s)
          (Function.update (0 : Point n) i w) z * F s z 0‖
        ≤ (fun _ : ℝ => secondBoundConst n Csec C_L α m) s :=
    Filter.Eventually.of_forall
      (witness_secondOrder_hbound_slot g gi hC hK S acut bcut F i u T α Csec C_L m snb
        (hUpos u hu) (hUT u hu) hα hεu hCsec hC_L (hOn m i u hu) hF)
  exact witness_secondOrder_interchange g gi hC hK S acut bcut F u (u - epsSeq m) i
    V hVopen hV0 (hQ1 m i u hu) snb hsnb'
    (hFmeas m i u hu) (hFint m i u hu) (hF'meas m i u hu)
    (fun _ => secondBoundConst n Csec C_L α m) hbdd hbound (hdiff m i u hu)

end QIQTH.SecondOrderInterchangeConcrete

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.SecondOrderInterchangeConcrete.witnessFieldDeriv2_shifted_hD2
#print axioms QIQTH.SecondOrderInterchangeConcrete.witness_secondOrder_hbound_slot
#print axioms QIQTH.SecondOrderInterchangeConcrete.witness_MemInterchange
#print axioms QIQTH.SecondOrderInterchangeConcrete.witness_MemInterchange_majorant
