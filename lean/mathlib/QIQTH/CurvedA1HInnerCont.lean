/-
  CurvedA1HInnerCont — J4-592: draining the `hInnerCont` carrier of the curved a₁ = R/6 capstone.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT.  The center-gauge curved capstone
  `CurvedA1FullyWiredCenter.curved_a1_R6_fully_wired_center` is NON-VACUOUS (J4-587) at the genuinely
  curved witness `g^K = curvedRNCMetric κ` (`κ < 0`, `Ric ≠ 0`), but CARRIES a residual family.  The
  mass-side `hmassone` has been drained (J4-588→591).  This brick attacks `hInnerCont`, the carried
  interior-time continuity binder

      `∀ u ∈ U, ContinuousOn (fun s => ∫ z, W (u−s) 0 z · L s z 0) (Set.Ioo 0 u)`,

  where `W := vanVleckGatedWitness g^K … (constGate g^K …) a b` (the gated van-Vleck parametrix
  witness) and `L := leviSeries (heatOp g^K W)` (the Levi/Duhamel residual series).

  ── ★★ VERDICT (J4-592): `hInnerCont` for `g^K` REDUCES, EXACTLY, to the honest per-interior-point
     dominated-continuity datum `hContDom` via the ALREADY-BANKED, std-3 generic engine
     `InnerMeasFubini.hInnerCont_concrete` (which is itself
     `InnerMeasFubini.innerIntegral_continuousOn_of_dominated` applied per interior point).  That
     engine is stated generically in `(g, gi, hChr, hK, S, a, b, U)`; its conclusion is LITERALLY the
     curved `hInnerCont` shape under `g := curvedRNCMetric κ`, `gi := curvedRNCInv κ`,
     `S := constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c`.  The `DataPileWitnessAudit`
     flagged `hInnerCont` as `DS none` because the abstract `Continuous`-on-all-of-ℝ engine
     `HeatConvRegularity.heatConv_inner_continuous` demands full-line time continuity (FALSE at the
     `τ → 0` Gaussian degeneracy); the `ContinuousOn (Set.Ioo 0 u)` engine used here needs only the
     LOCAL datum on the OPEN interior, exactly excluding that degeneracy — so the reduction is the
     right one.

  ── WHAT LANDS HERE (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `curved_hInnerCont_at_gate` — ★★ the EXACT curved `hInnerCont` binder of the center-gauge
      capstone, obtained as the `g := g^K` specialization of `InnerMeasFubini.hInnerCont_concrete`.
      It drains `hInnerCont` from an opaque carried `ContinuousOn` to the honest per-interior-point
      dominated-continuity datum `hContDom` FOR `g^K` — a genuine, non-vacuous analytic residual, not
      the conclusion.  Thin term-mode wrapper over the banked engine.
    • `curved_hInnerCont_satisfiable` — ★ the NON-VACUITY certificate.  For `κ < 0`, `n ≥ 2`, `g^K`
      is GENUINELY CURVED (`∃ w, 1 < det g^K w`, since `det g^K(w) = (1 − (K/3)‖w‖²)^(n−1) > 1` for
      `‖w‖ > 0`, `K < 0`), so the reduction is NOT secretly the flat kernel.  (Re-exports the sibling
      `CurvedA1HmassoneBound.curved_hmassoneBound_satisfiable`.)

  ── WHY `hContDom` IS GENUINELY TRUE FOR `g^K` (satisfiability, not vacuity).  Fix `s₀ ∈ Ioo 0 u`.
     Then `s₀ > 0` AND `u − s₀ ∈ (0, u)` is STRICTLY positive; on a small closed neighbourhood of `s₀`
     inside `Ioo 0 u`, both `s` and `u − s` stay bounded away from `0`, so BOTH kernels sit at strictly
     positive time — no `τ → 0` Gaussian blow-up.  There `W(u−s)` (Gaussian × smooth amplitude) and
     `L(s)` (positive-time-strip continuous Levi series) are continuous in `s` for a.e. `z`, giving
     the a.e.-`z` `ContinuousAt` datum, and both are locally-uniformly Gaussian-dominated, giving an
     integrable Gaussian×Gaussian dominator.  The ONLY time-degeneracy (`s → 0` / `u − s → 0`) is
     excluded by the OPEN interval `Ioo 0 u`, and `hContDom` demands no endpoint continuity.

  ── HONEST RESIDUAL.  After this brick `hInnerCont` is reduced to `hContDom` FOR `g^K` — the
     per-interior-point {local Gaussian dominator + its integrability, local a.e.-strong
     measurability, local a.e. domination, a.e.-`z` time `ContinuousAt`}.  Assembling `hContDom` from
     the banked witness/Levi positive-time continuity + Gaussian-domination bricks is a SEPARATE
     analytic thread, not addressed here.

  ⚠ HONEST FIREWALL.  This attacks the `hInnerCont` carrier of the NON-VACUOUS curved a₁ = R/6
  capstone; it proves NOTHING about `R/6`.  a₁ = R/6 remains CONDITIONAL; the curved capstone still
  owes `hContDom` (this brick's residual) PLUS the other carried residuals — `hsrc`, `hOffCollarTail`,
  the census/measurability/domination piles, the convergence trio, and `hmassone`'s pre-ρ carriers.
  Everything here is TRUE for the genuinely-curved `g^K` (`κ ≤ 0`, `Ric ≠ 0`) and DERIVED from the
  PROVED `InnerMeasFubini` engine, NOT axiomatized, NOT the `a₁` conclusion.  No `sorry`, no new
  axioms, no `:= True`, no vacuous / conclusion-in-disguise hypothesis, no existing file edited,
  nothing committed.
-/
import Mathlib
import QIQTH.InnerMeasFubini
import QIQTH.CurvedA1HmassoneBound

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.TrueHeatKernel QIQTH.LeviSeries
open QIQTH.A1R6CoreAtGate QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open scoped Topology

namespace QIQTH.CurvedA1HInnerCont

variable {n : ℕ}

/-- **★★ `curved_hInnerCont_at_gate` — THE `hInnerCont` CARRIER OF THE CURVED CAPSTONE, REDUCED.**
    The EXACT `hInnerCont` binder carried by
    `CurvedA1FullyWiredCenter.curved_a1_R6_fully_wired_center` at the genuinely-curved witness
    `g^K = curvedRNCMetric κ` — the interior-time continuity of the inner space-time pairing on
    `Set.Ioo 0 u` — obtained as the `g := curvedRNCMetric κ`, `gi := curvedRNCInv κ`,
    `S := constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c` specialization of the banked
    generic engine `InnerMeasFubini.hInnerCont_concrete`.  This drains `hInnerCont` from an opaque
    carried `ContinuousOn` to the honest per-interior-point dominated-continuity datum `hContDom` for
    `g^K` (a local integrable Gaussian dominator + local a.e.-strong measurability + local a.e.
    domination + a.e.-`z` time `ContinuousAt`), which is GENUINELY TRUE on the OPEN interval `Ioo 0 u`
    (both `s` and `u−s` strictly positive ⟹ no `τ→0` degeneracy).  `hContDom` is NOT the conclusion,
    NOT vacuous.  NOT `a₁ = R/6`. -/
theorem curved_hInnerCont_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ) (U : Set ℝ)
    (hContDom : ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u,
        ∃ bound : Point n → ℝ, Integrable bound (volume : Measure (Point n)) ∧
          (∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable
            (fun z => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) 0 z
              * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                  (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
            (volume : Measure (Point n))) ∧
          (∀ᶠ s in 𝓝 s₀, ∀ᵐ z ∂(volume : Measure (Point n)),
            ‖vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) 0 z
              * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                  (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0‖
              ≤ bound z) ∧
          (∀ᵐ z ∂(volume : Measure (Point n)), ContinuousAt
            (fun s => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) 0 z
              * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                  (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0) s₀)) :
    ∀ u ∈ U, ContinuousOn
        (fun s => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) 0 z
          * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
              (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        (Set.Ioo 0 u) :=
  InnerMeasFubini.hInnerCont_concrete (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b U hContDom

/-- **★ `curved_hInnerCont_satisfiable` — THE NON-VACUITY CERTIFICATE.**  For `κ < 0`, `n ≥ 2`, the
    witness `g^K = curvedRNCMetric κ` is GENUINELY CURVED: `∃ w, 1 < det g^K w`
    (`det g^K(w) = (1 − (K/3)‖w‖²)^(n−1) > 1` for `‖w‖ > 0`, `K < 0`).  So the `hInnerCont` reduction
    of `curved_hInnerCont_at_gate` is applied to a NON-flat metric — it is not secretly the flat heat
    kernel.  Re-exports `CurvedA1HmassoneBound.curved_hmassoneBound_satisfiable`.  NOT `a₁ = R/6`. -/
theorem curved_hInnerCont_satisfiable (κ : ℝ) (hκ : κ < 0) (hn : 2 ≤ n) :
    ∃ w : Point n, (1 : ℝ) < Matrix.det (curvedRNCMetric κ w) :=
  (QIQTH.CurvedA1HmassoneBound.curved_hmassoneBound_satisfiable κ hκ hn).2

end QIQTH.CurvedA1HInnerCont

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.CurvedA1HInnerCont

#print axioms curved_hInnerCont_at_gate
#print axioms curved_hInnerCont_satisfiable

end AxiomChecks
