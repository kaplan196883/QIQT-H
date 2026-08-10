/-
  CurvedA1FintDAdomSource — J4-570.  SOURCE the `hAdom` carry of the SECOND census member of the
  capstone at `g^K` — `CurvedA1ClassBFint.curved_hFint_d_at_gate` — namely its per-`m` CAPPED
  RAW-witness (order-0) Gaussian domination, from a NAMED, PROVED banked whole-time base-witness
  domination.  This is the CLEANER sibling of J4-569 (`CurvedA1FintAdomSource`, the `hFint`
  first-derivative carrier): the RAW order-0 witness has NO `τ → 0` derivative blow-up, so the
  WHOLE-TIME Gaussian bound already HOLDS (banked), the capped form is strictly weaker, and the
  per-`m` constant can be `m`-INDEPENDENT (a single constant `C`) — the honest choice HERE, unlike
  the first-derivative case where a single `m`-free constant is the FALSE clean bound.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`.  This file turns `hFint_d`'s `hAdom` carry into a THEOREM,
  discharged from the PROVED banked whole-time domination
  `CurvedRNCBaseWitnessDomAdom.curvedRNC_baseWitness_dom_adom` (its frozen `p = 0` window conjunct
  `hWDom`).  It does NOT make `a₁ = R/6` unconditional: the `hFint` sibling's crude first-derivative
  envelope `hcrude` (J4-569's honest carried residual), `hsrc`, `hOffCollarTail`, the convergence
  trio, and `hInnerCont` all remain owed.

  ── THE SATISFIABILITY CORE (why order-0 whole-time HOLDS, so `C` may be `m`-free).  The `hFint_d`
  binder demands a per-`m` CAPPED domination
      `∀ m τ, epsSeq m ≤ τ → τ ≤ T → ∀ z, |vanVleckGatedWitness g^K … τ 0 z| ≤ CA m · gaussDdim (wA·τ) (0−z)`
  with `CA : ℕ → ℝ`.  For the RAW order-0 witness (NOT a spatial derivative) the CLEAN whole-time
  analogue — a single `m`-free constant on the full window `τ ∈ (0, T]` — is GENUINELY TRUE at `g^K`:
  the banked `curvedRNC_baseWitness_dom_adom` delivers exactly it (its `hWDom` conjunct,
  `|vanVleckGatedWitness … τ 0 z| ≤ CW·gaussDdim (lam·τ) z` for `τ ∈ (0, τ0fr]`, `CW` a CONSTANT).
  There is NO `τ^(−1/2)`/`τ⁻¹` blow-up because there is no spatial derivative on the parametrix.  So
  `CA m := C` (constant `CW`) is the honest per-`m` constant — and the capped binder is the trivial
  restriction of the whole-time bound to `epsSeq m ≤ τ` (which forces `0 < τ`), with
  `gaussDdim (lam·τ) z = gaussDdim (lam·τ) (0−z)` by evenness (`WidthAdapters.gaussDdim_neg`).

  ── WHAT IS PROVED (axiom-free, no `sorry`).
    •  `curved_hFint_d_hAdom_at_gate` — THE EXACT per-`m` CAPPED order-0 `hAdom` binder shape consumed
       by `CurvedA1ClassBFint.curved_hFint_d_at_gate`, produced (existentially in the banked gate
       radius `c`, window width `wA := lam`, and constant `C := CW`) FROM the PROVED banked
       `curvedRNC_baseWitness_dom_adom` — NOT carried, NOT axiomatized.  `C` is `m`-independent.
    •  `curved_hFint_d_at_gate_via_source` — the demonstrator: `curved_hFint_d_at_gate`'s
       `IntervalIntegrable` conclusion re-derived with its `hAdom` slot FILLED by the sourced binder,
       the remaining Levi/measurability carries (`hFdom`/`hFzero`/`hmeas`, at the banked gate radius
       `c`) forwarded verbatim.
    •  `curved_hFint_d_hAdom_at_gate_curved_satisfiable` — the CURVED (not-secretly-flat) gate.

  ── THE CARRIED RESIDUAL (scoped precisely).
    •  `hw` — the mainline amplitude-smoothness carry (`foldedCoeff (vanVleck g^K) (transportCoeff …)
       k ∈ C^∞`), the SAME `hw` fed to `curvedRNC_baseWitness_dom_adom` and carried mainline-wide.
       This is the ONLY input; the ε-restriction and the `m`-free constant are DERIVED here from the
       banked whole-time bound.  Unlike the first-derivative `hFint` case (J4-569), NO crude envelope
       is carried — the order-0 base domination is genuinely BANKED.

  NO `sorry`.  NO new axioms.  NO `:= True`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CurvedA1ClassBFint
import QIQTH.CurvedRNCBaseWitnessDomAdom

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LeviSeries QIQTH.HeatResidualBound QIQTH.LeviSeriesLocalData
open QIQTH.DaLimLUWallRecon QIQTH.ResidueBound
open QIQTH.CConvV2GaussianPairing QIQTH.CConvV2WitnessStar
open QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCGaussWitness QIQTH.A1R6CoreAtGate
open QIQTH.RadialDistance QIQTH.VanVleck QIQTH.ExpMap
open QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion QIQTH.WidthAdapters
open QIQTH.CurvedA1ClassBFint QIQTH.CurvedRNCBaseWitnessDomAdom
open scoped Interval Topology BigOperators

namespace QIQTH.CurvedA1FintDAdomSource

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### THE order-0 `hAdom` SOURCE for `curved_hFint_d_at_gate` at `g^K`.
    ############################################################################### -/

/-- **★★★ J4-570 — `curved_hFint_d_hAdom_at_gate`.**  THE EXACT per-`m` CAPPED RAW-witness (order-0)
    Gaussian domination `hAdom` consumed by `CurvedA1ClassBFint.curved_hFint_d_at_gate`, at the
    genuinely-curved witness `g^K = curvedRNCMetric K` (`K < 0`), SOURCED from the PROVED banked
    whole-time base-witness domination `CurvedRNCBaseWitnessDomAdom.curvedRNC_baseWitness_dom_adom`
    (its frozen `p = 0` window conjunct `hWDom`).  There exist a banked gate radius `c > 0`, a window
    width `wA := lam > 0`, and a CONSTANT `C := CW ≥ 0` — `m`-INDEPENDENT, the honest choice for the
    order-0 witness (no `τ → 0` blow-up: the whole-time bound genuinely holds) — such that
    `∀ m τ, epsSeq m ≤ τ → τ ≤ T → ∀ z, |vanVleckGatedWitness g^K … τ 0 z| ≤ C · gaussDdim (wA·τ) (0−z)`.
    Proof: the banked `hWDom` gives the whole-time (window `τ ≤ T`) bound with the CONSTANT `CW`; the
    capped binder is its restriction to `epsSeq m ≤ τ` (⟹ `0 < τ`), with `gaussDdim (lam·τ) z =
    gaussDdim (lam·τ) (0−z)` by evenness (`gaussDdim_neg`).  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hFint_d_hAdom_at_gate (K : ℝ) (hK : K < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y))
    {Kset : Set (Point n)} (hKset : IsCompact Kset)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (T : ℝ) (hT : 0 < T)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric K))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric K))
          (curvedRNCMetric K) (curvedRNCInv K))) k : Point n → ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ wA : ℝ, 0 < wA ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m : ℕ) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |vanVleckGatedWitness (curvedRNCMetric K) (curvedRNCInv K) hChr hKset
              (constGate (curvedRNCMetric K) (curvedRNCInv K) hChr hKset c) a b τ (0 : Point n) z|
          ≤ C * gaussDdim (wA * τ) (0 - z) := by
  obtain ⟨A₀, A₁, hA₀, hA₁, c, hc0, CW, lam, hCW, hlam, hAdomBP, hWDom⟩ :=
    curvedRNC_baseWitness_dom_adom K hK hChr hKset a b ha hab T hT hw
  refine ⟨c, hc0, lam, hlam, CW, hCW, ?_⟩
  intro m τ hτlo hτT z
  have hτ0 : 0 < τ := lt_of_lt_of_le (epsSeq_pos m) hτlo
  have hz := hWDom τ hτ0 hτT z
  rw [zero_sub, gaussDdim_neg]
  exact hz

/-- **★★ J4-570 (demonstrator) — `curved_hFint_d_at_gate_via_source`.**  The SECOND census member
    (`curved_hFint_d_at_gate`), re-derived with its `hAdom` slot FILLED by the SOURCED order-0 binder
    `curved_hFint_d_hAdom_at_gate` (`wA := lam`, `CA := fun _ => C`, `C` the banked constant `CW`).
    Existential in the banked gate radius `c` (fixed by the sourcing), with the remaining independent
    Levi/measurability carries `hFdom`/`hFzero`/`hmeas` — stated at that `c` — forwarded verbatim to
    yield the census `IntervalIntegrable` conclusion.  This proves the sourced binder plugs into the
    capstone carrier VERBATIM.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hFint_d_at_gate_via_source (K : ℝ) (hK : K < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y))
    {Kset : Set (Point n)} (hKset : IsCompact Kset)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (U : Set ℝ) (T : ℝ) (hT : 0 < T)
    (wF CF : ℝ) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric K))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric K))
          (curvedRNCMetric K) (curvedRNCInv K))) k : Point n → ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ wA : ℝ, 0 < wA ∧ ∃ C : ℝ, 0 ≤ C ∧
      ((∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
          |leviSeries (heatOp (curvedRNCMetric K) (curvedRNCInv K)
                (vanVleckGatedWitness (curvedRNCMetric K) (curvedRNCInv K) hChr hKset
                  (constGate (curvedRNCMetric K) (curvedRNCInv K) hChr hKset c) a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z) →
       (∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
          leviSeries (heatOp (curvedRNCMetric K) (curvedRNCInv K)
            (vanVleckGatedWitness (curvedRNCMetric K) (curvedRNCInv K) hChr hKset
              (constGate (curvedRNCMetric K) (curvedRNCInv K) hChr hKset c) a b)) s z 0 = 0) →
       (∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
          (fun s => ∫ z, vanVleckGatedWitness (curvedRNCMetric K) (curvedRNCInv K) hChr hKset
                (constGate (curvedRNCMetric K) (curvedRNCInv K) hChr hKset c) a b (u - s) (0 : Point n) z
              * leviSeries (heatOp (curvedRNCMetric K) (curvedRNCInv K)
                  (vanVleckGatedWitness (curvedRNCMetric K) (curvedRNCInv K) hChr hKset
                    (constGate (curvedRNCMetric K) (curvedRNCInv K) hChr hKset c) a b)) s z 0)
          ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m)))) →
       ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness (curvedRNCMetric K) (curvedRNCInv K) hChr hKset
                (constGate (curvedRNCMetric K) (curvedRNCInv K) hChr hKset c) a b (u - s) (0 : Point n) z
              * leviSeries (heatOp (curvedRNCMetric K) (curvedRNCInv K)
                  (vanVleckGatedWitness (curvedRNCMetric K) (curvedRNCInv K) hChr hKset
                    (constGate (curvedRNCMetric K) (curvedRNCInv K) hChr hKset c) a b)) s z 0)
          volume 0 (u - epsSeq m)) := by
  obtain ⟨c, hc0, wA, hwA, C, hC, hAdom⟩ :=
    curved_hFint_d_hAdom_at_gate K hK hChr hKset a b ha hab T hT hw
  exact ⟨c, hc0, wA, hwA, C, hC, fun hFdom hFzero hmeas =>
    curved_hFint_d_at_gate K hChr hKset a b c U T wA (fun _ => C) wF CF
      hwA (fun _ => hC) hwF hCF hUpos hUT hAdom hFdom hFzero hmeas⟩

/-- **★ J4-570 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  For `κ ≠ 0`, `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0)`) of `g^K = curvedRNCMetric κ` is nonzero, so the sourced order-0
    `hAdom` binder is discharged at a genuinely curved witness (`κ < 0 ⊂ κ ≠ 0`), NOT the flat `δ`.
    NOT `a₁ = R/6`. -/
theorem curved_hFint_d_hAdom_at_gate_curved_satisfiable (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedA1FintDAdomSource

section AxiomChecks
open QIQTH.CurvedA1FintDAdomSource
#print axioms curved_hFint_d_hAdom_at_gate
#print axioms curved_hFint_d_at_gate_via_source
#print axioms curved_hFint_d_hAdom_at_gate_curved_satisfiable
end AxiomChecks
