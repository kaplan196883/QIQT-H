/-
  HBLgaussUnconditional — J4-1037 (part 2): fb's `hBLgauss` `c < δ₀` compatibility gap CLOSED — the S1
  jet reach `δ₀` obtained BEFORE the gate parameters (`ReachRequant.tripleHEmeas_flowball_requant`) fed
  as the prescribed ceiling into `ConstRadiusPkgPrescribed`'s package producer, so the pkg's own gate
  radius `c` satisfies `c < δ₀` BY CONSTRUCTION, turning `LeviBaseGaussEnvelopeConst`'s conditional
  `leviBase_gaussDdim2s_envelope_CONST` into an UNCONDITIONAL theorem (no `c < δ₀ →` antecedent).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  No `sorry`, no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file
  edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE FIX (construction-order inversion, per gpt-5.6-sol GO verdict).

  `LeviBaseGaussEnvelopeConst.leviBase_gaussDdim2s_envelope_CONST` obtains its gate parameters
  `a, b, c, δ₀` from `ConstRadiusGateExport.constRadius_package_and_S1`, which derives `a, b, c` FIRST
  (chart/coefficient geometry) and only THEN derives `δ₀` (the S1/jet reach), so `c < δ₀` is a bare,
  in-general-unprovable antecedent (cp995's countermodel: `a=1,b=2,c=3,δ₀=1` — every OTHER stated fact
  holds).  This file INVERTS the order:
    (A) `ReachRequant.tripleHEmeas_flowball_requant` — the S1 jet reach `δ₀ > 0`, produced BEFORE the
        gate parameters `(a,b,c)` (audited: every sub-supplier radius bottoms out in `(a,b)`-FREE
        geometry — J4-599, banked 2026-08-11).
    (B) `ConstRadiusPkgPrescribed.gatedWitnessN1_package_open_CONSTRADIUS_prescribed` — the package
        producer replayed with the PRESCRIBED ceiling `ε := δ₀` from (A), so its own gate radius `c`
        satisfies `c < δ₀` BY CONSTRUCTION (the ceiling is one more `min` in the internal availability
        radius; no proof step of the original package producer is disturbed since the radius only
        shrinks).
  Feeding (A)'s `hspec a b ha hab c hbc hcδ` DIRECTLY (not re-deriving a fresh, independent `δ₀` via
  `tripleHEmeas_AT_CONSTRADIUS_GATE`) yields `tripleHEmeas` UNCONDITIONALLY at THIS `a, b, c` — the
  compatibility gap dissolves because `δ₀` and `c` are no longer independently-produced witnesses: `c`
  is chosen AFTER, and BOUNDED BY, `δ₀`.  Non-circularity: `δ₀` from (A) depends only on the ambient
  `g, gi, hC, hK` data (fixed BEFORE any gate parameter is introduced); nothing in (A)'s construction
  is later instantiated with `a, b, c` — the standard direction-of-dependence check gpt-5.6-sol flagged
  (mirroring the earlier `hxmem` circularity trap, which does NOT recur here: no `.choose` inside (A)
  is applied to a term built from `(a,b,c)`).

  ## WHAT LANDS (ns `QIQTH.HBLgaussUnconditional`).
    • `leviBase_gaussDdim2s_envelope_UNCOND` — ★★★ the UNCONDITIONAL re-export of
      `leviBase_gaussDdim2s_envelope_CONST`: SAME conclusion shape, `c < δ₀` antecedent GONE.
    • `hBLgauss_capped_window_UNCOND` — ★★★ the `hzmass_capped_window_closed` `hBLgauss` slot,
      UNCONDITIONALLY (no `c < δ₀` residue anywhere in the hypothesis list).  fb's `hBLgauss` `c < δ₀`
      compatibility gap is CLOSED.  The other FIVE `hzmass_capped_window_closed` hypotheses (`hint`,
      `hBFpeak`, `hBLnn`, `hPpknn`, `hPCbound`) are UNTOUCHED by this file.  `hBFpeak`'s z-uniform-
      dominator gap REMAINS OPEN regardless of this brick.

  Consulted `gpt-5.6-sol` (high effort) BEFORE construction with the precise dependency chains traced
  below; verdict GO, no circularity, main risk flagged was the import DAG (checked here: no cycle —
  `ReachRequant`/`CurvedA1ReachAlign` do not transitively import `LeviBaseGaussEnvelopeConst` or its
  dependents).  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ReachRequant
import QIQTH.ConstRadiusPkgPrescribed
import QIQTH.LeviBaseGaussEnvelopeConst
import QIQTH.HZMassCappedWindowClosed

open MeasureTheory Finset Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound
open QIQTH.ReachRequant QIQTH.ConstRadiusPkgPrescribed
open scoped BigOperators ContDiff Topology Interval

namespace QIQTH.HBLgaussUnconditional

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-- **★★★ J4-1037 (A) — `leviBase_gaussDdim2s_envelope_UNCOND`.**  The UNCONDITIONAL re-export of
    `LeviBaseGaussEnvelopeConst.leviBase_gaussDdim2s_envelope_CONST`: obtains the S1 jet reach `δ₀`
    FIRST (`ReachRequant.tripleHEmeas_flowball_requant`, `(a,b)`-independent), feeds it as the
    prescribed ceiling into the package producer (`ConstRadiusPkgPrescribed`) so `c < δ₀` holds BY
    CONSTRUCTION, then replays the same gate-polymorphic downstream chain
    (`heatOp_gatedWitnessN1_eq_zero_of_nonpos`, `iterConvIntegrableW_of_locally_bound_baseMeas`,
    `leviSeries_dominatedW_le`) that `leviBase_gaussDdim2s_envelope_CONST` uses.  NO `c < δ₀`
    antecedent anywhere in the hypothesis list.  NOT `a₁ = R/6`. -/
theorem leviBase_gaussDdim2s_envelope_UNCOND (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p))
    (T : ℝ) (hT : 0 < T) :
    ∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧
      ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ (s : ℝ) (z : Point n), 0 < s → s ≤ T →
        |leviSeries (heatOp g gi
            (vanVleckGatedWitness g gi hC hK
              (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) a b)) s z 0|
          ≤ C_L * gaussDdim (2 * s) z := by
  obtain ⟨δ₀, hδ₀, hspec⟩ :=
    ReachRequant.tripleHEmeas_flowball_requant hn g gi hC hK hg hgiC hgpos hu hgiMeas hchr
  obtain ⟨a, b, C, c, ha, hab, hC0, hbc, hcδ, hbound, _hmemS0, _hopenS0⟩ :=
    ConstRadiusPkgPrescribed.gatedWitnessN1_package_open_CONSTRADIUS_prescribed g gi hg hC hK hgnd
      hgsymm hinvF hframeK hw hdg0 hg0 δ₀ hδ₀
  refine ⟨a, b, c, ha, hab, hbc, ?_⟩
  set S : Point n → Set (Point n) :=
    fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c with hSdef
  have hEmeas : StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) w.1 w.2.1 w.2.2) :=
    hspec a b ha hab c hbc hcδ
  have hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n,
      heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) τ p q = 0 :=
    heatOp_gatedWitnessN1_eq_zero_of_nonpos g gi hn K S (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK)
  have hboundS : ∀ (t : ℝ), ∀ τ p q, 0 < τ → τ ≤ t →
      |heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) τ p q|
        ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q :=
    hbound
  have hInt : IterConvIntegrableW (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))
      (2 : ℝ) (0 : ℝ) (C * (1 + T)) :=
    iterConvIntegrableW_of_locally_bound_baseMeas _ (C * (1 + T)) hEzero hEmeas
      (fun T' hT' => ⟨C * (1 + T'), mul_nonneg hC0 (by linarith),
        fun τ p q hτ hτT' => hboundS T' τ p q hτ hτT'⟩)
  obtain ⟨C_L, hCL0, hDom⟩ :=
    leviSeries_dominatedW_le (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))
      (C * (1 + T)) T (mul_nonneg hC0 (by linarith)) hT
      (fun τ p q hτ hτT => hboundS T τ p q hτ hτT) hInt
  refine ⟨C_L, hCL0, ?_⟩
  intro s z hs hsT
  have hb := hDom s z 0 hs hsT
  rw [baseKernelW_zero_apply] at hb
  simpa [sub_zero] using hb

/-- **★★★ J4-1037 (B) — `hBLgauss_capped_window_UNCOND`.**  Composes
    `leviBase_gaussDdim2s_envelope_UNCOND` (at `T := t`) into the EXACT a.e.-in-`s` `hBLgauss` shape
    `HZMassCappedWindowClosed.hzmass_capped_window_closed` consumes — UNCONDITIONALLY, with NO `c < δ₀`
    residue anywhere.  fb's `hBLgauss` compatibility gap is CLOSED.  The FIVE OTHER hypotheses of
    `hzmass_capped_window_closed` (`hint`, `hBFpeak`, `hBLnn`, `hPpknn`, `hPCbound`/`hMnn`) are UNTOUCHED
    and remain exactly as `HZMassCappedWindowClosed.lean` states them; `hBFpeak`'s z-uniform-dominator
    gap REMAINS OPEN.  NOT `a₁ = R/6`. -/
theorem hBLgauss_capped_window_UNCOND (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p))
    (t : ℝ) (m : ℕ) (hepspos : 0 < t - epsSeq m) :
    ∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧
      ∃ C_L : ℝ, 0 ≤ C_L ∧
        ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → ∀ z : Point n,
          leviSeries (heatOp g gi
              (vanVleckGatedWitness g gi hC hK
                (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) a b)) s z 0
            ≤ C_L * gaussDdim (2 * s) z := by
  have htpos : 0 < t := HZMassCappedWindowClosed.t_pos_of_epspos hepspos
  obtain ⟨a, b, c, ha, hab, hbc, C_L, hCL0, hbound⟩ :=
    leviBase_gaussDdim2s_envelope_UNCOND hn g gi hg hC hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
      hgiC hgpos hu hgiMeas hchr t htpos
  refine ⟨a, b, c, ha, hab, hbc, C_L, hCL0, ?_⟩
  refine ae_of_all _ (fun s hs z => ?_)
  obtain ⟨hspos, hgap⟩ := HZMassCappedWindowClosed.window_gap hepspos hs
  have hsleT : s ≤ t := by linarith [epsSeq_pos m]
  exact le_trans (le_abs_self _) (hbound s z hspos hsleT)

end QIQTH.HBLgaussUnconditional

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HBLgaussUnconditional
#print axioms leviBase_gaussDdim2s_envelope_UNCOND
#print axioms hBLgauss_capped_window_UNCOND
end AxiomChecks
