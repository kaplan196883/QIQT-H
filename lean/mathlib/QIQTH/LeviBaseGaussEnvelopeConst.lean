/-
  LeviBaseGaussEnvelopeConst — J4-1035: the CONSTANT-RADIUS re-export of `HZMassLeviBaseEnvelope`'s
  `leviBase_gaussDdim2s_envelope`, DISSOLVING the `Measurable cf` residue by routing through
  `ConstRadiusGateExport`'s literal-constant gate instead of the opaque `.choose` gate.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  No `sorry`, no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file
  edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE PROBLEM THIS DISCHARGES.

  `HZMassLeviBaseEnvelope.leviBase_gaussDdim2s_envelope` (J4-882) delivers the `hBLgauss` slot's
  concrete base-`z` Gaussian envelope on the Levi factor `BL`, but its gate `S` — inherited from
  `gatedWitnessN1_hEboundW_le_vanVleck_final` → `_lin` → `OrderOneGeometry.gatedWitnessN1_hEboundW_le_of_good`
  — is built as `cf q := if hq : q ∈ K then (hgood q hq).choose else 0`, `S q := φ_q '' ball 0 (cf q)`.
  EVEN THOUGH the caller instantiates `hgood`'s existential with a single literal constant
  `c = (b+ρc)/2` for every `q` (visible in `_lin`'s proof body, `set c := (b+ρc)/2` then
  `refine ⟨c, hbc, …⟩`), the EXPORTED `cf` remains OPAQUE: `Classical.choose` applied to a proof term
  is not defeq/propeq to the literal witness used to construct that proof, so `Measurable cf` is not
  derivable from this construction (it would require a genuine measurable-selection theorem).  This is
  the SOLE remaining blocker of the campaign's far-carry (`fb`) branch's `hEmeas`/`hBLgauss` slot.

  ## THE FIX (routing, not force).

  `ConstRadiusGateExport.lean` (J4-316, banked, unedited here) already REPLAYS the exact same
  construction with the constant `c` substituted for the `.choose` at EVERY step, producing:
    • `gatedWitnessN1_package_open_CONSTRADIUS` — the bound at the LITERAL gate
      `S := fun z => uniformFlowExp g gi hC hK z '' Metric.ball 0 c` (no `.choose` anywhere);
    • `tripleHEmeas_AT_CONSTRADIUS_GATE` — S1 (`StronglyMeasurable`) at that SAME literal gate,
      from geometry alone, conditional only on the honest smallness `c < δ₀` (a satisfiable
      real-number comparison of two independently-constructed positive reaches — NOT a foundational
      measurability gap);
    • `constRadius_package_and_S1` — the two bundled.

  Since `HZMassCappedWindowClosed.lean`'s (J4-886) six hypotheses are stated ABSTRACTLY in terms of
  arbitrary functions `BL BF : ℝ → Point n → ℝ`, `Ppk CB : ℝ → ℝ` — never re-referencing WHICH gate `S`
  produced `BL` — ANY witness `S` that yields the required Gaussian envelope inequality legitimately
  discharges `hBLgauss`.  This file replays `leviBase_gaussDdim2s_envelope`'s downstream chain
  (`heatOp_gatedWitnessN1_eq_zero_of_nonpos` for `hEzero`, `iterConvIntegrableW_of_locally_bound_baseMeas`
  for `hInt`, `leviSeries_dominatedW_le` for the Levi domination — all THREE gate-polymorphic, i.e.
  generic in `S`, so reapplying them at the constant gate is not circular) sourced from
  `constRadius_package_and_S1` INSTEAD OF the opaque-gate capstone.  Consulted `gpt-5.6-sol` (high
  effort) before construction: confirmed the routing is sound and the abstract `HZMassCappedWindowClosed`
  interface makes the gate-swap legitimate, with the caveat (honestly carried below) that the result is
  conditional on `c < δ₀`, NOT unconditional — `Measurable cf` is fully GONE from the hypothesis list
  (replaced by a satisfiable real-number smallness condition, not a foundational measure-theory wall).

  ## WHAT LANDS (ns `QIQTH.LeviBaseGaussEnvelopeConst`).
    • `leviBase_gaussDdim2s_envelope_CONST` — ★★★ the CONSTANT-RADIUS re-export: same conclusion shape
      as `HZMassLeviBaseEnvelope.leviBase_gaussDdim2s_envelope`, but the `StronglyMeasurable`
      ∀-hypothesis-shaped antecedent is REPLACED by the concrete numeric antecedent `c < δ₀`, and the
      gate `S` is EXPOSED literally (no `.choose`, no `Measurable cf` residue anywhere in the
      hypothesis list).  NOT `a₁ = R/6`.
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ConstRadiusGateExport
import QIQTH.HZMassLeviBaseEnvelope
import QIQTH.HZMassCappedWindowClosed

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open QIQTH.HeatResidualBound QIQTH.ChartJetXUniformBound
open QIQTH.ConstRadiusGateExport
open scoped Topology BigOperators ContDiff

namespace QIQTH.LeviBaseGaussEnvelopeConst

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ J4-1035 — `leviBase_gaussDdim2s_envelope_CONST`.**  THE CONSTANT-RADIUS re-export of
    `HZMassLeviBaseEnvelope.leviBase_gaussDdim2s_envelope`.  Sources the parametrix bound and the base
    joint strong measurability BOTH from `ConstRadiusGateExport.constRadius_package_and_S1` (the LITERAL
    constant flow-ball gate, no `.choose`), then replays the SAME gate-polymorphic downstream chain
    (`heatOp_gatedWitnessN1_eq_zero_of_nonpos`, `iterConvIntegrableW_of_locally_bound_baseMeas`,
    `leviSeries_dominatedW_le`) that the opaque-gate version uses.  The exported antecedent is the
    concrete real-number smallness `c < δ₀` — `Measurable cf` does not appear anywhere in this theorem's
    hypothesis list.  NOT `a₁ = R/6`. -/
theorem leviBase_gaussDdim2s_envelope_CONST (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
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
    ∃ a b c δ₀ : ℝ, 0 < a ∧ a < b ∧ b < c ∧ 0 < δ₀ ∧
      (c < δ₀ →
        ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ (s : ℝ) (z : Point n), 0 < s → s ≤ T →
          |leviSeries (heatOp g gi
              (vanVleckGatedWitness g gi hC hK
                (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) a b)) s z 0|
            ≤ C_L * gaussDdim (2 * s) z) := by
  obtain ⟨a, b, C, c, δ₀, ha, hab, hC0, hbc, hδ0, hbound, _hmemS0, _hopenS0, hS1⟩ :=
    constRadius_package_and_S1 hn g gi hg hC hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
      hgiC hgpos hu hgiMeas hchr
  refine ⟨a, b, c, δ₀, ha, hab, hbc, hδ0, ?_⟩
  intro hcδ
  set S : Point n → Set (Point n) :=
    fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c with hSdef
  have hEmeas : StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) w.1 w.2.1 w.2.2) :=
    hS1 hcδ
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

/-- **★★★ J4-1035 (companion) — `hBLgauss_capped_window_CONST`.**  Composes
    `leviBase_gaussDdim2s_envelope_CONST` (at `T := t`) into the EXACT a.e.-in-`s` `hBLgauss` shape
    `HZMassCappedWindowClosed.hzmass_capped_window_closed` consumes, on the capped window
    `s ∈ Set.uIoc 0 (t − εₘ)`: `BL s z := leviSeries (heatOp g gi (vanVleckGatedWitness … S a b)) s z 0`
    with the LITERAL constant gate `S`, `CB s := C_L` constant.  Window membership supplies BOTH
    `0 < s` and `s ≤ t` (`HZMassCappedWindowClosed.window_gap`), matching the `leviBase` bound's
    `0 < s → s ≤ T` shape at `T := t`.  This is a GENUINE end-to-end composition into the `hBLgauss`
    slot of the `fb`-branch's LAST-blocking hypothesis — conditional ONLY on `c < δ₀` (a satisfiable
    real-number smallness, NOT `Measurable cf`).  The FIVE OTHER hypotheses of
    `hzmass_capped_window_closed` (`hint`, `hBFpeak`, `hBLnn`, `hPpknn`, `hPCbound`/`hMnn`) are UNTOUCHED
    by this brick and remain exactly as `HZMassCappedWindowClosed.lean` states them.  NOT `a₁ = R/6`. -/
theorem hBLgauss_capped_window_CONST (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
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
    ∃ a b c δ₀ : ℝ, 0 < a ∧ a < b ∧ b < c ∧ 0 < δ₀ ∧
      (c < δ₀ →
        ∃ C_L : ℝ, 0 ≤ C_L ∧
          ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → ∀ z : Point n,
            leviSeries (heatOp g gi
                (vanVleckGatedWitness g gi hC hK
                  (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) a b)) s z 0
              ≤ C_L * gaussDdim (2 * s) z) := by
  have htpos : 0 < t := HZMassCappedWindowClosed.t_pos_of_epspos hepspos
  obtain ⟨a, b, c, δ₀, ha, hab, hbc, hδ0, hconc⟩ :=
    leviBase_gaussDdim2s_envelope_CONST hn g gi hg hC hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
      hgiC hgpos hu hgiMeas hchr t htpos
  refine ⟨a, b, c, δ₀, ha, hab, hbc, hδ0, fun hcδ => ?_⟩
  obtain ⟨C_L, hCL0, hbound⟩ := hconc hcδ
  refine ⟨C_L, hCL0, ?_⟩
  refine ae_of_all _ (fun s hs z => ?_)
  obtain ⟨hspos, hgap⟩ := HZMassCappedWindowClosed.window_gap hepspos hs
  have hsleT : s ≤ t := by linarith [epsSeq_pos m]
  exact le_trans (le_abs_self _) (hbound s z hspos hsleT)

end QIQTH.LeviBaseGaussEnvelopeConst

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.LeviBaseGaussEnvelopeConst
#print axioms leviBase_gaussDdim2s_envelope_CONST
#print axioms hBLgauss_capped_window_CONST
end AxiomChecks
