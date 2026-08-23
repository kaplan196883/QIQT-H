/-
  HLeviCappedWindowConst — J4-1036: composing the ALREADY-BANKED constant-radius Levi absolute-value
  envelope (`LeviBaseGaussEnvelopeConst.leviBase_gaussDdim2s_envelope_CONST`, J4-1035) into the EXACT
  `hLevi` shape consumed by `MixedEnvelopeAssembly.mixedEnvelope_of_named_carries`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  No `sorry`, no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file
  edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE PROBLEM THIS DISCHARGES.

  `MixedEnvelopeAssembly.mixedEnvelope_of_named_carries`'s `hLevi` slot has the EXACT type
    `∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t − εₘ) → ∀ᵐ z ∂volume,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
          ≤ CB s · gaussDdim (2·s) z`,
  i.e. an ABSOLUTE-VALUE bound on the signed Levi series `leviSeries = Σ (−1)^(k+1) E^{*(k+1)}`, for a
  GENERIC gate `S` and GENERIC coefficient `CB : ℝ → ℝ`.  A prior audit (session checkpoint cp996)
  flagged this as an apparently-open coupling: `hBLnn` (`HZMassCappedWindowClosed`'s Levi-nonnegativity
  slot) shares its coefficient `CB := C_L` with `hLevi`, and cp996's investigation of the LOCAL
  `hBLgauss_capped_window_CONST` composition (which explicitly WEAKENS an absolute-value bound down to
  one side via `le_trans (le_abs_self _) _` for the DIFFERENT `hBLgauss` consumer) left the impression
  that only a one-sided bound was banked anywhere for `leviSeries`.

  THE RESOLUTION (routing, not new estimation).  The UNDERLYING supplier
  `LeviBaseGaussEnvelopeConst.leviBase_gaussDdim2s_envelope_CONST` (J4-1035, banked, unedited here)
  ALREADY delivers the absolute-value form directly (it is sourced from `GatedWitnessPackage`'s
  `leviSeries_dominatedW_le`, whose conclusion is literally `|leviSeries E τ p q| ≤ C_L · baseKernelW …`
  — a genuine two-sided bound, never weakened at that stage).  `hBLgauss_capped_window_CONST` merely
  drops the extra strength it does not need for its OWN (one-sided) consumer; the abs-value form was
  never lost, only unexported in `hLevi`'s exact shape.  This file supplies that missing export: compose
  `leviBase_gaussDdim2s_envelope_CONST` (at `T := t`) with `HZMassCappedWindowClosed.window_gap` (which
  supplies `0 < s` and `s ≤ t` from window membership) WITHOUT discarding the absolute value, and lift
  the resulting `∀ z` bound to `∀ᵐ z ∂volume` via `ae_of_all` (a pointwise bound is always eventually
  true).  Consulted `gpt-5.6-sol` (high effort) before construction: confirmed the banked abs-value
  conclusion is exactly sufficient, `∀ z → ∀ᵐ z` is immediate via `ae_of_all` with no measurability
  side-condition, and the composition is genuine (not vacuous/circular) — reducing `hLevi`'s dependence
  on `C_L`/`CB` to the SAME already-identified `c < δ₀` conditional residue that `hBLgauss` already
  carries, NOT a new independent blocker.

  ## WHAT LANDS (ns `QIQTH.HLeviCappedWindowConst`).
    • `hLevi_capped_window_CONST` — ★★★ the EXACT `hLevi` shape of
      `MixedEnvelopeAssembly.mixedEnvelope_of_named_carries`, at the literal constant-radius gate
      `S := fun z => uniformFlowExp g gi hC hK z '' Metric.ball 0 c` and `CB := fun _ => C_L`,
      conditional ONLY on the same `c < δ₀` real-number smallness `hBLgauss_capped_window_CONST` carries
      (NOT `Measurable cf`, NOT a fresh nonnegativity fact about `leviSeries`).  NOT `a₁ = R/6`.

  ## SCOPE, HONESTLY.  This discharges `hLevi` ONLY at the literal constant gate, and ONLY conditional
  on `c < δ₀` — it does NOT discharge `hBLnn` (which needs GENUINE nonnegativity `0 ≤ leviSeries(...)`,
  a DIFFERENT and much stronger fact about a signed alternating series that this abs-value bound cannot
  supply; `hBLnn` remains open wherever `BL` is instantiated directly to `leviSeries`, though
  `MixedEnvelopeAssembly` itself sidesteps this by choosing `BL := CB·gaussDdim(2s)`, NOT `leviSeries`
  itself, for its OWN `hBLnn`/`hzmass` slots).  It does NOT touch `hBLgauss`'s remaining `c < δ₀`
  satisfiability gap, nor `hBFpeak`'s z-uniform-dominator gap.  `fb`'s TRUE remaining obstacle set is
  UNCHANGED in kind: {hBLgauss's `c < δ₀` compatibility gap, hBFpeak's z-uniform-dominator gap}; `hLevi`
  is REMOVED from the open list (it collapses into the `c < δ₀` residue, not an independent gap).
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.LeviBaseGaussEnvelopeConst
import QIQTH.HZMassCappedWindowClosed

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open QIQTH.HeatResidualBound QIQTH.ChartJetXUniformBound
open QIQTH.ConstRadiusGateExport QIQTH.LeviBaseGaussEnvelopeConst
open scoped Topology BigOperators ContDiff

namespace QIQTH.HLeviCappedWindowConst

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ J4-1036 — `hLevi_capped_window_CONST`.**  Composes
    `LeviBaseGaussEnvelopeConst.leviBase_gaussDdim2s_envelope_CONST` (at `T := t`) into the EXACT
    a.e.-in-`s`, a.e.-in-`z` `hLevi` shape `MixedEnvelopeAssembly.mixedEnvelope_of_named_carries`
    consumes, on the capped window `s ∈ Set.uIoc 0 (t − εₘ)`: at the LITERAL constant gate `S` and
    `CB s := C_L` constant, the ABSOLUTE-VALUE bound
      `|leviSeries (heatOp g gi (vanVleckGatedWitness … S a b)) s z 0| ≤ C_L · gaussDdim (2·s) z`
    holds `∀ᵐ s`, `∀ᵐ z` on the window.  Window membership supplies BOTH `0 < s` and `s ≤ t`
    (`HZMassCappedWindowClosed.window_gap`), matching the `leviBase` bound's `0 < s → s ≤ T` shape at
    `T := t`; the absolute value is KEPT throughout (unlike `hBLgauss_capped_window_CONST`, which
    weakens to one side for its own, different consumer).  Conditional ONLY on `c < δ₀` — `Measurable
    cf` does not appear anywhere in this theorem's hypothesis list, and no fresh nonnegativity fact
    about `leviSeries` is claimed or needed.  NOT `a₁ = R/6`. -/
theorem hLevi_capped_window_CONST (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
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
          ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → ∀ᵐ z ∂volume,
            |leviSeries (heatOp g gi
                (vanVleckGatedWitness g gi hC hK
                  (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) a b)) s z 0|
              ≤ C_L * gaussDdim (2 * s) z) := by
  have htpos : 0 < t := HZMassCappedWindowClosed.t_pos_of_epspos hepspos
  obtain ⟨a, b, c, δ₀, ha, hab, hbc, hδ0, hconc⟩ :=
    leviBase_gaussDdim2s_envelope_CONST hn g gi hg hC hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
      hgiC hgpos hu hgiMeas hchr t htpos
  refine ⟨a, b, c, δ₀, ha, hab, hbc, hδ0, fun hcδ => ?_⟩
  obtain ⟨C_L, hCL0, hbound⟩ := hconc hcδ
  refine ⟨C_L, hCL0, ?_⟩
  refine ae_of_all _ (fun s hs => ?_)
  obtain ⟨hspos, hgap⟩ := HZMassCappedWindowClosed.window_gap hepspos hs
  have hsleT : s ≤ t := by linarith [epsSeq_pos m]
  exact ae_of_all _ (fun z => hbound s z hspos hsleT)

end QIQTH.HLeviCappedWindowConst

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HLeviCappedWindowConst
#print axioms hLevi_capped_window_CONST
end AxiomChecks
