/-
  HLeviBLGaussUnconditionalTriple — J4-1038: `fb`'s `{hBLnn, hBLgauss, hLevi}` triple of
  `MixedEnvelopeAssembly.mixedEnvelope_of_named_carries` CLOSED SIMULTANEOUSLY, UNCONDITIONALLY, at
  Track 2's `BL := CB · gaussDdim(2s)` choice — resolving the `cp999` architectural choice point in
  FAVOR of Track 2, using the UNCONDITIONAL Levi supplier (J4-1037).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}; hCConv is NOT closed here.  No `sorry`,
  no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no
  existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE CHOICE POINT THIS RESOLVES (`cp999`).

  `HZMassCappedWindowClosed.hzmass_capped_window_closed`'s `hBLnn`/`hBLgauss` are stated for an ABSTRACT
  `BL : ℝ → Point n → ℝ`.  `MixedDirectionsFieldHessianEnvelope`'s `hLevi` field is
    `|leviSeries (heatOp g gi (vanVleckGatedWitness … S a b)) s z 0| ≤ BL s z`
  — a DOMINATION bound, never an equality — so `BL` is used PURELY as an upper bound on `|leviSeries|`
  throughout the whole census; nothing downstream (`hzmass`, `magnitude_legs_of_mixedEnvelope`,
  `kPrime_R2prime_magnitude`) ever requires `BL` to literally BE `leviSeries`.  There are two possible
  instantiations of `BL`:
    • Track 1 (`BL := leviSeries` itself) — makes `hBLgauss`/`hLevi` trivial but `hBLnn` demands genuine
      SIGN-nonnegativity `0 ≤ leviSeries(…)` of a signed alternating series, which `cp999` (Sol-confirmed
      with an explicit countermodel) found is NOT obtainable from any banked envelope bound and is
      plausibly FALSE.
    • Track 2 (`BL s z := CB s · gaussDdim (2·s) z`, the ENVELOPE itself) — `hBLnn`/`hBLgauss` are BOTH
      trivial (`mul_nonneg`, `le_refl`); the only remaining question is whether `hLevi`'s LITERAL
      statement can accept this `BL`, i.e. whether `CB · gaussDdim(2s)` DOMINATES `|leviSeries|`.
  It does — `LeviBaseGaussEnvelopeConst`/`HBLgaussUnconditional` already prove exactly this domination
  (as an absolute-value bound, never weakened).  Track 2 is ALREADY the choice `MixedEnvelopeAssembly.
  mixedEnvelope_of_named_carries` (J4-913, banked long before this sub-campaign) uses; the missing piece
  was an UNCONDITIONAL supplier of `hLevi`'s exact a.e.-shape at that same `BL` (the sibling
  `HLeviCappedWindowConst.hLevi_capped_window_CONST`, J4-1036, supplied only the `c < δ₀`-CONDITIONAL
  version).  `HBLgaussUnconditional.leviBase_gaussDdim2s_envelope_UNCOND` (J4-1037) already removed that
  `c < δ₀` residue for the `hBLgauss` consumer — this file re-exports the SAME unconditional supplier
  into `hLevi`'s exact (abs-value-preserving) shape, and packages the resulting UNCONDITIONAL triple.

  ## WHAT LANDS (ns `QIQTH.HLeviBLGaussUnconditionalTriple`).
    • `hLevi_capped_window_UNCOND` — ★★★ `hLevi_capped_window_CONST`'s exact conclusion shape, but
      sourced from the UNCONDITIONAL `leviBase_gaussDdim2s_envelope_UNCOND` — NO `c < δ₀` antecedent
      anywhere in the hypothesis list.
    • `hBLnn_hBLgauss_hLevi_UNCOND_triple` — ★★★ THE SIMULTANEOUS discharge: at the literal
      constant-radius gate and `CB := fun _ => C_L`, ALL THREE of `mixedEnvelope_of_named_carries`'s
      `{hBLnn, hBLgauss, hLevi}` inputs (Track 2's `BL := CB · gaussDdim(2s)`) hold TOGETHER,
      UNCONDITIONALLY — resolving `cp999`'s choice point in favor of Track 2, with the architectural
      "conflict" DISSOLVED (it was an artifact of Track 1's unnecessary choice, never a genuine
      requirement of the consuming structure).

  ## HONEST RESIDUAL (unchanged).  This does NOT touch `hBFpeak` (the z-uniform-dominator gap, confirmed
  hard, `cp996`/`cp999`), nor `hint`/`hcpt`/`hpeak`/`hbint`/`hmeas` (`mixedEnvelope_of_named_carries`'s
  other five carries), nor does it construct a `MixedDirectionsFieldHessianEnvelope` term (that also
  needs `hFd`/`hkint`, which need `hcpt`/`hpeak`/`hbint`/`hmeas`/`hBFpeak`).  `fb` is NOT closed; its
  TRUE remaining obstacle set narrows to `{hBFpeak}` for the `{hBLnn, hBLgauss, hLevi}` sub-package,
  PROVIDED the caller adopts Track 2's `BL` throughout (not Track 1's).  `nb` (near-carry, blocked on
  `hxmem`) is untouched.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HBLgaussUnconditional
import QIQTH.HZMassCappedWindowClosed
import QIQTH.MixedEnvelopeAssembly

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open QIQTH.HeatResidualBound QIQTH.ChartJetXUniformBound
open QIQTH.ConstRadiusGateExport QIQTH.HBLgaussUnconditional
open scoped Topology BigOperators ContDiff

namespace QIQTH.HLeviBLGaussUnconditionalTriple

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — the UNCONDITIONAL `hLevi` export (abs-value KEPT, no `c < δ₀` residue).
    ############################################################################### -/

/-- **★★★ §1 — `hLevi_capped_window_UNCOND`.**  Composes
    `HBLgaussUnconditional.leviBase_gaussDdim2s_envelope_UNCOND` (at `T := t`) into the EXACT a.e.-in-`s`,
    a.e.-in-`z` `hLevi` shape `MixedEnvelopeAssembly.mixedEnvelope_of_named_carries` consumes, on the
    capped window `s ∈ Set.uIoc 0 (t − εₘ)`, at the LITERAL constant-radius gate `S` and `CB s := C_L`
    constant — UNCONDITIONALLY (no `c < δ₀` antecedent anywhere, unlike `HLeviCappedWindowConst.
    hLevi_capped_window_CONST`).  The absolute value is KEPT throughout (unlike `hBLgauss_capped_window_
    UNCOND`, which weakens to one side for its own, different consumer).  NOT `a₁ = R/6`. -/
theorem hLevi_capped_window_UNCOND (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
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
        ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → ∀ᵐ z ∂volume,
          |leviSeries (heatOp g gi
              (vanVleckGatedWitness g gi hC hK
                (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) a b)) s z 0|
            ≤ C_L * gaussDdim (2 * s) z := by
  have htpos : 0 < t := HZMassCappedWindowClosed.t_pos_of_epspos hepspos
  obtain ⟨a, b, c, ha, hab, hbc, C_L, hCL0, hbound⟩ :=
    leviBase_gaussDdim2s_envelope_UNCOND hn g gi hg hC hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
      hgiC hgpos hu hgiMeas hchr t htpos
  refine ⟨a, b, c, ha, hab, hbc, C_L, hCL0, ?_⟩
  refine ae_of_all _ (fun s hs => ?_)
  obtain ⟨hspos, hgap⟩ := HZMassCappedWindowClosed.window_gap hepspos hs
  have hsleT : s ≤ t := by linarith [epsSeq_pos m]
  exact ae_of_all _ (fun z => hbound s z hspos hsleT)

/-! ###############################################################################
    ### §2 — THE SIMULTANEOUS UNCONDITIONAL TRIPLE (`hBLnn`, `hBLgauss`, `hLevi`).
    ############################################################################### -/

/-- **★★★ §2 — `hBLnn_hBLgauss_hLevi_UNCOND_triple`.**  THE SIMULTANEOUS discharge resolving `cp999`'s
    architectural choice point in favor of Track 2.  At the literal constant-radius gate and
    `CB := fun _ => C_L`, ALL THREE of `MixedEnvelopeAssembly.mixedEnvelope_of_named_carries`'s
    `{hBLnn, hBLgauss, hLevi}` inputs hold TOGETHER, UNCONDITIONALLY, for Track 2's
    `BL s z := C_L · gaussDdim (2·s) z`:
      • `hBLnn`    — `0 ≤ C_L · gaussDdim (2·s) z`     (trivial, `mul_nonneg hCL0 (gaussDdim_nonneg _ _)`);
      • `hBLgauss` — `C_L · gaussDdim(2s) z ≤ C_L · gaussDdim(2s) z`  (trivial, `le_refl`);
      • `hLevi`    — `|leviSeries …| ≤ C_L · gaussDdim(2s) z`         (§1, UNCONDITIONAL).
    No `c < δ₀` residue anywhere.  Does NOT construct a full `MixedDirectionsFieldHessianEnvelope` term
    (that also needs `hFd`/`hkint`, hence `hcpt`/`hpeak`/`hbint`/`hmeas`, and separately `hBFpeak`, all
    UNTOUCHED here).  NOT `a₁ = R/6`. -/
theorem hBLnn_hBLgauss_hLevi_UNCOND_triple (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
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
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ∀ z : Point n, 0 ≤ C_L * gaussDdim (2 * s) z)
        ∧ (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ∀ z : Point n, C_L * gaussDdim (2 * s) z ≤ C_L * gaussDdim (2 * s) z)
        ∧ (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → ∀ᵐ z ∂volume,
            |leviSeries (heatOp g gi
                (vanVleckGatedWitness g gi hC hK
                  (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) a b)) s z 0|
              ≤ C_L * gaussDdim (2 * s) z) := by
  obtain ⟨a, b, c, ha, hab, hbc, C_L, hCL0, hLevi⟩ :=
    hLevi_capped_window_UNCOND hn g gi hg hC hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
      hgiC hgpos hu hgiMeas hchr t m hepspos
  refine ⟨a, b, c, ha, hab, hbc, C_L, hCL0, ?_, ?_, hLevi⟩
  · exact ae_of_all _ (fun _ _ z => mul_nonneg hCL0 (gaussDdim_nonneg _ z))
  · exact ae_of_all _ (fun _ _ z => le_refl _)

end QIQTH.HLeviBLGaussUnconditionalTriple

section AxiomChecks
open QIQTH.HLeviBLGaussUnconditionalTriple
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms hLevi_capped_window_UNCOND
#print axioms hBLnn_hBLgauss_hLevi_UNCOND_triple
end AxiomChecks
