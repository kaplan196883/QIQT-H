/-
  WhiteU1R6Conditional — J4-736: THE PIVOT.  `whiteU1 κ hκ hKc q (0) = R/6` DISCHARGED down to
  exactly the whitened-metric SMOOTHNESS frontier — every 2-jet / gauge fact SUPPLIED from banked
  theorems.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE DOES (and does NOT do).

  Everywhere it appears (`WhiteOrder1.whiteChartKernel1_diagonal_a1` :284, `WhiteF1` :394,
  `WhiteF1Reg` :868) the DeWitt value `hu1 : whiteU1 κ hκ hKc q (0) = R/6` is carried as an ASSUMED
  hypothesis.  This file turns it into a THEOREM `whiteU1_eq_ricci6_of_smooth`, CONDITIONAL on
  exactly THREE whitened-chart smoothness antecedents:
    • `hgTop`  — `∀ a b, ContDiff ℝ ⊤ (fun y => ĝ_q y a b)`            (whitened metric ⊤-smoothness);
    • `hgiTop` — `∀ a b, ContDiff ℝ ⊤ (fun y => ĝ⁻¹_q y a b)`          (whitened inverse ⊤-smoothness);
    • `hsrc`   — `ContDiff ℝ ∞ (T̂_q û₀)`                              (transport-source ∞-smoothness),
  where `T̂_q = transportOp (vanVleck ĝ_q) ĝ_q ĝ⁻¹_q` and `û₀ = transportCoeff T̂_q 0`.

  EVERY OTHER hypothesis of the flat DeWitt lemma `VanVleckCancellation.transportCoeff_vanVleck_one_diag`
  (`∞` mirror `OmegaHsrcC4cAudit.transportCoeff_vanVleck_one_diag_infty`) is DISCHARGED here from the
  banked whitened-chart facts:
    • `hg0`  (ĝ_q(0) = δ)              ← `WhiteWitness.whitePullbackMetric_zero`;
    • `hgi`  (ĝ⁻¹_q(0) = δ)            ← `WhiteReplay.whitePullbackMetricInv_zero`;
    • `hdg0` (∂ĝ_q(0) = 0)             ← `WhiteWitness.whitePullbackMetric_pd_zero`;
    • `hΓ`   (Γ[ĝ_q,ĝ⁻¹_q](0) = 0)     ← derived from `hdg0` (the `curvedRNCMetric_christoffel_zero`
                                          pattern: every metric derivative at `0` vanishes);
    • `hgsymm` (ĝ_q symmetric)         ← `WhiteAnnulus.whitePullbackMetric_symm`;
    • `htr`  (the metric-Hessian trace = −(2/3)·Ric) ← `NCRiemannTwoJet.htr_from_hGauss`, fed the
                                          germ Gauss lemma `WhiteGauss.whitePullbackMetric_gauss`
                                          (§2: `ĝ_q(w)·w = w` on a ball — a PROVEN theorem, not a
                                          labelled input).

  So the WHITENED tower's `u₁(0) = R/6` now rests on the SAME residue as the whole whitened program:
  the whitened-chart smoothness antecedents.  Per the repo audit (`AxiomAudit` J4-639) the whitened
  metric is banked only at finite local order (`ContDiffAt`-4 flow chart / `IsC2At` pullback metric);
  GLOBAL `ContDiff ⊤`/`∞` of `ĝ_q` at the whitened chart is the CITED FRONTIER, not discharged.  This
  file isolates that frontier precisely: `hu1` is no longer a free-standing carried value — it is
  REDUCED to `{hgTop, hgiTop, hsrc}`.

  ── WHICH `R`.  The value is `(∑ᵢ ricci ĝ_q ĝ⁻¹_q i i 0) / 6` — the trace of the Ricci tensor of the
  WHITENED chart metric at the chart centre.  Because `ĝ_q(0) = ĝ⁻¹_q(0) = δ` (whitening), this lower-
  index trace `∑ᵢ Ric_{ii}(0)` coincides with the scalar curvature `R = gⁱʲRic_{ij}` at `0`, which is
  the intrinsic scalar curvature of the curved base at the row `q` (RNC/whitening preserve curvature at
  the centre).  So it IS the DeWitt `R/6`.

  ⚠ HONEST FIREWALL.  This is NOT "a₁ = R/6 UNCONDITIONAL".  It is `whiteU1(0) = R/6` CONDITIONAL on
  `{hgTop, hgiTop, hsrc}` — the whitened-chart smoothness frontier.  The downstream a₁ = R/6 program
  additionally owes {h0, h1, hΔ / the C² pair} + the Duhamel-split integrability carry + the fat-`K`
  carrier piles + the capstone co-instantiation + the prior analytic piles.  This brick discharges ONE
  carried value (`hu1`) modulo the smoothness frontier.  No axioms, no `sorry`, no `:= True`.

  NON-VACUITY (cp466).  The three antecedents are jointly SATISFIABLE: the flat DeWitt lemma
  `transportCoeff_vanVleck_one_diag_infty` is exactly the same shape and is inhabited at the flat /
  polynomial `curvedRNCMetric` (banked `curvedRNCMetric_contDiff` gives `ContDiff ⊤`, etc.); at
  `κ = 0` the whitened metric is `δ` (analytic), so `{hgTop, hgiTop, hsrc}` hold there and the conclusion
  fires.  The hypotheses are a SUBSET of the known-inhabited flat antecedent census, so the theorem is
  not a `{0}`-collapse / not vacuous.
-/
import Mathlib
import QIQTH.WhiteGauss
import QIQTH.WhiteAnnulus
import QIQTH.NCRiemannTwoJet
import QIQTH.OmegaHsrcC4cAudit

open Finset Filter Topology MeasureTheory Set
open QIQTH.Curvature QIQTH.VanVleck QIQTH.ParametrixFunction
open QIQTH.HeatKernelA1 QIQTH.HeatTransportRecursion
open QIQTH.WhiteWitness QIQTH.WhiteReplay QIQTH.WhiteAnnulus
open QIQTH.WhiteGauss QIQTH.WhiteOrder1
open QIQTH.NCRiemannTwoJet QIQTH.VanVleckCancellation QIQTH.OmegaHsrcC4cAudit
open QIQTH.CurvedRNCGaussWitness
open scoped BigOperators Topology ContDiff

namespace QIQTH.WhiteU1R6Conditional

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★★★ J4-736 — THE PIVOT: `whiteU1(0) = R/6`, `hu1` DISCHARGED modulo the smoothness frontier.**
    For every `κ ≤ 0`, compact base `K`, row `q ∈ K`, GIVEN the three whitened-chart smoothness
    antecedents `{hgTop, hgiTop, hsrc}` (the CITED FRONTIER; everything else banked), the transported
    first heat coefficient of the whitened chart at the centre is the whitened-metric Ricci trace over
    six:
        `whiteU1 κ hκ hKc q (0) = (∑ᵢ ricci ĝ_q ĝ⁻¹_q i i 0) / 6` .
    The 2-jet / gauge / Gauss-lemma inputs are all supplied from banked theorems (see file header).
    ⚠ CONDITIONAL on `{hgTop, hgiTop, hsrc}` only — NOT `a₁ = R/6` unconditional. -/
theorem whiteU1_eq_ricci6_of_smooth (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset)
    (hgTop : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => whiteMetric κ hκ hKc q y a b))
    (hgiTop : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => whiteMetricInv κ hκ hKc q y a b))
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck (whiteMetric κ hκ hKc q)) (whiteMetric κ hκ hKc q)
        (whiteMetricInv κ hκ hKc q)
        (transportCoeff (transportOp (vanVleck (whiteMetric κ hκ hKc q)) (whiteMetric κ hκ hKc q)
          (whiteMetricInv κ hκ hKc q)) 0))) :
    whiteU1 κ hκ hKc q (0 : Point n)
      = (∑ i, ricci (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q) i i 0) / 6 := by
  -- ── the banked whitened-chart 2-jet / gauge facts.
  have hgsymm : ∀ y a b, whiteMetric κ hκ hKc q y a b = whiteMetric κ hκ hKc q y b a :=
    fun y a b => whitePullbackMetric_symm κ hκ hKc q y a b
  have hg0if : ∀ i j, whiteMetric κ hκ hKc q 0 i j = if i = j then (1 : ℝ) else 0 :=
    fun i j => whitePullbackMetric_zero κ hκ hKc q hq i j
  have hg0mat : ∀ i j, whiteMetric κ hκ hKc q 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    intro i j
    rw [hg0if i j, Matrix.one_apply]
  have hgi0 : ∀ i j, whiteMetricInv κ hκ hKc q 0 i j = if i = j then (1 : ℝ) else 0 :=
    fun i j => whitePullbackMetricInv_zero κ hκ hKc q hq i j
  have hdg0 : ∀ a b e, pd (fun y => whiteMetric κ hκ hKc q y a b) e (0 : Point n) = 0 :=
    fun a b e => whitePullbackMetric_pd_zero κ hκ hKc q hq a b e
  -- ── the Christoffel vanishing at the centre, DERIVED from `hdg0` (the RNC pattern).
  have hΓ : ∀ k i j, christoffel (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q) k i j
      (0 : Point n) = 0 := by
    intro k i j
    simp only [christoffel]
    have hz : (∑ α, whiteMetricInv κ hκ hKc q (0 : Point n) k α *
        (pd (fun y => whiteMetric κ hκ hKc q y α j) i (0 : Point n)
          + pd (fun y => whiteMetric κ hκ hKc q y α i) j (0 : Point n)
          - pd (fun y => whiteMetric κ hκ hKc q y i j) α (0 : Point n))) = 0 := by
      apply Finset.sum_eq_zero
      intro α _
      rw [hdg0, hdg0, hdg0]; ring
    rw [hz, mul_zero]
  -- ── the germ Gauss lemma of the whitened metric, from the PROVEN `whitePullbackMetric_gauss`.
  have hGauss : ∀ i, (fun x => ∑ j, whiteMetric κ hκ hKc q x i j * x j)
      =ᶠ[𝓝 (0 : Point n)] (fun x => x i) := by
    obtain ⟨r, hr0, hgb⟩ := whitePullbackMetric_gauss κ hκ hKc q hq
    intro i
    filter_upwards [Metric.ball_mem_nhds (0 : Point n) hr0] with x hx
    have hxr : ‖x‖ < r := by rwa [Metric.mem_ball, dist_zero_right] at hx
    exact hgb x hxr i
  -- ── the metric-Hessian trace, from `htr_from_hGauss` at the whitened chart.
  have htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => whiteMetric κ hκ hKc q w a a) d y) c 0)
      = -(2 / 3) * ricci (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q) c d 0 :=
    fun c d => htr_from_hGauss (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
      hgTop hgsymm hgiTop hgi0 hdg0 hGauss c d
  -- ── the flat DeWitt cancellation, instantiated at the whitened metric.
  have key := transportCoeff_vanVleck_one_diag_infty (whiteMetric κ hκ hKc q)
    (whiteMetricInv κ hκ hKc q)
    (fun c d => ricci (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q) c d 0)
    hgTop hg0mat hgi0 hΓ hdg0 htr hsrc
  -- `whiteU1 … 0` is DEFINITIONALLY `transportCoeff (transportOp (vanVleck ĝ) ĝ ĝ⁻¹) 1 0`.
  exact key

/-- **★ THE DIAGONAL `a₁` CARRIER, DISCHARGED.**  `WhiteOrder1.whiteChartKernel1_diagonal_a1` with its
    labelled `hu1` now SUPPLIED by `whiteU1_eq_ricci6_of_smooth` (so no free `hu1` remains, only the
    smoothness frontier `{hgTop, hgiTop, hsrc}`):
        `W₁(t,0) = √det g^κ(q) · (4πt)^{−n/2}·(1 + (R/6)·t)`   with `R = ∑ᵢ ricci ĝ_q ĝ⁻¹_q i i 0`.
    ⚠ CONDITIONAL on the smoothness frontier; NOT `a₁ = R/6` unconditional. -/
theorem whiteChartKernel1_diagonal_a1_discharged (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) (t : ℝ)
    (hgTop : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => whiteMetric κ hκ hKc q y a b))
    (hgiTop : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => whiteMetricInv κ hκ hKc q y a b))
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck (whiteMetric κ hκ hKc q)) (whiteMetric κ hκ hKc q)
        (whiteMetricInv κ hκ hKc q)
        (transportCoeff (transportOp (vanVleck (whiteMetric κ hκ hKc q)) (whiteMetric κ hκ hKc q)
          (whiteMetricInv κ hκ hKc q)) 0))) :
    whiteChartKernel1 κ hκ hKc q t (0 : Point n)
      = Real.sqrt (Matrix.det (curvedRNCMetric κ q))
        * ((heatKernel1D t 0) ^ n
            * (1 + (∑ i, ricci (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q) i i 0) / 6 * t)) :=
  whiteChartKernel1_diagonal_a1 κ hκ hKc q hq t
    (∑ i, ricci (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q) i i 0)
    (whiteU1_eq_ricci6_of_smooth κ hκ hKc q hq hgTop hgiTop hsrc)

end QIQTH.WhiteU1R6Conditional

section AxiomChecks
open QIQTH.WhiteU1R6Conditional
#print axioms whiteU1_eq_ricci6_of_smooth
#print axioms whiteChartKernel1_diagonal_a1_discharged
end AxiomChecks
