/-
  HFrozenAILocallyUniform — J4-1097: promotes J4-1096's `frozenAI_tUniform` (`HFrozenAIUniform.lean`,
  `TendstoUniformlyOn ... (Icc ta tb)`) to the FULL `TendstoLocallyUniformlyOn ... U` shape that
  `LocUnifDerivConv.hbdryLU_of_movingCorr_frozen`'s `hfroLU` slot (`LocUnifDerivConv.lean:305-307`)
  actually needs, over an OPEN time-set `U ⊆ ℝ`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  chart-FREE, kernel-agnostic real-analysis WRAPPER (mechanical composition, per J4-1096's own
  "standard wrapper" characterization of this exact gap).  No `sorry` (header prose excepted), no new
  axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially
  yielding) the conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE LANDS.

  `frozenAI_tLocallyUniform` — the exact `hfroLU` target shape:
      `TendstoLocallyUniformlyOn (fun m u => ∫ z, H (epsSeq m) 0 z * F u z 0) (fun u => F u 0 0)
        atTop U`
  for `U` OPEN in `ℝ`, given the SAME five analytic inputs as `frozenAI_tUniform`
  (`hHmeas, hFmeas, hFbdd, hDom, hmass1`, all genuinely `ta,tb`-FREE already in J4-1096) PLUS a
  window-indexed version of `hlocal`, `hlocalAll`, quantified over EVERY compact window `Icc ta tb ⊆ U`
  rather than one fixed window (the honest generalization forced by `U` not being compact itself).

  ROUTE.  Mathlib's `tendstoLocallyUniformlyOn_of_forall_exists_nhds` reduces
  `TendstoLocallyUniformlyOn F f p U` to: every `u₀ ∈ U` has a neighbourhood-within-`U` `t` on which
  `F` → `f` uniformly.  Since `U` is open in `ℝ` (`Metric.isOpen_iff`), pick `δ > 0` with
  `ball u₀ δ ⊆ U`; the closed sub-interval `Icc (u₀ - δ/2) (u₀ + δ/2)` is then (a) a genuine `𝓝 u₀`
  member (`Icc_mem_nhds`, since `u₀ - δ/2 < u₀ < u₀ + δ/2`), hence a `𝓝[U] u₀` member, and (b) `⊆ U`
  (it sits inside `ball u₀ δ`).  Apply `frozenAI_tUniform` at this window with `hlocalAll` instantiated
  there.  This is the FULL "standard wrapper" flagged as gap (i) in J4-1096's honest-gaps list; gap (ii)
  (supplying the six hypotheses at the concrete curved-tower witness) is UNTOUCHED here.

  `hlocalAll` is genuinely satisfiable and is not the conclusion: e.g. whenever `(u,z) ↦ F u z 0` is
  jointly continuous on `ℝ × Point n` (or merely on `U × closedBall 0 r₀` for arbitrarily large `r₀`),
  Heine–Cantor on each compact `Icc ta tb × closedBall 0 r₀` supplies exactly this fact — precisely the
  same abstract-input pattern `frozenAI_tUniform`'s own `hlocal` already used (cf. that file's docstring
  discussion of `EnvelopeWiringLocUnif.heine_timeShift_sup_tendsto_tUniform`), merely requantified over
  all windows instead of one fixed window.

  ## HONEST REMAINING GAP (NOT closed here).

  `hfroLU` is now discharged AT THE ABSTRACT-`H,F` LEVEL: `hbdryLU_of_movingCorr_frozen`'s second slot
  is fully suppliable from `frozenAI_tLocallyUniform` (mechanical `apply`, once the six hypotheses are
  in hand).  What remains UNTOUCHED — genuinely open, not attempted here — is supplying `hHmeas, hFmeas,
  hFbdd, hDom, hmass1, hlocalAll` AT THE CONCRETE curved-tower witness (`H := vanVleckGatedWitness …`,
  `F := leviSeries(heatOp …)`): per `HFrozenAIUniform`'s own header and `LocUnifDerivConv`'s L2
  discussion, the concrete `hlocal`/`hmass1` supply for the CONCRETE chart-built witness plausibly DOES
  need `uniformInverseChart`/`EnrichedChartBundle` machinery, exactly as
  `GateAnnulusSplit.chartImage_approx_identity_final` already needed for the single-fixed-`f` case —
  that is a SEPARATE, NOT-yet-attempted, later dispatch, and MAY be where the chart wall is finally met
  for this branch.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
  NOT `a₁ = R/6`.
-/
import QIQTH.HFrozenAIUniform

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound QIQTH.ResidueBound
open QIQTH.LeviSeries QIQTH.TrueHeatKernel QIQTH.HFrozenAIUniform
open scoped Topology

namespace QIQTH.HFrozenAILocallyUniform

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ `frozenAI_tLocallyUniform`.**  The FULL `hfroLU` target: the frozen approximate identity
    converges to `u ↦ F u 0 0` LOCALLY UNIFORMLY on an open time-set `U ⊆ ℝ`, promoted from J4-1096's
    `HFrozenAIUniform.frozenAI_tUniform` by the standard open-set / compact-window wrapper.  See file
    header for the full route and honest scope. ⚠ NOT `a₁ = R/6`. -/
theorem frozenAI_tLocallyUniform
    (H F : ℝ → Point n → Point n → ℝ)
    (U : Set ℝ) (hU : IsOpen U)
    (lam CW Cf τ₀ : ℝ)
    (hlam : 0 < lam) (hCW : 0 ≤ CW) (hCf : 0 ≤ Cf) (hτ₀ : 0 < τ₀)
    (hHmeas : ∀ m : ℕ, AEStronglyMeasurable (fun z => H (epsSeq m) 0 z) volume)
    (hFmeas : ∀ u : ℝ, AEStronglyMeasurable (fun z => F u z 0) volume)
    (hFbdd : ∀ u z, |F u z 0| ≤ Cf)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z, |H τ 0 z| ≤ CW * gaussDdim (lam * τ) z)
    (hmass1 : Tendsto (fun m => ∫ z, H (epsSeq m) 0 z) atTop (𝓝 (1 : ℝ)))
    (hlocalAll : ∀ ta tb : ℝ, Set.Icc ta tb ⊆ U → ∀ ε : ℝ, 0 < ε → ∃ r > 0, ∀ u ∈ Set.Icc ta tb,
        ∀ z : Point n, ‖z‖ < r → |F u z 0 - F u 0 0| < ε) :
    TendstoLocallyUniformlyOn
      (fun m u => ∫ z, H (epsSeq m) 0 z * F u z 0)
      (fun u => F u 0 0) atTop U := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro u₀ hu₀
  obtain ⟨δ, hδ, hballU⟩ := Metric.isOpen_iff.mp hU u₀ hu₀
  set ta := u₀ - δ / 2 with hta
  set tb := u₀ + δ / 2 with htb
  have hIccSub : Set.Icc ta tb ⊆ U := by
    intro x hx
    apply hballU
    rw [Metric.mem_ball, Real.dist_eq]
    obtain ⟨h1, h2⟩ := hx
    rw [abs_lt]
    refine ⟨?_, ?_⟩
    · linarith [hta]
    · linarith [htb]
  refine ⟨Set.Icc ta tb, mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith) (by linarith)), ?_⟩
  exact frozenAI_tUniform H F ta tb lam CW Cf τ₀ hlam hCW hCf hτ₀ hHmeas hFmeas hFbdd hDom hmass1
    (hlocalAll ta tb hIccSub)

end QIQTH.HFrozenAILocallyUniform

section AxiomChecks
open QIQTH.HFrozenAILocallyUniform
#print axioms frozenAI_tLocallyUniform
end AxiomChecks
