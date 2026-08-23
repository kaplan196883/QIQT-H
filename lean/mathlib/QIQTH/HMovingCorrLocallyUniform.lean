/-
  HMovingCorrLocallyUniform — J4-1098: promotes `LocUnifDerivConv.movingCorr_tUniform` (L1,
  `TendstoUniformlyOn ... (Icc ta tb)`) to the FULL `TendstoLocallyUniformlyOn ... U` shape that
  `LocUnifDerivConv.hbdryLU_of_movingCorr_frozen`'s `hmovLU` slot (`LocUnifDerivConv.lean:302-304`)
  actually needs, over an OPEN time-set `U ⊆ ℝ`.  Mirrors J4-1097's `HFrozenAILocallyUniform` promotion
  of the SIBLING `hfroLU` slot exactly, `gpt-5.6-sol` (high)-confirmed as a mechanical mirror (no new
  wrapper-level difficulty from the "moving" character — that content is entirely concentrated in the
  `hsupAll` hypothesis, unattempted here at the concrete witness).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  chart-FREE, kernel-agnostic real-analysis WRAPPER (mechanical composition, same pattern as J4-1097).
  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## CONTEXT — the `hmovLU` slot and its relation to the ALREADY-LANDED `movingCorr_tUniform` (L1).

  `LocUnifDerivConv.hbdryLU_of_movingCorr_frozen` needs, as its FIRST input,

      `hmovLU : TendstoLocallyUniformlyOn
          (fun m u => BoundaryTrunc H F m u - ∫ z, H (epsSeq m) 0 z * F u z 0)
          (fun _ => (0 : ℝ)) atTop U`

  where `BoundaryTrunc H F m u := ∫ z, H (u - (u - epsSeq m)) 0 z * F (u - epsSeq m) z 0`, which
  `sub_sub_cancel` (`u - (u - epsSeq m) = epsSeq m`) reduces to
  `∫ z, H (epsSeq m) 0 z * F (u - epsSeq m) z 0`.  Instantiating `movingCorr_tUniform`'s abstract
  triple `(W, fmov, ffro)` as `W τ z := H τ 0 z`, `fmov m u z := F (u - epsSeq m) z 0`,
  `ffro u z := F u z 0` makes its conclusion EXACTLY the `Icc ta tb`-level restriction of `hmovLU`'s
  target (this file's `hsrc` rewrite lemma verifies the match).  `movingCorr_tUniform`'s `hsup`
  hypothesis becomes exactly the TIME-SHIFT closeness statement
  `|F (u - epsSeq m) z 0 - F u z 0| < ε` uniform over `u ∈ Icc ta tb`, `z` in a closed ball — a
  genuinely DIFFERENT hypothesis in KIND from `hfroLU`'s `hlocal` (which concerns `z → 0` at a FIXED
  `u`, not a time shift), already flagged in `movingCorr_tUniform`'s own docstring as satisfied by
  `EnvelopeWiringLocUnif.heine_timeShift_sup_tendsto_tUniform`.

  ## WHAT THIS FILE LANDS.

  `movingCorr_tLocallyUniform` — the exact `hmovLU` target shape:
      `TendstoLocallyUniformlyOn (fun m u => BoundaryTrunc H F m u - ∫ z, H (epsSeq m) 0 z * F u z 0)
        (fun _ => (0 : ℝ)) atTop U`
  for `U` OPEN in `ℝ`, given the SAME `ρ, lam, CW, Cf, τ₀`-parametrised measurability/domination/mass
  hypotheses as `movingCorr_tUniform` (`hWmeas, hfmov_meas, hffro_meas, hfmov_bdd, hffro_bdd, hDom,
  hmass`, all genuinely `ta,tb`-FREE already in `movingCorr_tUniform`) PLUS a window-indexed version of
  `hsup`, `hsupAll`, quantified over EVERY compact window `Icc ta tb ⊆ U` rather than one fixed window
  (the same honest generalization `hlocalAll` used for `hfroLU`, forced by `U` not being compact).

  ROUTE (identical to `HFrozenAILocallyUniform.frozenAI_tLocallyUniform`).  Mathlib's
  `tendstoLocallyUniformlyOn_of_forall_exists_nhds` reduces `TendstoLocallyUniformlyOn F f p U` to:
  every `u₀ ∈ U` has a neighbourhood-within-`U` `t` on which `F → f` uniformly.  `U` open in `ℝ` gives
  (`Metric.isOpen_iff`) a `δ > 0` with `ball u₀ δ ⊆ U`; the closed sub-interval
  `Icc (u₀ - δ/2) (u₀ + δ/2)` is a genuine `𝓝[U] u₀` member and `⊆ U`.  Apply `movingCorr_tUniform` at
  this window with `hsupAll` instantiated there, then rewrite the resulting family
  `fun m u => (∫ z, H(ε_m) 0 z · F(u-ε_m) z 0) - ∫ z, H(ε_m) 0 z · F u z 0` back to the literal
  `hmovLU` shape `fun m u => BoundaryTrunc H F m u - ∫ z, H(ε_m) 0 z · F u z 0` via a single `funext` +
  `simp [BoundaryTrunc, sub_sub_cancel]` global function-equality rewrite (per `gpt-5.6-sol`'s
  robustness recommendation, preferred over a pointwise `TendstoUniformlyOn.congr`).

  `hsupAll` is genuinely satisfiable and is not the conclusion: e.g. whenever `(u,z) ↦ F u z 0` is
  jointly continuous and `epsSeq m → 0`, `u - epsSeq m → u` uniformly on compacts, so ordinary
  Heine–Cantor joint uniform continuity on `Icc ta tb × closedBall 0 ρ` (widened slightly in time to
  absorb the shift) supplies exactly this fact — the SAME abstract-input pattern already used for
  `hlocal`/`hlocalAll`, merely in the time direction, per `movingCorr_tUniform`'s own docstring
  pointer to `EnvelopeWiringLocUnif.heine_timeShift_sup_tendsto_tUniform`.

  ## HONEST REMAINING GAP (NOT closed here).

  `hmovLU` is now discharged AT THE ABSTRACT-`H,F` LEVEL: `hbdryLU_of_movingCorr_frozen`'s FIRST slot
  is fully suppliable from `movingCorr_tLocallyUniform` (mechanical `apply`, once the parameters and
  seven hypotheses are in hand).  Combined with J4-1097's `frozenAI_tLocallyUniform` for `hfroLU`, BOTH
  of `hbdryLU_of_movingCorr_frozen`'s inputs are now discharged at the abstract level — the composer
  itself is now a mechanical `apply` away from `hbdryLUTarget H F U`, GIVEN both witnesses' concrete
  hypothesis bundles.  What remains UNTOUCHED — genuinely open, not attempted here — is supplying
  `hWmeas, hfmov_meas, hffro_meas, hfmov_bdd, hffro_bdd, hDom, hmass, hsupAll` (for `hmovLU`) and the
  six `hfroLU` hypotheses AT THE CONCRETE curved-tower witness (`H := vanVleckGatedWitness …`,
  `F := leviSeries(heatOp …)`): per `gpt-5.6-sol`'s consult, `hsupAll`'s concrete supply is a TIME-SHIFT
  uniform-continuity statement (genuinely distinct in kind from `hlocalAll`'s spatial-at-`z=0`
  statement) and plausibly ALSO needs `uniformInverseChart`/`EnrichedChartBundle` machinery to control
  the shifted-time chart domain, exactly as `hlocalAll`'s concrete supply does — that is a SEPARATE,
  NOT-yet-attempted, later dispatch, and MAY be where the chart wall is finally met for this branch.
  The Section-G census (13 members) also remains untouched.  `a₁ = R/6` remains STRICTLY CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import QIQTH.LocUnifDerivConv

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound QIQTH.ResidueBound
open QIQTH.LeviSeries QIQTH.TrueHeatKernel QIQTH.LocUnifDerivConv
open scoped Topology

namespace QIQTH.HMovingCorrLocallyUniform

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ `movingCorr_tLocallyUniform`.**  The FULL `hmovLU` target: the moving-vs-frozen boundary
    correction converges to `0` LOCALLY UNIFORMLY on an open time-set `U ⊆ ℝ`, promoted from
    `LocUnifDerivConv.movingCorr_tUniform` (L1) by the standard open-set / compact-window wrapper —
    the exact mirror of J4-1097's `HFrozenAILocallyUniform.frozenAI_tLocallyUniform` promotion of the
    sibling `hfroLU` slot.  See file header for the full route and honest scope. ⚠ NOT `a₁ = R/6`. -/
theorem movingCorr_tLocallyUniform
    (H F : ℝ → Point n → Point n → ℝ)
    (U : Set ℝ) (hU : IsOpen U)
    (ρ lam CW Cf τ₀ : ℝ)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ₀ : 0 < τ₀)
    (hWmeas : ∀ τ, AEStronglyMeasurable (fun z => H τ 0 z) volume)
    (hfmov_meas : ∀ (m : ℕ) (u : ℝ), AEStronglyMeasurable (fun z => F (u - epsSeq m) z 0) volume)
    (hffro_meas : ∀ u : ℝ, AEStronglyMeasurable (fun z => F u z 0) volume)
    (hfmov_bdd : ∀ (m : ℕ) (u : ℝ) (z : Point n), |F (u - epsSeq m) z 0| ≤ Cf)
    (hffro_bdd : ∀ (u : ℝ) (z : Point n), |F u z 0| ≤ Cf)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z, |H τ 0 z| ≤ CW * gaussDdim (lam * τ) z)
    (hmass : ∀ᶠ m in atTop, ∫ z, |H (epsSeq m) 0 z| ≤ CW)
    (hsupAll : ∀ ta tb : ℝ, Set.Icc ta tb ⊆ U → ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.closedBall (0 : Point n) ρ, |F (u - epsSeq m) z 0 - F u z 0| < ε) :
    TendstoLocallyUniformlyOn
      (fun m u => BoundaryTrunc H F m u - ∫ z, H (epsSeq m) 0 z * F u z 0)
      (fun _ => (0 : ℝ)) atTop U := by
  -- rewrite the literal `hmovLU` shape into `movingCorr_tUniform`'s instantiated shape.
  have hsrc :
      (fun m u => BoundaryTrunc H F m u - ∫ z, H (epsSeq m) 0 z * F u z 0)
        = (fun (m : ℕ) (u : ℝ) =>
            (∫ z, H (epsSeq m) 0 z * F (u - epsSeq m) z 0) - ∫ z, H (epsSeq m) 0 z * F u z 0) := by
    funext m u
    simp only [BoundaryTrunc, sub_sub_cancel]
  rw [hsrc]
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
  exact movingCorr_tUniform (n := n)
    (W := fun τ z => H τ 0 z) (fmov := fun m u z => F (u - epsSeq m) z 0)
    (ffro := fun u z => F u z 0)
    ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hfmov_meas hffro_meas hfmov_bdd hffro_bdd hDom hmass
    (hsupAll ta tb hIccSub)

end QIQTH.HMovingCorrLocallyUniform

section AxiomChecks
open QIQTH.HMovingCorrLocallyUniform
#print axioms movingCorr_tLocallyUniform
end AxiomChecks
