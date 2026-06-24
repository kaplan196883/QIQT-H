/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# BORN-C — μ-selection from refinement equivariance

The no-go theorems (`NoBornFromNothing`) prove decoherence + holographic structure UNDERDETERMINE the typicality
measure μ.  This file grounds the **μ-SELECTION** in a physically-motivated, amplitude-free principle —
**refinement equivariance** (the typicality measure is preserved by the refinement dynamics; the
Dürr–Goldstein–Zanghì quantum-equilibrium / Valentini condition) — and connects it to selector no-signaling, the
bridge to Born (via `BORN-A1`).

Stage 1 (this file, setup): the selection principle, the canonical (uniform/quantum-equilibrium) measure is
equivariant, and **equivariance ⟹ selector no-signaling** (restating `equivariant_marg_invariant` in the
selection vocabulary).  Stage 2 (next): equivariance ⟹ Born (compose with `BORN-A1.apc_iff_positiveAdditive`).

Honest limit (plan §2, mirroring BORN-A1): some selection principle MUST be assumed — equivariance is the
physically-motivated choice, a GROUNDING of μ-selection, not a from-nothing derivation.  Axiom-free.
-/
import QIQTH.SelectorRefinement
import QIQTH.NoBornFromNothing
import QIQTH.BornRoutes
import Mathlib.Tactic

namespace QIQTH.BornMuSelection

open QIQTH.SelectorRefinement

/-- A typicality measure `μ` is **refinement-equivariant** under a refinement dynamics `R` if `R` preserves it
    (`μ ∘ R = μ`) — the Dürr–Goldstein–Zanghì quantum-equilibrium condition, stated amplitude-free. -/
def Equivariant {Ω : Type*} (μ : Ω → ℝ) (R : Ω ≃ Ω) : Prop := ∀ ω, μ (R ω) = μ ω

/-- The **uniform (equiprobable) typicality measure** is equivariant under EVERY refinement bijection — the
    canonical quantum-equilibrium measure. -/
theorem uniform_equivariant {Ω : Type*} (c : ℝ) (R : Ω ≃ Ω) :
    Equivariant (fun _ => c) R := fun _ => rfl

/-- **Equivariance ⟹ selector no-signaling.**  A refinement preserving the typicality measure leaves every
    local-readout marginal invariant — the selection-side no-signaling, with NO Born input (restates
    `equivariant_marg_invariant` in the selection vocabulary; the bridge to Born via BORN-A1). -/
theorem equivariant_no_signaling {Ω K : Type*} [Fintype Ω] [DecidableEq K]
    (μ : Ω → ℝ) (XL : Ω → K) (R : Ω ≃ Ω) (hR : Equivariant μ R) (k : K) :
    marg μ (fun ω => XL (R ω)) k = marg μ XL k :=
  equivariant_marg_invariant μ XL R hR k

/-- **★ Stage 2 — equivariance ⟹ context-independent marginals (the kinematic selection).**  For an
    equivariant typicality measure, a selector and its image under the equivariant refinement `R` have the
    SAME outcome marginal (the *whole* marginal function, not just per-outcome).  So the equivariant
    (quantum-equilibrium) measure has **no preferred refinement** — its outcome statistics are
    **non-contextual**.  Non-contextuality is exactly the Born-strength premise consumed by
    `BornJoinGleason.finite_noCollapseBorn_fromNoncontextuality` (and, on the rule side, ⟺ additivity ⟺ Born
    via `BORN-A1.apc_iff_positiveAdditive`).  So **equivariance GROUNDS the Born selection** — μ-selection is
    relocated to the physically-motivated quantum-equilibrium condition.  Per plan §2 this is a *grounding*:
    closing "context-independence ⟹ Born" rigorously is the same additivity bridge BORN-A1 showed is logically
    equivalent, not a strictly weaker from-nothing derivation. -/
theorem equivariant_context_independent {Ω K : Type*} [Fintype Ω] [DecidableEq K]
    (μ : Ω → ℝ) (XL : Ω → K) (R : Ω ≃ Ω) (hR : Equivariant μ R) :
    marg μ (fun ω => XL (R ω)) = marg μ XL :=
  funext (fun k => equivariant_no_signaling μ XL R hR k)

/-! ### Stage 3 — the underdetermination bracket + the dynamical (martingale) selection.

These tie the kinematic grounding (equivariance, Stage 2) to the two-sided selection picture: WITHOUT a
principle μ is underdetermined; WITH a physically-motivated principle (equivariance, *or* the dynamical
martingale conservation) Born is selected; and the α=2 (non-equivariant) rule SIGNALS under refinement
(`BornRoutes.sqRule_refinement_signals`) — so the principle is a genuine, non-vacuous discriminator. -/

/-- **Underdetermination (the no-go bracket).**  WITHOUT a selection principle, the structural axioms realize
    ANY outcome distribution `p` — μ is underdetermined (restates `NoBornFromNothing.any_anti_born_realizable`
    in the selection vocabulary). -/
theorem mu_underdetermined {Γ Outcome : Type*} [Fintype Γ] [Fintype Outcome]
    (outcome : Γ → Outcome) (h_surj : Function.Surjective outcome)
    (p : Outcome → ℝ) (hp_nn : ∀ k, 0 ≤ p k) (hp_sum : ∑ k, p k = 1) :
    ∃ μ : Γ → ℝ, ∀ k, QIQTH.NoBornFromNothing.outcomeMarginal outcome μ k = p k :=
  QIQTH.NoBornFromNothing.any_anti_born_realizable outcome h_surj p hp_nn hp_sum

/-- **The dynamical (martingale) selection.**  WITH squared-weight conservation in μ-expectation + an absorbing
    record, the μ-probability of an outcome equals its Born weight `wk` — a second, independent grounding of
    μ-selection (the GRW/CSL / optional-stopping mechanism; restates `BornRoutes.born_from_martingale`). -/
theorem mu_selection_martingale {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (W0 WT : Ω → ℝ)
    (k : Ω → Prop) [DecidablePred k] (wk : ℝ) (hμ : ∑ ω, μ ω = 1)
    (hW0 : ∀ ω, W0 ω = wk) (hWT : ∀ ω, WT ω = if k ω then 1 else 0)
    (hmart : ∑ ω, μ ω * WT ω = ∑ ω, μ ω * W0 ω) :
    (∑ ω, if k ω then μ ω else 0) = wk :=
  QIQTH.BornRoutes.born_from_martingale μ W0 WT k wk hμ hW0 hWT hmart

end QIQTH.BornMuSelection
