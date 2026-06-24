/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# BORN-A1 — Actuality Projective Consistency (APC)

The Born discriminating premise is effect-algebra additivity (`EffectGleason.EffectMeasure.additive`), which is
"Born in disguise."  This file grounds it in a more primitive, amplitude-free, physically-motivated principle:
**Actuality Projective Consistency** — the actuality selector λ does not signal under outcome-refinement
(its marginals are Kolmogorov-consistent: a coarse outcome's marginal equals the sum of the fine marginals that
merge into it).

Stage 1 (this file, foundation): the **structural** half — an *honest* coarse-graining selector
(`selC = π ∘ selF`, the coarse readout literally coarse-grains the fine one) satisfies APC *automatically*
(`marg_coarseGrain`).  So selector no-signaling under refinement is automatic for genuine refinements; the α=2
rule fails it (`SelectorRefinement.Countermodel.alphaSq_selector_signals`) precisely because its coarse and fine
realizations are NOT genuine refinements of one another — the non-vacuity witness.

Stages 2–3 (next): bridge APC to refinement-additivity of the weight rule (`RefinementBorn.refinementNatural`)
⟹ Born.  Honest limit (plan §4): APC is expected ⟺ additivity at the linear level — a *grounding/reframing*
(Born from selector no-signaling), not a strict from-nothing derivation.

Axiom-free.
-/
import QIQTH.SelectorRefinement
import Mathlib.Tactic

namespace QIQTH.BornActualityConsistency

open QIQTH.SelectorRefinement

/-- **Actuality Projective Consistency (structural).**  For a fine selector `selF : Ω → K'` and a merge map
    `π : K' → K`, the marginal of the coarse-grained readout `π ∘ selF` at a coarse outcome `k` equals the sum
    of the fine marginals over the merge fiber `π⁻¹{k}`.  So a genuine coarse-graining selector's marginals are
    Kolmogorov-consistent under refinement — selector no-signaling, with NO Born input, automatic from the
    coarse-graining structure alone. -/
theorem marg_coarseGrain {Ω K K' : Type*} [Fintype Ω] [Fintype K'] [DecidableEq K] [DecidableEq K']
    (μ : Ω → ℝ) (selF : Ω → K') (π : K' → K) (k : K) :
    marg μ (fun ω => π (selF ω)) k
      = ∑ k' ∈ Finset.univ.filter (fun k' => π k' = k), marg μ selF k' := by
  unfold marg
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.sum_ite_eq (Finset.univ.filter (fun k' => π k' = k)) (selF ω) (fun _ => μ ω)]
  simp [Finset.mem_filter]

end QIQTH.BornActualityConsistency
