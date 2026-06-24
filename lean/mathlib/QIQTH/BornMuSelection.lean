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

end QIQTH.BornMuSelection
