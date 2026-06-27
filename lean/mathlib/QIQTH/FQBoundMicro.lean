/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# P4-MICRO — the holographic area floor as a COROLLARY of the finite-microstate postulate

P4's deliverable is the holographic area floor `S(ρ_R) ≤ A/4ℓ_P²`.  The campaign's **Route 1** derives it from the
crossed-product Type II construction (the dual-weight trace `τ∘θ_s = e^{−s}τ` + JLMS), which explains *why the bound
is the area* but rests on a genuine multi-year Mathlib-grade frontier.  **Route 2 (P4-MICRO)** postulates the
*microstate count* directly — the finite quantized capacity that is the literal "QI" core of QIQT-H — and the area
floor falls out of an **already-proven finite theorem**:

  `P4-MICRO :  log |𝓗_R| = A/4ℓ_P²`   (the region has a finite effective dimension; its log = the area term)
  `        +  S(ρ) ≤ log |𝓗_R|`        (`shannon_le_log_card`, axiom-free — Jensen/Gibbs)
  `        ⟹  S(ρ_R) ≤ A/4ℓ_P²`        (P4, now a COROLLARY)

So P4 stops being an independent postulate and becomes a theorem *conditional on the framework's own finite-capacity
postulate* — on-thesis: the same finite-`Q_max` move that removes the collapse postulate now also retires the
area-law postulate.  This file lands the core corollary (`area_floor_of_microstate`) via the `MicrostatePostulate`
typeclass, mirroring the `Phase5Master`/`DonaldSystem` interface discipline that kept the QIQT-H core axiom-free.

HONEST SCOPE.  The value of `G` / the edge normalization `⟨A_edge⟩ = A/4ℓ_P²` is the **carried UV datum**: the
`capacity` equation contains the dimensionful area term, but its coefficient is a **free real parameter**, never
assigned a value.  The pivot RELOCATES where the datum sits (macroscopic entropy postulate → microscopic counting
postulate); it does NOT derive the value of `G`.  `P4-MICRO` is a **typeclass hypothesis, not a Lean `axiom`** (the
budget stays 0).  Route 2 does NOT reproduce Route 1's modular-origin explanation of *why area* — the holographic
input `log|𝓗_R| ∝ A` is assumed here and stays the labelled open frontier (the Type II dual-weight trace).  The
`1/4` *ratio* is derived elsewhere (`SakharovRatio`); it is not re-asserted here.  Free scalar only; no `sorry`.
-/
import QIQTH.RecordContract

namespace QIQTH

/-- **P4-MICRO** — the finite-microstate (quantized-information) postulate for a region `R`.
    `R` has a finite effective Hilbert space (`Fintype R`) whose log-dimension equals the area term:
    `capacity : log|𝓗_R| = areaTerm`.  This is the **holographic** input `log|𝓗_R| = A/4ℓ_P²`; the area
    coefficient is the carried UV datum (a free real parameter, never assigned).  Carried as a *typeclass
    hypothesis*, never as a Lean `axiom` — the budget stays 0. -/
class MicrostatePostulate (R : Type*) [Fintype R] (areaTerm : ℝ) where
  /-- The holographic capacity equation `log|𝓗_R| = areaTerm` (`= A/4ℓ_P²`, the carried UV datum). -/
  capacity : Real.log (Fintype.card R) = areaTerm

/-- **★★★ P4's holographic area floor as a COROLLARY of P4-MICRO.**  For any Born record law `p` on the finite
    microstate set `R` (nonnegative weights summing to `1`), the Shannon entropy is at most the area term — by the
    axiom-free finite max-entropy bound `shannon_le_log_card` rewritten through the P4-MICRO `capacity` equation.

    This is P4's bound *derived*, modulo the named `MicrostatePostulate` interface: P4 is no longer an independent
    postulate but a theorem conditional on the framework's finite-capacity postulate.  Axiom-free; the area
    coefficient is never assigned a value (carried UV datum); the holographic content `log|𝓗_R| = areaTerm` lives
    entirely in the typeclass hypothesis. -/
theorem area_floor_of_microstate {R : Type*} [Fintype R] {areaTerm : ℝ}
    [h : MicrostatePostulate R areaTerm] (p : R → ℝ) (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1) :
    QIQTH.BranchLedger.Shannon Finset.univ p ≤ areaTerm := by
  rw [← h.capacity]
  exact QIQTH.RecordContract.shannon_le_log_card p hp h1

/-- **P4-MICRO in manifest physical form** — the capacity equation specialized to `edgeArea/(4·ellP²)`, so the
    area floor reads `S ≤ A/(4ℓ_P²)` with the `1/4ℓ_P²` coefficient explicit in the statement rather than hidden in
    an abstract `areaTerm`.  `edgeArea` (`= ⟨A_edge⟩ = A(∂R)`, the carried UV datum, never assigned a value) and
    `ellP` (the Planck length) are explicit fields.  Still a typeclass hypothesis, not a Lean `axiom`. -/
class MicrostatePostulateArea (R : Type*) [Fintype R] (edgeArea ellP : ℝ) where
  /-- The holographic capacity equation in manifest form: `log|𝓗_R| = A/(4ℓ_P²)`. -/
  capacity : Real.log (Fintype.card R) = edgeArea / (4 * ellP ^ 2)

/-- **★★★ The holographic area floor in manifest form `S ≤ A/(4ℓ_P²)`, as a corollary of P4-MICRO.**  For any
    Born record law `p` on the finite microstate set `R`, the Shannon entropy is at most the **area over `4ℓ_P²`**.
    Exhibits P4's bound in its physical shape (`area_floor_of_microstate` with the capacity specialized to
    `edgeArea/(4·ellP²)`).  The coefficient `1/4ℓ_P²` is manifest in the statement; its value is the carried UV datum,
    never asserted (`edgeArea`, `ellP` free reals).  The `1/4` *ratio* is derived elsewhere (`SakharovRatio`).
    Axiom-free, relative only to the named `MicrostatePostulateArea` postulate. -/
theorem holographic_area_floor_micro {R : Type*} [Fintype R] {edgeArea ellP : ℝ}
    [h : MicrostatePostulateArea R edgeArea ellP] (p : R → ℝ) (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1) :
    QIQTH.BranchLedger.Shannon Finset.univ p ≤ edgeArea / (4 * ellP ^ 2) := by
  rw [← h.capacity]
  exact QIQTH.RecordContract.shannon_le_log_card p hp h1

end QIQTH
