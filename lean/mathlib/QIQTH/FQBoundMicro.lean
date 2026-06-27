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
area-law postulate.  This file lands the core corollary (`area_floor_of_microstate`) via the
`HolographicCapacityBound`/`HolographicCapacityExact` typeclasses, mirroring the `Phase5Master`/`DonaldSystem`
interface discipline that kept the QIQT-H core axiom-free.

HONEST SCOPE.  The value of `G` / the edge normalization `⟨A_edge⟩ = A/4ℓ_P²` is the **carried UV datum**: the
capacity hypothesis contains the dimensionful area term, but its coefficient is a **free real parameter**, never
assigned a value.  The pivot RELOCATES where the datum sits (macroscopic entropy postulate → microscopic counting
postulate); it does NOT derive the value of `G`.  The capacity postulate is a **typeclass hypothesis, not a Lean
`axiom`** (the budget stays 0).  Route 2 does NOT reproduce Route 1's modular-origin explanation of *why area* — the
holographic input `log|𝓗_R| ∝ A` is assumed here and stays the labelled open frontier (the Type II dual-weight
trace).  The `1/4` *ratio* is derived elsewhere (`SakharovRatio`); it is not re-asserted here.  Free scalar only;
no `sorry`.

WHAT THE CAPACITY IS — REGIONAL, AND A TYPE-I/CODE CUTOFF (GPT-5.5-pro C3).  `Fintype.card R` here is **not** a
global Hilbert-space dimension.  It is the **regional operational capacity** `Q_R = log N_R` — the number `N_R` of
mutually distinguishable microstates accessible to the region `R` (equivalently, the dimension of a finite regional
effective Hilbert space / a fixed-area sector / a code subspace).  This is a deliberate **finite type-I cutoff**:
the *actual* local algebra of a region in continuum QFT is **type III₁** — it has NO finite trace, NO tensor-factor
density matrix `ρ_R`, and a divergent local entanglement entropy.  Granting a finite-dimensional `R` (so that `ρ_R`
and `S_vN(ρ_R)` even exist) is therefore itself the holographic/quantum-gravity regularization — the finite-`Q_max`
postulate — *not* bookkeeping.  We state it as such: the bound is read in a fixed-area sector, `≤` is the safe form
(area-operator fluctuations make exact `log dim = ⟨A⟩/4` suspect — hence `HolographicCapacityBound`), and the
type-III obstruction is exactly what the Type II dual-weight trace (Route 1) would have to resolve to *derive* this
capacity rather than postulate it.
-/
import QIQTH.RecordContract
import QIQTH.QuantumRelativeEntropy

namespace QIQTH

/-- **P4-MICRO, bound form** — the finite-microstate (quantized-information) postulate for a region `R`, in the
    form P4's *floor* actually needs.  `R` is the finite set of mutually distinguishable **regional** microstates
    (a finite effective Hilbert space / fixed-area sector / code subspace — a type-I/code cutoff of the genuinely
    type-III local algebra; see the module header), and its log-capacity is **bounded** by the area term:
    `bound : log N_R ≤ areaTerm`.  This is the **holographic** input `Q_R = log N_R ≤ A/4ℓ_P²`; the area coefficient
    is the carried UV datum (a free real parameter, never assigned).  Carried as a *typeclass hypothesis*, never as
    a Lean `axiom` — the budget stays 0. -/
class HolographicCapacityBound (R : Type*) [Fintype R] (areaTerm : ℝ) where
  /-- The holographic capacity **bound** `log|𝓗_R| ≤ areaTerm` (`= A/4ℓ_P²`, the carried UV datum). This is all
      P4's *floor* needs (GPT-5.5-pro C2). -/
  bound : Real.log (Fintype.card R) ≤ areaTerm

/-- **P4-MICRO, exact (saturation) form** — the holographic capacity *equality* `log|𝓗_R| = areaTerm`.  Strictly
    stronger than `HolographicCapacityBound`; needed only where the area floor is achieved as an EQUALITY (the
    maximally-mixed / local-equilibrium record, `area_floor_saturates`).  The area coefficient is the carried UV
    datum; a typeclass hypothesis, never a Lean `axiom`.  (Formerly `MicrostatePostulate`.) -/
class HolographicCapacityExact (R : Type*) [Fintype R] (areaTerm : ℝ) where
  /-- The holographic capacity equation `log|𝓗_R| = areaTerm`. -/
  capacity : Real.log (Fintype.card R) = areaTerm

/-- **`=` implies `≤`:** every exact capacity postulate is a fortiori a bound postulate.  So all the *floor*
    theorems (stated for `HolographicCapacityBound`) fire from an exact postulate too; only saturation needs the
    exact form. -/
instance instCapacityBoundOfExact {R : Type*} [Fintype R] {areaTerm : ℝ}
    [h : HolographicCapacityExact R areaTerm] : HolographicCapacityBound R areaTerm :=
  ⟨le_of_eq h.capacity⟩

/-- **★★★ P4's holographic area floor as a COROLLARY of P4-MICRO.**  For any Born record law `p` on the finite
    microstate set `R` (nonnegative weights summing to `1`), the Shannon entropy is at most the area term — by the
    axiom-free finite max-entropy bound `shannon_le_log_card` rewritten through the P4-MICRO `capacity` equation.

    This is P4's bound *derived*, modulo the named `HolographicCapacityBound` interface: P4 is no longer an
    independent postulate but a theorem conditional on the framework's finite-capacity postulate.  Axiom-free; the
    area coefficient is never assigned a value (carried UV datum); the holographic content `log|𝓗_R| ≤ areaTerm`
    lives entirely in the typeclass hypothesis. -/
theorem area_floor_of_microstate {R : Type*} [Fintype R] {areaTerm : ℝ}
    [h : HolographicCapacityBound R areaTerm] (p : R → ℝ) (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1) :
    QIQTH.BranchLedger.Shannon Finset.univ p ≤ areaTerm :=
  le_trans (QIQTH.RecordContract.shannon_le_log_card p hp h1) h.bound

/-- **★★★ The holographic area floor in manifest form `S ≤ A/(4ℓ_P²)`, as a corollary of P4-MICRO.**  For any
    Born record law `p` on the finite microstate set `R`, the Shannon entropy is at most the **area over `4ℓ_P²`**.
    This is just `area_floor_of_microstate` specialized to `areaTerm = edgeArea/(4·ellP²)` (no separate class needed
    — the bound postulate is already parameterized by an arbitrary `areaTerm`).  The coefficient `1/4ℓ_P²` is
    manifest in the statement; its value is the carried UV datum, never asserted (`edgeArea`, `ellP` free reals).
    The `1/4` *ratio* is derived elsewhere (`SakharovRatio`).  Axiom-free, relative only to the bound postulate. -/
theorem holographic_area_floor_micro {R : Type*} [Fintype R] {edgeArea ellP : ℝ}
    [HolographicCapacityBound R (edgeArea / (4 * ellP ^ 2))]
    (p : R → ℝ) (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1) :
    QIQTH.BranchLedger.Shannon Finset.univ p ≤ edgeArea / (4 * ellP ^ 2) :=
  area_floor_of_microstate p hp h1

/-- **Capacity saturation under P4-MICRO** — at the maximally-mixed record `p ≡ 1/|𝓗_R|` the area floor is an
    EQUALITY `S = areaTerm`, not just a bound.  This is the equilibrium / horizon local-equilibrium regime (the
    maximum-entropy state), via the Jensen saturation `shannon_uniform_eq_log_card` rewritten through the P4-MICRO
    `capacity` equation.  So P4-MICRO delivers both the bound (`area_floor_of_microstate`) and the saturation: the
    area floor is achieved exactly when the region is maximally mixed.  Axiom-free; the area coefficient is the
    carried UV datum, never assigned. -/
theorem area_floor_saturates {R : Type*} [Fintype R] [Nonempty R] {areaTerm : ℝ}
    [h : HolographicCapacityExact R areaTerm] :
    QIQTH.BranchLedger.Shannon Finset.univ (fun _ : R => (Fintype.card R : ℝ)⁻¹) = areaTerm := by
  rw [QIQTH.RecordContract.shannon_uniform_eq_log_card, h.capacity]

/-! ### The HONEST von Neumann form (GPT-5.5-pro C1 fix)

The bounds above are stated for the SHANNON entropy of a Born record law `p` over the microstates — the
*decohered / record* entropy.  P4 proper is about the VON NEUMANN entropy `S_vN(ρ_R)` of a regional density
matrix; routing it through a record law is honest only because `S_vN(ρ) = H(spectrum of ρ)`, i.e. Shannon applied
to the *eigenvalues* (dephasing only raises entropy, so `S_vN ≤ H(record)` one-way — a pure superposition has
`H = log d` but `S_vN = 0`).  The lemmas below state the genuine von Neumann max-entropy bound directly. -/

/-- **The honest von Neumann max-entropy bound** `S_vN(ρ) ≤ log dim 𝓗_R`.  For a finite-dimensional density
    matrix `ρ` (`IsDensity`: positive semidefinite, unit trace), the von Neumann entropy is at most the log of the
    Hilbert-space dimension.  This is `S_vN = ∑ negMulLog(λ_i)` (Shannon of the *spectrum* — the eigenvalues form a
    probability vector by `eigenvalues_nonneg` + `sum_eigenvalues`) fed into the axiom-free Jensen/Gibbs bound
    `shannon_le_log_card`.  This is the correct object for P4 — von Neumann entropy, not the record-law Shannon
    entropy of `area_floor_of_microstate`. Axiom-free. -/
theorem vonNeumannEntropy_le_log_card {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}
    (h : QIQTH.QuantumEntropy.IsDensity ρ) :
    QIQTH.QuantumEntropy.vonNeumannEntropy h ≤ Real.log (Fintype.card n) := by
  have key := QIQTH.RecordContract.shannon_le_log_card h.eigenvalues h.eigenvalues_nonneg h.sum_eigenvalues
  rw [QIQTH.RecordContract.shannon_eq_sum_negMulLog] at key
  simpa only [QIQTH.QuantumEntropy.vonNeumannEntropy] using key

/-- **★★★ P4's holographic area floor for the VON NEUMANN entropy** (the honest C1 form).  Under the
    finite-microstate postulate `MicrostatePostulate n areaTerm` (`log dim 𝓗_R = areaTerm = A/4ℓ_P²`), the von
    Neumann entropy of any regional density matrix obeys `S_vN(ρ) ≤ areaTerm`.  This is P4 stated for the genuine
    regional entropy `S_vN(ρ_R)`, not the record-law Shannon entropy — `vonNeumannEntropy_le_log_card` rewritten
    through the capacity bound (`HolographicCapacityBound`, the `≤`-form — all the floor needs).  Axiom-free; the
    area coefficient is the carried UV datum, never assigned; the postulate is a typeclass hypothesis, not a Lean
    axiom. -/
theorem area_floor_vonNeumann {n : Type*} [Fintype n] [DecidableEq n] {areaTerm : ℝ}
    [hcap : HolographicCapacityBound n areaTerm] {ρ : Matrix n n ℂ}
    (h : QIQTH.QuantumEntropy.IsDensity ρ) :
    QIQTH.QuantumEntropy.vonNeumannEntropy h ≤ areaTerm :=
  le_trans (vonNeumannEntropy_le_log_card h) hcap.bound

end QIQTH
