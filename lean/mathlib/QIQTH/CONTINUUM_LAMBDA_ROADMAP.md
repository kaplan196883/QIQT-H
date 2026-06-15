# Continuum λ-law roadmap — lifting the finite λ-law to the standard-subspace / free-field modular flow

> **STATUS (2026-06-16): Stages 1–3 DONE (axiom-free, budget 0).** `ContinuumLambda` (modular automorphism +
> Takesaki criterion + persistence), `NaturalConeBorn` (algebraic Born rule), `ContinuumSelection` (Type-blind
> selection event) all built on the genuine `Δ^{it}`. Stage 4 = the honest closure (Type III₁ cited; residual
> walls = Haagerup natural-cone existence + interacting case) — recorded in `PROGRAM_STATUS.md` and below.

**Goal.** Lift the finite (Type I) λ-law — `LambdaPointer.lean` (Takesaki criterion, conditional
expectation, persistence) and `SelectionEvent.lean` (one record per seed, Born frequency) — to the
**genuine continuum** modular flow `Δ^{it}` already built axiom-free in this repo. This is the
*Type-III-native* continuum λ-law identified in the 2026-06-15 redirect: it rides the **standard
form / natural cone** and the **modular automorphism** `σ_t = Ad(Δ^{it})`, **not** the retired
gravitational crossed product.

**Honest boundary up front.** We do *not* prove the local algebras are Type III₁ (Buchholz–Wichmann,
cited). We *do* build, on the bounded RvD modular data, the continuum modular automorphism, the
continuum Takesaki criterion + persistence, and the algebraic Born rule via the canonical
state↦vector correspondence — i.e. λ's kinematic-and-persistence law at the continuum / free-field
level, with the Type-classification physics input cited, not reproved.

---

## What is already DONE (axiom-free, build on it)

| Component | File | Status |
|---|---|---|
| Projection-valued measures, scalar spectral measures, simple integral | `Spectral/PVM.lean` | ✅ |
| **Bounded Borel FC multiplicativity** `boundedFC_mul` | `Spectral/PVM.lean` | ✅ (keystone residual closed) |
| **Bounded spectral theorem** `PVM_of_selfAdjoint`, `borelFC` | `Spectral/SpectralTheorem.lean` | ✅ |
| RvD bounded modular objects `P,Q,R,T,J` on `StandardSubspace`; `rvdT_injective` | `StandardSubspaceModular.lean` | ✅ |
| **Continuum modular flow** `Δ^{it} = modUnitary` (1-param unitary group), `Δ^{it}𝒦=𝒦`, `JΔ^{it}=Δ^{it}J` | `StandardSubspaceModularFlow.lean` | ✅ |
| `modUnitary_commute_specProj`, `modUnitary_commute_rvdRC` (flow commutes with functions of `R`) | `StandardSubspaceModularFlow.lean` | ✅ ← **persistence enabler** |
| One-particle CGP relative entropy `S(ξ)=−∫log((2−r)/r)dμ^R_ξ` | `ModularRelativeEntropy.lean` | ✅ |
| **Second-quantized** `Γ(Δ^{it}) = secondQuantModFlowH`, `σ_t(W(u))=W(Δ^{it}u)`, vacuum-fixing, strong continuity | `Fock/SecondQuantModularFlow.lean` | ✅ |
| Relative modular flow `Δ^{it}_{W(f)Ω∣Ω}`, Connes cocycle + chain rule, **Araki = CGP** `hasDerivAt_relModFlow_vacuum` | `Fock/RelativeModularFlow.lean` | ✅ |

So the modular *unitary* group and its second quantization exist. **Missing for the λ-law:** the
modular *automorphism* on operators, the canonical Born rule via the natural cone, and the continuum
lift of the finite Takesaki/persistence/selection theorems.

---

## The stages (each an axiom-free, green-building increment)

### Stage 1 — Continuum modular automorphism + Takesaki criterion + persistence  *(START HERE; most tractable, directly lifts `LambdaPointer`)*
New file `QIQTH/ContinuumLambda.lean`. Reuses `modUnitary` + `modUnitary_commute_specProj`.
1. `modAutOp S t A := modUnitary S t * A * modUnitary S (-t)` — the modular automorphism `Ad(Δ^{it})`
   on `H →L[ℂ] H`. Prove it is a one-parameter group of unital ⋆-endomorphisms:
   `modAutOp_zero` (`σ_0 = id`), `modAutOp_add` (`σ_s∘σ_t = σ_{s+t}`), `modAutOp_one`,
   `modAutOp_mul` (multiplicativity — the `U_{-t}U_t = 1` in the middle cancels), `modAutOp_star`.
   *(Uses `modUnitary_add`, `modUnitary_zero`, the adjoint relation `U_t⋆ = U_{-t}`.)*
2. **Continuum Takesaki criterion** `modAutOp_fixes_iff_commute`: `σ_t(A) = A ⟺ A` commutes with
   `Δ^{it}` (the continuum analogue of `LambdaPointer.modAut_fixes_iff_commute`).
3. **Pointer projections are fixed** `modAutOp_fixes_specProj`: a spectral projection of the modular
   generator `R` is fixed by the modular flow for every `t` — via `modUnitary_commute_specProj`. The
   continuum "exact decoherence ⇒ the flow fixes the pointer".
4. **Continuum persistence** `dephase_modAutOp_commute`: for a finite pointer family of spectral
   projections (commuting with `Δ^{it}`), the dephasing map `E(A)=Σ P_α A P_α` commutes with `σ_t`
   for every `t` — the continuum lift of `dephase_modAut_commute`/`dephase_sigmaDiag_commute`. A
   dephased state stays dephased under the genuine continuum modular flow.

*Acceptance:* `lake build QIQTH.ContinuumLambda` green; `#print axioms` standard-three; budget 0.

### Stage 2 — The algebraic Born rule via the canonical state↦vector correspondence  *(moderate)*
New file `QIQTH/NaturalConeBorn.lean`.
1. For a normal/vector state on the standard subspace, the Born weight of a spectral pointer `P_α` is
   `ω(P_α) = ⟪ξ, P_α ξ⟫` (real, nonneg via `P_α ≥ 0`). Prove `bornWeight_nonneg`, and that a spectral
   resolution `Σ P_α = 1` gives `Σ ω(P_α) = ‖ξ‖²` (= 1 for a unit vector) — a genuine probability,
   *Type-independent* (no trace). The continuum lift of `LambdaPointer.bornWeights_sum`.
2. (If reachable on Mathlib's `StandardSubspace`/standard-form API) connect `ξ` to the canonical
   vector in the natural cone; otherwise state the Born rule directly on unit vectors and note the
   natural-cone identification as the cited refinement. *Honest: the full Haagerup standard-form /
   natural-cone existence is a Mathlib gap; we use the explicit vector state and flag the cone step.*

### Stage 3 — Continuum selection event via the spectral measure  *(moderate; lifts `SelectionEvent`)*
New file `QIQTH/ContinuumSelection.lean`.
1. With Born weights `p_α = ω(P_α)` from Stage 2 over a *finite* spectral pointer family, reuse the
   inverse-CDF constructor `SelectionEvent.selects_exists_unique` / `volume_selects` verbatim — the
   selection event is finite-record even in the continuum (records are a finite coarse-graining of a
   Type III₁ algebra). Deliver `continuum_selects_exists_unique` + `continuum_volume_selects` as the
   instantiation, making explicit that the selection event needs only the finite *record* structure,
   not finiteness of the algebra. *This closes the conceptual loop: the selection event is Type-blind.*

### Stage 4 — Type III₁ boundary (cited, not proved) + second-quantized lift note  *(honest closure)*
Docstring/audit only (+ optional `Γ(Δ^{it})`-level persistence if the second-quant commutation is
cheap from `secondQuantModFlowH_weylH`). State precisely: (a) the local algebra is Type III₁
(Buchholz–Wichmann, cited); (b) the modular data, automorphism, Takesaki criterion, persistence,
Born rule, and selection event are all built/lifted on the bounded RvD substrate, axiom-free; (c) the
remaining genuine gaps are the *existence* of the Haagerup natural cone in Mathlib and the
interacting case. No new axioms; update `AxiomAudit.lean` + `PROGRAM_STATUS.md`.

---

## Files
**New:** `QIQTH/ContinuumLambda.lean` (Stage 1), `QIQTH/NaturalConeBorn.lean` (Stage 2),
`QIQTH/ContinuumSelection.lean` (Stage 3).
**Extend:** `QIQTH.lean` (imports), `QIQTH/AxiomAudit.lean` (`#print axioms` per new theorem),
`PROGRAM_STATUS.md` (Stage 4 note). Reuse — do not duplicate — `StandardSubspaceModularFlow`
(`modUnitary`, `modUnitary_commute_specProj`), `LambdaPointer`, `SelectionEvent`, `Spectral/*`.

## Verification (per stage)
- `~/.elan/bin/lake build QIQTH.<Module>` green; full `lake build QIQTH QIQTH.AxiomAudit` green.
- every new theorem `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
- `bash scripts/axiom_budget_check.sh` passes, budget stays **0**; vacuity-lint clean.
- one commit per stage (ship-green-increments), with the Co-Authored-By trailer.

## Honest scale note
Stage 1 is days (it reuses the hardest pieces, already done). Stages 2–3 are days–week each. Stage 4
is documentation. The genuine residual walls — *Haagerup natural-cone existence in Mathlib* and the
*interacting (non-free) case* — are cited, not closed; this roadmap delivers the continuum λ-law for
the **free-field / standard-subspace** sector, which is exactly the verified substrate's reach.
