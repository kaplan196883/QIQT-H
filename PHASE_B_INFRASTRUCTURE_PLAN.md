# Phase-B infrastructure plan — building the two real walls

*Written 2026-06-08. The continuum covariant-μ prize (XL_STEP_PLAN.md) is complete EXCEPT the
physical Phase-B input: a **normal state on a Type III₁ relativistic-QFT local net**.  This document
plans building that input honestly, in two genuinely separate parts:*

- **Part A — predual / trace-class / normal states of `B(H)`** (bounded functional analysis;
  Mathlib-contributable; the **critical path** for the measure).
- **Part B — Type III₁-ness of local QFT algebras** (the **Buchholz–Wichmann / Fredenhagen** theorem;
  research-grade, multi-year; depends on Part A + the full Tomita–Takesaki/Connes tower + QFT axioms).

Difficulty key: **S** hours · **M** days · **L** weeks · **XL** months / new Mathlib infrastructure ·
**XXL** multi-person-year research formalization.

> **★ Strategic note (load-bearing).** The typicality measure μ∞ (XL Phase A/B) needs ONLY a *normal
> state* `ω` on the net (`EffectStateNet`); it does **not** use the algebra's *type*.  So **Part A is
> the genuine prerequisite for the prize μ**, and **Part B (Type III₁) is NOT needed for the measure** —
> it characterizes the local algebras (the QIQT-H *foundational narrative*: why the continuum forces
> finite records / no global trace), a separate and far larger goal.  Sequence Part A first.

---

## 0. What Mathlib has today (verified 2026-06-08)

| Component | Status |
|---|---|
| Finite-dim trace `LinearMap.trace`, `trace_eq_sum_inner` (`InnerProductSpace/Trace.lean`) | ✅ |
| Compact operators + Fredholm; **compact self-adjoint spectral theorem** (`InnerProductSpace/Spectrum.lean`, `Normed/Operator/Compact/`) | ✅ |
| `CStarAlgebra (H →L[ℂ] H)`, continuous + **our** bounded-Borel FC (`borelFC`), bounded spectral theorem (`PVM_of_selfAdjoint`), `CFC.sqrt` (complex), `modFlow` (Δ^{it} bounded Stone) | ✅ (ours / Mathlib) |
| `WStarAlgebra M` = `CStarAlgebra` + `exists_predual` — **mere existence, predual NOT constructed** | 🟡 stub |
| `VonNeumannAlgebra H` (double commutant), `commutant`, `centralizer_centralizer` | ✅ structural only |
| **Infinite-dim trace-class (Schatten-1), trace norm, `Tr(Tx)` pairing, predual `B(H)_* ≅ T(H)`** | ❌ missing |
| **Normal states / density operators / σ-weak (ultraweak) topology** | ❌ missing |
| **Modular operator Δ/J from a state, KMS, Tomita's theorem (unbounded)** | ❌ missing (we have bounded fragments) |
| **Connes modular spectrum S(M), Type I/II/III, III_λ/III₁, crossed product, flow of weights** | ❌ missing entirely |
| **Haag–Kastler net, vacuum, wedge modular = boost (Bisognano–Wichmann), nuclearity** | ❌ missing entirely |

---

## Part A — predual / trace-class / normal states of `B(H)`  (critical path, Mathlib-grade)

Goal: construct the predual `B(H)_* = T(H)` (trace-class operators) and **normal states** (density
operators), discharging `WStarAlgebra (H →L[ℂ] H)`'s `exists_predual` with a *constructed* predual, and
giving the `ω(x) = Tr(ρ x)` normal-state functional that `EffectStateNet` consumes.

- **A1 — trace-class operators `T(H)` (Schatten-1).** **(XL.)**
  Define `|T| = √(T⋆ T)` (we have `CFC.sqrt` for positive bounded operators; `T⋆T ≥ 0`); trace-class :=
  `∑ₙ ⟨eₙ, |T| eₙ⟩ < ∞` (basis-independent); the **trace** `Tr T = ∑ₙ ⟨eₙ, T eₙ⟩` (well-defined,
  linear, `Tr(T⋆)=conj Tr T`, `Tr(AB)=Tr(BA)`); trace norm `‖T‖₁`; completeness ⇒ `T(H)` Banach.
  *Hooks:* `InnerProductSpace/Trace` (finite-dim, extend), compact-operator spectral theorem (singular
  values), `CFC.sqrt`, our `PVM_of_selfAdjoint`/`borelFC` for `|T|` of non-compact positives.
  *Deps:* none beyond Mathlib + our spectral theorem. *Risk:* the basis-independence + `Tr(AB)=Tr(BA)`
  for the infinite sum is the classic analytic core.

- **A2 — the predual duality `B(H)_* ≅ T(H)`.** **(XL.)**
  The pairing `⟨T, x⟩ = Tr(T x)` (`T : T(H)`, `x : B(H)`); `T(H)⋆ ≅ B(H)` (isometric); the σ-weak
  (ultraweak) topology on `B(H)` as `σ(B(H), T(H))`; σ-weakly continuous functionals `= T(H)`.
  *Hooks:* `Analysis/Normed/Module/Dual`, Hahn–Banach, A1. *Deps:* A1.

- **A3 — normal states.** **(L.)**
  Density operators `ρ ≥ 0`, `Tr ρ = 1`; the state `ωρ(x) = Tr(ρ x)` (positive, normalized);
  **normality** = σ-weak continuity ⇔ given by a density operator; countable additivity on projections.
  *Deps:* A1, A2.

- **A4 — discharge `WStarAlgebra (H →L[ℂ] H)` + feed `EffectStateNet`.** **(M.)**
  Construct the `WStarAlgebra (H →L[ℂ] H)` instance with predual `T(H)` (replacing `exists_predual`'s
  stub); package `ωρ` as the `A →+ ℝ` of an `EffectStateNet` so the existing μ∞ machinery applies to a
  genuine normal state on `B(H)`.  *Deps:* A1–A3 + `QIQTH/StateNetMeasure.lean`.

**Part-A verdict.** A bounded, well-defined operator-theory project (≈ XL, several months solo;
genuinely a flagship Mathlib contribution).  It is the ONLY Phase-B piece the prize μ requires, and it
reuses our bounded spectral theorem / `CFC.sqrt`.  **Do this first.**

---

## Part B — Type III₁-ness of local QFT algebras (Buchholz–Wichmann)  (research-grade, XXL)

Goal: the theorem that the local von Neumann algebras of a relativistic QFT are factors of **type III₁**.
This is the QIQT-H *foundational* statement (no global trace ⇒ finite-record/no-collapse narrative), NOT
a prerequisite for μ.  It is a multi-person-year formalization with a long dependency chain.

- **B1 — full Tomita–Takesaki from a state.** **(XXL.)**
  Cyclic-separating vector `Ω` for `M ⊆ B(H)`; Tomita operator `S₀: xΩ ↦ x⋆Ω` (closable, antilinear);
  `S = JΔ^{1/2}` (J antiunitary, Δ positive self-adjoint **unbounded** — needs unbounded operator
  theory + our `modFlow` generalized via Stone to unbounded Δ); **`JMJ = M′`**, `σ_t(M)=M`, KMS.
  *Builds on:* our bounded `modFlow`/`modAut`/`modAutC`/RvD objects; Part A (the state, GNS standard
  form). *Missing Mathlib:* unbounded self-adjoint operators, closable antilinear operators, polar
  decomposition of closed antilinear operators.

- **B2 — Connes classification.** **(XXL.)**
  Modular spectrum **`S(M) = ⋂_φ spec(Δ_φ)`** (Connes invariant); Type I/II/III by
  trace existence; **III_λ** (`S(M)={λⁿ}∪{0}`) vs **III₁** (`S(M)=[0,∞)`); the crossed-product core
  `M ≅ M̃ ⋊_θ ℝ` (M̃ type II∞) / flow of weights; Connes cocycle `(Dφ:Dψ)_t`.
  *Deps:* B1 + semifinite traces/weights + crossed products (all missing in Mathlib).

- **B3 — the Haag–Kastler net + Bisognano–Wichmann.** **(XXL.)**
  Isotonic, microcausal, Poincaré-covariant net `O ↦ M(O)` of vN algebras on a fixed `H`; the vacuum
  `Ω` (cyclic-separating for wedges, Reeh–Schlieder); **Bisognano–Wichmann**: the modular group of a
  wedge algebra is the Lorentz boost (`Δ_W^{it} = U(Λ_W(−2πt))`).  *Deps:* B1 + Part A + free-field /
  Weyl-algebra construction (`StandardSubspaceModular` second-quantized).

- **B4 — Buchholz–Wichmann / Fredenhagen: local algebras are III₁.** **(XXL, the theorem.)**
  Under an energy/nuclearity condition (or for free fields explicitly), `S(M(O)) = [0,∞)` ⇒ type III₁.
  *Deps:* B1+B2+B3.

**Part-B verdict.** Genuine research-grade formalization (multi-person-year, several pieces are open
Mathlib targets in their own right).  Honest recommendation: keep B **cited** (Buchholz–Wichmann 1986;
Fredenhagen 1985; Bisognano–Wichmann 1975/76) unless/until pursued as a dedicated long-horizon program;
it is **not** on the path to the measure prize.

---

## Dependency DAG & first move

```
Part A:  A1 trace-class ─→ A2 predual duality ─→ A3 normal states ─→ A4 WStarAlgebra + EffectStateNet
                                                                         └─→ μ∞ for a genuine B(H) state  ★ PRIZE INPUT
Part B:  (Part A) + unbounded-operator theory ─→ B1 Tomita–Takesaki ─→ B2 Connes types
                                                  B3 Haag–Kastler + Bisognano–Wichmann ─┘
                                                                         └─→ B4 Type III₁ (Buchholz–Wichmann)  [foundational narrative, CITED]
```

**First concrete move:** **A1** — define `|T| = √(T⋆T)` (via `CFC.sqrt`) and trace-class operators on a
separable Hilbert space, with the trace `Tr` and `Tr(AB)=Tr(BA)`.  This is self-contained, reuses our
spectral theorem, and is the foundation everything else in Part A rests on.  Each A-stage is an
axiom-free, Mathlib-contributable checkpoint; the budget stays at 33 (no new project axioms — these are
*constructions*, not interface assumptions).

**Honest scope.** Part A is large-but-bounded and worth doing (it completes the prize input and is
upstream-worthy).  Part B is a multi-year research formalization that is NOT required for μ; it stays a
clearly-labelled cited frontier (the shared open problem of mathematical QFT), to be undertaken only as a
deliberate long-horizon program.
