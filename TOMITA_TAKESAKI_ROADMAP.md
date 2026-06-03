# Roadmap: Tomita–Takesaki modular theory + Type III in Lean/Mathlib

**Goal.** Build the operator-algebra machinery that the QIQT-H *continuum* open
problems need (OP1 Born/typicality continuum, OP3b Lorentz continuum), whose
common wall is: modular theory of von Neumann algebras and the Type III local
algebras of relativistic QFT. This is a multi-person-year, Mathlib-grade effort;
the roadmap is phased so each phase is a usable, axiom-free checkpoint, with the
next layer's analytic input named as an explicit interface until it is built
(the project's standard *interface-as-hypothesis* discipline).

## What Mathlib has today (verified, lean4 v4.30 vendored copy)

| Component | Status |
|---|---|
| C\*-algebras, Gelfand duality, **GNS for states** (`CStarAlgebra/`) | ✅ solid |
| **Continuous** functional calculus (bounded normal/self-adjoint) | ✅ extensive |
| von Neumann algebra **definition** (bicommutant), `commutant_commutant`; `WStarAlgebra` (Sakai predual *existence* only) | ✅ `VonNeumannAlgebra/Basic.lean` only (162 lines) |
| Unbounded operators `LinearPMap` + adjoints | ✅ partial (`InnerProductSpace/LinearPMap.lean`) |
| **`StandardSubspace`** — explicitly *"an analogue of Tomita–Takesaki modular theory"* | 🟡 **active (2026, Y. Tanimoto)** — the one-particle / spatial route |
| **Spectral theorem / Borel FC / projection-valued measures** (bounded *or* unbounded self-adjoint) | ❌ **missing** (only compact/finite-dim) |
| Normal states/weights constructively; predual of B(H); trace-class / Schatten | ❌ missing |
| Modular Δ, J, S=JΔ^½, σₜ, KMS, commutation theorem JMJ=M′ | ❌ missing |
| Murray–von Neumann I/II/III; **Connes Type III_λ**, flow of weights, crossed products, Connes cocycle | ❌ missing entirely |

**Keystone gap:** the spectral theorem with projection-valued measures (PVM) for
(un)bounded self-adjoint operators. Without it there is no `Δ^{it}`, no modular
flow. That is Phase 1.

## Dependency DAG

```
[A] Bounded spectral theorem + Borel FC (PVM, ∫λ dE)      ← keystone (Phase 1)
[B] Unbounded self-adjoint: spectral thm, Δ^{it} 1-param group, polar decomp (Phase 2)
[C] vN alg + cyclic/separating Ω; S₀(aΩ)=a*Ω closable; S=JΔ^½ (Phase 3)
[D] TOMITA–TAKESAKI: JMJ=M′, σₜ(M)=M  (Phase 3, the theorem)
[E] KMS + modular automorphism group of a normal state (Phase 4)
[F] Murray–von Neumann I/II/III              [G] weights, Connes cocycle (Dφ:Dψ)ₜ
                                             [H] crossed product M⋊_σℝ, flow of weights
                                             [I] CONNES Type III_λ classification (Phase 5, optional)
```

**Scoping for QIQT-H.** We need **[D]+[E]** (modular flow + KMS for the regional
state) and the **Type II crossed-product** of CPW — i.e. the *use* of modular
theory, not the classification. *That local QFT algebras are Type III₁* is a deep
QFT theorem (Buchholz–Wichmann, Fredenhagen) to be **cited as input, not proved**.
Full Connes Type III_λ ([F]–[I]) is **out of scope**.

*Scoping corrections (GPT-5.5-pro consultation).* (i) The **Type II
crossed-product** `M⋊_σℝ` is NOT a small Phase-4 add-on — it needs W\*-dynamical
systems, normal weights, the dual action, operator-valued integration, semifinite
traces, and usually the Connes cocycle; it is Phase-5-scale and should be **cited**
unless heavily scoped. (ii) **KMS**: C\*-KMS assumes norm-continuous dynamics, but
modular automorphism groups are only point-**ultraweakly** continuous — formalize
an interim KMS on a specified analytic core / the Weyl C\*-algebra before the vN
closure. (iii) the **Connes cocycle** `(Dψ:Dφ)ₜ` is needed *iff* the
decoherence-functional covariance compares **different** states/weights (likely
for QIQT-H) — if so, carry at least a stated/interface version.

## Two routes

- **Route 1 (general/abstract):** [A]→[B]→[C]→[D]. Canonical, heaviest; [A] alone
  is a flagship contribution.
- **Route 2 (spatial + free fields):** build on `StandardSubspace` (one-particle
  modular theory) + second quantization (CCR/CAR, quasi-free states) to reach
  **free-field** Tomita–Takesaki sooner, with explicit modular objects that
  sidestep much of the general unbounded machinery. Connects to `FreeFieldRecord`
  / `LorentzWitness`.

**Decision:** Route 2 for the QIQT-H *deliverable* (free-field modular flow → a
free-field instance of the OP3b/OP1 continuum), while contributing **[A]**
upstream because it is the keystone everyone needs and unblocks Route 1.

## Phases (each = a usable checkpoint)

- **Phase 0 — DONE.** Finite/matrix Tomita–Takesaki: `FiniteModularTheory.lean`
  (σₜ = ρ^{it}·ρ^{−it}, KMS boundary identity, 1-parameter group). The spec the
  abstract version must generalize.
- **Phase 1 — keystone [A]: PVM + bounded spectral theorem + Borel FC.**
  *(STARTED — `QIQTH/Spectral/PVM.lean`; revised after GPT-5.5-pro consultation.)*
  Two layers: `PVContent` (finitely-additive projection-valued content — the
  algebraic lemmas `inner_E_self`, `E_compl`, the scalar set function, the simple
  integral, all proved axiom-free) and the genuine `ProjectionValuedMeasure`
  (laws on a `MeasurableSpace`'s measurable sets + **strong-operator** countable
  additivity `HasSum (fun n => E(Aₙ)x) (E(⋃Aₙ)x)`). *Correctness note from the
  consultation:* finite additivity + multiplicativity does **not** imply countable
  additivity (ultrafilter counterexample), so the scalar `μ_x`-is-a-`Measure`
  claim (T1) is sound only on the σ-additive `ProjectionValuedMeasure`, not on a
  content; and σ-additivity must be strong-operator, never operator-norm (norm
  σ-additivity is false). Named analytic targets: **(T1) ✅ PROVED** —
  `ProjectionValuedMeasure.scalarMeasure x` is a genuine `MeasureTheory.Measure`
  with `μ_x s = ofReal ‖E s x‖²` and total mass `ofReal ‖x‖²` (strong σ-additivity
  pushed through the bounded functional `⟪x,·⟫`; axiom-free); **(T2)** bounded-Borel
  FC `f↦∫f dE` (hard step = continuous→Borel multiplicativity extension +
  SOT bounded convergence, *not* uniqueness); **(T3)** the spectral theorem, via
  Mathlib's **continuous FC + Riesz–Markov** (extend `π : C(spec T)→B(H)` to a
  normal rep of bounded Borel functions, then `E(B):=Φ(1_B)`; *avoid* the
  bidual/universal-W\* route in Lean).
- **Phase 2 — [B]:** unbounded self-adjoint operators (closed/closable
  `LinearPMap`, adjoint theory), spectral theorem for unbounded self-adjoint **via
  the Cayley transform from the bounded normal spectral theorem [A]**, `Δ^{it}` as
  a **strongly**-continuous 1-parameter unitary group (note: `λ↦λ^{it}` is bounded
  Borel, not continuous at `0` where `Δ` typically has continuous spectrum — so
  [A]'s Borel FC, not the continuous FC, is what's required), polar decomposition
  of closed densely-defined operators.
- **Phase 3 — [C]+[D]:** abstract Tomita–Takesaki: cyclic/separating Ω,
  `S/F/Δ/J`, `S=JΔ^½`, `JMJ=M′`, `σₜ(M)=M`. *Extra cost flagged in consultation:*
  the Tomita operator `S` is **conjugate-linear AND unbounded**, so this needs
  antilinear closed/closable-operator theory + polar decomposition of antilinear
  closed operators — beyond ordinary linear closed operators.
- **Phase 3′ (parallel, Route 2 — the pragmatic QIQT-H path):** free-field modular
  theory via `StandardSubspace` + second quantization. *Key shortcut (consultation):*
  in geometric/Bisognano–Wichmann free-field cases the one-particle modular group
  is an **explicit** unitary group `U(t)=Δ_V^{it}` (boosts/dilations); second
  quantizing it directly, `σₜ(W(f)) = W(U(t)f)`, does **not** need the general
  spectral theorem (only second quantization of a strongly-continuous unitary
  group, built on finite-particle vectors by density) — it is `Γ(Δ)`/`Γ(log Δ)`
  that would need [A]/[B]. So **coordinate with the `StandardSubspace` line**
  (complementary, not parallel) and avoid a competing antilinear/unbounded stack.
  Deliverable: first non-toy `RecordedHistoryNet` / `UnitaryCovariance` with a
  genuine `σₜ` and Poincaré transport.
- **Phase 4 — [E]:** KMS + normal states; modular automorphism group; discharge
  the free-field `decoherence_functional_measure`-type covariance inputs.
- **Phase 5 (optional, long) — [F]/[G]:** types + Connes cocycle + weights. Only
  if the *classification* is wanted; cite Type III₁-ness rather than prove it.

## Effort & risk

- Person-years, not weeks. Phase 1 alone is a flagship Mathlib contribution.
- One phase = one usable, axiom-free layer; the next layer's analytic input stays
  a named hypothesis until built.
- Biggest risk is Phase 1/2 (spectral/unbounded analysis) — collaborate with /
  build on the people already in this corner of Mathlib (the standard-subspace
  line is the obvious ally).
- QIQT-H payoff lands at **Phase 3′ + 4**: free-field modular flow + KMS converts
  the OP3b/OP1 continuum from "named axiom" to "proved for the free field" — the
  first genuine dent in the continuum wall.

## Route-2 target, grounded in the literature (Neeb, arXiv:1707.05506)

The modular theory of **standard subspaces** is the clean, finite-prerequisite
core to formalize on top of Mathlib's `StandardSubspace` (whose own TODO is
exactly *"Define the Tomita conjugation, prove Tomita's theorem, prove the KMS
condition"*). Precise statements (Neeb, *On the geometry of standard subspaces*):

- **Standard subspace** `V ⊆ H`: closed real subspace, *cyclic* (`V + iV` dense)
  and *separating* (`V ∩ iV = {0}`).
- **Tomita operator** `S_V : V + iV → H`, `S_V(v + iw) = v − iw` — antilinear,
  involutive (`S_V² = id` on its domain), and **closed**.
- **Polar decomposition** `S_V = J_V Δ_V^{1/2}`: `J_V` antiunitary conjugation
  (`J_V² = id`, `J_V* = J_V`), `Δ_V > 0` self-adjoint (modular operator, unbounded
  in general).
- **Theorems** (target chain): (T-i) `J_V Δ_V J_V = Δ_V^{-1}`; (T-ii)
  `Δ_V^{it} V = V` for all `t` (modular flow preserves `V`); (T-iii)
  `J_V V = V'` (symplectic complement); + the one-parameter group laws.
- **Dependency order** (Neeb; the formalization plan): define `V` → construct
  `S_V` (closed/antilinear/involutive) → polar decomposition `S_V = J_V Δ_V^{1/2}`
  → `J_V` antiunitary, `Δ_V` positive self-adjoint (uses the **spectral theorem**,
  i.e. our Phase 1/2) → (T-i) → (T-ii) → (T-iii) → modular flow.

Note the dependency on `Δ_V^{1/2}` / `Δ_V^{it}` still routes through the spectral
theorem for the (unbounded, positive) `Δ_V` — i.e. Phase 1/2 remain the
prerequisite even on Route 2 — UNLESS the modular group is given **explicitly**
(Bisognano–Wichmann: for wedge regions `Δ_V^{it}` is the geometric boost group),
in which case one second-quantizes the explicit `U(t)` directly (see Phase 3′).

## References (open-access only — no pirated/in-copyright texts)

Grounding sources, all author-posted / arXiv (the source trail behind Mathlib's
`StandardSubspace`); the canonical textbooks (Takesaki, Bratteli–Robinson,
Kadison–Ringrose, Connes) are in copyright and deliberately NOT used here.

- K.-H. Neeb, *On the geometry of standard subspaces*, arXiv:1707.05506 — the
  precise S_V / J_V / Δ_V theory used above. **Primary.**
- K.-H. Neeb, G. Ólafsson, *Antiunitary representations and modular theory*,
  arXiv:1704.01336 — modular theory ↔ antiunitary representations.
- *Inclusions of Standard Subspaces*, arXiv:2506.16085 (2025) — inclusions
  (relevant to the diamond-poset net structure).
- R. Longo, *Lecture Notes* (Part 1, Ch. 2) — cited directly by Mathlib's
  `StandardSubspace`; modular theory of standard subspaces + second quantization.
- E. Witten, *Notes on Some Entanglement Properties of QFT*, arXiv:1803.04993 —
  Tomita–Takesaki, KMS, why local algebras are **Type III₁**, Bisognano–Wichmann;
  the physics-facing reference for the *cited* deep facts (Type III₁-ness, BW).

**Action item:** coordinate with the `StandardSubspace` Mathlib development rather
than duplicate it — its open TODO (Tomita conjugation / Tomita's theorem / KMS) is
precisely Route 2, and our Phase-1 PVM/spectral work is the complementary
prerequisite it will need for `Δ_V^{it}`.
