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
  SOT bounded convergence, *not* uniqueness; ◧ STARTED — the `*`-homomorphism
  CORE on simple functions is PROVED axiom-free: `integralSimple_adjoint`
  (`∫f̄=(∫f)†`) and `integralSimple_mul` (`∫f·∫g=∫(fg)` over a disjoint family, the
  multiplicativity heart); remaining = norm bound + simple→Borel extension +
  sesquilinear form); **(T3)** the spectral theorem, via
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
- S. J. Summers, *Tomita–Takesaki Modular Theory*, arXiv:math-ph/0511034 — the
  clean open survey of the vN-algebra TT theorem + KMS + Type III + applications.
  **Primary for Phases 3–4 statements.**
- H. Kosaki, *Type III Factors and Index Theory* (Univ. of Oregon lecture notes,
  pages.uoregon.edu/njp/lec-f.pdf) — structure analysis of Type III factors via
  modular theory (for Phase 5 / Connes classification, cite-only).
- T. Masuda, *Tomita–Takesaki theory and ...*, Math. J. Okayama Univ. 60 (2018),
  37–58 (open) — classification via Takesaki duality / approximate innerness.

## Type III classification — precise statements (cite-only; Summers survey)

For the vN-algebra TT theorem (`M` with cyclic+separating `Ω`, `S₀(AΩ)=A*Ω`,
`S = JΔ^{1/2}`): **`J M J = M'`** and **`σ_t(A)=Δ^{it}AΔ^{-it}` preserves `M`**;
the vector state `ω_Ω` satisfies the **KMS condition** `ω(A σ_t(B))` analytically
continued `= ω(B A)`, and `σ_t` is the *unique* modular flow of `ω_Ω`.
Classification: **Type I** (minimal projections, finite/semifinite trace);
**Type II** (no minimal projections, semifinite normal trace; II₁ if `τ(1)=1`,
else II_∞); **Type III** (NO semifinite normal trace; `σ_t` outer). The **Connes
invariant `S(M)`** (modular spectrum, a closed subgroup of `(0,∞)`) subclassifies
Type III: **III_λ** when `S(M)={λⁿ : n∈ℤ}∪{0}` (`0<λ<1`), **III₁** when
`S(M)=[0,∞)`. *Deep — cite:* TT existence/uniqueness, the trace-characterization
of Type III, Connes' `S(M)` computation, and **Haag–Kastler ⇒ Type III₁** for
local QFT algebras. *Derivable from `S=JΔ^{1/2}`:* `JMJ=M'`, `σ_t` central
commutation. This is the precise basis for the scoping decision: QIQT-H **cites**
Type III₁-ness and the Connes `S(M)` material (Phase 5), and **uses** only the
modular flow `σ_t` + KMS (Phases 3–4).

**Action item:** coordinate with the `StandardSubspace` Mathlib development rather
than duplicate it — its open TODO (Tomita conjugation / Tomita's theorem / KMS) is
precisely Route 2, and our Phase-1 PVM/spectral work is the complementary
prerequisite it will need for `Δ_V^{it}`.

---

# Detailed formalization plan (grounded in the sources, read in full)

Sources read: **Neeb**, *On the geometry of standard subspaces* (arXiv:1707.05506,
§§1–2); **Witten**, *Notes on Some Entanglement Properties of QFT*
(arXiv:1803.04993, §2.6, §3.1, §3.6, §4); **Summers**, *Tomita–Takesaki Modular
Theory* (arXiv:math-ph/0511034). Equation numbers below are from those papers.

## A. Object & theorem inventory (what to state in Lean, with sources)

- **Standard subspace** `V` (Neeb Def 2.1): closed real `V` with `V∩iV={0}` and
  `V+iV` dense. *(Mathlib `StandardSubspace` already has this.)*
- **Tomita operator** `S : D(S)=V+iV → H`, `S(v+iw)=v−iw` — antilinear, **closed**,
  `V = Fix(S) = ker(S−1)` (Neeb §2).
- **Modular operator/conjugation**: `Δ_V := S*S` positive self-adjoint; polar
  `S = J_V Δ_V^{1/2}`; **modular relation `J_V Δ_V J_V = Δ_V^{−1}`** (Neeb §2).
- **Classifying bijection** `Φ : Mod(H) → Stand(H)`, `Φ(Δ,J) = Fix(JΔ^{1/2})`
  (Neeb (2.1)), where `Mod(H)` = pairs `(Δ,J)`, `J` a conjugation, `Δ>0`
  self-adjoint, `JΔJ=Δ^{−1}`; antiunitary-rep model `Ψ(Δ,J)(eᵗ)=Δ^{−it/2π}`,
  `Ψ(Δ,J)(−1)=J`; **dilation-space law (Neeb Thm 2.3)** on `Stand(H)`:
  `V₁•_r V₂ = J_{V₁}J_{V₂}V₂` (r=−1), `Δ_{V₁}^{−it/2π}V₂` (r=eᵗ).
- **vN-algebra TT** (Summers; Witten §3.1): `M` with cyclic+separating `Ω`,
  `S₀(AΩ)=A*Ω`, `S=JΔ^{1/2}` ⇒ **`JMJ=M'`** and **`Δ^{it}MΔ^{−it}=M`**; the vector
  state satisfies **KMS**.
- **Finite-dimensional spec** (Witten §4 — the exact target our Phase 0 meets):
  `H=H₁⊗H₂`, `Ψ=∑cₖ|k,k⟩`, `S_Ψ((a⊗1)Ψ)=(a†⊗1)Ψ`; **`Δ_Ψ=ρ₁⊗ρ₂^{−1}`** (4.26);
  **modular flow `Δ_Ψ^{is}(a⊗1)Δ_Ψ^{−is}=ρ₁^{is}aρ₁^{−is}⊗1`** (4.35);
  `J_Ψ A J_Ψ=A'` (4.37); relative modular `Δ_{Ψ|Φ}^α(x)=σ₁^α x ρ₁^{−α}` (4.33);
  **KMS** = strip holomorphy of `F(z)=⟨Ψ|bΔ_Ψ^{iz}a|Ψ⟩`, `F(s)` vs `F(−i+s)`
  (4.42–4.47).
- **Type I/II/III + Connes `S(M)`** (Summers): III_λ when `S(M)={λⁿ}∪{0}`, III₁
  when `S(M)=[0,∞)`. **Cite-only** (Phase 5).

## B. Three concrete entry points, ranked

- **E1 — the keystone (unavoidable for non-explicit Δ): finish Phase 1 → Phase 2.**
  T2 bounded-Borel FC, T3 spectral theorem (continuous FC + Riesz–Markov), then
  unbounded self-adjoint via Cayley and `Δ^{it}` as a strongly-continuous group.
  *Everything below that uses a non-explicit `Δ` routes through this.*

- **E2 — Route 2 on Mathlib's `StandardSubspace`, following Neeb (coordinate with
  Tanimoto).** Formalize, in dependency order (Neeb §2): `S` closed antilinear →
  `Δ_V=S*S` positive self-adjoint → polar `S=J_VΔ_V^{1/2}` → `J_VΔ_VJ_V=Δ_V^{−1}`
  → `Δ_V^{it}V=V` → `J_V V=V'` → the `Φ` bijection + Thm 2.3. **Needs E1** (spectral
  theorem for the positive self-adjoint `Δ_V`, to form `Δ_V^{1/2}`, `Δ_V^{it}`),
  *unless* `Δ_V^{it}` is given **explicitly** (Bisognano–Wichmann boosts), in which
  case the explicit `U(t)` is second-quantized directly. This is Mathlib's open
  `StandardSubspace` TODO verbatim.

- **E3 — the matrix-limit route (Witten §4.2, fn 20–21), which REUSES Phase 0.**
  For QFT the local algebra is an ascending limit of matrix algebras
  `M₁⊂M₂⊂⋯⊂A_U`; the finite modular operators `Δ_Ψ^{(n)}` (built by
  `FiniteModularTheory.lean`: `σ_s=ρ^{is}·ρ^{-is}`) converge `Δ_Ψ^{(n)}→Δ_Ψ`, and
  (4.35)/(4.37)/(4.39) are **stable under the limit**. Formalize: the chain `M_n`,
  the finite `Δ^{(n)}` (done), and the limit/approximation theorems. Lower
  prerequisite than E2 for the *QFT* statement and directly extends what we have —
  but the limit theorems still ultimately need the unbounded `Δ_Ψ` (E1) to be the
  named limit object. Best as the *bridge* connecting Phase 0 to Phase 3.

## C. Per-phase Lean lemma lists (refined, with Mathlib touchpoints)

- **Phase 1 (E1a).** Done: `PVM`/`scalarMeasure` (T1). Next: `integralSimple`
  re-homed to `MeasureTheory.SimpleFunc`; T2 `∫f dE` as a `⋆`-hom (build the
  bounded operator from the sesquilinear form `⟪x,·⟫ via μ_{x,y}` + `ContinuousLinearMap`
  of a bounded form; multiplicativity by monotone-class from indicators); T3 from
  `CStarAlgebra/ContinuousFunctionalCalculus` + `MeasureTheory` Riesz–Markov
  (`RieszMarkovKakutani`).
- **Phase 2 (E1b).** Cayley transform `(T−i)(T+i)^{−1}` of a self-adjoint
  `LinearPMap` (`InnerProductSpace/LinearPMap`); unbounded Borel FC; `Δ^{it}` via
  `f_t(λ)=λ^{it}` bounded-Borel; Stone-type strong continuity.
- **Phase 3 (E2).** On `StandardSubspace`: closability of `S` (Neeb), `Δ_V=S*S`,
  polar (needs antilinear polar decomposition — new), the (T-i)/(T-ii)/(T-iii)
  chain. **The conjugate-linear unbounded `S` is the main new operator-theory
  burden** (Mathlib has linear `LinearPMap`; antilinear closed operators are new).
- **Phase 4.** KMS interim on a C\*/analytic core (Witten 4.42–4.47 strip), then vN
  ultraweak version; `σ_t` automorphism of `M`.
- **Phase 5 (cite).** Type III / Connes `S(M)` — stated, cited (Summers), not
  proved.

## D. Verdict & first move

The plan is internally consistent and the **single binding prerequisite is E1**
(bounded spectral theorem → `Δ^{it}`); both the standard-subspace route (E2) and
the matrix-limit route (E3) ultimately need it for a non-explicit `Δ`. **First
concrete move:** push Phase 1 to **T2/T3** (the spectral theorem), because it
unblocks E2 and E3 simultaneously; in parallel, the *zero-new-prerequisite* task
is **E3's finite scaffolding** — extend `FiniteModularTheory.lean` with the
matrix-algebra chain `M_n` and state the (4.35)/(4.37) modular-flow/commutation
facts as the n-th approximation, since those need nothing beyond Phase 0.
