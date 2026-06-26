# Stone's theorem — campaign plan (the unbounded generator: `K = −log Δ` and the clock energy `X`)

**Status:** PLAN (not started). **Track:** GR / continuum operator algebra (the Phase-4 wall of
`P4_WALL_CAMPAIGN_PLAN.md`; the `K = −log Δ` frontier of JLMS Stage 1). **Goal:** build the unbounded
self-adjoint operator theory needed to turn a strongly-continuous one-parameter unitary group into its
**self-adjoint generator** `U_t = exp(itA)` — Stone's theorem — and apply it to (i) the modular flow `Δ^{it}`
→ the modular Hamiltonian `K`, and (ii) the clock translation `λ_t` → the clock energy `X = A_edge`.

## 0. The decisive observation (why this is two campaigns, not one)

Stone's theorem has two directions, and **they are not equally hard *for us*** because of what we already have:

- **Direction I — `f(A)` from a known PVM (the unbounded *functional calculus*).** We ALREADY have, axiom-free:
  - `PVM_of_selfAdjoint` (`QIQTH/Spectral/SpectralTheorem.lean`) — the **bounded spectral theorem**: a bounded
    self-adjoint `T : H →L[ℂ] H` yields a genuine `ProjectionValuedMeasure E` on `spectrum ℝ T` with `∫ id dE = T`.
  - `boundedFC` (`QIQTH/Spectral/PVM.lean`) — the **bounded Borel functional calculus**, proved a unital
    `*`-algebra hom, with `scalarMeasure` (the scalar spectral measures `μ_x`).
  The QIQT-H modular operator is `Δ = (2−R)R⁻¹` with **`R` bounded self-adjoint** (the RvD operator `R = P+Q`).
  So `E_R := PVM_of_selfAdjoint R` **exists today**, and the modular Hamiltonian is just an *unbounded function*
  of it:  `K = −log Δ = log(R/(2−R)) = ∫ log(r/(2−r)) dE_R(r)`.  The only missing piece is the **unbounded**
  functional calculus `∫ f dE` (`f` unbounded Borel) as a self-adjoint `LinearPMap`, plus the identity
  `exp(it · ∫f dE) = ∫ e^{itf} dE`.  **That delivers Stone for `K` directly — no general theorem, no Cayley.**
  This is the *tractable keystone*.

- **Direction II — generator from an abstract group (Stone proper).** For the **clock energy `X`**, the group
  `λ_t` is translation on `L²(ℝ;H)`; there is **no pre-existing bounded operator whose PVM presents it**, so we
  must *construct* the generator from the group and prove it self-adjoint (the Cayley transform + the spectral
  theorem for the Cayley unitary).  This is the genuine multi-month Mathlib-grade frontier.

**So the plan front-loads Direction I (Phases 1–2: the unbounded FC + the modular Hamiltonian `K`), which is
reachable now and discharges JLMS Stage 1; Direction II (Phases 3–4: general Stone + the clock energy `X`) is
the harder, separable frontier that unblocks the crossed-product Phase 4.**  No `1/4` is ever claimed (it is the
UV datum, per `P4_WALL_CAMPAIGN_PLAN.md` §0); Stone delivers the *operators*, not the coefficient.

## 1. What Mathlib has vs lacks (verified)

- **Has:** `LinearPMap` (`E →ₗ.[𝕜] F`, densely-defined unbounded maps) with `adjoint` (`T†`), `IsFormalAdjoint`,
  `adjoint_isClosed`, `IsSelfAdjoint.isClosed` (`Analysis/InnerProductSpace/LinearPMap.lean`); `LinearMap.IsSymmetric`
  (`Analysis/InnerProductSpace/Symmetric.lean`); bounded spectral theory, CFC, scalar Fourier transform.
- **Lacks (the wall):** Stone's theorem, the infinitesimal-generator API, the **Cayley transform**, the
  **unbounded self-adjoint spectral theorem**, `exp(itA)` for unbounded `A`, C₀-semigroup/Hille–Yosida theory,
  vector-valued (`H`-coefficiented) Fourier/Plancherel.  (All confirmed absent by search.)
- **Our substrate (axiom-free, the launch pad):** `PVM_of_selfAdjoint`, `boundedFC` (unital `*`-hom),
  `scalarMeasure`/`specMeasure`, `rvdRC` (`R = P+Q`), the RvD modular formulas (`Δ = (2−R)R⁻¹`, `Δ^{it}` via
  `boundedFC` of `R`, all proved), `modUnitary`/`clockTransl` (strongly-continuous unitary groups).

## 2. The phases (each an axiom-free, green-building checkpoint; ref §s in brackets)

### Phase 1 — the unbounded functional calculus `∫ f dE` on a PVM  *(TRACTABLE KEYSTONE)*
*New file `QIQTH/Spectral/UnboundedFC.lean`.*  Given a `ProjectionValuedMeasure E` on `Ω` and a Borel
`f : Ω → ℝ` (possibly unbounded), build the self-adjoint operator `∫ f dE`.
1. **1.1 — the domain.** `D_f := {x : H | ∫ |f|² dμ_x < ∞}` (`μ_x = scalarMeasure E x`) is a `Submodule ℂ H`
   (the parallelogram/`μ_{x+y} ≤ 2μ_x + 2μ_y` bound gives closure under `+`; scaling is clear).  Dense (it
   contains every `E(f⁻¹ boundedset) x`).
2. **1.2 — the operator.** `fcLinear E f : D_f →ₗ[ℂ] H`, `x ↦` the vector with `⟪fcLinear x, y⟫ = ∫ f dμ_{x,y}`
   (the complex spectral measure from `boundedFC`'s polarization, extended to `f ∈ L¹(μ_{x,y})`); bundle as
   `unboundedFC E f : H →ₗ.[ℂ] H` with domain `D_f`.
3. **1.3 — self-adjoint.** `unboundedFC E f` is **symmetric** (`f` real ⟹ `⟪fc x, y⟫ = ⟪x, fc y⟫`) and **equals
   its adjoint** (the domain `D_f` is exactly the adjoint domain — the maximality is the spectral-integral
   estimate).  Uses Mathlib `LinearPMap.IsSelfAdjoint` / `IsFormalAdjoint`.
4. **1.4 — bounded compatibility.** For bounded `f`, `unboundedFC E f` is `boundedFC E f` (total domain) — ties
   the new FC to the existing one and lets `boundedFC` discharge the bounded sub-lemmas.
**Risk: medium–high** (the `L²(μ_x)` domain + the spectral-integral self-adjointness is real analysis, but it
rides the *existing* `scalarMeasure`/`boundedFC` machinery — no group theory, no Cayley).  **Buys:** genuine
unbounded self-adjoint operators as functions of any operator whose PVM we have — the core of the spectral theorem.

### Phase 2 — Stone for FC-operators + the modular Hamiltonian `K`  *(the JLMS Stage-1 payoff)*
*New file `QIQTH/Spectral/ModularHamiltonianOp.lean`.*
1. **2.1 — the FC exponential law.**  `exp(it · unboundedFC E f) = boundedFC E (fun ω => exp (i·t·f ω))` — the
   one-parameter unitary group generated by `∫f dE` is `∫ e^{itf} dE`.  Route: both sides agree on each `D_f`
   vector via the scalar spectral measure + dominated convergence (`|e^{itf}| = 1`, bounded; `boundedFC` a
   `*`-hom gives the group law and strong continuity).  **This is Stone (existence + reconstruction) for every
   operator presented as `∫ f dE`** — proved *without* the general theorem.
2. **2.2 — `K` as a genuine self-adjoint operator.** `E_R := PVM_of_selfAdjoint R`; define
   `K := unboundedFC E_R (fun r => Real.log (r / (2 − r)))` (`= log R − log(2−R)`, the modular Hamiltonian).
   Self-adjoint by Phase 1.3.  **Completes JLMS Stage 1**: `K` is now an operator, not just the spectral
   function `kFn` — the first law `cgpEntropy = ⟨K⟩` upgrades from a scalar integral to `⟪Φ, KΦ⟫`.
3. **2.3 — `Δ^{it} = exp(−itK)`.**  `modUnitary t = Δ^{it} = boundedFC E_R (fun r => ((2−r)/r)^{it})
   = exp(−it·K)` by 2.1 (the phase `((2−r)/r)^{it} = e^{−it log(r/(2−r))}` has modulus 1).  **Stone for the
   modular flow**, axiom-free, discharging the `K = −log Δ` frontier flagged throughout.
**Risk: medium given Phase 1.**  **Buys:** the modular Hamiltonian as a real operator; JLMS Stage 1 closed; the
modular-flow side of the crossed product upgraded from spectral function to generator.

### Phase 3 — general Stone: generator of an abstract unitary group  *(FRONTIER — Cayley + unitary spectral thm)*
*New file `QIQTH/Spectral/Stone.lean`.*  For a strongly-continuous one-parameter unitary group `U : ℝ → (H →L[ℂ] H)`
(group law + isometry + strong continuity — exactly what `clockTransl`/`modUnitary` satisfy) construct the
self-adjoint generator.  [Conway Ch. X; Reed–Simon VIII.4]
1. **3.1 — the generator as a `LinearPMap`.**  `D(A) := {x : lim_{t→0} (U_t x − x)/t exists}` (the smooth
   domain), `A x := −i · (d/dt U_t x)|₀`.  Dense (Gårding: the `U`-smoothed vectors `∫ φ(t) U_t x dt` for
   `φ ∈ C_c^∞` lie in `D(A)` and are dense).  `A` symmetric.
2. **3.2 — essential self-adjointness via the group.**  The smooth domain is `U`-invariant; by Nelson's
   analytic-vector / the deficiency-index argument (`Range(A ± i)` dense), `A` is essentially self-adjoint, so
   its closure `Ā` is self-adjoint.  **(The hard analytic core.)**
3. **3.3 — the Cayley transform + the unitary spectral theorem.**  `V := (Ā − i)(Ā + i)⁻¹` is unitary; obtain
   its PVM `E_V` on the unit circle (extend `PVM_of_selfAdjoint` to the unitary/normal case, or build `E_V` from
   `boundedFC` of the bounded self-adjoint `Re V`, `Im V`).  Transport `E_V` through the Möbius map
   `λ ↦ (λ−i)/(λ+i)` (ℝ → circle) to a PVM `E_A` for `Ā` on ℝ:  `Ā = ∫ λ dE_A`.
4. **3.4 — `U_t = exp(itĀ)`.**  Show `U_t = ∫ e^{itλ} dE_A = exp(itĀ)` (by Phase 2.1 applied to `E_A`), and
   **uniqueness** (two self-adjoint generators of the same group coincide).  **Stone, fully, both directions.**
**Risk: HIGH (multi-month, Mathlib-grade).**  Phase 3.2 (essential self-adjointness) and 3.3 (Cayley + the
unitary spectral theorem) are open Mathlib targets in their own right.  **Honest expectation:** deliver 3.1 (the
generator + density, tractable) and checkpoint at 3.2/3.3, recording the Cayley/essential-self-adjointness wall —
unless the unitary spectral theorem (3.3) factors cleanly through the existing `PVM_of_selfAdjoint` on `Re V`.

**PROGRESS — Sub-step 3.1 (the generator) ✅** (`QIQTH/Spectral/Stone.lean`, axiom-free, budget 0, full build
green): `stoneDomain U = {x : t↦U_t x differentiable at 0}` is a **ℂ-submodule** (each `U_t` ℂ-linear ⟹ closed
under `+`/`•`, via `map_add`/`map_smul` + `DifferentiableAt.add`/`.const_smul`), and `stoneGen U : H →ₗ.[ℂ] H` is
the **infinitesimal generator** `A x = −i·(d/dt U_t x)|₀` as a genuine `LinearPMap` (linearity from
`deriv_add`/`deriv_const_smul` on the smooth domain; `stoneGen_apply` the action). No hypotheses on `U` — works
for any operator family; for a strongly-continuous unitary group this is the self-adjoint Stone generator.
**FRONTIER (recorded):** density of the domain (Gårding), symmetry, essential self-adjointness (3.2, Nelson
analytic vectors), and the Cayley transform / unbounded spectral theorem (3.3) — the genuine Mathlib gaps.
Also ✅ `hasDerivAt_stoneGen` — the generator–derivative relation `HasDerivAt (t↦U_t x) (i·A x) 0` (the
`HasDerivAt` form `A x=−i(d/dt U_t x)|₀`), the foundational helper every downstream argument differentiates
through.
Also ✅ `stoneDomain_apply_mem` — **flow-invariance of the smooth domain**: for a one-parameter group, `U_s`
maps `stoneDomain U` into itself (`τ↦U_τ x` differentiable at `s` via `U_τ=U_s∘U_{τ−s}` + chain rule;
`HasDerivAt.scomp_of_eq` with `hy : y = h x` named-arg form + `HasFDerivAt.comp_hasDerivAt` with
`(U s).restrictScalars ℝ` for the ℂ-CLM over the ℝ-curve, and `import Deriv.Comp`). The `U`-invariance — a
prerequisite for essential self-adjointness (Phase 3.2).
Also ✅ `hasDerivAt_stoneGen_neg` (backward flow `t↦U_{−t}x` deriv `−i·Ax`) + `stoneGen_symmetric` — **the
generator is SYMMETRIC**: `⟪Ax,y⟫=⟪x,Ay⟫` on the smooth domain for a one-parameter unitary group (`U` group +
`U_t` inner-preserving). Proof: the unitary relation `⟪U_t x,y⟫=⟪x,U_{−t}y⟫` differentiated at `0` two ways
(`HasDerivAt.inner` product rule, full-name not dot-notation; `import InnerProductSpace.Calculus`) gives
`⟪i·Ax,y⟫=⟪x,−i·Ay⟫` ⟹ `−i⟪Ax,y⟫=−i⟪x,Ay⟫` (`Complex.conj_I`+`inner_smul`); cancel `−i`. **The first half of
self-adjointness — `A` is Hermitian on its domain.**
**REMAINING wall (Phase 3.2/3.3, the genuine Mathlib-grade frontier):** density of the smooth domain (Gårding:
the `U`-smoothed vectors `∫φ(t)U_t x dt` are dense) + **essential self-adjointness** (`Range(A±i)` dense / Nelson
analytic vectors) + the **Cayley transform**/unbounded spectral theorem. Symmetric + densely-defined + e.s.a. ⟹
`Ā` self-adjoint ⟹ Stone (`U_t=e^{itĀ}`). The Stone scaffolding (domain, generator, derivative, flow-invariance,
symmetry) is now complete; the e.s.a./Cayley analytic core is the wall.

### Phase 4 — apply general Stone to the clock energy `X = A_edge`  *(unblocks Wall Phase 4.2/4.3)*
*Extends `QIQTH/CrossedProductGenerator.lean`.*  Apply Phase 3 to `clockTransl` (`λ_t`, already proved a
strongly-continuous unitary group via `clockTransl_stronglyContinuous` — the Stone hypothesis is in hand) to get
the self-adjoint **clock energy `X`** with `λ_t = exp(itX)`; set `A_edge := X`.  **This is exactly the
crossed-product campaign's Phase 4.2/4.3, currently the recorded frontier wall** — Stone is the missing input.
*Lighter alternative (noted, also a Mathlib gap):* the `L²(ℝ)` special case — Fourier-conjugate `λ_t` to
multiplication by `e^{itξ}`, so `X = −i d/ds` is multiplication by frequency `ξ`; blocked only on **vector-valued
Fourier/Plancherel** on `L²(ℝ;H)`, which Mathlib lacks (scalar only).  Gated on Phase 3 (or that Fourier gap).

## 3. Dependency graph
```
Phase 1 (unbounded FC ∫f dE) ─→ Phase 2 (Stone for FC-ops; K, Δ^{it}=e^{−itK}) ──→ [JLMS Stage 1 DONE]
        │
        └────────────────────→ Phase 3 (general Stone: group→generator, Cayley) ─→ Phase 4 (X = A_edge)
                                                                                     [Wall Phase 4.2/4.3 DONE]
```
Phases 1–2 are reachable **now** (ride `PVM_of_selfAdjoint`/`boundedFC`).  Phase 3 is the frontier; Phase 4 is the
crossed-product payoff once Phase 3 lands.

## 4. Realistic stopping points (value at each)
- **After Phase 1:** unbounded functional calculus on a PVM — genuine unbounded self-adjoint operators; contributed
  Mathlib-grade infrastructure (the unbounded spectral integral), independently valuable.
- **After Phase 2:** the modular Hamiltonian `K` is a real operator and `Δ^{it} = e^{−itK}` — **JLMS Stage 1
  closed, the `K = −log Δ` frontier discharged for the free field** (the highest-value near-term target).
- **After Phase 3:** Stone's theorem proper — any strongly-continuous unitary group has its self-adjoint
  generator; a Mathlib-worthy result on its own.
- **After Phase 4:** the clock energy `X = A_edge` is a genuine operator — **crossed-product Phase 4.2/4.3 done,
  the "is `A_edge` vacuous?" objection closed**, Phases 5–6 (trace, JLMS, FQ bound) unblocked.

## 5. Verification (per phase/sub-step)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.Spectral.<Module>` green; `#print axioms` = standard 3 (or a
clearly-labelled cited input with an `AxiomAudit` note); `bash scripts/axiom_budget_check.sh` budget 0 (never
raised without a written audit justification); wire into `QIQTH.lean` + `AxiomAudit.lean`; one commit per
sub-step with the `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>` trailer; push via schannel; refresh
`reports/`.  Cross-check each result against its reference statement (Phase 1 vs the spectral-integral
construction; Phase 2.3 vs `Δ^{it}` RvD formula; Phase 3 vs Conway X / Reed–Simon VIII.4 / Stone).

## 6. Honest scale and scope note
Full Stone (Phase 3) is a **multi-month, research-grade** Lean undertaking — essential self-adjointness, the
Cayley transform, and the unbounded/unitary spectral theorem are open Mathlib targets.  **But the high-value
half is *not*:** Phases 1–2 (the unbounded FC + the modular Hamiltonian `K`) are reachable now because we already
hold the PVM of the bounded RvD operator `R`, and they close JLMS Stage 1 outright.  Nothing here manufactures
the `1/4` coefficient (the UV datum); Stone delivers the **operators** — `K`, `Δ^{it} = e^{−itK}`, and
(frontier) `X = A_edge` — that the trace and the JLMS bound consume.  Value lands incrementally; each phase is a
self-contained axiom-free checkpoint, and the honest frontier (Phase 3.2/3.3) is recorded, not faked.

## 7. References
Conway, *A Course in Functional Analysis* (GTM 96) — Ch. X unbounded self-adjoint operators, Cayley transform,
Stone; Reed–Simon, *Methods of Modern Mathematical Physics* I — VIII.4 (Stone), VIII.3 (spectral theorem via
Cayley); Rieffel–Van Daele (the bounded RvD modular objects — already used for `R`, `Δ`); Takesaki §1 (modular
`Δ`, the unbounded generator).
