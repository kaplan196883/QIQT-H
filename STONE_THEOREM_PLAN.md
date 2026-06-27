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
Also ✅ `stoneGen_isFormalAdjoint_self` — the generator bundled as a **symmetric unbounded operator in Mathlib's
`LinearPMap` framework**: `(stoneGen U).IsFormalAdjoint (stoneGen U)` (direct from `stoneGen_symmetric`; `import
InnerProductSpace.LinearPMap`). This is the precise `A ⊆ A*` entry point — once the domain is dense,
`stoneGen U ⊆ (stoneGen U)†` (`IsFormalAdjoint.le_adjoint`), and self-adjointness is `Ā = Ā*`. The symmetric
unbounded operator now lives in Mathlib's adjoint framework, ready for the e.s.a. criteria.

Also ✅ `stoneGen_norm_cayley_eq` + `stoneGen_norm_le_norm_add_smul_I` — **the Cayley transform's defining
properties**: `‖(A−i)x‖ = ‖(A+i)x‖` (both `= √(‖Ax‖²+‖x‖²)`), so `V : (A+i)x ↦ (A−i)x` is **norm-preserving** —
the isometry property of `V = (A−i)(A+i)⁻¹ : Range(A+i) → Range(A−i)`; and `‖x‖ ≤ ‖(A+i)x‖` (`A+i` bounded
below, hence **injective**). The Cayley transform `V` is now characterized as an isometry on the range; it is
*unitary* — equivalently `A` is essentially self-adjoint — exactly when both ranges are dense (Phase 3.3, the
open analytic wall).

Also ✅ `stoneGen_norm_add_smul_I_sq` + `stoneGen_norm_sub_smul_I_sq` (+ aux `stoneGen_re_inner_smul_I`) —
**the Cayley estimate** `‖(A ± i) x‖² = ‖A x‖² + ‖x‖²` for the symmetric generator. The cross term
`re⟪A x, i•x⟫ = 0` (since `⟪A x, x⟫` is real by symmetry, and `×i` rotates it to the imaginary axis;
`RCLike.I_mul_re` + `RCLike.conj_eq_iff_im`). Consequence: `A ± i` are **bounded below** (`‖(A±i)x‖ ≥ ‖x‖`),
hence **injective** — this is the entry point to the **Cayley transform** `V = (A−i)(A+i)⁻¹` and the
**deficiency-index** criterion for essential self-adjointness. (Injectivity is unconditional/algebraic here;
*surjectivity* of `A ± i`, i.e. `Range(A±i)` dense, is the open analytic wall of Phase 3.3.)

Also ✅ `hasDerivAt_stoneGen_flow` + `stoneGen_comm_flow` — **the generator commutes with the flow**
`[A, U_s] = 0`: `stoneGen U (U_s x) = U_s (stoneGen U x)` on the smooth domain. The shifted orbit
`t ↦ U_t (U_s x)` has derivative `i • U_s (A x)` at `0` (factored out as `hasDerivAt_stoneGen_flow` — the key
derivative computation, of which `stoneDomain_apply_mem` is now simply the `.differentiableAt`), so by
generator-identification `A (U_s x) = U_s (A x)`. This `U`-invariance of `A` is what makes the generator —
hence the clock energy `X = A_edge` (Phase 4.3) — compatible with the very modular flow it is read off from.

Also ✅ `stoneGen_eq_of_hasDerivAt` — **generator identification** (the uniqueness half of Stone's
correspondence): if `HasDerivAt (t ↦ U_t x) (i•v) 0` then `stoneGen U ⟨x,hx⟩ = v` (via `HasDerivAt.unique` +
`smul_right_injective` on `i ≠ 0`). The generator is *pinned* by any witnessed derivative — the bridge from the
abstract `stoneGen` to a concrete operator: to show `stoneGen` of a given group equals a known `B`, it suffices
to exhibit `HasDerivAt (t ↦ U_t x) (i•B x) 0`. No density needed; this is exactly the tool that will identify
`stoneGen translationLp = P`, `stoneGen modUnitary = −K`, `stoneGen clockTransl = X` once those derivatives are
in hand.

Also ✅ `stoneGen_le_adjoint` — the **explicit `A ⊆ A†` containment**, `stoneGen U ≤ (stoneGen U)†` via
`IsFormalAdjoint.le_adjoint`, **conditional on `hdense : Dense (stoneGen U).domain`** (left as an explicit
hypothesis — `le_adjoint` genuinely requires it). This is the symmetric-operator containment that
self-adjointness `Ā = Ā†` upgrades from `⊆` to `=`. The density hypothesis is the honestly-carried wall:
proving `Dense (stoneGen U).domain` for the concrete C₀ groups (the **Gårding/mollified-vector** argument,
`x_φ = ∫ φ(t) U_t x dt`) is the genuine Mathlib-grade analytic frontier of Phase 3.2 — the whole symmetric
operator-theoretic scaffolding above it is now complete and Mathlib-integrated, axiom-free at budget 0.

### Phase 4 — apply general Stone to the clock energy `X = A_edge`  *(unblocks Wall Phase 4.2/4.3)*
*Extends `QIQTH/CrossedProductGenerator.lean`.*  Apply Phase 3 to `clockTransl` (`λ_t`, already proved a
strongly-continuous unitary group via `clockTransl_stronglyContinuous` — the Stone hypothesis is in hand) to get
the self-adjoint **clock energy `X`** with `λ_t = exp(itX)`; set `A_edge := X`.  **This is exactly the
crossed-product campaign's Phase 4.2/4.3, currently the recorded frontier wall** — Stone is the missing input.
*Lighter alternative (noted, also a Mathlib gap):* the `L²(ℝ)` special case — Fourier-conjugate `λ_t` to
multiplication by `e^{itξ}`, so `X = −i d/ds` is multiplication by frequency `ξ`; blocked only on **vector-valued
Fourier/Plancherel** on `L²(ℝ;H)`, which Mathlib lacks (scalar only).  Gated on Phase 3 (or that Fourier gap).

**PROGRESS — Phase 4 (the clock energy `X` as a symmetric operator) ✅** (`QIQTH/CrossedProductGenerator.lean`,
axiom-free, budget 0): `clockTransl_inner` — `⟪λ_t a, λ_t b⟫ = ⟪a, b⟫` (clock translation a ℂ-linear isometry,
`inner_map_map`), the diamond-free **unitary** statement and the third Stone hypothesis (`hUinner`); with
`clockTransl_add` + `clockTransl_zero` + `clockTransl_stronglyContinuous`, all three hypotheses of the general
`stoneGen` are discharged for the concrete clock group. Then the **concrete clock energy operator**:
`clockEnergy := stoneGen clockTransl` (its closure `= A_edge`), `clockEnergy_isFormalAdjoint_self` (X symmetric),
`clockEnergy_norm_add_smul_I_sq` (Cayley estimate), `clockEnergy_norm_le_norm_add_smul_I` (X+i bounded below /
injective) — instantiating the general lemmas (the new `_dom` projection-typed forms) for `clockTransl`.
**The `Lp`-elaboration wall is DEFEATED:** the `whnf`/`isDefEq` divergence on the `(stoneGen _).domain` projection
through the heavy `Lp` instance tower (Phase-1.1/1.3 friction) is killed by
`attribute [local irreducible] stoneGen stoneDomain` + explicit ambient `(H := Lp H 2 volume)`. **Remaining
analytic frontier:** essential self-adjointness `Range(X ± i)` dense (Gårding density) — needed before Stone
returns `λ_t = exp(itX)` — stays the carried wall, NOT claimed.

**PROGRESS — Phase 4 (the momentum operator `P`) ✅** (`QIQTH/Spectral/MomentumGenerator.lean`, axiom-free,
budget 0): the same instantiation pattern applied to the translation group `τ_t = translationLp t = e^{itP}` on
`L²(ℝ)` — `translationCLM` (CLM form) with `translationCLM_zero`/`_add`/`_inner` (the three Stone hypotheses),
then `momentumOp := stoneGen translationCLM = −i d/dx` with `momentumOp_isFormalAdjoint_self` (P symmetric),
`momentumOp_norm_add_smul_I_sq` (Cayley estimate), `momentumOp_norm_le_norm_add_smul_I` (P+i injective). Two of
the three named C₀ generators (`X = A_edge`, `P`) now exist as concrete symmetric operators; the modular `Δ^{it}`
(→ `K`) is the third. e.s.a. (`Range(P ± i)` dense) stays the carried analytic frontier.

**PROGRESS — Phase 4 (the modular Hamiltonian `K`) ✅ — the trio is complete** (`QIQTH/Spectral/ModularGenerator.lean`,
axiom-free, budget 0): the same pattern applied to the modular flow `Δ^{it} = modUnitary S t` on the abstract
one-particle space — `modUnitary_compL`/`modUnitary_zero`/`inner_modUnitary_self` (the three Stone hypotheses, the
last derived from `modUnitary_adjoint`), then `modularGen := stoneGen (modUnitary S) = −i d/dt Δ^{it}` (= the JLMS
`K`) with `modularGen_isFormalAdjoint_self` (K symmetric), `modularGen_norm_add_smul_I_sq` (Cayley estimate),
`modularGen_norm_le_norm_add_smul_I` (K+i injective). On the abstract space — **no `Lp`/`irreducible` workaround
needed**. **All three named C₀ generators (`X = A_edge`, `P`, `K`) are now concrete symmetric operators with
`±i` injective.** The shared remaining analytic frontier is e.s.a. = `Range(·±i)` dense (Gårding density).

**PROGRESS — Gårding mollifier foundation ✅** (`QIQTH/Spectral/Garding.lean`, axiom-free, budget 0): the first
constructive step into the e.s.a. frontier. `mollify U φ x := ∫ φ(t) U_t x dt` (the Gårding mollified vector);
`mollify_integrable` (the integrand `φ(t)U_t x` is integrable — continuous × compact support, for `φ ∈ Cc` and
`U` strongly continuous); `mollify_apply_flow` — the **flow-shift identity** `U_s x_φ = ∫ φ(t) U_{s+t} x dt`
(`U_s` through the Bochner integral via `integral_comp_comm` + the group law). This is the algebraic core of
Gårding: differentiating the RHS in `s` *under the integral* is exactly what places `x_φ` in the smooth domain.
Also ✅ `mollify_apply_flow_cov` — the orbit in **differentiation-ready form** `U_s x_φ = ∫ φ(u − s) U_u x du`
(change of variables `u = s + t`, `integral_add_right_eq_self`). Now the `s`-dependence sits *entirely* in the
smooth scalar `φ(u − s)` — the `U_u x` factor is `s`-independent — so the orbit is set up for differentiation
under the integral (`d/ds|₀ = −∫ φ'(u) U_u x du`).
Also ✅ `mollify_integrand_hasDerivAt` — the **calculus core** of the differentiation step (the `h_diff`
hypothesis of `hasDerivAt_integral_of_dominated_loc_of_deriv_le`): for `φ ∈ C¹`, `σ ↦ φ(u−σ) • U_u x` has
derivative `−φ'(u−σ₀) • U_u x` at `σ₀` (chain rule `HasDerivAt.scomp` on the inner `u−σ`, then `smul_const` by
`U_u x`). The pointwise derivative is now in hand.
Also ✅ the remaining *easy* differentiation hypotheses: `mollify_shifted_aestronglyMeasurable` (`hF_meas`, ∀σ)
+ `mollify_deriv_aestronglyMeasurable` (`hF'_meas`) — the integrands are continuous ⟹ `AEStronglyMeasurable`;
and `mollify_neg_deriv_eq` — `∫ (−φ'(u)) • U_u x = −mollify U φ' x`, i.e. **the would-be derivative of `U_s x_φ`
is again a Gårding vector** (`−x_{φ'}`), so the smooth subspace is *closed under the generator*.
**Remaining (the genuine analytic frontier — now a SINGLE hypothesis):** with `mollify_integrable` (`hF_int`),
`mollify_integrand_hasDerivAt` (`h_diff`), the two measurability lemmas (`hF_meas`/`hF'_meas`), the only missing
hypothesis of `hasDerivAt_integral_of_dominated_loc_of_deriv_le` is the **integrable dominating bound**
`supₛ |φ'(u−s)|·‖x‖` (from compact support of `φ'` ⟹ indicator of a compact set).
Also ✅ the two compact-support consequences the bound `C·M·𝟙_K` rests on: `exists_norm_le_of_compactSupport`
(`φ'` bounded, `C = ‖φ'‖_∞`, via `Continuous.bddAbove_range_of_hasCompactSupport`) +
`exists_support_subset_of_compactSupport` (`φ'` vanishes outside `{|y| ≤ ρ}`, via `tsupport` bounded +
`image_eq_zero_of_notMem_tsupport`).
**★★ MILESTONE — the Gårding differentiation is DONE; the smooth domain is nonempty.**
✅ `integrable_indicator_closedBall_const` — the dominating bound `C·M·𝟙_{closedBall}` is integrable (compact ⟹
finite measure). ✅ `mollify_orbit_hasDerivAt` — the orbit `s ↦ ∫ φ(u−s) U_u x du` is **differentiable at `0`**
with derivative `∫ (−φ'(u)) U_u x du`, via `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the bound
`C·M·𝟙_K` (domination = case split on `|u| ≤ ρ+1`; needs a uniform `‖U_u x‖ ≤ M`, `= ‖x‖` for unitary).
✅ `mollify_mem_stoneDomain` — **`mollify U φ x ∈ stoneDomain U`**: the orbit `U_s x_φ = ∫ φ(u−s) U_u x du`
(`mollify_apply_flow_cov`) is differentiable ⟹ `x_φ` is in the smooth domain. **The smooth domain of the Stone
generator is NONEMPTY — it contains every Gårding vector. The hardest analytic step of essential
self-adjointness (differentiation under the Bochner integral) is complete, axiom-free.**
Also ✅ the **Gårding-approximation identity** toward density: `mollify_sub` — `x_φ − (∫φ)·x = ∫ φ(t)(U_t x − x) dt`
(subtract the constant field `(∫φ)·x = ∫ φ(t)·x`, via `integral_smul_const` + `integral_sub`); `norm_mollify_sub_le`
— `‖x_φ − (∫φ)·x‖ ≤ ∫ ‖φ(t)‖·‖U_t x − x‖` (`norm_integral_le_integral_norm`). With `∫φ = 1` and `φ ≥ 0`
concentrated near `0`, the bound `→ 0` by strong continuity (`U_t x → x`), i.e. `x_φ → x`.
Also ✅ the **Gårding ε-bound** `norm_mollify_sub_le_uniform`: if `‖U_t x − x‖ ≤ ε` wherever `φ(t) ≠ 0`
(on `supp φ`), then `‖x_φ − (∫φ)·x‖ ≤ ε · ∫‖φ‖` (pointwise integrand bound `‖φ t‖·‖U_t x−x‖ ≤ ε·‖φ t‖` +
`integral_mono` + `integral_const_mul`). For a Dirac sequence (`∫|φ| = 1`, `φ` supported near `0`) this is `≤ ε`,
and `→ 0` by strong continuity ⟹ `x_φ → x`.
Also ✅ the **density assembly** `exists_mem_stoneDomain_norm_sub_le`: combining `mollify_mem_stoneDomain`
(Gårding vector ∈ smooth domain) + `norm_mollify_sub_le_uniform` (the ε-bound) — a normalized `C¹_c` mollifier
`φ` averaging to `x` (`(∫φ)·x = x`) and supported where `‖U_t x − x‖ ≤ ε` yields `y = x_φ ∈ stoneDomain U` with
`‖y − x‖ ≤ ε · ∫‖φ‖`. With a Dirac bump (`∫‖φ‖ = 1`, support shrinking) this gives, for every `x` and `ε`, a
smooth-domain vector within `ε` — i.e. **density of the smooth domain**.
**★★★ MILESTONE — THE SMOOTH DOMAIN IS DENSE (the Gårding-density argument is complete, axiom-free).**
✅ `exists_delta_norm_sub_lt` — strong continuity (`U_0 = 1`, `t ↦ U_t x` cont) ⟹ for each `ε > 0`, `∃ δ`,
`‖U_t x − x‖ < ε` for `|t| < δ`. ✅ `stoneDomain_dense` — for a contractive strongly-continuous family
(`U_0 = 1`, `‖U_t y‖ ≤ ‖y‖`, `t ↦ U_t y` cont), **`Dense (stoneDomain U)`**: a normalized `C^∞` bump
(`ContDiffBump.normed`, `ℝ → ℂ`-coerced, supported in `(−δ/2, δ/2)`) fed to `exists_mem_stoneDomain_norm_sub_le`
yields a Gårding vector `x_φ ∈ stoneDomain U` with `‖x_φ − x‖ < r`. **This discharges the density hypothesis of
`stoneGen_le_adjoint` — the last analytic input to essential self-adjointness.**
Also ✅ `stoneGen_subset_adjoint` — **the unconditional `A ⊆ A†`**: `stoneGen U ≤ (stoneGen U)†` for a
contractive one-parameter unitary group, composing `stoneGen_le_adjoint` (conditional on density) with
`stoneDomain_dense` (which discharges it). The symmetric densely-defined generator is now contained in its
`LinearPMap` adjoint *with no carried hypotheses* beyond the C₀-unitary-group structure — the textbook
"symmetric operator" statement, machine-checked.
Also ✅ `stoneGen_isClosable` — **the closure `Ā` exists**: `(stoneGen U).IsClosable` for a contractive unitary
group. The symmetric densely-defined generator has a closed extension (its adjoint `A†`, closed by
`LinearPMap.adjoint_isClosed` given the dense smooth domain) and `A ⊆ A†`, so it is closable
(`IsClosable.leIsClosable`) — the prerequisite for forming `Ā = (stoneGen U).closure` and asking `Ā = Ā†`.
Also ✅ the **resolvent foundation** toward `Range(A±i)` dense: `resolvent U x := ∫₀^∞ e^{−t} U_t x dt = (1−iA)⁻¹ x`
+ `resolvent_integrand_integrableOn` — the half-line integrand `e^{−t} U_t x` is `IntegrableOn (0,∞)` (exp decay
`e^{−t}` dominates the bounded orbit `‖U_t x‖ ≤ ‖x‖`, `∫₀^∞ e^{−t} < ∞` via `exp_neg_integrableOn_Ioi`).
Also ✅ `norm_resolvent_le` — **the resolvent is a contraction** `‖R x‖ ≤ ‖x‖` (since `‖e^{−t} U_t x‖ ≤ e^{−t}‖x‖`
and `∫₀^∞ e^{−t} = 1`, via `integral_exp_neg_Ioi_zero` + `setIntegral_mono_on` + `norm_integral_le_integral_norm`);
so `R = (1 − iA)⁻¹` is a bounded operator (norm `≤ 1`), giving `1 − iA = −i(A + i)` a bounded right inverse.
Also ✅ `resolvent_apply_flow` — **the flow-on-resolvent identity** `U_s (R x) = ∫₀^∞ e^{−t} U_{s+t} x dt`
(`U_s` through the set Bochner integral via `integral_comp_comm` + `ContinuousLinearMap.map_smul_of_tower` for
the `ℝ`-smul + the group law) — the algebraic core of the resolvent identity. Plus `resolvent_add` (`R(x+y)=Rx+Ry`)
+ `resolvent_smul` (`R(c•x)=c•Rx`): **`R` is ℂ-linear**, so with `norm_resolvent_le` it is a bounded ℂ-linear
operator `(1 − iA)⁻¹`. Plus `resolvent_comm_flow` — **`R` commutes with the flow** `U_s (R x) = R (U_s x)` (from
`resolvent_apply_flow` + the group law, `U_{s+t} = U_{t+s}`), hence with the generator `A`. Plus
`resolvent_apply_flow_cov` — **the differentiation-ready form** `U_s (R x) = e^s ∫_s^∞ e^{−u} U_u x du` (change of
variables `u = s+t` via `setIntegral_preimage_emb` for the translation, `(·+s)⁻¹(Ioi s)=Ioi 0`, + `integral_smul`
+ the exponent algebra `e^s·e^{−(t+s)}=e^{−t}`): now the `s`-dependence sits in the smooth `e^s` factor and the
integration *limit* `s` only. Plus `resolvent_halfline_hasDerivAt` — **the FTC for the half-line integral**
`d/ds ∫_s^∞ e^{−u} U_u x du = −(e^{−s} U_s x)` (splitting `∫_{Ioi s} = ∫_{Ioi s₀} − ∫_{s₀}^s` via
`integral_Ioi_sub_Ioi'`, with `resolvent_integrand_integrableOn_Ioi` for any lower limit, + the FTC
`integral_hasDerivAt_right` + `HasDerivAt.congr_of_eventuallyEq`).

**★★ MILESTONE — the RESOLVENT IDENTITY `(A + i)(R x) = i x`.** `resolvent_orbit_hasDerivAt` — `d/ds U_s(R x)|₀ =
R x − x` (product rule `(Real.hasDerivAt_exp 0).smul` on `e^s G(s)` + the FTC + `U_0 = 1`); `resolvent_mem_stoneDomain`
— **`R x ∈ stoneDomain U`** (the resolvent maps `H` *into* the generator's domain); `resolvent_stoneGen` —
**`stoneGen U (R x) = −i(R x − x)`** (generator identification), i.e. `(A + i)(R x) = i x`, so
`Range(A + i) ⊇ {i x : x} = H`. **The deficiency-index-zero fact that makes the generator essentially self-adjoint
is now machine-checked.** Also ✅ `stoneGen_add_I_surjective` — **`A + i` is surjective, `Range(A + i) = H`**:
`∀ y, ∃ z ∈ stoneDomain U, A z + i z = y` (witness `z := R(−i y)`, since `(A+i)(R(−i y)) = i(−i y) = y`). So the
deficiency subspace `Range(A+i)^⊥ = ker(A† − i) = 0` — the essential-self-adjointness criterion (with the `A − i`
mirror).

**★★ MILESTONE — BOTH deficiency indices are zero (`Range(A ± i) = H`).** The reversed group `t ↦ U_{−t}` has
generator `−A` (`stoneGen_reversed_eq`, via `hasDerivAt_stoneGen_neg` + `mem_stoneDomain_reversed`/`_of_reversed`);
applying `stoneGen_add_I_surjective` to it + the bridge gives `stoneGen_sub_I_surjective` —
**`∀ y, ∃ z ∈ stoneDomain U, A z − i z = y`, i.e. `Range(A − i) = H`**. With `Range(A + i) = H` already proven,
**both deficiency indices of the symmetric generator `A = stoneGen U` vanish — the essential-self-adjointness
criterion is fully machine-checked.** The remaining Mathlib-grade gap is the *criterion itself*: bundling
`A ⊆ A†` + `Range(A ± i) = H` ⟹ `Ā = Ā†` (`IsSelfAdjoint`) via the Cayley transform, then the unbounded spectral
theorem ⟹ Stone `U_t = exp(it Ā)`. Mathlib has neither the Cayley transform nor the criterion; all the *inputs*
are now proven. Also ✅ `deficiency_add_trivial` / `deficiency_sub_trivial` — **the deficiency subspaces are
trivial in canonical inner-product form**: if `⟪(A ± i)x, y⟫ = 0 ∀ x` (i.e. `y ⊥ Range(A ± i)`) then `y = 0`
(from surjectivity: `y = (A ± i)z` ⟹ `⟪y, y⟫ = 0` ⟹ `y = 0` by `inner_self_eq_zero`). So
`ker(A† ∓ i) = Range(A ± i)^⊥ = 0` — the textbook essential-self-adjointness criterion's exact content.
Also ✅ `ker_adjoint_sub_I_trivial` / `ker_adjoint_add_I_trivial` — **`A†` has no `±i`-eigenvectors** in Mathlib's
`LinearPMap.adjoint` API: if `(stoneGen U).adjoint ⟨w,hw⟩ = ±i w` then `w = 0` (via the formal-adjoint relation
`⟪A z, w⟫ = ⟪z, A† w⟫` from `adjoint_isFormalAdjoint.symm`, reducing to the deficiency lemmas). This is the *exact
hypothesis* the self-adjointness criterion `A ⊆ A† + ker(A† ∓ i) = 0 ⟹ Ā = Ā†` consumes — now in adjoint form.

**★★★ MILESTONE — THE STONE GENERATOR IS SELF-ADJOINT.** `stoneGen_isSelfAdjoint` —
`IsSelfAdjoint (stoneGen U)`, i.e. `(stoneGen U).adjoint = stoneGen U`, for a contractive strongly-continuous
one-parameter unitary group. The **basic criterion for self-adjointness** (symmetric `A ⊆ A†` with
`Range(A ± i) = H` ⟹ `A = A†`, *no Cayley transform needed*): `A ⊆ A†` + `LinearPMap.eq_of_le_of_domain_eq`,
with the domain equality `dom(A) = dom(A†)` from surjectivity (`stoneGen_add_I_surjective`) + `ker(A† + i) = 0`
(`ker_adjoint_add_I_trivial`): for `y ∈ dom(A†)`, `∃ z ∈ dom(A)` with `(A + i)z = (A† + i)y`, then
`A†(y − z) = −i(y − z)` ⟹ `y = z ∈ dom(A)`. **The generator of a unitary group is a genuine self-adjoint
unbounded operator** — the spectral theorem's hypothesis, machine-checked axiom-free. **Instantiated for all three named generators** (axiom-free): `clockEnergy_isSelfAdjoint`
(`X = A_edge = stoneGen clockTransl`, Lp), `momentumOp_isSelfAdjoint` (`P = stoneGen translationCLM`, L²(ℝ)),
`modularGen_isSelfAdjoint` (`K = stoneGen (modUnitary S)`, the JLMS modular Hamiltonian, abstract space).
Also ✅ `stoneGen_add_I_bijective` — **`A + i` is a bijection `dom(A) → H`** (the Cayley-transform foundation):
injective from the bounded-below estimate `‖x‖ ≤ ‖(A + i)x‖`, surjective from `stoneGen_add_I_surjective`. So
`(A + i)⁻¹ : H → dom(A)` exists.
Also ✅ `cayley` + `norm_cayley` — **the Cayley transform `V = (A − i)(A + i)⁻¹` is built and is an isometry
`‖V y‖ = ‖y‖`**: `cayleyEquiv := Equiv.ofBijective _ stoneGen_add_I_bijective` is the bijection `A+i : dom(A) ≃ H`,
its `.symm` is `(A+i)⁻¹`, and `cayley y := (A−i)((A+i)⁻¹ y)`. The isometry is `‖V y‖ = ‖(A−i)z‖ = ‖(A+i)z‖ = ‖y‖`
where `z = (A+i)⁻¹ y` (the Cayley isometry `stoneGen_norm_cayley_eq` + `apply_symm_apply`).
Also ✅ `stoneGen_sub_I_bijective` + `cayley_bijective` — **`V` is a unitary (bijective + isometric)**:
`A−i : dom(A) → H` is a bijection (mirror of `A+i`: injective from `‖x‖ ≤ ‖(A−i)x‖ = ‖(A+i)x‖`, surjective from
`stoneGen_sub_I_surjective`), and `V = (A−i) ∘ (A+i)⁻¹ = (stoneGen_sub_I_bijective).comp (cayleyEquiv).symm.bijective`
is bijective. With `norm_cayley` (`‖V y‖ = ‖y‖`), `V` is a **unitary**.
Also ✅ `cayleyEquiv_symm_add/_smul` + `cayley_add/_smul` + `cayleyLM` + **`cayleyUnitary : H ≃ₗᵢ[ℂ] H`** —
`V` is **bundled as a genuine unitary operator**: `(A+i)⁻¹` is ℂ-linear (additive + homogeneous, from injectivity
of `A+i` + `LinearPMap.map_add/map_smul`), so `V` is ℂ-linear (`cayleyLM : H →ₗ[ℂ] H`), and
`cayleyUnitary := LinearEquiv.ofBijective cayleyLM cayley_bijective` with `norm_map' := norm_cayley` packages it as
a `LinearIsometryEquiv`. The three generators `X=A_edge`, `P`, `K` each have a Cayley unitary.
Also ✅ `cayley_mem_unitary` + `cayleyUnitaryElt` — **`V` is a unitary element of the C\*-algebra** `H →L[ℂ] H`
(`star V * V = V * star V = 1`, via `LinearIsometryEquiv.star_eq_symm`), bundled as `cayleyUnitaryElt :
unitary (H →L[ℂ] H)`. This is the **doorway to Mathlib's continuous functional calculus**: `V` is unitary/normal,
so `cfc f V` exists for continuous `f` and `spectrum ℂ V ⊆ circle`.
Also ✅ `cayley_spectrum_subset_circle` — **`spectrum ℂ V ⊆ Metric.sphere 0 1`** (from
`spectrum.subset_circle_of_unitary` + `cayley_mem_unitary`): the geometric foundation of `V`'s spectral theorem —
the circle-PVM is supported on `S¹`, and the inverse Cayley map `z ↦ i(1+z)(1−z)⁻¹` pulls `S¹∖{1}` back to the real
spectrum of `A = stoneGen U`.
Also ✅ `cayley_one_sub` + `cayley_one_sub_injective` — **`1` is not an eigenvalue of `V`** (`ker(1 − V) = 0`):
`y − V y = 2i·(A + i)⁻¹ y` (explicit defect formula), and `(A + i)⁻¹` is injective, so `y ↦ y − V y` is injective.
This is the precise condition that `V` is the **Cayley transform of a densely-defined self-adjoint operator**: the
inverse Cayley `A = i(1 + V)(1 − V)⁻¹` is well-defined on `ran(1 − V)` = the smooth domain — the route back from the
circle-spectral data to the generator.
Also ✅ `cayley_one_sub_denseRange` — **`1 − V` has dense range** (`DenseRange (fun y => y − V y)`): `ran(1 − V) =
2i·dom(A) = 2i·stoneDomain U`, dense (`stoneDomain_dense`) since scaling by `2i ≠ 0` is a homeomorphism
(`Homeomorph.smulOfNeZero`). Together with `cayley_one_sub_injective` this is the **complete** characterization:
`V` is the Cayley transform of a densely-defined self-adjoint `A` (both `ker(1 − V) = 0` *and* `ran(1 − V)` dense).
Also ✅ `cayley_spectrum_isCompact` — **`spectrum ℂ V` is compact** (`spectrum.isCompact`); with the circle
containment, `σ(V)` is a *compact subset of `S¹`*. This is the **Riesz–Markov precondition**: on the compact
`σ(V)`, `C(σV) = C_c(σV)`, so the positive functional `f ↦ ⟨x, cfc f V x⟩` (CFC in hand via `V ∈ unitary`;
`H →L[ℂ] H` is a `StarOrderedRing`) yields a finite Borel `μ_x` via `RealRMK.rieszMeasure` — the first rung of the
operator → PVM keystone, now API-identified.
Also ✅ `cayley_isStarNormal` — **`IsStarNormal V`** (`isStarNormal_of_mem_unitary ∘ cayley_mem_unitary`), the
predicate the ℂ continuous functional calculus requires — and `nonneg_re_inner_nonneg` — **`0 ≤ T ⟹ 0 ≤ re⟪x,Tx⟫`**
(`ContinuousLinearMap.nonneg_iff_isPositive` + `IsPositive.re_inner_nonneg_right`), the **functional-positivity
step**: once `cfc` gives `0 ≤ cfc f V` for `f ≥ 0` on `σ(V)`, `f ↦ re⟪x, cfc f V x⟫` is a positive functional that
`RealRMK.rieszMeasure` turns into `μ_x`.
Also ✅ `cayley_cfc_id` `[Nontrivial H]` — **`cfc id V = V`**, the `C(σ(V))`-level form of `V = ∫_{S¹} z dE(z)`:
the coordinate function `z ↦ z`, applied to `V` through its continuous spectral data, returns `V` itself. Once the
bounded-PVM `E` exists this *becomes* the PVM identity; here it is its continuous-FC shadow and the base case the
scalar-measure construction integrates against.
**Obstruction (raised last fire) now RESOLVED:** the ℂ-normal CFC is a *local-instance theorem*
(`IsStarNormal.instContinuousFunctionalCalculus`) needing `[Nontrivial A]`, but it IS enableable —
`attribute [local instance]` + importing `CStarAlgebra.ContinuousLinearMap` (the `CStarAlgebra (H→L[ℂ]H)` instance)
and `CFC.Basic` + threading `[Nontrivial H]` (the named generators `X=A_edge`, `P`, `K` are all on nontrivial
spaces). So the cfc-of-`V` route is open; the scalar measures `μ_x` can now be built.
Also ✅ `cayley_cfc_one` (`cfc 1 V = 1`, the **resolution of identity** `∫ 1 dE = 1`; with `cayley_cfc_id`'s
`∫ z dE = V` these are `μ_x`'s total mass and first moment) and `cayley_cfc_sq_re_inner_nonneg` — **the
Riesz–Markov functional is positive**: `0 ≤ re⟪x, cfc (conj f · f) V x⟫` for `f` continuous on `σ(V)`, since
`cfc (conj f·f) V = (cfc f V)⋆(cfc f V) ≥ 0` (`cfc_mul`+`cfc_star`+`star_mul_self_nonneg`) so the expectation is
`‖cfc f V x‖² ≥ 0`. As the `|f|²` generate the nonneg cone of `C(σ(V), ℝ)`, this is exactly the positivity
`RealRMK.rieszMeasure` consumes to produce `μ_x` (with `∫ g dμ_x = re⟪x, cfc g V x⟫`).
Also ✅ `cayley_cfc_re_inner_nonneg_of_nonneg` — **the RMK functional is positive on the whole nonnegative cone**:
`0 ≤ re⟪x, cfc g V x⟫` for *any* `g` continuous on `σ(V)` that is real and `≥ 0` there (reduce to the square via
`g = |√g|²`: `h z = √((g z).re)`, `conj(h)·h = g` on `σ(V)` by `cfc_congr`, then the square lemma; closed with
`le_of_le_of_eq` + `congrArg` to dodge cfc proof-irrelevance). This is exactly the `0 ≤ g ⟹ 0 ≤ Λg` hypothesis a
positive linear functional needs.
Also ✅ `cayley_cfc_re_inner_add` + `cayley_cfc_re_inner_smul` — **the functional is ℝ-linear**:
`re⟪x, cfc (f+g) V x⟫ = re⟪x, cfc f V x⟫ + re⟪x, cfc g V x⟫` (`cfc_add` + `inner_add_right` + `Complex.add_re`) and
`re⟪x, cfc (↑c·f) V x⟫ = c·re⟪x, cfc f V x⟫` for `c : ℝ` (`cfc_const_mul` + `inner_smul_right` +
`Complex.re_ofReal_mul`). **With the positivity, `g ↦ re⟪x, cfc g V x⟫` is now a fully machine-checked positive
ℝ-linear functional** — every mathematical component `RealRMK.rieszMeasure` needs.
Also ✅ `expectationCLM x` (`Φ_x : (H→L[ℂ]H) →L[ℂ] ℂ`, `T ↦ ⟪x,Tx⟫` = `innerSL ℂ x ∘ eval_x`) and
`reExpectationCLM x` (`(H→L[ℂ]H) →L[ℝ] ℝ`, `T ↦ re⟪x,Tx⟫` = `Complex.reCLM ∘ Φ_x|_ℝ`) — **the bundled
Riesz–Markov functional** (postcomposition complete): precomposed with `cfcHom V` and restricted to `C_c(σ(V),ℝ)`,
`reExpectationCLM` *is* `g ↦ re⟪x, cfc g V x⟫`, whose positivity + ℝ-linearity (proven) are the `→ₚ[ℝ]` data.
Also ✅ `cfcReExpectationCLM` `[Nontrivial H]` — **the RMK functional on `C(σ(V), ℂ)`** as a bundled ℝ-linear CLM:
`φ ↦ re⟪x, cfcHom V φ x⟫` = `reExpectationCLM x ∘ (cfcL V)|_ℝ`, where `cfcL V : C(σ(V),ℂ) →L[ℂ] (H→L[ℂ]H)` is the
continuous functional calculus bundled as a CLM. **The `cfcHom` precomposition is now done** — only the `ℝ↪ℂ`
domain restriction + the `→ₚ[ℝ]`/`C_c` packaging remain before `RealRMK.rieszMeasure`.
Also ✅ `realCfcReExpectationCLM` `[Nontrivial H]` — **the RMK functional on the real functions `C(σ(V), ℝ)`** as a
bundled ℝ-linear CLM: `g ↦ re⟪x, cfcHom V (↑∘g) x⟫` = `cfcReExpectationCLM x ∘ (ℝ↪ℂ)`, the `ℝ↪ℂ` embedding being
`ContinuousLinearMap.compLeftContinuous ℝ (σ(V)) Complex.ofRealCLM`. **The `ℝ↪ℂ` domain restriction is now done** —
the functional is a concrete `C(σ(V),ℝ) →L[ℝ] ℝ`. Since `σ(V)` is compact, `C(σ(V),ℝ) = C_c(σ(V),ℝ)`.
Also ✅ `realCfcReExpectation_nonneg` `[Nontrivial H]` — **the functional is monotone/positive**: `0 ≤ g ⟹ 0 ≤
realCfcReExpectationCLM x g` for `g : C(σ(V),ℝ)`. Bridge `cfcL ha (↑∘g) = cfcHom ha (↑∘g) = cfc (extend (↑∘g)) V`
(`cfcL_apply` + `cfcHom_eq_cfc_extend`); the extended function is `ContinuousOn σ(V)` and real-`≥0` there, so
`cayley_cfc_re_inner_nonneg_of_nonneg` applies. **This is the `→o`/`monotone'` field** — with the ℝ-linearity
(`realCfcReExpectationCLM` is a CLM), `realCfcReExpectationCLM x` upgrades to a `C(σ(V),ℝ) →ₚ[ℝ] ℝ` positive linear
functional.
Also ✅ `cfcPLM` `[Nontrivial H]` — **the scalar spectral functional as a `C(σ(V), ℝ) →ₚ[ℝ] ℝ` positive linear
functional**: `toLinearMap := (realCfcReExpectationCLM x).toLinearMap`, `monotone'` from
`realCfcReExpectation_nonneg` (a linear map is monotone iff `0 ≤ y ⟹ 0 ≤ f y`, via `f b − f a = f (b − a) ≥ 0`).
**This is THE input `RealRMK.rieszMeasure` consumes.**
Also ✅ `cfcPLMcc` `[Nontrivial H]` — **the RMK input** `C_c(σ(V), ℝ) →ₚ[ℝ] ℝ`, `f ↦ re⟪x, cfc f V x⟫` = `cfcPLM`
precomposed with the forgetful `C_c(σV,ℝ) → C(σV,ℝ)` (compact spectrum ⟹ bijection); `map_add'`/`map_smul'` from
`cfcPLM`'s, `monotone'` from `cfcPLM.monotone'`. **This is exactly the type `RealRMK.rieszMeasure` consumes.**
Also ✅ `cayleyScalarMeasure` `[Nontrivial H]` — **the scalar spectral measure `μ_x` of `V` is CONSTRUCTED**:
`Measure (spectrum ℂ V) := RealRMK.rieszMeasure (cfcPLMcc x)`, the finite Borel measure on `σ(V) ⊆ S¹` from the
Riesz–Markov theorem applied to the positive functional `f ↦ re⟪x, cfc f V x⟫`. (`CompactSpace σ(V)` via
`spectrum.isCompact` ⟹ the `T2`/`MeasurableSpace`/`BorelSpace`/`LocallyCompactSpace` instances all resolve.)
Also ✅ `cayleyScalarMeasure_integral` `[Nontrivial H]` — **`μ_x` represents the functional**:
`∫ f dμ_x = re⟪x, cfc f V x⟫` for `f : C_c(σ(V), ℝ)` (`RealRMK.integral_rieszMeasure` for `cfcPLMcc x`). This pins
`μ_x` to `V` — its moments are the expectations of functions of `V` in the state `x`. **The operator →
scalar-spectral-measure half of the spectral theorem is now end-to-end machine-checked** (Cayley unitary → cfc
functional → positivity + linearity → RMK → `μ_x` → integral identity).
Also ✅ `cayleyScalarMeasure_isFiniteMeasure` `[Nontrivial H]` — **`μ_x` is a finite measure** (`RealRMK`'s
`CompactSpace` instance): a genuine finite spectral distribution of the state `x` (total mass `‖x‖²`), so
`∫ g dμ_x` is defined for every *bounded Borel* `g` — the extension beyond continuous functions underlying the
Borel FC / the PVM `E(S) = ∫ 1_S dE`.
Also ✅ `cayleyScalarMeasure_univ` `[Nontrivial H]` — **total mass `μ_x(σ(V)) = ‖x‖²`**:
`(μ_x univ).toReal = ∫ 1 dμ_x = re⟪x, cfc 1 V x⟫ = re⟪x, x⟫ = ‖x‖²` (integral identity at the constant `1` via
`continuousMapEquiv` on the compact spectrum; `cfc 1 V = 1` from `map_one cfcHom`; `inner_self_eq_norm_sq`). So
`μ_x` is the **Born-like spectral distribution of the state `x`**, total mass `‖x‖²`.
Also ✅ `cayleyScalarMeasure_isProbabilityMeasure` `[Nontrivial H]` — **for a unit vector `‖x‖ = 1`, `μ_x` is a
probability measure** (total mass `1`): the spectral-measure realization of the **Born rule** for the Cayley
unitary of the self-adjoint generator (`μ_x` = the probability distribution of measuring a function of `V` in the
normalized state `x`).
Also ✅ `cayley_norm_cfc_le` `[Nontrivial H]` — **`‖cfc f V‖ ≤ ‖f‖_∞`** (`norm_cfc_le`; the ℂ-normal CFC on
`H →L[ℂ] H` is isometric, `IsStarNormal.instIsometricContinuousFunctionalCalculus`, global). This is the
**boundedness of `f ↦ cfc f V`** that lets the FC extend from continuous to *bounded-Borel* functions (by
approximation / dominated convergence over `μ_x`) — the analytic input to the Borel FC and the PVM `E(S)`.
Also ✅ `cayley_cfc_isSelfAdjoint` `[Nontrivial H]` — **cfc of a real function is self-adjoint**: `(f z).im = 0`
on `σ(V)` ⟹ `IsSelfAdjoint (cfc f V)` (`star (cfc f V) = cfc (conj∘f) V = cfc f V` via `cfc_star` + `cfc_congr`).
So spectral operators of real observables of `V` are self-adjoint — the bridge making `⟪x, cfc f V x⟫` real
(`= ∫ f dμ_x`) and underlying the polarization `μ_{x,y}` toward the PVM.
Also ✅ `cayley_cfc_inner_self_im_zero` `[Nontrivial H]` — **the expectation of a real observable is real**:
`(⟪x, cfc f V x⟫).im = 0` for `f` real on `σ(V)` (from self-adjointness via `adjoint_inner_left` +
`Complex.conj_eq_iff_im`). Hence `⟪x, cfc f V x⟫ = ↑(∫ f dμ_x)` — the real scalar diagonal the complex polarization
`μ_{x,y}` extends to the off-diagonal toward the PVM.
Also ✅ `cayley_norm_inner_cfc_le` `[Nontrivial H]` — **the spectral sesquilinear form is bounded**:
`‖⟪x, cfc f V y⟫‖ ≤ c·‖x‖·‖y‖` when `‖f z‖ ≤ c` on `σ(V)` (Cauchy–Schwarz + `le_opNorm` + `cayley_norm_cfc_le`).
This is the boundedness of `(x,y) ↦ ⟪x, cfc f V y⟫` that lets the form — extended to bounded-Borel `f` via `μ_{x,y}`
— be **Riesz-represented by an operator** `f(V)`; for `f = 1_S` this is the projection `E(S)` of the PVM.
Also ✅ `cayley_cfc_inner_polarization` `[Nontrivial H]` — **the spectral polarization identity**:
`⟪cfc f V y, x⟫` = the complex polarization combination of the four diagonals `⟪cfc f V z, z⟫` at
`z = x±y, x±iy` (`inner_map_polarization`). With the real diagonal (`⟪cfc f V z, z⟫ = ↑(∫ f dμ_z)`), this expresses
the **full sesquilinear form via the scalar measures `μ_z`** — the formula that *defines* the bounded-Borel operator
`f(V)` (and `E(S) = 1_S(V)`) once `f` is only bounded Borel: the heart of the PVM construction.
Also ✅ `cayleyScalarMeasure_le_norm_sq` `[Nontrivial H]` — **the diagonal spectral content is bounded**:
`μ_x(S) ≤ ‖x‖²` for every `S` (`μ_x` finite of total mass `‖x‖²`, monotone). This is the bound the diagonal
`⟪x, E(S) x⟫ = μ_x(S)` of the spectral projection `E(S)` must satisfy (`0 ≤ E(S) ≤ 1` on `x`) and the boundedness
controlling the Riesz representation of `(x,y) ↦ ∫ 1_S dμ_{x,y}` into `E(S)`.
Also ✅ `cayleyScalarMeasure_union` `[Nontrivial H]` — **finite additivity of the spectral distribution**:
`μ_x(S ∪ T) = μ_x(S) + μ_x(T)` for disjoint measurable `S, T`. The diagonal shadow of the PVM additivity
`E(S ∪ T) = E(S) + E(T)` (and, normalized, the additivity of the **Born probabilities** over disjoint spectral
outcomes) — refined to σ-additivity by the eventual PVM `E`.
Also ✅ `cayley_cfc_norm_sq` `[Nontrivial H]` — **L²-isometry (operator side)**: `‖cfc f V x‖² = re⟪x, cfc(|f|²) V x⟫`
(`(cfc f V)⋆(cfc f V) = cfc(conj f·f) V` + adjoint). With the integral identity this is Parseval
`‖cfc f V x‖² = ∫ |f|² dμ_x` — the L² estimate behind the **dominated-convergence / Cauchy argument that builds the
Stone exponential** `U_t = exp(it A)` as a strong limit of `cfc(e^{it·φₙ}) V x` (GPT-5.5-pro's endorsed Stone-via-
strong-limit route, NOT the PVM).
Also ✅ `cayley_cfc_sub_norm_sq` `[Nontrivial H]` — **the L²-distance estimate**:
`‖cfc f V x − cfc g V x‖² = re⟪x, cfc(|f−g|²) V x⟫` (= `∫ |f−g|² dμ_x`), via `cfc_sub` + `cayley_cfc_norm_sq`.
This is literally the **Cauchy estimate** making `n ↦ cfc(e^{it·φₙ}) V x` a Cauchy sequence — the next named step
of the strong-limit Stone-exponential recipe.
Also ✅ `cayleyScalarMeasure_integral_C` `[Nontrivial H]` — **integral identity on `C(σ(V), ℝ)`** (compact-domain
wrapper): `∫ h dμ_x = re⟪x, cfcL ha (↑∘h) x⟫` for continuous real `h` (via `continuousMapEquiv`, σ(V) compact).
The clean form the **function-form CFC bridge** `re⟪x, cfc g V x⟫ = ∫ (g∘↑) dμ_x` consumes — removing the `C_c`
plumbing from the Stone/Parseval development (GPT-5.5-pro recipe). **Next:** `cfc_eq_cfcL` to land the function-form
bridge, then Parseval `‖cfc f V x‖² = ∫ |f|² dμ_x` and `μ_x({1})=0` (rational cutoffs).
Also ✅ `integral_re_cfc_ofReal` `[Nontrivial H]` — **the function-form CFC↔measure bridge**:
`re⟪x, cfc (↑∘r) V x⟫ = ∫ ω, r ω.1 dμ_x` for `r : ℂ→ℝ` continuous on `σ(V)` (`cfc_eq_cfcL` — `cfc(↑∘r)V =
cfcL ha (restrict(↑∘r))`, defeq to `cfcL ha (↑∘(r∘↑))` — then `cayleyScalarMeasure_integral_C`). The recurring
dictionary entry connecting the function-form `cfc g V` (operator-side identities) to the `μ_x`-integral; e.g. it
upgrades `cayley_cfc_sub_norm_sq` to the genuine L² identity `‖cfc f V x − cfc g V x‖² = ∫|f−g|² dμ_x`. **Next:**
`μ_x({1})=0` (rational cutoffs) → the strong-limit Stone exponential.
Also ✅ `cayley_cfc_sub_norm_sq_integral` `[Nontrivial H]` — **the full Parseval / L²-distance identity in honest
integral form**: `‖cfc f V x − cfc g V x‖² = ∫ ω, ‖f ω.1 − g ω.1‖² dμ_x` for `f,g` continuous on `σ(V)`. Capstone of
the CFC↔measure dictionary: composes `cayley_cfc_sub_norm_sq` (operator side) with the function-form bridge
`integral_re_cfc_ofReal` at `r z = ‖f z − g z‖²`, using the pointwise ℂ-identity `star w·w = ↑‖w‖²`
(`RCLike.conj_mul`, then `norm_cast`). This is the genuine **Parseval/Cauchy estimate in MEASURE form**:
`n ↦ cfc(e^{it·φₙ}) V x` is Cauchy **iff** `∫ ‖e^{itφₙ} − e^{itφₘ}‖² dμ_x → 0` — exactly what defines the Stone
exponential `U_t = exp(it A)` as a strong limit without a PVM (GPT-5.5-pro's endorsed route). The L²-side dictionary
is now complete; the strong-limit construction can proceed entirely in `∫·dμ_x`. **Next:** `μ_x({1})=0` via rational
cutoffs `ψ_N(ω)=(1+(N+1)‖ω−1‖²)⁻¹` (off the P4 critical path per GPT — Phase 5 dual-weight trace is P4's true gap).
Also ✅ `cayley_cfc_norm_sq_integral` `[Nontrivial H]` — **the Parseval / L²-isometry identity (integral form, f-version)**:
`‖cfc f V x‖² = ∫ ω, ‖f ω.1‖² dμ_x` for `f` continuous on `σ(V)` (the `g=0` companion of the sub-version; composes
`cayley_cfc_norm_sq` with `integral_re_cfc_ofReal` at `r z=‖f z‖²`). This is *the* Parseval identity: `f ↦ cfc f V x`
is an **L²(μ_x) → H isometry** on continuous functions.
Also ✅ `cayley_cfc_tendsto_zero_of_integral` `[Nontrivial H]` — **the L² convergence engine**: `∫‖F n ω.1‖² dμ_x → 0`
⟹ `cfc(F n) V x → 0` strongly in `H` (from Parseval, then `‖·‖=√(‖·‖²)→0` via `tendsto_zero_iff_norm_tendsto_zero`
+ `Real.sqrt_sq`). The convergence half of the Cauchy/DCT machine that turns `L²(μ_x)`-limits of continuous functions
into **strong operator limits** — the device that (with the rational cutoffs) kills the Cayley atom `μ_x({1})=0` and
assembles `U_t=exp(itA)` as a strong limit, no PVM. **Next:** the cutoff sequence `ψ_N` + its DCT limits
(`∫ψ_N dμ_x → μ_x({1})`, `∫|(ω−1)ψ_N|² → 0`) → `μ_x({1})=0` via `cayley_one_sub_injective`.
Also ✅ `cayley_cfc_cauchySeq_of_integral` `[Nontrivial H]` — **the existence half of the operator-limit toolkit**:
if `F n` is **Cauchy in `L²(μ_x)`** (`∀ε>0 ∃N ∀m,n≥N, ∫‖F m ω.1−F n ω.1‖²dμ_x<ε`) then `cfc(F n) V x` is a `CauchySeq`
in `H` (hence converges, `H` complete). From the L²-distance Parseval `cayley_cfc_sub_norm_sq_integral`: an L²-Cauchy
condition at `ε²` gives `‖·‖²<ε²` ⟹ `‖·‖<ε` (`lt_of_pow_lt_pow_left₀`). With the convergence half this is the **FULL
bridge** `L²(μ_x)` continuous-function limits ⟶ strong operator limits: any L²-convergent sequence of continuous
functions yields a convergent `cfc(F n) V x`. Directly enables both `μ_x({1})=0` (the cutoff sequence converges) and
`U_t=exp(itA)`. **Next:** the cutoff sequence `ψ_N` + its DCT limits → `μ_x({1})=0`.
Also ✅ `cayley_defect_energy` `[Nontrivial H]` — **the Cayley defect-energy identity**: `‖V x − x‖² =
∫ ω, ‖(ω:ℂ)−1‖² dμ_x` (the `f=z−1` specialization of `cayley_cfc_norm_sq_integral`, using `cfc(z↦z−1)V = V−1`
via `cfc_sub` + the keystones `cayley_cfc_id`/`cayley_cfc_one`). The spectral mass weighted by squared distance-to-1
= the Cayley defect `‖(V−1)x‖²` — the integral witnessing `ker(1−V)=0`. The inverse-Cayley generator
`A=i(1+V)(1−V)⁻¹` is obstructed only by the spectral **atom** `μ_x({1})`. **Next (μ_x({1})=0, full recipe):**
cutoff `ψ_N(ω)=(1+(N+1)‖ω−1‖²)⁻¹` (continuous, `0<ψ_N≤1`, `ψ_N→1_{{1}}` ptwise); 3 DCT limits
[`∫ψ_N dμ_x→μ_x({1})`, `∫‖ψ_N−ψ_M‖²→0` (L²-Cauchy), `∫‖(ω−1)ψ_N‖²→0`]; existence-half ⟹ `cfc(ψ_N)V x→w`;
convergence-half ⟹ `(V−1)cfc(ψ_N)V x = cfc((ω−1)ψ_N)V x → 0`, so `(V−1)w=0` ⟹ `w=0` (`cayley_one_sub_injective`);
`re⟪x,cfc(ψ_N)V x⟫=∫ψ_N dμ_x → μ_x({1})` and `→ re⟪x,w⟫=0`, hence `μ_x({1})=0`.
Also ✅ `cayleyCutoff` + scaffolding (`cayleyCutoff_pos`/`_le_one`/`_continuous`/`_tendsto_zero_of_ne`/
`_tendsto_indicator`/`_sq_mul_tendsto_zero`) — **the rational cutoff sequence** `ψ_N(z)=(1+(N+1)‖z−1‖²)⁻¹` and its
analytic properties: `0<ψ_N≤1` (the DCT dominator), each `ψ_N` continuous, `ψ_N(z)→0` for `z≠1` (denom→∞ via
`Filter.Tendsto.inv_tendsto_atTop`), the **pointwise limit `ψ_N→1_{z=1}`** (the convergence DCT consumes for
`∫ψ_N dμ_x→μ_x({1})`), and `‖z−1‖²·ψ_N²→0` (the integrand for `∫‖(ω−1)ψ_N‖²→0`, dominated by the defect-energy
integrand `‖ω−1‖²`). Pure real analysis, `U`-independent. **Next:** the 3 DCT limits over `μ_x` (using these +
`cayley_defect_energy` as the dominator) + the L²→strong bridge ⟹ `μ_x({1})=0`.
Also ✅ `cayleyCutoff_integral_tendsto_atom` `[Nontrivial H]` — **the first DCT step of the atom-killing**:
`∫ ψ_N(ω) dμ_x → μ_x({1})` where `{1} = {ω ∈ σ(V) | (ω:ℂ)=1}`. Dominated convergence
(`tendsto_integral_of_dominated_convergence`) with the cutoff scaffolding: `ψ_N∘↑` continuous, `≤1` (the integrable
dominator, `μ_x` finite), `→1_{{1}}` ptwise (`cayleyCutoff_tendsto_indicator`); the limit `∫1_{{1}}dμ_x=μ_x({1})`
is `integral_indicator_one`; `{1}` measurable via `isClosed_eq`. With `∫ψ_N dμ_x = re⟪x,cfc(ψ_N)V x⟫`
(`integral_re_cfc_ofReal`) this evaluates the diagonal limit of the spectral projection toward `1` — the value
`w = lim cfc(ψ_N)V x` must reproduce. **Next (remaining for μ_x({1})=0):** DCT-2 `∫‖ψ_N−1_{{1}}‖²→0` (⟹ L²-Cauchy
⟹ `cfc(ψ_N)V x→w` via existence-half) + DCT-3 `∫‖(ω−1)ψ_N‖²→0` (⟹ `(V−1)cfc(ψ_N)V x→0` via convergence-half
⟹ `(V−1)w=0` ⟹ `w=0` by `cayley_one_sub_injective`); then `μ_x({1})=lim∫ψ_N=re⟪x,w⟫=0`.
Also ✅ `cayleyCutoff_defect_integral_tendsto_zero` `[Nontrivial H]` — **DCT-3, the third DCT step**:
`∫ ‖(ω−1)·ψ_N(ω)‖² dμ_x → 0`. Dominated convergence with the `(z−1)`-weighted cutoff: integrand
`‖(ω−1)ψ_N‖²=‖ω−1‖²ψ_N² ≤ 4` (since `σ(V)⊆S¹` ⟹ `‖(ω:ℂ)‖=1` ⟹ `‖ω−1‖≤2`, and `ψ_N≤1`), continuous, `→0` ptwise
(`cayleyCutoff_sq_mul_tendsto_zero`). Stated in the form `∫‖F_N ω.1‖²dμ_x→0` with `F_N(z)=(z−1)ψ_N(z)` — it feeds
`cayley_cfc_tendsto_zero_of_integral` to give `(V−1)cfc(ψ_N)V x = cfc((z−1)ψ_N)V x → 0`, forcing `(V−1)w=0` ⟹ `w=0`.
Also ✅ `cayleyCutoff_sub_indicator_sq_tendsto_zero` (helper: `‖(ψ_N z:ℂ)−1_{z=1}‖²→0` ptwise, by cases) +
`cayleyCutoff_L2_tendsto_zero` `[Nontrivial H]` — **DCT-2, the L²-Cauchy input**: `∫ ‖ψ_N(ω)−1_{{1}}(ω)‖² dμ_x → 0`
(the cutoff → the indicator of `{1}` in `L²(μ_x)`). Dominated convergence: integrand `≤ 4` (`ψ_N≤1`, `‖1_{{1}}‖≤1`),
`AEStronglyMeasurable` (continuous cutoff − indicator of the measurable `{1}`, `Measurable.indicator`+`isClosed_eq`),
`→0` ptwise (the helper). An L²-convergent sequence is L²-Cauchy, so this feeds `cayley_cfc_cauchySeq_of_integral`
(via the triangle ineq) ⟹ the **strong limit** `w = lim cfc(ψ_N)V x` (`H` complete) — the existence input.
**ALL THREE DCT LIMITS NOW DONE.**
Also ✅ `cayleyCutoff_cfc_cauchySeq` `[Nontrivial H]` — **★★★ the cutoff CFC vectors form a `CauchySeq`** (the
existence input): `cfc(ψ_N) V x` is a `CauchySeq` in `H` (hence converges, `H` complete). The cutoff sequence is
`L²(μ_x)`-Cauchy from DCT-2 + the pointwise quadratic triangle `‖a−b‖²≤2‖a−c‖²+2‖b−c‖²` (`c=1_{{1}}`) integrated via
`integral_mono_of_nonneg`: `∫‖ψ_m−ψ_n‖² ≤ 2∫‖ψ_m−1_{{1}}‖²+2∫‖ψ_n−1_{{1}}‖² < ε`; then
`cayley_cfc_cauchySeq_of_integral` (the existence half) gives the `CauchySeq`. *(Build notes: removed `set μ/V`
— `set` made them opaque, breaking defeq with the lemma-produced goals; used `apply integral_mono_of_nonneg` so
`f/g/μ` unify from the goal before the subgoals; `integral_nonneg`/`sq_nonneg` need the integrand pinned via an
explicit `have`.)*
Also ✅ `cayleyCutoff_cfc_tendsto_zero` `[Nontrivial H]` — **★★★ the cutoff CFC vectors tend to `0`**: `cfc(ψ_N) V x →
0` strongly in `H` (the operator heart of the atom-killing). Assembles: (existence) `cauchySeq_tendsto_of_complete`
on the CauchySeq ⟹ `cfc(ψ_N)V x→w`; (`(V−1)w=0`) the defect `(V−1)cfc(ψ_N)V x = cfc((z−1)ψ_N)V x → 0` (DCT-3 fed
through `cayley_cfc_tendsto_zero_of_integral`, the convergence half — the `cfc(z−1)V=V−1` step is `cfc_mul`+`cfc_sub`
+`cayley_cfc_id`/`_one`) and `→ (V−1)w` by continuity of `V−1`, so `tendsto_nhds_unique` ⟹ `(V−1)w=0`; (`w=0`)
`ker(1−V)=0` (`cayley_one_sub_injective`). *Built green first try.*
Also ✅ `cayleyScalarMeasure_atom_eq_zero` `[Nontrivial H]` — **★★★★ the Cayley spectral atom VANISHES: `μ_x({1})=0`.**
The scalar spectral measure of the Cayley unitary `V` puts **no mass** on the exceptional point `1∈S¹` (image of `∞`
under inverse Cayley). DCT-1 (`∫ψ_N dμ→μ_x({1})`) + `∫ψ_N dμ=re⟪x,cfc(ψ_N)V x⟫` (`integral_re_cfc_ofReal`) +
`cfc(ψ_N)V x→0` (with `Filter.Tendsto.inner` + `Complex.continuous_re`) ⟹ `∫ψ_N→re⟪x,0⟫=0`; `tendsto_nhds_unique`
⟹ `μ_x({1}).toReal=0` ⟹ `μ_x({1})=0` (`ENNReal.toReal_eq_zero_iff` + `measure_ne_top`). *Built green first try.*
**ATOM-KILLING COMPLETE.** **Consequence:** the inverse-Cayley / Stone-exponential symbol `exp(it·invCayley(ω))`
(continuous + bounded off `ω=1`) is now `μ_x`-a.e. defined — the precondition for the strong-limit Stone exponential
`U_t=exp(itA)`.
Also ✅ `cayleyInv` + `cayleyInv_continuousOn` + `cayleyInv_im_eq_zero` — **the inverse Cayley map** `c(ω)=i(1+ω)/(1−ω)`
(the Stone-exp symbol's argument): continuous off the excluded point `1`, and **real on the unit circle** (off `1`):
`(c(ω)).im=0` for `‖ω‖=1, ω≠1` (i.e. `A=i(1+V)(1−V)⁻¹` is **self-adjoint** ⟹ `exp(it·c(ω))` has modulus 1 ⟹ `U_t`
unitary). Proof of real-valuedness: on the circle `conj ω=ω⁻¹` (`RCLike.mul_conj`+`h1`) + `div_eq_div_iff` +
`linear_combination (2I)·(ω·conj ω=1)`. *Built green (one fix: `field_simp/ring` couldn't reduce `ω⁻¹`; switched to
keeping `conj ω` + `linear_combination`).* **Next:** assemble the strong limit `U_t x = lim cfc(g_{t,N}) V x` with
`g_{t,N}` continuous cutoffs of `exp(it·c(·))` (continuous+bounded off `1`, `μ_x`-a.e. defined since `μ_x({1})=0`;
the convergence + existence bridges feed this) ⟹ group law / strong continuity / generator ⟹ Stone.
**Next:** the bounded-Borel functional `g ↦ ∫ g dμ_x` (now well-defined) + polarization `μ_{x,y}`; assemble the
family `{μ_x}` into a **projection-valued measure** `E` on `σ(V) ⊆ S¹` with `V = ∫ z dE` — the genuine Mathlib gap
(no `ProjectionValuedMeasure` type; QIQTH's `Spectral/PVM.lean` defines its own, where the polarization `μ_{x,y}`
→ genuine projections `E(S)` is `PVM_of_selfAdjoint`, the documented residual); then transport `E` through the
inverse Cayley to `A = ∫ λ dE` ⟹ Stone `U_t = exp(it A)`.
**Next multi-fire sub-construction (the operator → PVM keystone, RMK + cfc supported):** the scalar spectral
measures `μ_x` of `V` (positive functional `f ↦ re⟨x, cfc f V x⟩` → `RealRMK.rieszMeasure`), then their assembly
into a circle-PVM `E` with `V = ∫ z dE`, then transport through inverse Cayley to `A = ∫ λ dE` ⟹ Stone.
**Remaining (Mathlib gap):** the **Borel/PVM** functional calculus on `S¹` (`∫ z dE` for the unitary `V` — Mathlib
has the *continuous* FC but not the projection-valued-measure form) → transport to the unbounded spectral theorem
(PVM `∫ λ dE` for the now-self-adjoint `A`) ⟹ Stone `U_t = exp(it A)`.
**Remaining (the genuine Mathlib-grade operator-theory frontier):** differentiate the RHS in `s` at `0` (after
the change of variables `u = s+t` ⟹ `e^s ∫_s^∞ e^{−u} U_u x du`, whose `d/ds|₀ = R x − x` by the **FTC for the
improper integral with variable lower limit**) ⟹ `R x ∈ stoneDomain U` + the resolvent identity
`(A + i)(R x) = i x` ⟹ `Range(A + i) = H` dense ⟹ `Ā = Ā†` (e.s.a.) ⟹ the Cayley transform / unbounded spectral
theorem ⟹ Stone `U_t = exp(it Ā)`. Mathlib has none of these; the Cayley injectivity estimates
`‖(A±i)x‖²=‖Ax‖²+‖x‖²` are in `Spectral/Stone.lean`.

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
