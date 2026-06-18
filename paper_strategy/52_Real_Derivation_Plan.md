# 52 — Plan: the *real* derivation of the Einstein field equations (close the honesty gap)

**Status:** plan, 2026-06-18. Turns the *conditional* `einstein_field_equation` into the strongest
honest machine-checked statement, addressing the GPT-5.5-pro red-team (pro confirmed soundness +
gave a model; flagged: `Ric`/`tr` are free fields not the actual curvature; `bianchi` is assumed;
local-at-`x`; need `a≠0`, `n=4`). Authority order Lean > papers > pro; pro's points verified against Lean.

## Goal (end state)

One theorem `einstein_field_equation_real` whose **only** non-discharged hypotheses are the two
*genuinely-cited physics* inputs, with **all geometry proven** and curvature objects instantiated to
their real definitions:

> **IRREDUCIBLE hypotheses (Mathlib cannot formalize these — they are the cited physics):**
> 1. the **per-null Clausius/heat relation** `T_{μν}k^μk^ν = c·R_{μν}k^μk^ν ∀ null k` at `x`
>    (packages the area law `S=A/4ℓ_P²` + Unruh temperature + Raychaudhuri focusing);
> 2. **local conservation** `∇^μ T_{μν} = 0`.
>
> **CONCLUSION:** `a·T_{μν} = G_{μν} + Λ·g_{μν}` with `G = Ric − ½R·g` the *actual* Einstein tensor
> (`Ric = ricci g gi`, `R = scalarCurv g gi`), and `Λ = f + ½R` covariantly constant.

Everything between (1)+(2) and the conclusion is machine-checked, axiom-free.

## Current state (committed, axiom-free)

`second_bianchi` → `second_bianchi_contracted`; `inv_metric_compat` (`∇g^{μν}=0`) + `covDeriv20`;
`lowered_riemann_antisymm` (`R_{ρσμν}=−R_{σρμν}`) + `lowered_riemann_gi_trace`;
`div02`/`div02_add`/`div02_scalar_metric`; `einstein_field_equation` (conditional — `Ric`,`tr` free,
`bianchi` a hypothesis); the algebraic crux `symmTensor_eq_smul_metric_of_null` (Fin 4 Minkowski).

## Phase 1 — Discharge `bianchi`: the twice-contracted Bianchi  *(the big geometry phase)*

Target: **`twice_contracted_bianchi`** : `div02 g gi (ricci g gi) ν x = ½ · pd (scalarCurv g gi) ν x`,
obtained by contracting `second_bianchi_contracted` with `g^{σν}`. Three terms:

- **1.1 `ricci_gi_raise` (piece C, raised) — ✅ DONE, axiom-free (commit on `main`).**
  `∑_{σν} g^{σν} R^ρ_{σνλ} = −∑_β g^{ρβ} Ric_{βλ}`. Built via `lowered_riemann_gi_trace` + a triple-sum
  swap (`hswap`) + an abstract-`Q` inversion (`hinvert ∀Q`, `g⁻¹·g=δ` via `hleft`). Landed in 2 iters.
- **1.2 T3 = contraction-commutes + raise.** `∑_{σν} g^{σν} ∑_ρ covDerivRiem ρ ρ σ ν λ = −div02(ricci)λ`.
  - **✅ CORE DONE, axiom-free** (`gi_trace_covDerivRiem`): for fixed ρ, `∑_{σν}g^{σν}∇_ρR^ρ_{σνλ}
    = ∂_ρS^ρ_λ + Γ^ρ_{ρκ}S^κ_λ − Γ^κ_{ρλ}S^ρ_κ` (the (1,1) divergence of `S^a_b=∑g^{σν}R^a_{σνb}`).
    Copied T1's shape (`swap13`/`swap23`+`inv_metric_compat`) — compiled first try.
  - **REMAINING (∑ρ assembly, ~60–80 ln):** sum over ρ + substitute `S=−`(raised Ricci)
    [`ricci_gi_raise`, function level] + `∇g=0`. The (1,1) divergence of `S^ρ_λ=−g^{ρβ}Ric_{βλ}` equals
    `div02(S_lowered)` with `S_lowered=−Ric` (`g_{μρ}g^{ρβ}=δ`) ⟹ `−div02(ricci)`. Refactor distributed
    spectators `∑σνκ gΓR→∑κ Γ S`; Leibniz `∇_ρ(g^{ρβ}Ric)=g^{ρβ}∇_ρRic` via `inv_metric_compat`.
- **1.3 T1 = scalar-curvature derivative — ✅ DONE, axiom-free** (`gi_trace_covDeriv_ricci`).
  `∑_{σν} g^{σν} ∇_λ Ric_{σν} = ∂_λ R`. Product rule (`pd_sum`+`pd_mul`) + `inv_metric_compat` + the
  triple-sum swaps `swap13`/`swap23` (the `Γ·g·Ric` cancellation `A=C`, `B=D`). Added `PdiffAt_ricci`.
  NOTE for T3: the contraction-commutes step `gi_trace_covDerivRiem` is STRUCTURALLY IDENTICAL — same
  product rule + `inv_metric_compat` + `swap13`/`swap23` cancellation, with `riemann ρ·· λ` in place of
  `ricci`, plus two spectator terms `+∑Γ^ρ_{ρκ}S^κ − ∑Γ^κ_{ρλ}S^ρ_κ` that pass through. Copy T1's shape.
- **1.4 T2 = the divergence** ≈20 ln. `∑_{σν} g^{σν} covDeriv02(ricci) ν σ λ = div02(ricci)λ`
  (reindex σ→μ, ν→ρ — `div02` *is* this contraction). RISK: low.
- **1.5 Assemble** ≈30 ln. Contract `second_bianchi_contracted` with `g^{σν}`: `T1 − T2 + T3 = 0` ⟹
  `pd(scalarCurv)λ − div02(ricci)λ − div02(ricci)λ = 0` ⟹ `div02(ricci)λ = ½ pd(scalarCurv)λ`.

Needs `ricci`/`gi`/`g` differentiability (= `PdiffAt_riemann` lifted to `ricci`; `gi` smoothness hyp).
Also needs `hsymm_gi` (gi symmetric) for the `gi·g=δ` collapses. **~230 ln, the bulk of the work.**

## Phase 2 — Instantiate to the actual curvature  *(closes pro's main hit)* ≈30 ln

`einstein_field_equation_inst`: re-state `einstein_field_equation` with `Ric := ricci g gi`,
`tr := scalarCurv g gi`, and **discharge `bianchi`** with Phase-1's `twice_contracted_bianchi`. Now the
first conjunct is the *genuine* Einstein tensor, and the theorem depends only on `crux` + `conserv`
(physics) + proven geometry. (`a≠0` recorded; conservation of `a·T` ⟺ of `T`.)

## Phase 3 — Wire the null-cone crux  *(ties physics to the proven algebraic step)*  ≈ moderate

Replace the `crux` *tensor* hypothesis by the more primitive **per-null Clausius relation** + the
machine-checked `symmTensor_eq_smul_metric_of_null`. FRAMEWORK BRIDGE (honest subtlety): the null-cone
lemma is Fin 4 *Minkowski*; the curvature tower is general `Point n`/general `g`. Options:
- (a) **Local inertial frame**: specialize to `n=4` with `g(x)` = Minkowski at the point (Jacobson's
  argument is local — at each point pick a frame where `g(x)=η`). Cleanest; states the honest locality.
- (b) Generalize the null-cone lemma to a general Lorentzian metric (harder; deferrable).
Pick (a). This makes the physics input the *per-null heat relation*, exactly Jacobson's premise.

## Phase 4 — Polish the honest statement  ≈40 ln

`n=4`, Lorentzian signature noted; `a≠0`; **global Λ**: add `zero_gradient_imp_const` (on connected
`ℝ^n`, `∀ν ∂_νΛ=0` everywhere ⟹ `Λ` constant — a small analysis lemma) to upgrade "covariantly
constant at `x`" → "cosmological constant", *if* hypotheses hold at all points. Final docstring states
EXACTLY: the two irreducible cited-physics hypotheses, that everything else is proven, and the residual
boundary (below).

## Honest residual even the "real derivation" cannot close (state plainly)

- The **physics package** behind the per-null relation (Raychaudhuri focusing, Unruh, the area law) is
  **not** in Lean — Mathlib has no Lorentzian-GR/congruence stack. It is textbook physics, cited.
- **Component calculus**, not covariant tensor calculus on an abstract manifold (`Point n = Fin n→ℝ`).
- The derivation **presupposes** a spacetime + metric + `G` + the area law; it shows GR is their
  *equation of state*. It does **not** originate spacetime/`G` — that is the deep open QIQT-H question.

## Strongest honest headline at the end state

> *Modulo the per-null Clausius relation (area law + Unruh + Raychaudhuri — cited physics) and local
> stress-energy conservation, the full geometric path to the Einstein field equation
> `G_{μν}+Λg_{μν}=a·T_{μν}` — including the contracted Bianchi identity and the emergence of the
> cosmological constant as an integration constant — is machine-checked, axiom-free.*

## Order / risk

Phase 1 is the long pole (~230 ln, T3 the risky bit; everything it needs is built). Phases 2,4 are
quick once Phase 1 lands. Phase 3 is independent and can be deferred (it's the physics-input
refinement, not the geometry). Recommended order: 1 → 2 → 4 → 3.
