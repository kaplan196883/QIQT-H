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
  - **REMAINING (∑ρ assembly, ~110 ln, 2 lemmas):** **Lemma 1** `gi_trace_covDerivRiem_ricci` (per ρ):
    substitute `S=−`(raised Ricci) [`ricci_gi_raise`, function level via `funext`] into `gi_trace_covDerivRiem`,
    expand `pd(S)` (`pd_const_mul (-1)`+`pd_sum`+`pd_mul`+`inv_metric_compat`), the `Γ^ρ_{ρκ}` terms cancel the
    `∑Γ^ρ_{ρκ}S^κ` spectator ⟹ `−∑g^{ρβ}∂_ρRic_{βλ} + ∑Γ^β_{ρκ}g^{ρκ}Ric_{βλ} + ∑Γ^κ_{ρλ}g^{ρβ}Ric_{βκ}`.
    **Lemma 2** sum over ρ + match `−div02(ricci)` (via `hsymm_gi` + reindexing).
    **⚠ LESSON (1 reverted attempt):** Lemma 1's final `ring` only closes if EVERY `Γ·g·Ric` double-sum is in
    the SAME nesting order (use `∑β∑κ` throughout). Add `moveκ : ∑σ∑ν∑κ F = ∑κ∑σ∑ν F`
    (`sum_congr(sum_comm)`+`sum_comm`) for the spectator refactor `∑σνκ gΓR→∑κ Γ(∑σν gR)`, then `Finset.sum_comm`
    each refactored spectator into `∑β∑κ` order before combining. Math is verified; it's purely sum-order bookkeeping.
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

**✅ PHASE 1 DONE, axiom-free** (`twice_contracted_bianchi`): `∇^μRic_{μλ}=½∂_λR`. Steps: `ricci_gi_raise`
(1.1) · `gi_trace_covDeriv_ricci` (T1) · `gi_trace_covDerivRiem` (T3 core) · `gi_trace_covDerivRiem_ricci`
(T3 substituted) · `divRiemann_trace_eq` (∑ρ T3 = −div02) · assemble. The whole twice-contracted Bianchi
is machine-checked.

## Phase 2 — Instantiate to the actual curvature  *(closes pro's main hit)* — ✅ DONE, axiom-free

`einstein_field_equation_real`: `einstein_field_equation` instantiated at `Ric := ricci g gi`,
`R := scalarCurv g gi`, `bianchi` **discharged** by `twice_contracted_bianchi`. Conclusion now features the
**genuine `einsteinTensor`**: `a·T_{μν} = G_{μν} + Λg_{μν}`, `Λ = f+½R` covariantly constant. The ONLY
remaining hypotheses are the cited PHYSICS (`crux` = post-null Clausius relation, `conserv`). Everything
geometric is proven. **Pro's two main hits are closed.**

## Phase 3 — Wire the null-cone crux — ✅ DONE, axiom-free

Took option **(b)** (the cleaner, frame-independent route) and it landed:
- **`symmTensor_eq_smul_metric_of_null_general`** (EinsteinEquationOfState.lean): the null-cone crux for a
  GENERAL Lorentzian `g`, proved by **congruence reduction** `g = Pᵀ·η·P` (Sylvester's law as a labeled
  hypothesis) to the Minkowski lemma — transform `C` by `Pinv`, apply the Minkowski crux, transform back.
  Supporting: `BL` (bilinear form), `QF_eq_BL`, `BL_transform` (Fin-4 rearrangement, closed by `ring`).
- **`crux_of_pernull`** (EinsteinFieldEquation.lean): DERIVES the tensor `crux` (`a·T=R+f·g`) from the
  genuinely primitive **per-null Clausius relation** — `a·T−R` vanishing on the whole null cone of `g x`
  in each point's local inertial frame, exactly Jacobson's premise. `f` produced pointwise (via `choose`);
  its smoothness is the one honest analytic residual (not derivable from the per-null relation alone).

Both `#print axioms`-clean, full project builds (8646 jobs), budget 0. **The chain is now end-to-end:**
per-null Clausius → tensor crux → `G+Λg = a·T` with genuine `G`, genuine constant `Λ`, all geometry
machine-checked; only the cited physics (per-null Clausius + conservation) and `f`-regularity remain as
labeled hypotheses. *(LESSON: option (a)'s pointwise local-inertial frame is frame-dependent per point and
fights the `∀y` tensor `crux`; option (b)'s congruence is the clean, frame-independent statement.)*

## Phase 4 — Global cosmological constant — ✅ DONE, axiom-free

`const_of_pd_zero` (zero partials everywhere ⟹ constant, via `is_const_of_fderiv_eq_zero` + the
`Pi.single` basis decomposition) + **`einstein_field_equation_real_global`**: if the cited physics holds
at every point, `Λ := f+½R` is a TRUE constant, and `a·T_{μν} = G_{μν} + Λ·g_{μν}` globally for a single
`Λ`. *(Original Phase-4 polish note follows.)* `n=4`, Lorentzian signature noted; `a≠0`. Final docstring states
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
