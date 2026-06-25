# The Wall, Phase 3 — the covariance relation + the crossed product `M ⋊_σ ℝ`

**Status:** PLAN (not started). **Track:** GR / continuum (campaign Phase 3 of `P4_WALL_CAMPAIGN_PLAN.md`).
**Goal:** **join** the two factors of the crossed product — the matter representation `π(a) = matterRep S a`
(Phase 1) and the clock translation group `λ_t = clockTransl t` (Phase 2) — via the **covariance relation**, and
package the crossed product `M ⋊_σ ℝ` as the algebra they generate.  This is the defining identity of the
construction and the most tractable of the remaining phases (it's `modularAut_add` at the fiber level).

## 0. Scope (stated up front)
Bounded operators only.  No trace (Phase 5), no unbounded generator (Phase 4), no `1/4` coefficient.  Axiom-free.

## 1. The covariance — the exact form (verified by the fiber computation)
With `(π(a)ξ)(s) = σ_{-s}(a)(ξ s) = modularAut S (-s) a (ξ s)` (Phase 1) and `(λ_t ξ)(s) = ξ(s + t)` (Phase 2):
```
(λ_{-t} ∘ π(a) ∘ λ_t) ξ (s)
  = (π(a)(λ_t ξ))(s - t)                                  [λ_{-t}: shift by -t]
  = modularAut S (-(s-t)) a ((λ_t ξ)(s - t))             [π(a) at s-t]
  = modularAut S (t-s) a (ξ ((s-t)+t)) = modularAut S (t-s) a (ξ s)   [λ_t: shift by +t]
```
and `(π(σ_t a)ξ)(s) = modularAut S (-s) (modularAut S t a)(ξ s) = modularAut S (-s + t) a (ξ s)
   = modularAut S (t-s) a (ξ s)` (by `modularAut_add`).  **They match**, so the covariance is
```
  clockTransl (-t) ∘L matterRep S a ∘L clockTransl t  =  matterRep S (modularAut S t a).
```

## 2. Sub-steps (each axiom-free, green-building, one commit) — `QIQTH/CrossedProductCovariance.lean`

### 3.1 — the covariance relation `λ_{-t} π(a) λ_t = π(σ_t a)`  *(the defining identity)*
Prove `clockTransl (-t) ∘L matterRep S a ∘L clockTransl t = matterRep S (modularAut S t a)`.
Route (mirrors `clockTransl_add`): `refine ContinuousLinearMap.ext fun ξ => ?_` (CLM-level only — `ext` is
over-aggressive), `rw [comp_apply, comp_apply, Lp.ext_iff]`, then `filter_upwards` with the `coeFn` lemmas
(`matterRepFun_coeFn`, `clockTransl_coeFn` for `t` and `-t`) + an `ae_eq_comp` for the nested shift
(`(λ_t ξ)(s-t) =ᵐ ξ s` under the measure-preserving `(· - t)`), then `modularAut_add` for the time arithmetic.
**Risk: medium** (the nested-shift `ae_eq_comp` bookkeeping, as in `clockTransl_add`; H must be pinned via type
ascription on the statement).

### 3.2 — the crossed-product algebra `M ⋊_σ ℝ`  *(packaging)*
Define the crossed product as the data `(matterRep S, clockTransl)` satisfying: `matterRep` a unital algebra
`*`-homomorphism (Phase 1), `clockTransl` a unitary group (Phase 2), and the covariance (3.1).  Concretely:
- the **generating set** `crossGens S := Set.range (matterRep S) ∪ Set.range clockTransl` (operators on
  `L²(ℝ;H)`), and `M ⋊_σ ℝ := ` the von Neumann algebra it generates (double commutant
  `(crossGens S)''` via Mathlib `VonNeumannAlgebra` / `commutant`), OR the `StarSubalgebra` generated +
  `topologicalClosure` — whichever is lightest.
- restate the structural facts (π unital `*`-hom, λ unitary group, covariance) as the **crossed-product
  package** — a `structure` or a bundle of the Phase-1/2/3.1 lemmas.
**Risk: medium** (the vN-generation is structural but the Mathlib `VonNeumannAlgebra`/`commutant` API may be
thin; if generating-the-vN-algebra-as-such is heavy, deliver the generating set + the covariant-representation
*package* (the lemmas) and record the full vN object as the lighter follow-on — the covariance (3.1) is the
substantive content).

## 3. Honest deliverable
The **covariant representation** of `M ⋊_σ ℝ` on `L²(ℝ;H)`: `π` (matter, Phase 1) + `λ` (clock, Phase 2)
satisfying `λ_{-t} π(a) λ_t = π(σ_t a)` (3.1), with the crossed-product algebra as the generated structure
(3.2).  The gravitational dressing is now an explicit Lean object; **Phase 4** (Stone) extracts the clock
energy `X` = the area edge operator, and **Phase 5** the trace.  The `1/4` stays the cited UV datum.

## 4. Verification (per sub-step)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.CrossedProductCovariance` green; `#print axioms` = standard 3;
`bash scripts/axiom_budget_check.sh` budget 0; wire into `QIQTH.lean` + `AxiomAudit.lean`; one commit per
sub-step with the `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>` trailer; push via schannel; refresh.

## Progress log
- **Sub-step 3.1 ✅** (`QIQTH/CrossedProductCovariance.lean`) — **the covariance relation**
  `clockTransl (-t) ∘L matterRep S a ∘L clockTransl t = matterRep S (modularAut S t a)` (`covariance`), the
  defining identity of `M ⋊_σ ℝ`. Proof via `refine ContinuousLinearMap.ext fun ξ => ?_` (CLM-level), two
  nested `ae_eq_comp` shifts (the matter-fiber `ζ` and clock-fiber `λ_t ξ`, both under `(· + (-t))`),
  `matterRep_apply` to bridge `matterRep`↔`matterRepFun`, and `modularAut_add` for the time arithmetic
  (both fibers `= modularAut S (t-s) a (ξ s)`). Axiom-free (std 3); wired into AxiomAudit; budget 0.
  *(Both factors of the crossed product are now joined by the covariant identity.)*
- **NEXT: Sub-step 3.2** — package the crossed-product algebra: the generating set
  `Set.range (matterRep S) ∪ Set.range clockTransl` + the covariant-representation bundle (π unital `*`-hom,
  λ unitary group, covariance), as the `M ⋊_σ ℝ` data. If the Mathlib `VonNeumannAlgebra`/`commutant`
  generation API is thin, deliver the package + record the full vN object as the lighter follow-on.
