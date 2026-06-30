# Scoping the Type II crossed-product frontier — toward an honest area operator

**Status:** SCOPE — REFRESHED 2026-06-30. The operator-level crossed product off `σ_t` is **BUILT** (Increments
1a–1c + the dressed self-adjoint `K̃` + the clock energy `A_edge` + the `Phase5Master` reduction). The single
remaining obligation is the **Type II trace → the JLMS master inequality**. **Track:** GR / continuum.
**Goal:** from the JLMS engine (`K` pinned to BW flow, `S = ⟨K⟩`, dressed `K̃` self-adjoint) to a **genuine
trace** on `M ⋊_σ ℝ` whose first law supplies the master inequality `S_vN + cgpEntropy ≤ ⟨A_edge⟩/4ℓ_P²` — at
which point P4's holographic floor is an *unconditional* theorem (relative only to the carried UV datum `1/4ℓ_P²`).

---

## 0. The physics target (what the construction delivers)

The matter wedge algebra `M` is Type III₁ (no trace, divergent entropy). Crossing it with its modular
automorphism flow `σ_t` (which we **have** as `modUnitary S t = Δ^{it}`) gives
```
M̃ = M ⋊_σ ℝ     (Type II_∞, with a faithful semifinite trace τ)
```
One adjoins an **observer/clock** with energy operator `X` conjugate to modular time; the **dressed modular
Hamiltonian** is `K̃ = K_bulk + X`. The area operator is the trace-renormalization of `M̃`: in CLPW the
generalized entropy `S_gen = ⟨X⟩ + S_out + const`, with `const` the area term `A/4G`. The key point for us:
**`X` (the clock energy) is an *independently defined* operator** — so the JLMS split `K̃ = K_bulk + c·A_edge`,
`A_edge := X/c`, is **not vacuous**. `A_edge` is a real operator the moment the crossed product exists (✅ done);
the residual frontier is the trace `τ`, the first law as a theorem of `τ`, and the *geometric* identification
`⟨A_edge⟩ ↔ A(∂R)` with coefficient `1/4ℓ_P²` (the UV datum — carried, never derived).

---

## 1. What the project has vs. lacks (REFRESHED)

**HAVE — the entire operator layer of `M ⋊_σ ℝ`, axiom-free (std-3, budget 0):**

| Piece | Theorem / file |
|---|---|
| `σ_t` = a one-param group of unital `*`-automorphisms | `modularAut_{zero,one,mul,add,star}` — `CrossedProduct.lean` |
| Covariant rep `π(a)` (operator-valued `Lp`-multiplication) | `CrossedProductRep.lean` |
| Clock translations `λ_t` (`clockTransl`), strongly continuous unitary group | `CrossedProductTranslation.lean`, `clockTransl_stronglyContinuous` |
| Covariance `λ_t π(a) λ_{−t} = π(σ_t a)` | `CrossedProductCovariance.lean` |
| **Clock energy `X = A_edge` self-adjoint** (via Stone, now built) | `clockEnergy_isSelfAdjoint` — `CrossedProductGenerator.lean` |
| Fiberwise bulk modular `Δ̂^{it}`, commutes with the clock | `fiberModFlow`, `fiberModFlow_stronglyContinuous` — `CrossedProductModularFlow.lean` |
| **Dressed `K̃ = K_bulk + A_edge` self-adjoint** | `dressedModularGen_isSelfAdjoint` (via `Spectral/StoneProduct.lean`) |
| The bound reduced to ONE inequality (`Phase5Master`) | `FQBoundCGP.lean`, `FQBoundConditional.lean` |
| Slack positivity (proved) | `cgpEntropy_nonneg` — `ModularRelativeEntropy.lean` |

**LACK — the campaign:** the crossed product *as a von Neumann algebra* (weak closure of `π(M) ∪ {λ_t}`), its
**dual-weight trace `τ`**, the Type II classification, the renormalized entropy, and the first law as a theorem
of `τ`. None of these are in Mathlib.

---

## 2. The reduction is COMPLETE — only the trace is missing

`FQBoundCGP.lean` reduces P4's bound to a single, **non-vacuous, minimal** interface:

```lean
class Phase5Master (S : StandardSubspace H) (ξ : H) (SvN areaTerm : ℝ) where
  remainder        : ℝ
  remainder_nonneg : 0 ≤ remainder
  jlms_balance     : SvN + cgpEntropy S ξ + remainder = areaTerm
```

- `phase5_master_ineq` : the instance ⟹ `SvN + cgpEntropy S ξ ≤ areaTerm`.
- `Phase5Master.of_le` : the converse — the instance is constructible **iff** that inequality holds (remainder =
  the gap). So `Phase5Master` carries **neither more nor less** than the one inequality: it is **non-vacuous**
  (cannot be instanced for arbitrary `SvN`, `areaTerm`) and **minimal**.
- `holographic_area_floor` : **given a `Phase5Master` instance**, `SvN ≤ edgeArea/(4·ellP²)` — P4's floor in
  manifest form. The slack positivity is the *proved* `cgpEntropy_nonneg`; `edgeArea = ⟨A_edge⟩` and `1/4ℓ_P²`
  are the carried UV datum, never assigned.

**Consequence:** the dual-weight trace's *entire* job is to instance `Phase5Master` **from an actual trace** —
i.e. with `SvN`, `areaTerm = ⟨A_edge⟩·c`, and the `remainder` all being the trace's genuine quantities, and
`jlms_balance` a **theorem** of the first law. Instancing it via `of_le` fed an *assumed* inequality would be a
vacuous (circular) discharge and is explicitly **not** the deliverable.

---

## 3. The NEXT increment — T1: a non-vacuous `Phase5Master` instance from a finite trace *(buildable now, weeks)*

The operator layer is done and the continuum trace (§4) is the multi-month frontier. The tractable,
independently-valuable next step — mirroring the `DonaldSystem` typeclass move that made the finite QIQT-H core
axiom-free — is a **concrete finite-dimensional model where the trace exists and the master inequality is a
theorem**, discharging `Phase5Master` non-vacuously.

*New file `QIQTH/CrossedProductFiniteTrace.lean`.*

### T1.1 — the finite standard subspace + state
Reuse the **existing** `StandardSubspace`/`rvdRC`/`projK`/`cgpEntropy` machinery on a **finite-dimensional** `H`
(e.g. the "real points of an ONB" standard subspace — `K = ℝ`-span of an orthonormal basis, `K ∩ iK = 0`,
`K + iK = H`). This gives a finite, computable `cgpEntropy S_fin ξ = ⟨ξ, (−log Δ_S) ξ⟩`-type quantity from the
finite RvD `rvdRC S_fin` — **no new entropy notion**, the same `cgpEntropy` the certificate already uses.

### T1.2 — the finite crossed-product trace
On `H ⊗ (finite clock)` (cross by `ℤ/n`, or `H ⊗ ℓ²`-truncation), define the trace `τ_fin = tr ⊗ clockTrace`.
Finite algebras carry a genuine faithful trace, so:
- `τ_fin` is a faithful positive trace (`τ_fin(ab) = τ_fin(ba)`, `τ_fin(a*a) ≥ 0`) — provable from `Matrix.trace`.
- **Exhibit the dual-action scaling** `τ_fin ∘ θ_s = e^{−s} τ_fin` on the *discrete* clock (the Type II_∞
  signature) — **honestly a Type I/II₁ shadow**: the literal `e^{−s}` continuum scaling needs the *unbounded*
  clock (= T2); T1 exhibits the structural identity on a finite/discrete clock and says so.
- the finite clock energy `A_edge_fin` (self-adjoint; reuse `clockEnergy` finite-dim) and
  `areaTerm_fin := ⟪A_edge_fin⟫_τ · c`, with `c` a **free** parameter.

### T1.3 — the finite first law ⟹ the balance (the crux theorem)
From the **existing finite first law** (`ArakiEntropy.lean`: `S(ρ) + D(ρ‖σ) = ⟨K_σ⟩_ρ`, `firstLaw_saturation`,
`kms_condition`) plus a genuine clock positivity (`⟨A_edge_fin⟩·c ≥ ⟨K_σ⟩` — the clock energy dominates the bare
modular energy, the finite shadow of CLPW's `S_gen = ⟨X⟩ + S_out + const`), prove
```lean
theorem phase5_balance_fin :
    SvN_fin + cgpEntropy S_fin ξ + remainder_fin = areaTerm_fin    -- remainder_fin ≥ 0
```
with `remainder_fin` the **model's actual** clock/bulk gap (≥ 0 from clock positivity + `cgpEntropy_nonneg`),
**not** an assumed slack.

### T1.4 — the instance + the unconditional corollary
```lean
noncomputable instance : Phase5Master S_fin ξ SvN_fin areaTerm_fin :=
  ⟨remainder_fin, remainder_fin_nonneg, phase5_balance_fin⟩    -- NOT Phase5Master.of_le ‹assumed ›
example : SvN_fin ≤ edgeArea_fin / (4 * ellP ^ 2) := holographic_area_floor S_fin …
```
So **P4's holographic floor holds unconditionally in this finite model** — the certificate is discharged from a
real trace, non-vacuously.

### T1 honest scope (enforced)
- A **finite Type I/II₁ shadow**, NOT genuine Type II_∞: the `e^{−s}` continuum trace-scaling and the unbounded
  clock stay in T2. The file header and the doc must say this — no implying the continuum trace is built.
- **Non-vacuity is the soundness deliverable:** the instance must derive `remainder` from model arithmetic + a
  genuine positivity (clock dominance + `cgpEntropy_nonneg`), and the model must be non-trivial (`ρ ≠ σ`,
  `SvN_fin > 0`). Add an `AxiomAudit` `#print axioms` (= std-3) and a vacuity note.
- The `1/4` / `c` is never assigned; `⟨A_edge⟩ = A(∂R)` is never asserted.
- **Tractability: medium, weeks.** The finite entropy/first-law/KMS machinery already exists; the new work is the
  finite clock factor, the trace-scaling exhibit, the clock-dominance positivity, and assembling the instance.
  Risk concentrates in (i) aligning the finite clock so the balance is a clean theorem and (ii) making the
  dual-action scaling honestly Type-II-shaped on the discrete clock (state it's a shadow if it stays Type II₁).

---

## 4. The continuum frontier — T2–T4 *(mapped, not scheduled; multi-month, Mathlib-grade)*

2. **T2 — the genuine Type II trace `τ`** on `M ⋊_σ ℝ`: the von Neumann weak closure of `π(M) ∪ {λ_t}`, the
   **dual weight** (Takesaki–Haagerup) from a weight on `M`, and the semifinite trace with `τ ∘ θ_s = e^{−s} τ`
   (the *literal* continuum scaling that defines Type II_∞ — the deep analytic step, with the **unbounded** clock
   `X`). None in Mathlib.
3. **T3 — finite renormalized entropy** `S_τ(ρ) = −τ(h_ρ log h_ρ)`, finite where the Type III entropy diverged —
   the "removes one infinity (entropy)" win, now *internal* to QIQT-H rather than cited.
4. **T4 — the JLMS first law as a theorem of `τ`**, yielding the master inequality with `areaTerm =
   ⟨A_edge⟩/4ℓ_P²` ⟹ `holographic_area_floor` unconditional in the continuum. The coefficient `1/4` remains the
   one carried UV input (the fatal-obstruction §0 datum).

---

## 5. Honest scale

The operator-level crossed product off `σ_t` (Increments 1a–1c, the clock energy, the dressed self-adjoint `K̃`)
is **DONE**. **T1** (the finite-trace certificate instance) is the tractable, self-contained next increment:
weeks, on existing finite-entropy infrastructure, converting P4's floor from "conditional on `Phase5Master`" to
"theorem in a concrete model + a named continuum obligation." **T2–T4** (the genuine continuum dual-weight Type
II_∞ trace) are a multi-month, Mathlib-grade undertaking — crossed-product vN algebras, the dual-weight trace,
Type II classification are open Mathlib targets in their own right. Nothing here claims the `1/4` or the
geometric area identification; those are the cited UV frontier throughout.

---

## 6. Verification (per increment)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green; `#print axioms` = standard 3;
`bash scripts/axiom_budget_check.sh` budget 0; wire into `QIQTH.lean` + `AxiomAudit.lean`; one commit per
increment with the `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>` trailer; push via schannel.
**T1 acceptance:** a `Phase5Master` instance built from `phase5_balance_fin` (NOT `of_le` on an assumed
inequality), `holographic_area_floor` instantiated for `S_fin`, a non-vacuity note (`ρ ≠ σ`, `SvN_fin > 0`),
`#print axioms` std-3, and a header stating the Type I/II₁-shadow scope.

---

## Progress log

- **Increment 1a-0 ✅** (`CrossedProduct.lean`) — the **modular automorphism** `σ_t(a) = Δ^{it} a Δ^{-it}`
  (`modularAut`) as a one-parameter group of unital `*`-homomorphisms (`modularAut_{zero,one,mul,add,star}`).
- **Increments 1a/1b/1c ✅ COMPLETE** (superseding the earlier "BLOCKED" checkpoint — the `L²(ℝ;H)`
  operator-valued infrastructure and Stone got built):
  - `π(a)` operator-valued `Lp`-multiplication (`CrossedProductRep.lean`); `λ_t` clock translations as a
    strongly-continuous unitary group (`CrossedProductTranslation.lean`, `clockTransl_stronglyContinuous`);
  - the covariance `λ_t π(a) λ_{−t} = π(σ_t a)` (`CrossedProductCovariance.lean`);
  - **the clock energy `X = A_edge` self-adjoint** (`clockEnergy_isSelfAdjoint`, `CrossedProductGenerator.lean`)
    via the now-built Stone's theorem (`Spectral/Stone.lean` + `Garding.lean`);
  - the fiberwise bulk modular `Δ̂^{it}` with strong continuity + clock-commutation (`CrossedProductModularFlow.lean`);
  - **the dressed `K̃ = K_bulk + A_edge` proved self-adjoint** (`dressedModularGen_isSelfAdjoint`, via
    `Spectral/StoneProduct.lean`).
- **The `Phase5Master` reduction ✅** (`FQBoundCGP.lean`, `FQBoundConditional.lean`) — P4's holographic floor is
  reduced to the single, non-vacuous, minimal inequality `SvN + cgpEntropy ≤ ⟨A_edge⟩/4ℓ_P²`; the slack
  positivity `cgpEntropy_nonneg` is proved; `holographic_area_floor` is unconditional relative to the certificate.
- **NEXT → T1** (`CrossedProductFiniteTrace.lean`) — a non-vacuous `Phase5Master` instance from a **finite**
  crossed-product trace (§3): the finite first law supplies the balance, discharging the certificate in a concrete
  model (Type I/II₁ shadow). Then T2–T4 = the continuum dual-weight Type II_∞ trace (§4, multi-month frontier).
