# Prize execution plan — from the finite core to the covariant μ

*Staged, Lean-grounded plan to reach the QIQT-H prize: a canonical, Lorentz-covariant
typicality measure μ over actuality-selectors λ, **derived not chosen**. Written 2026-06-06,
grounded in the existing formalization. Difficulty key: **S** = hours, **M** = days, **L** =
weeks, **XL** = months / new Mathlib infrastructure. Each item lists what EXISTS, the concrete
Lean target, and dependencies. The honest standing: Stages 1–2 (free fields) would already be a
major result; Stage 3 is the deep analytic frontier.*

---

## 0. Where we stand (inventory — what is already axiom-free)

The continuum scaffolding is NOT axiomatized — it is encoded as **structures** (interface-as-
hypothesis); the open problem is *inhabiting* them from a real field, plus the analytic core.

| Module | Provides (axiom-free) | What it still lacks |
|---|---|---|
| `EffectGleason` | finite effect-Gleason: normalized+positive+coexistent-additive functional = `tr(ρ·)` | continuum (Bunce–Wright) version |
| `RecordGleason` | Born tensor-multiplicativity (`born_kron`), decoherent-partition additivity (`decoherent_partition_additive`) | continuum partitions |
| `GleasonSelector` | Born from positivity + ray-certainty; rank-one sandwich | the covariant μ |
| `BornJoin`/`BornJoinGleason`/`OneSiteGleason` | **finite no-collapse Born representation** (this thread) | continuum lift |
| `FreeFieldRecord` | free-field **finite-mode** instance: record count ≤ `e^Q`, Gaussian decoherence decay `γ^L→0`, finite Lorentz action via mode permutations | genuine field modes (infinite); real Poincaré |
| `FiniteModularTheory` | **finite-dim Tomita–Takesaki**: modular automorphism `σ_t`, KMS, `deltaConj_eq_modAut` | Type III / infinite dim |
| `Spectral/PVM` | `ProjectionValuedMeasure` structure + `boundedFC`, `scalarMeasure`, σ-additive POVM lemmas | — (feeds `SpectralTheorem`) |
| `Spectral/SpectralTheorem` | **DONE (2026-06): bounded spectral theorem** `PVM_of_selfAdjoint`, `T=∫λ dE`; **bounded Borel FC** `borelFC`; **continuum modular flow** `Δ^{it}`=`modFlow` (unitary group, Stone), modular automorphism `*`-group `σ_t`=`modAut`, state-invariance, entire complex-time flow `modFlowC`/`modDelta` | KMS identity (needs genuine modular Δ); unbounded `T` |
| `StandardSubspaceModular` | **DONE up to the analytic √ (2026-06)**: RvD `P,Q,R=P+Q`; `0≤R≤2`; **`R` ℂ-linear, positive `Rℂ`**; **`D=P−Q` conjugate-linear ⇒ `J` antiunitary** | `R^{1/2}`/polar decomp — blocked on missing Mathlib `StarOrderedRing (B(H))` (circular with the operator √) |
| `LorentzSelection` | `RecordPresheaf` (functorial restriction), `GlobalSection` (=λ), `PoincareAction`, `RecordedHistoryNet`; `covariant_selection_exists`, `net_no_signaling` — covariance **derived** from the net | a non-toy `RecordedHistoryNet` instance |
| `LorentzSelectionStrong` | genuine `GroupAction` on Γ(X), `group_evaluation_covariance`, equivariant total-mass/cell, Born link; `LorentzWitness` toy models | free-field instance, cohomology |

**Net:** the finite case is done; the Stage-3 analytic core is now substantially built
(`Spectral/SpectralTheorem` + `StandardSubspaceModular`, axiom-free, at three named Mathlib walls —
see `TOMITA_TAKESAKI_ROADMAP.md`). The prize is (1) a real free-field instance of the
`RecordedHistoryNet`/sheaf with an equivariant Born μ, (2) the global-section / cohomology layer,
(3) the continuum Type III₁ realization closing the analytic core. The 33 remaining project axioms
are entirely **honest named entropy/modular interface inputs** — ArakiInterface (11), Donald (8),
DPI (4), EntropyBridge (6), RelEntPositivity (2), MarginalLocality (1) — standard Araki/
Tomita–Takesaki facts beyond current Mathlib; a full-codebase audit (2026-06-08) confirmed none is
vacuous or doing illegitimate load-bearing work, and that `tsirelson_bound` / Goldstein–Struyve
Steps 1 & 3 / `FQEquivarianceUniqueness` are all now *discharged* (axiom-free).

---

## STAGE 1 — Free-field finite-mode instance (highest leverage; closest to existing code)

*Goal: a NON-TOY `RecordedHistoryNet` instance from a free field truncated to `n` modes, with an
equivariant Born μ on its recorded histories — converting the Lorentz promissory note into a
finite-mode result. Effort: **M–L**. Builds directly on `FreeFieldRecord` + `RecordGleason` +
`LorentzSelectionStrong`.*

> **STATUS (2026-06-06, commit bf6cb23): core deliverable DONE (minimal 2-mode version).**
> `QIQTH/FreeFieldNet.lean` builds, axiom-free, the first `RecordedHistoryNet` with GENUINE
> marginalizing restriction (vs `LorentzWitness`'s trivial identity restriction) and the product
> Born measure `ω`, where the no-signaling marginal `ω_marg` is a real THEOREM (`bornNet`,
> `bornNet_no_signaling`); `bornNet_covariant_selection` discharges `covariant_selection_exists`
> for it. This realizes the heart of 1.4 for a 2-mode (`false ≤ true`) net with a TRIVIAL action.
>
> **1.2 DONE (commit 0b7a7d1, `QIQTH/QubitIC.lean`):** finite Covariant Record-Completeness for a
> qubit — explicit rational IC-POVM `qubitIC` (mixed tetrahedron), `qubitIC_sum` (POVM),
> `qubitIC_separating` (the four record traces tomographically SEPARATE density matrices —
> informationally complete; the make-or-break lemma's finite case, NOT a restatement of
> `trace_form_unique`), `qubitIC_records_imply_all_effects` (bridge into effect-Gleason). Residual:
> PSD of each `Eₖ` deferred (tedious quadratic-form computation; not needed for separation).
>
> **1.3 DONE (equivariance):** `BornTypicalityFinite.w_perm_invariant` (product Born measure is
> permutation-invariant) + `FreeFieldNet.Dω_swap_invariant` (2-mode instance).
>
> **Diamond-permuting action DONE (commit 40f50b0, `QIQTH/DiamondSwapNet.lean`):** the 2-atom
> diamond `left,right ≤ top` (a 2-mode region with two 1-mode sub-diamonds via `fst`/`snd`);
> `swapIso` (left↔right swap is a genuine non-trivial order-iso), `swapAction` (a `PoincareAction`
> that MOVES the geometry, `act left = right`, acting on the top fibre by `Prod.swap`, naturality
> from `snd ∘ swap = fst`), `swap_covariant_selection` (covariant selector over the orbit — the
> covariance machinery exercised over a real geometry permutation WITH a marginalizing
> restriction, unlike `LorentzWitness`).
>
> **Still to do for full Stage 1:** ground the fibres/state in `FreeFieldRecord` sectors (1.1) and
> unify the four pieces (FreeFieldNet ω + DiamondSwapNet action + QubitIC records + permutation
> equivariance) into ONE net with the IC-POVM Born weights as `p`. Conceptual core of Stage 1 is
> now in hand; next is **Stage 2** (sheaf / global-section / Roberts–DHR cohomology).

- **1.1 (M) Finite-mode measurement POVM.** Define the `n`-mode number-basis / Gaussian PVM as a
  concrete `FinPVM` (or matrix POVM) on `⊗ⁿ ℂ^d`. Target: `freefield_pvm_complete` (∑ E = 1) and
  each `E` an `IsEffect`. *Exists:* `FreeFieldRecord` sectors + `kronN` machinery in
  `BornTypicalityQuantum`. *Dep:* none.
- **1.2 (L) Covariant Record-Completeness (finite-mode) — the make-or-break lemma, finite case.**
  Show the finite-mode record protocols are **effect-complete**: they tomographically separate all
  effects on the mode algebra (so Gleason has enough effects). Target:
  `freefield_records_separate_effects : (∀ a, (ρ₁*E_a).trace = (ρ₂*E_a).trace) → ρ₁ = ρ₂`. *Exists:*
  `EffectGleason.trace_form_unique` (finite separation already proved for ALL effects). So 1.2 is
  largely *citing* `trace_form_unique` once records = effects (1.1). *Dep:* 1.1.
- **1.3 (M) Equivariant μ on finite-mode cylinders.** Combine `RecordGleason.born_kron`
  (tensor-multiplicativity) + `decoherent_partition_additive` + `FreeFieldRecord.boost_*` (mode-
  permutation Lorentz action) to define μ on product histories and prove
  `freefield_mu_equivariant : g_*μ_Φ = μ_{U_gΦ}` for the finite mode-permutation group. *Exists:*
  `BornMeasureUniqueness` (product measure + uniqueness), `LorentzSelectionStrong.measure_pushforward_*`.
  *Dep:* 1.1, 1.2.
- **1.4 (M) Instantiate `RecordedHistoryNet`.** Assemble 1.1–1.3 into a concrete
  `LorentzSelection.RecordedHistoryNet` (over a finite Diam of mode-regions) and discharge
  `covariant_selection_exists` / `net_no_signaling` for it — a genuine (finite-mode) model, not
  `LorentzWitness`'s toy. *Deliverable:* `FreeFieldNet.lean` — "the covariant selection structure is
  realized by a free field's finite-mode truncation." *Dep:* 1.1–1.3.

**Stage-1 result:** the covariant Born μ exists for free-field finite-mode records — the first
non-toy inhabitant of the covariant interface. Retires (in the finite-mode regime) the
`FQEquivarianceUniqueness` interface axioms.

---

## STAGE 2 — Sheaf / global-section / cohomology layer (the linchpin structure)

*Goal: the Poincaré-equivariant recorded-history sheaf with a nonempty global-section space
(λ exists) and Kolmogorov-consistent equivariant μ — the linchpin theorem of OP3b, proved for the
free-field (finite-mode) net. Effort: **L–XL**. The genuine new math is net cohomology.*

> **STATUS (2026-06-06, commit c6d00b6, `QIQTH/SheafSection.lean`): 2.1, 2.2 DONE and 2.3 settled
> for the finite/product case — axiom-free (depends on NO axioms).** `topSection` (every ⊤-record
> extends to a global section — gluing unobstructed, λ EXISTS), `globalSection_eq_top` (every
> section is determined by its ⊤-value — `Γ(X) ≃ X⊤`, the Roberts–DHR cocycle vanishes trivially
> because ⊤ is a global chart), instantiated on the diamond net (`diamondSelector` /
> `diamondSelector_classifies`: selectors = joint 2-mode records). 2.5 (linchpin one-liner
> `A_{gD}=g·A_D`) is `evaluation_covariance` / `swap_covariant_selection` (done in Stage 1).
> **Remaining (genuinely XL, continuum-facing):** 2.3 for posets WITHOUT a global ⊤ chart (the
> NON-trivial net cohomology) and 2.4 (Kolmogorov/Carathéodory for the σ-additive continuum μ).

- **2.1 (M) Presheaf from the net.** Build `RecordPresheaf` over the causal-diamond poset from the
  Stage-1 net (functorial restriction = record coarse-graining). *Exists:* `RecordPresheaf` structure;
  `restrict_cast`. *Dep:* Stage 1.
- **2.2 (L) Global-section existence (λ).** Prove `Γ(X_Φ)` nonempty for the finite-mode net:
  `freefield_global_section_exists`. For a finite product poset this is gluing compatible local
  valuations — tractable. *Exists:* `GlobalSection` structure, `covariant_selection_exists`. *Dep:* 2.1.
- **2.3 (XL) Net-cohomology obstruction (the real depth).** Formalize the Roberts/DHR gluing cocycle
  `[g_{ij}] ∈ Ȟ¹(Aut X_Φ)` and prove it VANISHES for the product/finite-mode case (⇒ global section
  exists without obstruction; identifies WHERE covariance could break for general nets). Target:
  `net_cocycle_trivial_of_product`. *Exists:* nothing — new. This is the genuine mathematical
  contribution of OP3b; even stating it cleanly is progress. *Dep:* 2.1, 2.2.
- **2.4 (L) Kolmogorov/Carathéodory extension.** Extend the cylinder Born weights (Stage 1.3) to a
  σ-additive μ on Γ(X_Φ). Finite-mode = finite product ⇒ near-trivial; the continuum needs
  Carathéodory. Target: `freefield_mu_kolmogorov`. *Dep:* 1.3, 2.2.
- **2.5 (M) The linchpin (finite-mode).** Assemble: ∃ finite record algebras (log #atoms ≤ Q_D),
  boundary reconstruction, nonempty Γ(X_Φ), equivariant Kolmogorov μ, no-signaling marginals ⇒
  `A_{gD}[U_gΦ, gλ] = g·A_D[Φ,λ]` in one line (evaluation). Target:
  `freefield_linchpin`. *Deliverable:* the OP3b linchpin theorem for free fields. *Dep:* 2.1–2.4.

**Stage-2 result:** the equivariant holographic recorded-history sheaf theorem for free fields —
PRIZE_ROADMAP's linchpin, finite-mode. This is the "prove it for free fields first" milestone that
converts the Lorentz promissory note into a theorem.

---

## STAGE 3 — Continuum analytic infrastructure (the long pole)

*Goal: replace "finite-mode" with genuine infinite-dim Type III₁ QFT. Effort: **XL** — requires
new Mathlib operator-algebra infrastructure. This discharges the remaining continuum interface.*

> **STATUS (2026-06-06): finite shadows in hand; continuum proper is the genuine wall.**  The
> finite-dimensional groundwork for Stage 3 is axiom-free and built: `FiniteModularTheory`
> (`modAut`/`kms_condition`/`modAut_stateOf_invariant` — finite Tomita–Takesaki: the modular flow
> exists, satisfies KMS, and PRESERVES its state, commit 5c0d71d) and `Spectral/PVM` (structural
> PVM content).  **The continuum Stage 3 (3.1 bounded spectral theorem, 3.2 infinite-dim
> Tomita–Takesaki, 3.3 Type III₁ free-field net, 3.4 continuum Bunce–Wright) is NOT
> session-achievable**: it needs Type III von Neumann algebra theory absent from Mathlib (the
> bounded spectral theorem for self-adjoint operators on Hilbert space is itself an open Mathlib
> target).  Honest options: (a) a multi-month Mathlib operator-algebra contribution; (b) accept
> these as named cited-interface axioms (would re-grow the axiom budget — against the ratchet-down
> discipline).  Until then, the finite prize (Stages 1+2, machine-checked axiom-free) stands on
> its own; the continuum is openly gated.

- **3.1 (XL) Bounded spectral theorem / PVM analytic core.** Complete `Spectral/PVM.lean`:
  σ-additivity of the PVM, bounded Borel functional calculus, the spectral theorem for bounded
  self-adjoint operators. *Exists:* `PVContent` structure + structural lemmas; the analytic core is
  the named Phase-1 target. *Path:* contribute to Mathlib `Analysis.InnerProductSpace.Spectrum`
  (finite-dim spectral theorem exists; bounded infinite-dim does not). *Dep:* none (parallel track).
  > **FINITE CASE DONE (commit 4374c73, `QIQTH/SpectralPVM.lean`, axiom-free):** the matrix
  > spectral theorem packaged as a PVM — `specProj` (eigenprojections `U·diag(δᵢ)·U⋆`),
  > `specProj_sum_eq_one` (resolution of identity ∑P=1), `specProj_idem`/`specProj_orthogonal`/
  > `specProj_selfAdjoint`, `A_eq_conj_diag`.  The discrete spectral measure is a finite PVM.
  > The CONTINUUM (bounded Borel FC / PVM for Hilbert-space operators) is the open Mathlib target.
- **3.2 (XL) Tomita–Takesaki at infinite dimension.** Extend `FiniteModularTheory` (which proves the
  finite-dim modular flow + KMS) to the Type III setting: modular operator Δ from a cyclic-separating
  vector, `σ_t = Δ^{it}·Δ^{-it}`, KMS. *Exists:* finite-dim `modAut`, `kms_condition`,
  `deltaConj_eq_modAut`. *Path:* major new Mathlib vNA development; or accept Tomita–Takesaki as a
  cited interface theorem (honest, common in physics formalization). *Dep:* 3.1.
- **3.3 (XL) Type III₁ free-field net instance.** Inhabit `RecordedHistoryNet` *with its unitary
  Poincaré transport* from an actual relativistic free field (CPW/Witten net): wedge algebras,
  Bisognano–Wichmann modular covariance, split property. *Exists:* the structural target in
  `LorentzSelection`; the finite-mode instance from Stage 1. *Dep:* 3.1, 3.2, Stage 1–2.
- **3.4 (XL) Bunce–Wright–Christensen–Yeadon continuum Gleason.** The σ-additive Mackey–Gleason
  uniqueness on type II/III algebras — retires the `TypicalityMackeyGleason` content-free placeholder.
  *Path:* cited interface or major build. *Dep:* 3.1.

**Stage-3 result:** the genuine continuum covariant μ — the actual prize. Retires the bulk of the 33
continuum interface axioms.

---

## Dependency DAG (critical path)

```
finite core (DONE) ─┐
                    ├─► 1.1 ─► 1.2 ─► 1.3 ─► 1.4 ──► 2.1 ─► 2.2 ─► 2.4 ─► 2.5  (free-field prize)
                    │                                   └─► 2.3 (cohomology) ─┘
3.1 (spectral) ─► 3.2 (Tomita) ─► 3.3 (Type III net) ─► [continuum prize]
3.1 ─► 3.4 (continuum Gleason) ───────────────────────┘
```

Stages 1–2 are independent of Stage 3 (they stay finite-mode) — **do them first**. Stage 3 is a
parallel, long infrastructure track (or cite-as-interface).

---

## Honest kill-criteria (pivot if any fires — from PRIZE_ROADMAP §7)

1. A non-Born assignment satisfies the exact finite axioms *including record certainty*.
2. Record certainty turns out disallowed (maximally-mixed survives ⇒ uniqueness false).
3. Record protocols are not effect-complete (Stage 1.2 fails ⇒ Born underdetermined).
4. Overlapping recorded partitions cannot form a consistent cylinder system (Stage 2.4 fails ⇒ no global μ).
5. Finite records cannot be localized in diamonds without foliation dependence (covariance fails).
6. The recorded sheaf has no sector-twisted global sections (Stage 2.3 obstruction nonzero ⇒ drop λ-as-section).
7. Normality cannot be justified (singular finitely-additive states spoil uniqueness).

---

## Recommended order & honest effort

1. **Stage 1 (M–L, do now).** Free-field finite-mode instance — highest leverage, near existing code; a real (finite-mode) inhabitant of the covariant interface. *This is the next concrete build.*
2. **Stage 2.1–2.2, 2.4–2.5 (L).** Sheaf + global section + Kolmogorov + linchpin, finite-mode. Defer 2.3 (cohomology, XL) — state it, vanish it for the product case, flag the general case open.
3. **Stage 3 (XL, parallel/long).** Spectral theorem + Tomita–Takesaki as either a Mathlib contribution or a cited interface; Type III net instance last.

**Brutal honesty:** Stages 1–2 give "the covariant Born μ, derived, for free fields (finite-mode)"
— a genuine, publishable advance and the honest meaning of "prove it for free fields first." The
*full* continuum prize requires Stage 3, which is months of operator-algebra infrastructure (or
honest cited interfaces). And the prize may, in the end, be a sharpened restatement of the
measurement problem's shared debt — owned, not hidden.
