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
| `Spectral/PVM` | `PVContent` structure + structural lemmas (idempotent, adjoint, `mu_nonneg`, …) | the analytic spectral theorem (σ-additivity, bounded Borel FC) |
| `LorentzSelection` | `RecordPresheaf` (functorial restriction), `GlobalSection` (=λ), `PoincareAction`, `RecordedHistoryNet`; `covariant_selection_exists`, `net_no_signaling` — covariance **derived** from the net | a non-toy `RecordedHistoryNet` instance |
| `LorentzSelectionStrong` | genuine `GroupAction` on Γ(X), `group_evaluation_covariance`, equivariant total-mass/cell, Born link; `LorentzWitness` toy models | free-field instance, cohomology |

**Net:** the finite case is done; the prize is (1) a real free-field instance of the
`RecordedHistoryNet`/sheaf with an equivariant Born μ, (2) the global-section / cohomology layer,
(3) the infinite-dim analytic core. The 33 remaining project axioms (Araki / Donald / DPI /
EntropyBridge / Mackey–Gleason / `TypicalityMackeyGleason` / `FQEquivarianceUniqueness`) are the
continuum interface those stages would retire.

---

## STAGE 1 — Free-field finite-mode instance (highest leverage; closest to existing code)

*Goal: a NON-TOY `RecordedHistoryNet` instance from a free field truncated to `n` modes, with an
equivariant Born μ on its recorded histories — converting the Lorentz promissory note into a
finite-mode result. Effort: **M–L**. Builds directly on `FreeFieldRecord` + `RecordGleason` +
`LorentzSelectionStrong`.*

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

- **3.1 (XL) Bounded spectral theorem / PVM analytic core.** Complete `Spectral/PVM.lean`:
  σ-additivity of the PVM, bounded Borel functional calculus, the spectral theorem for bounded
  self-adjoint operators. *Exists:* `PVContent` structure + structural lemmas; the analytic core is
  the named Phase-1 target. *Path:* contribute to Mathlib `Analysis.InnerProductSpace.Spectrum`
  (finite-dim spectral theorem exists; bounded infinite-dim does not). *Dep:* none (parallel track).
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
