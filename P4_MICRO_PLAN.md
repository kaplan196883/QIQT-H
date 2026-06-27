# P4-MICRO — deriving the holographic area floor from the finite microstate postulate

**Status:** active · supersedes the dual-weight-trace dependency as the *shippable* P4 endpoint
(the Type II / crossed-product route in `P4_WALL_CAMPAIGN_PLAN.md` remains the deeper, open frontier).
**Created:** 2026-06-27. **Owner:** PK. **Co-author trailer:** `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`.

---

## 1. The pivot (why P4-MICRO)

P4 is the holographic area floor `S(ρ_R) ≤ A/4ℓ_P²`. The campaign has been deriving it via **Route 1**
(the crossed-product Type II construction): the area emerges as the generator of the dual flow, JLMS gives
`K̃ = A_edge·(1/4ℓ_P²) + K_bulk`, and relative-entropy positivity (`cgpEntropy_nonneg`) closes it. That route
*explains why the bound is the area*, but it rests on the **dual-weight trace** `τ∘θ_s = e^{−s}τ` on
`M ⋊_σ ℝ` — a genuine multi-year Mathlib-grade gap (no von Neumann weights, crossed products, or Takesaki
duality in Mathlib). General Stone is already DONE (`stoneGen_isSelfAdjoint`, `clockEnergy_isSelfAdjoint = X =
A_edge`); the trace is the one wall left, and it does not fall soon.

**Route 2 — P4-MICRO.** Postulate the *microstate count* directly (the finite quantized capacity that is the
literal "QI" core of QIQT-H) and the area floor falls out of an **already-proven finite theorem**:

```
P4-MICRO :  log |𝓗_R|  =  A/4ℓ_P²              -- region has a finite effective dimension; its log = the area term
        +   S(ρ) ≤ log |𝓗_R|                    -- shannon_le_log_card  (QIQTH/RecordContract.lean:132, AXIOM-FREE)
        ────────────────────────────────────────
        ⟹   S(ρ_R) ≤ A/4ℓ_P²   =   P4           -- the holographic area floor, now a COROLLARY
```

The derivation step `P4-MICRO ⟹ P4` is one line of finite QM. P4 stops being an independent postulate and
becomes a theorem conditional on the framework's own finite-capacity postulate — **on-thesis**: the same finite
`Q_max` move that already removes the collapse postulate now also retires the area-law postulate.

## 2. The factorization of P4 (what each ingredient supplies — be precise)

| Ingredient | Role | Status in QIQT-H |
|---|---|---|
| **P4-MICRO** — region has *finite* effective dimension (`Fintype 𝓗_R`) | finiteness / quantized information | **the postulate** (the "QI" core; the deep, native move) |
| **Holographic postulate** — capacity scales with boundary *area*, not bulk volume (`log|𝓗_R| ∝ A`) | "why area" | the holographic input; carried, labelled |
| **Sakharov 1/4** — coefficient is `1/4ℓ_P²` | the ratio | **derived** (`SakharovRatio.lean`, circularity-clean) — NOT postulated |
| `S ≤ log|𝓗_R|` (Jensen/Gibbs) | finite max-entropy bound | **THEOREM** (`shannon_le_log_card`, axiom-free) |

P4-MICRO supplies *finite + counted*; the holographic postulate supplies *by area*; Sakharov supplies *1/4*.
Together ⟹ P4.

## 3. HONEST scope (constraints that do NOT relax under the pivot)

- **The UV datum is still carried, never claimed.** P4-MICRO = `log|𝓗_R| = A/4ℓ_P²` still contains the
  dimensionful value `A/4ℓ_P²` (the value of `G`/`ℓ_P`). The pivot **relocates** where the datum sits (from a
  macroscopic entropy postulate to a microscopic counting postulate); it does **not** derive the value of `G`.
  The area term's coefficient is a free real parameter throughout. Never assert `⟨A_edge⟩ = A/4ℓ_P²`.
- **The derivation is cheap by design** — that is the *point* (a hard explanation traded for a clean postulate
  + a proven theorem). Route 2 does NOT reproduce Route 1's modular-origin explanation of "why area"; the
  holographic postulate is assumed, clearly labelled. Route 1 stays in the paper as the open frontier that
  would *derive* the holographic postulate itself.
- **No `sorry`; free scalar only; standard-3 axioms; budget 0.** The `1/4` ratio is derived elsewhere
  (`SakharovRatio`), never re-asserted here.

## 4. Lean design — `QIQTH/FQBoundMicro.lean` (new)

Mirrors the `Phase5Master`/`DonaldSystem` typeclass-interface pattern: P4-MICRO is a **named typeclass**, P4's
bound is an **unconditional theorem relative to it**, and the engine is the already-green `shannon_le_log_card`.

```lean
import QIQTH.RecordContract            -- shannon_le_log_card, BranchLedger.Shannon, RecordLaw
namespace QIQTH

/-- **P4-MICRO** — the finite-microstate (quantized-information) postulate for a region `R`:
    `R` has a finite effective Hilbert space (`Fintype R`) whose log-dimension equals the area term.
    `capacity` is the *holographic* input `log|𝓗_R| = A/4ℓ_P²`; the coefficient is the carried UV datum. -/
class MicrostatePostulate (R : Type*) [Fintype R] (areaTerm : ℝ) where
  capacity : Real.log (Fintype.card R) = areaTerm

/-- **★★★ P4's holographic area floor as a COROLLARY of P4-MICRO.**  For any Born record law `p` on the
    finite microstate set `R`, the Shannon entropy is at most the area term — by `shannon_le_log_card`
    rewritten through the P4-MICRO capacity equation.  Axiom-free; the area coefficient is never assigned. -/
theorem area_floor_of_microstate {R : Type*} [Fintype R] {areaTerm : ℝ}
    [h : MicrostatePostulate R areaTerm] (p : R → ℝ) (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1) :
    QIQTH.BranchLedger.Shannon Finset.univ p ≤ areaTerm := by
  rw [← h.capacity]; exact shannon_le_log_card p hp h1

/-- Manifest physical form `S ≤ A/(4ℓ_P²)` (capacity specialized to `edgeArea/(4·ellP²)`). -/
class MicrostatePostulateArea (R : Type*) [Fintype R] (edgeArea ellP : ℝ) where
  capacity : Real.log (Fintype.card R) = edgeArea / (4 * ellP ^ 2)

theorem holographic_area_floor_micro {R : Type*} [Fintype R] {edgeArea ellP : ℝ}
    [h : MicrostatePostulateArea R edgeArea ellP] (p : R → ℝ) (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1) :
    QIQTH.BranchLedger.Shannon Finset.univ p ≤ edgeArea / (4 * ellP ^ 2) := by
  rw [← h.capacity]; exact shannon_le_log_card p hp h1

/-- **Capacity saturation under P4-MICRO:** at the maximally-mixed record the bound is an EQUALITY
    `S = areaTerm` (equilibrium / horizon local-equilibrium regime), via `shannon_uniform_eq_log_card`. -/
theorem area_floor_saturates {R : Type*} [Fintype R] [Nonempty R] {areaTerm : ℝ}
    [h : MicrostatePostulate R areaTerm] :
    QIQTH.BranchLedger.Shannon Finset.univ (fun _ : R => (Fintype.card R : ℝ)⁻¹) = areaTerm := by
  rw [shannon_uniform_eq_log_card, h.capacity]

end QIQTH
```

**Non-vacuity check** (mirror `Phase5Master.of_le`): exhibit a concrete instance — e.g. `R := Fin n` with
`areaTerm := Real.log n` — so the interface is demonstrably instantiable and the theorem fires on a real
witness (a small `example`/`def` at the bottom of the file). This proves the postulate is not empty and the
bound is not vacuous.

**Bridge to the existing conditional core.** `area_floor_of_microstate` discharges, for the finite-record
sector, exactly the `areaTerm` bound that `FQBoundCGP.holographic_area_floor` carried conditionally on
`Phase5Master`. Add a one-line remark/lemma noting the two endpoints agree on the area term: Route 1 supplies it
via the trace, P4-MICRO supplies it via finite capacity.

## 5. Increment checklist (most-tractable-first; one commit each)

- [x] **M-1 `area_floor_of_microstate`** — the core corollary + `MicrostatePostulate` class. ✅ LANDED 2026-06-27
  (`QIQTH/FQBoundMicro.lean`): green, `#print axioms` = standard 3, budget 0, wired into `QIQTH.lean` + `AxiomAudit.lean`.
- [x] **M-2 manifest area form** — `MicrostatePostulateArea` + `holographic_area_floor_micro` (`S ≤ edgeArea/(4ℓ_P²)`).
  ✅ LANDED 2026-06-27: green, `#print axioms` standard 3, budget 0.
- [x] **M-3 saturation** — `area_floor_saturates` (equality at the maximally-mixed record). ✅ LANDED 2026-06-27:
  green, `#print axioms` standard 3, budget 0.
- [ ] **M-4 non-vacuity witness** — concrete `Fin n` instance + `example` firing the bound (proves the interface non-empty).
- [ ] **M-5 bridge remark** — connect to `FQBoundCGP.holographic_area_floor`; note Route 1 vs Route 2 deliver the same area term.
- [ ] **M-6 paper hook** — one paragraph in the foundations paper / scope note: "P4 as a corollary of the finite
  capacity postulate (machine-checked), with the Type II trace as the open frontier that would derive the
  holographic postulate." *(doc-only; no Lean)*

Each Lean brick: `cd lean/mathlib && ~/.elan/bin/lake build QIQTH.FQBoundMicro` green · `#print axioms` standard 3 ·
`bash scripts/axiom_budget_check.sh` budget 0 · wire into `QIQTH.lean` + `AxiomAudit.lean` · ONE commit on main with
the Co-Authored-By trailer · push via `git -c http.sslBackend=schannel push origin main` · update §6 progress log
AND the `P4_WALL_CAMPAIGN_PLAN.md` checklist (note the P4-MICRO endpoint beside the Type II frontier).

## 6. Progress log

- 2026-06-27 — plan authored. Confirmed engine `shannon_le_log_card` (`QIQTH/RecordContract.lean:132`) and
  `shannon_uniform_eq_log_card` (`:170`) are axiom-free and in the library; `FQBoundCGP.holographic_area_floor`
  is the conditional Route-1 endpoint this complements.
- 2026-06-27 — **M-1 LANDED.** `QIQTH/FQBoundMicro.lean`: `MicrostatePostulate` typeclass + `area_floor_of_microstate`
  (`[MicrostatePostulate R areaTerm] → Shannon univ p ≤ areaTerm`) via `shannon_le_log_card` ∘ `← capacity`. Builds
  green, `#print axioms` = standard 3, budget 0, full `QIQTH` green; wired into `QIQTH.lean` + `AxiomAudit.lean`.
  P4's area floor is now a theorem conditional on the finite-microstate postulate (Route 2 endpoint), beside the
  Type II trace (Route 1, open). Next: **M-2** (manifest `S ≤ edgeArea/(4ℓ_P²)` form).
- 2026-06-27 — **M-2 LANDED.** `MicrostatePostulateArea` class + `holographic_area_floor_micro`
  (`[MicrostatePostulateArea R edgeArea ellP] → Shannon univ p ≤ edgeArea/(4·ellP²)`): the area floor in manifest
  `S ≤ A/(4ℓ_P²)` shape, the `1/4ℓ_P²` coefficient explicit in the statement (`edgeArea`, `ellP` free reals; UV
  datum never assigned). Green, `#print axioms` standard 3, budget 0, wired into `AxiomAudit.lean`. Next: **M-3**
  (`area_floor_saturates`, equality at the maximally-mixed record via `shannon_uniform_eq_log_card`).
- 2026-06-27 — **M-3 LANDED.** `area_floor_saturates` (`[MicrostatePostulate R areaTerm] [Nonempty R] →
  Shannon univ (fun _ => (card R)⁻¹) = areaTerm`): the area floor is an EQUALITY at the maximally-mixed record
  (equilibrium regime), via `shannon_uniform_eq_log_card` ∘ `capacity`. So P4-MICRO gives both bound and
  saturation. Green, `#print axioms` standard 3, budget 0, wired into `AxiomAudit.lean`. Next: **M-4** (concrete
  `Fin n` non-vacuity witness firing the bound).

## 7. Files

**New:** `QIQTH/FQBoundMicro.lean`.
**Extend:** `QIQTH.lean` (import), `QIQTH/AxiomAudit.lean` (`#print axioms` per new theorem),
`P4_WALL_CAMPAIGN_PLAN.md` (record the P4-MICRO endpoint), the foundations paper / scope note (M-6).
**Reuse (do not duplicate):** `shannon_le_log_card`, `shannon_uniform_eq_log_card`, `BranchLedger.Shannon`,
`RecordLaw` (`QIQTH/RecordContract.lean`); the typeclass-interface discipline of `Phase5Master`/`DonaldSystem`.

## 8. Verification

- `~/.elan/bin/lake build QIQTH.FQBoundMicro` green; full `~/.elan/bin/lake build QIQTH` green.
- Every new theorem `#print axioms` → only `propext, Classical.choice, Quot.sound`.
- `bash scripts/axiom_budget_check.sh` → budget 0 (no new axioms; P4-MICRO is a *typeclass hypothesis*, not an axiom).
- Non-vacuity: the `Fin n` witness instantiates `MicrostatePostulate` and the bound fires — the interface is not empty.
- Honest-scope lint: the area coefficient appears only as a free variable; no numeric value of `G`/`ℓ_P` asserted;
  `1/4` not re-derived here (only referenced to `SakharovRatio`).
