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

## 3.1 GPT-5.5-pro review (2026-06-27) — verdict **sound-with-fix**, 3 corrections to fold in

Consulted via the OpenAI MCP (`mcp__OpenAI__ask`, model `gpt-5.5-pro`). Verdict: the pivot is mathematically
sound as a **conditional finite-capacity theorem** — it does NOT derive holography from nothing, it replaces the
entropy-area postulate with a holographic *capacity / microstate-count* postulate; legitimate iff stated honestly
("P4 is a theorem **conditional on** the holographic capacity postulate", never "axiom-free / area law derived").
Three highest-value corrections (now the corrected design):

- **C1 — object mismatch (BIGGEST, technical).** `shannon_le_log_card` bounds the SHANNON entropy of an arbitrary
  Born *record law* `p`; P4 is about the VON NEUMANN entropy `S_vN(ρ_R)`. Routing P4 through "Shannon of a record
  law" is a category slip unless `p` is the *spectrum* of `ρ` (dephasing only *raises* entropy: a pure equal
  superposition has `H(p)=log d` but `S_vN=0`, so `S_vN ≤ H(p)` one-way only). **Fix:** state the honest
  finite-dim max-entropy theorem `S_vN(ρ) ≤ log rank ρ ≤ log dim 𝓗_R` (Shannon applied to the *eigenvalues*), and
  present the record-law bound separately as the decohered/record entropy with `S_vN ≤ H(record)`.
- **C2 — split & rename the postulate.** P4 needs only the INEQUALITY `log N_R ≤ areaTerm`; exact equality
  `log N_R = areaTerm` belongs to a *separate* saturation postulate. Rename `MicrostatePostulate` →
  `HolographicCapacity`, with `…Bound` (`≤`, for the floor) and `…Exact` (`=`, for saturation only).
- **C3 — capacity is a regional operational invariant, not global Hilbert cardinality.** `Q_R := log N_R` = max
  number of mutually distinguishable *regional* microstates (capacity of the finite regional algebra / area
  sector). Continuum local algebras are **type III** (no finite trace, no factorized `ρ_R`): a literal
  finite-dim `𝓗_R` is already a type-I/code CUTOFF — acceptable inside QIQT-H but must be stated explicitly, as a
  fixed-area-sector / code-subspace capacity, not a global dimension. Prefer fixed-area sectors (area-as-operator
  fluctuations make exact `log dim = ⟨A⟩/4` suspect; `≤` is the safe form).

Route 1 (Type II) is **not** superseded: Route 2 = the completed *kinematic* finite-capacity reduction (capacity ⇒
bound); Route 1 = the open *dynamical/modular* derivation of *why* capacity is holographic (area generator, JLMS,
type-III resolution). Present them as different logical levels.

## 3.2 GPT-5.5-pro review #2 (2026-06-27) — "does P4-MICRO give GR?" → NO alone; conditional yes

Consulted `gpt-5.5-pro`. Verdict on the GR question: **"P4-MICRO ⟹ GR" is FALSE as written.** The
machine-checked `jacobson_einstein_from_area_law` (`ClausiusToPernull.lean:181`) takes FIVE labelled physics
premises; P4-MICRO discharges only `hAreaLaw` (`δS = η δA`). The thermal pair `htemp` (Unruh `T=ℏκ/2π`) +
`hClausius` (`δQ=TδS`) and the geometric `hQ`,`hRay` are separate. Two tightenings (now binding):

- **GR-T1 — capacity provably CANNOT supply the temperature (decisive countermodel).** Fix `N` + self-adjoint
  boost `X`; P4-MICRO holds via `dim 𝓗_R = N`, but the saturated state `ρ_sat = I/N` has `β = 0` (infinite
  temperature) relative to `X`, NOT the Unruh `β = 2π/ℏκ`. A count fixes a max-entropy *number*, not a Gibbs
  weight. `dE = T dS` is no escape (boost-`E` ⇒ it *is* Clausius; modular-`E` ⇒ `T=1` in modular units, Unruh
  re-enters only via BW). So `htemp`/`hClausius` are irreducibly modular/KMS = **Route 1's job** — fundamental,
  not a formalization gap.
- **GR-T2 — static saturation ≠ the differential area law.** `shannon_eq_area_at_saturation` gives the *static*
  `S = ηA` at one equilibrium record; `hAreaLaw` is the *variational* `δS = η δA` under matter flux. The static
  fact implies the differential law only via a **saturated-variational bridge** (smooth family of local-eq horizon
  records + capacity tracks instantaneous area + the record entropy IS Jacobson's `dS` = the Gap-2 localization).
  So the honest statement is "P4-MICRO **+ the saturated-variational bridge** ⟹ `hAreaLaw`", not flatly "supplies
  `hAreaLaw`". Also flag the discrete-`N` vs smooth-`dA` subtlety (real-capacity model / large-area limit).

Honest paper sentence (GPT-5.5-pro): *"QIQT-H's finite holographic capacity postulate supplies the saturated local
horizon entropy–area variation `dS = dA/(4ℓ_P²)`; combined with independently established Unruh/KMS–Clausius
thermality and standard boost-flux/Raychaudhuri geometry, the Lean-checked Jacobson theorem yields the Einstein
field equations `G_{μν}+Λg_{μν}=8πG T_{μν}`."*  Scope the free-field claim as "only Gap-2 remains **on the
thermal/BW side**" — not "only Gap-2 remains" for the whole chain (`hQ`,`hRay`,regularity,conservation persist).

## 3.3 Verified P4-MICRO ⟹ GR chain map (agentic search, 2026-06-27) — exact theorem ledger

Three parallel Explore agents read the actual signatures of the entire chain. Two findings change the roadmap:

**Update 1 — GR-T2 (the static→variational bridge) is ALREADY machine-checked.** I had called `S=ηA ⟹ δS=ηδA`
an open assumption. It is a proven lemma: `QIQTH.DifferentialAreaLaw.differential_area_law_of_relEntropy` derives
`δS = η·δA` from exactly `hbound : S t ≤ η·A t` (= `area_floor`), `hsat : S 0 = η·A 0` (= `area_floor_saturates`),
and `hDnn, hD0` (the entanglement first law — Klein positivity, proven). So the bridge LOGIC is done; what remains
of GR-T2 is only that the capacity family be SMOOTH (differentiable in the horizon deformation), a regularity
condition — not a conceptual gap.

**Update 2 — the GR capstones already expose EXACTLY P4-MICRO's outputs as their entropy slots.**
`QIQTH.QiqtToGR.qiqt_bekenstein_gives_gr` (and `WedgeKMSToGR.qiqt_gr_from_flux_complete`,
`qiqt_gr_from_wedge_kms_complete`) take the entropy side as four hypotheses and leave the thermal/geometry inputs
labelled:
```
hbound : BL(g x)v=0 → ∀ᶠ t, S x v t ≤ η·A x v t        ← area_floor_of_microstate  (P4-MICRO)
hsat   : BL(g x)v=0 → S x v 0 = η·A x v 0               ← area_floor_saturates       (P4-MICRO)
hDnn   : BL(g x)v=0 → ∀ t, 0 ≤ KE x v t − S x v t        ← entanglement first law (Klein, PROVEN)
hD0    : BL(g x)v=0 → KE x v 0 − S x v 0 = 0
hFlux  : kd x v = 2π/ℏ · BL(T x)v   ← Bisognano–Wichmann boost flux = Unruh/Clausius (THERMAL — cited; derived
                                       for the free field via Fock.OneParticleBW.oneParticleBW_complete, RvD 3.8)
hFocus : ad x v = BL(ricci…)v        ← Raychaudhuri (geometry)
hreg, conserv                        ← f-regularity + ∇·T=0
```
So the entire chain is: **P4-MICRO fills `hbound`+`hsat`; Klein fills `hDnn`+`hD0`; `hFlux` (BW/Unruh) is the one
irreducible thermal input** (GR-T1 confirmed — the thermal slot is the only thing P4-MICRO cannot touch).

**Exact theorem ledger (signatures loaded, axiom-free unless noted):**
- Entropy engine: `RecordContract.shannon_le_log_card`, `…shannon_uniform_eq_log_card`,
  `BranchLedger.Shannon`, `QuantumRelativeEntropy.{IsDensity, vonNeumannEntropy, relEntropy_nonneg (Klein)}`,
  `SpectralSum.{vonNeumannEntropy_diagonal, vonNeumannEntropy_unitaryConj}`. **GAP:** no `vonNeumannEntropy ≤ log
  card` exists (= M-4); proof path: eigenvalues are a prob vector → `shannon_le_log_card`.
- Jacobson: `ClausiusToPernull.jacobson_einstein_from_area_law` (5 premises: `hAreaLaw, htemp, hClausius, hQ, hRay`
  + geometry), `DifferentialAreaLaw.{differential_area_law, differential_area_law_of_relEntropy}`,
  `EinsteinFieldEquation.{jacobson_einstein_equation_of_state, einstein_field_equation_real, twice_contracted_bianchi,
  einsteinTensor_divergence_zero}`, `EinsteinEquationOfState.symmTensor_eq_smul_metric_of_null(_general)`.
- Free-field thermal/BW: `QiqtToGR.qiqt_bekenstein_gives_gr`, `WedgeKMSToGR.{qiqt_gr_from_flux_complete,
  qiqt_gr_from_wedge_kms_complete, hFlux_of_wedgeKMS_complete, WedgeKMSFlux_complete}`,
  `Fock.OneParticleBW.{oneParticleBW_complete, oneParticleBW_wedge_complete, wedge_hBoostCharge_of_smooth}`,
  `EntanglementFirstLaw.{firstLaw_of_stationary, gibbs_first_law}`, `ArakiEntropy.{vonNeumann_le_modEnergy,
  firstLaw_saturation}`, `SakharovRatio.sakharov_ratio` (η=1/4).

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
*Bricks below revised per the GPT-5.5-pro review (§3.1). C1/C2/C3 take priority over the original M-4/5/6.*

- [ ] **M-4 (C1) honest von Neumann max-entropy bound** — `vonNeumannEntropy_le_log_card : S_vN(ρ) ≤ log dim 𝓗_R`
  (`[Fintype n]`, `h : QuantumEntropy.IsDensity ρ`). VERIFIED proof path (agentic search §3.3): `vonNeumannEntropy h
  = ∑ negMulLog(h.eigenvalues)` by def; the eigenvalues are a probability vector (nonneg + sum = 1, from `IsDensity`
  PosSemidef + trace 1) → apply `RecordContract.shannon_le_log_card h.eigenvalues _ _` after `shannon_eq_sum_negMulLog`.
  First confirm the exact eigenvalue-nonneg / sum-one lemma names on `IsDensity` (e.g. `h.eigenvalues_nonneg`,
  trace→`∑ eigenvalues = 1`); if absent, add the 2 short lemmas. Then `area_floor_vonNeumann
  [HolographicCapacityBound] : S_vN(ρ) ≤ areaTerm`. This is the HONEST P4 (von Neumann, not record-law Shannon).
  Keep the landed Shannon theorems, relabelled as the decohered/record-entropy bound with `S_vN ≤ H(record)`.
  *(highest value — the real fix; proof path now fully scoped)* — ✅ **LANDED 2026-06-27**:
  `vonNeumannEntropy_le_log_card` + `area_floor_vonNeumann` in `FQBoundMicro.lean` (used the existing `=`-form
  `MicrostatePostulate`; M-5 splits the `≤`-form). Green, `#print axioms` standard 3, budget 0.
- [x] **M-5 (C2) split + rename the postulate** — `HolographicCapacityBound` (`log dim ≤ areaTerm`, for the floor)
  vs `HolographicCapacityExact` (`= areaTerm`, for saturation only). ✅ **LANDED 2026-06-27**: + instance
  `instCapacityBoundOfExact` (`=⟹≤`); `area_floor_of_microstate`/`holographic_area_floor_micro`/`area_floor_vonNeumann`
  migrated to `Bound`; `area_floor_saturates` keeps `Exact`; `MicrostatePostulateArea` deleted
  (`holographic_area_floor_micro` is now a one-line corollary of `area_floor_of_microstate`). Green, standard 3,
  budget 0, full `QIQTH` green.
- [x] **M-6 (C3) regional `Q_R` framing + type-III caveat** — ✅ **LANDED 2026-06-27**: added a "WHAT THE CAPACITY
  IS — REGIONAL, AND A TYPE-I/CODE CUTOFF" block to the `FQBoundMicro.lean` module header (capacity = `Q_R = log N_R`
  = max distinguishable *regional* microstates / finite regional algebra / fixed-area sector / code subspace; the
  continuum local algebra is type III₁ — no finite trace, no `ρ_R` — so a finite-dim `R` is itself the holographic
  cutoff, not bookkeeping; `≤` is the safe form). Bound-class docstring rewritten to the regional `Q_R` reading.
  Doc-only; green.
- [x] **M-7 non-vacuity witness** — ✅ **LANDED 2026-06-27**: `finCapacityExact n : HolographicCapacityExact (Fin n)
  (Real.log n)` (a `@[reducible] def`, NOT a global instance — a deliberately-asserted witness, no resolution
  pollution) + two `example`s firing `area_floor_of_microstate` (bound) and `area_floor_saturates` (exact) on it.
  Proves the interface is inhabited and the bounds non-vacuous (mirrors `Phase5Master.of_le`). Green, standard 3,
  budget 0.
- [x] **M-8 bridge remark** — ✅ **LANDED 2026-06-27**: `holographic_area_floor_micro_vonNeumann`
  (`[HolographicCapacityBound n (edgeArea/(4·ellP²))] → S_vN(ρ) ≤ edgeArea/(4·ellP²)`) — the capacity-conditional
  analogue of Route 1's `FQBoundCGP.holographic_area_floor` (identical conclusion; conditional on capacity not
  `Phase5Master`). + a doc "Bridge" section: Route 2 kinematic (capacity⇒bound) vs Route 1 dynamical (the trace that
  would derive the capacity); complementary, same area term, each carries a named hypothesis. Green, standard 3,
  budget 0.
- [x] **M-9 paper hook** — ✅ **LANDED 2026-06-27**: added a "P4-MICRO (Route 2)" section to
  `paper_strategy/44_Formalization_Scope_Note.md` (the drop-in paragraph + honest-framing rules: "theorem
  conditional on the capacity postulate" not "area law derived"; carried UV datum; "P4-MICRO ⟹ GR" false alone) and
  updated the "what is / is not formalized" table — the capacity *axiom* stays a postulate (now a typeclass
  hypothesis, not a Lean axiom), but `S_vN ≤ Q_R` GIVEN it is now **machine-checked** (`area_floor_vonNeumann`).
  Doc-only.
- [ ] **M-10 (GR bridge) `gr_from_p4micro` against `QiqtToGR.qiqt_bekenstein_gives_gr`** — REVISED per §3.3: do NOT
  re-route through `jacobson_einstein_from_area_law`'s `hAreaLaw`; instead instantiate the free-field capstone
  `qiqt_bekenstein_gives_gr`, whose entropy slots are *already* P4-MICRO's outputs:
  · `hbound` ← `area_floor_of_microstate` (over a smooth family of `MicrostatePostulate` instances with
    `log N(t) = η·A(t)` — the only residual GR-T2 content, a SMOOTHNESS condition; the bridge logic
    `δS=ηδA` is already proven in `DifferentialAreaLaw.differential_area_law_of_relEntropy`),
  · `hsat` ← `area_floor_saturates`,
  · `hDnn`/`hD0` ← the entanglement first law (`EntanglementFirstLaw.firstLaw_of_stationary`, Klein — PROVEN).
  Resulting theorem keeps EXACTLY `hFlux` (BW/Unruh — the one thermal input; derived for the free field via
  `Fock.OneParticleBW.oneParticleBW_complete`), `hFocus` (Raychaudhuri), `hreg`, `conserv` as residual hypotheses —
  making "P4-MICRO fills the entropy slots; the thermal slot is BW/Route-1" a checkable Lean dependency, not prose.
  HONEST: temperature stays modular (GR-T1 — do not route `hFlux` through counting); the capacity-tracks-area family
  (`log N(t)=η A(t)`) and the record-entropy = horizon-`dS` identification are the Gap-2 localization, exposed as
  such. Optionally instantiate `η` with the Sakharov `1/4` (`SakharovRatio.sakharov_ratio`) so the output coupling is
  `8πG`. *(the high-value GR increment; do after M-4..M-6)* — ✅ **LANDED 2026-06-27**: new file
  `QIQTH/GRFromMicro.lean` — `hbound_hsat_of_capacity_family` (finite-capacity family ⟹ `hbound` ∧ `hsat`, via
  `area_floor_of_microstate` + `area_floor_saturates`) + `gr_from_p4micro` (plugs them into
  `qiqt_bekenstein_gives_gr`, leaving `hDnn,hD0,hFlux,hFocus,hreg,conserv` + structural as residual). Green, both
  standard 3, budget 0, full `QIQTH` green; wired into `QIQTH.lean` + `AxiomAudit.lean`.

Each Lean brick: `cd lean/mathlib && ~/.elan/bin/lake build QIQTH.FQBoundMicro` green · `#print axioms` standard 3 ·
`bash scripts/axiom_budget_check.sh` budget 0 · wire into `QIQTH.lean` + `AxiomAudit.lean` · ONE commit on main with
the Co-Authored-By trailer · push via `git -c http.sslBackend=schannel push origin main` · update §6 progress log
AND the `P4_WALL_CAMPAIGN_PLAN.md` checklist (note the P4-MICRO endpoint beside the Type II frontier).

- [x] **M-11 (bonus) von Neumann non-vacuity witness** — ✅ **LANDED 2026-06-27**: `oneDensity_isDensity :
  IsDensity (1 : Matrix (Fin 1) (Fin 1) ℂ)` (the one-microstate pure state, via `PosSemidef.one` + `trace_one`) +
  an `example` firing `area_floor_vonNeumann` on it (`S_vN = 0 ≤ log 1`). Completes M-7's Shannon-only witness with
  the von Neumann side. Needed `open scoped ComplexOrder` (ℂ's order is scoped). Green, standard 3, budget 0.

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
  saturation. Green, `#print axioms` standard 3, budget 0, wired into `AxiomAudit.lean`.
- 2026-06-27 — **GPT-5.5-pro review** (§3.1): verdict **sound-with-fix**. Folded 3 corrections into the design and
  revised the checklist: C1 (honest von Neumann max-entropy `S_vN ≤ log dim`, not Shannon-of-record-law — the real
  fix), C2 (split/rename postulate into `…Bound` `≤` vs `…Exact` `=`), C3 (regional `Q_R` / type-III cutoff
  caveat). M-1/M-2/M-3 stand as theorems but get relabelled (record-law entropy) and migrated onto the bound form.
  Next: **M-4** (von Neumann max-entropy bound + `area_floor_vonNeumann`).
- 2026-06-27 — **GR question + chain mapped** (§3.2 review #2 + §3.3 agentic search). Verdict: "P4-MICRO ⟹ GR" is
  false alone; conditional yes. Two findings refined the roadmap: GR-T2 (static→variational bridge) is already
  machine-checked (`differential_area_law_of_relEntropy`); and the free-field capstone `qiqt_bekenstein_gives_gr`
  already exposes P4-MICRO's outputs (`area_floor`, `area_floor_saturates`) as its `hbound`/`hsat` slots, with the
  entanglement first law filling `hDnn`/`hD0` and `hFlux` (BW/Unruh) the one residual thermal input. M-4 proof path
  and M-10 wiring now fully scoped against exact theorem names. Next: **M-4** (von Neumann max-entropy bound).
- 2026-06-27 — **M-4 LANDED (the C1 fix).** `FQBoundMicro.lean`: `vonNeumannEntropy_le_log_card`
  (`[IsDensity ρ] → S_vN(ρ) ≤ log (card n)`, via `shannon_le_log_card` on the eigenvalue prob-vector +
  `shannon_eq_sum_negMulLog`) and `area_floor_vonNeumann` (`[MicrostatePostulate n areaTerm] → S_vN(ρ) ≤ areaTerm`).
  P4 is now stated for the genuine regional VON NEUMANN entropy, not the record-law Shannon entropy. Added
  `import QIQTH.QuantumRelativeEntropy`; green, `#print axioms` standard 3, budget 0, full `QIQTH` green; wired into
  `AxiomAudit.lean`. Next: **M-5** (split/rename `HolographicCapacityBound` `≤` vs `…Exact` `=`).
- 2026-06-27 — **M-5 LANDED (the C2 split).** `MicrostatePostulate` → `HolographicCapacityBound` (`log card ≤
  areaTerm`, the floor) + `HolographicCapacityExact` (`= areaTerm`, saturation), with `instCapacityBoundOfExact`
  (`=⟹≤`). Floor theorems (`area_floor_of_microstate`, `holographic_area_floor_micro`, `area_floor_vonNeumann`)
  migrated to the weaker `Bound` via `le_trans`; `area_floor_saturates` keeps `Exact`; `MicrostatePostulateArea`
  deleted (manifest form is now a corollary). No dangling refs; green, standard 3, budget 0, full `QIQTH` green;
  `AxiomAudit` prose synced. Next: **M-6** (C3 regional `Q_R` framing + type-III/code-cutoff caveat in the header).
- 2026-06-27 — **M-6 LANDED (the C3 framing).** Added the regional-`Q_R` + type-III/finite-type-I-code-cutoff
  caveat to the `FQBoundMicro.lean` module header and rewrote the `HolographicCapacityBound` docstring: capacity is
  `Q_R = log N_R` (distinguishable *regional* microstates / fixed-area sector / code subspace), an explicit type-I
  cutoff of the genuinely type-III₁ local algebra — granting finite-dim `R` is the holographic regularization, not
  bookkeeping. Doc-only; green. Next: **M-7** (`Fin n` non-vacuity witness firing the bound-form theorem).
- 2026-06-27 — **M-7 LANDED (non-vacuity witness).** `finCapacityExact n : HolographicCapacityExact (Fin n)
  (Real.log n)` (`@[reducible] def`, not a global instance) + two `example`s firing `area_floor_of_microstate` and
  `area_floor_saturates` on it — the interface is inhabited, the bounds non-vacuous (fixed a `↑n+1` vs `↑(n+1)` cast
  mismatch by stating saturation over a generic `m` with `[Nonempty (Fin m)]`). Green, standard 3, budget 0, full
  `QIQTH` green. Next: **M-8** (bridge remark to `FQBoundCGP.holographic_area_floor` — Route 1 vs Route 2).
- 2026-06-27 — **M-8 LANDED (the Route-1/Route-2 bridge).** `holographic_area_floor_micro_vonNeumann`:
  `[HolographicCapacityBound n (edgeArea/(4·ellP²))] → S_vN(ρ) ≤ edgeArea/(4·ellP²)` — same conclusion as Route 1's
  `FQBoundCGP.holographic_area_floor`, conditional on finite capacity rather than `Phase5Master` (the dual-weight
  trace). + a doc "Bridge" section making the two endpoints explicit (kinematic capacity⇒bound vs dynamical
  modular-trace derivation; complementary, same carried UV datum). Green, standard 3, budget 0, wired into
  `AxiomAudit.lean`. Next: **M-9** (doc-only paper hook, the §3.1/§3.2 framing).
- 2026-06-27 — **M-9 LANDED (paper hook, doc-only).** Added the P4-MICRO drop-in paragraph + honest-framing rules
  to `paper_strategy/44_Formalization_Scope_Note.md`, and updated its formalization table: the FQ capacity *axiom*
  stays a postulate (now a typeclass hypothesis, not a Lean axiom), while `S_vN(ρ_R) ≤ Q_R = A/4ℓ_P²` GIVEN FQ is
  now **machine-checked** (`area_floor_vonNeumann`). Includes the "P4-MICRO ⟹ GR is false alone" caveat. Next:
  **M-10** (the GR bridge `gr_from_p4micro` against `QiqtToGR.qiqt_bekenstein_gives_gr` — the headline increment).
- 2026-06-27 — **M-10 LANDED — ALL 10 BRICKS COMPLETE.** New file `QIQTH/GRFromMicro.lean`:
  `hbound_hsat_of_capacity_family` proves a smooth finite-capacity family (microstate type `R x v t` per horizon
  patch, record law `p`, `Shannon = S`, `log N = η·A`) yields exactly the Jacobson capstone's two entropy slots
  `hbound`/`hsat` (via `area_floor_of_microstate` + `area_floor_saturates`); `gr_from_p4micro` plugs them into
  `qiqt_bekenstein_gives_gr`, concluding `∃ Λ, a·T = G + Λ·g` with the HONEST residual `hDnn,hD0` (Klein first law),
  `hFlux` (BW/Unruh — the irreducibly modular thermal input, GR-T1, not from counting), `hFocus,hreg,conserv` +
  structural. Fixed a duplicate-`Fintype`-instance defeq error (dropped the `haveI := hfin` and let the
  instance-binder resolve consistently). Green, both standard 3, budget 0, full `QIQTH` green; wired into
  `QIQTH.lean` + `AxiomAudit.lean`. **The P4-MICRO checklist (M-1…M-10) is complete.** Remaining beyond this plan =
  the Gap-2 localization + general (non-free-field) thermal side = Route 1 (Type II), the labelled open frontier.
- 2026-06-27 — **M-11 LANDED (bonus — von Neumann non-vacuity witness).** `oneDensity_isDensity : IsDensity (1 :
  Matrix (Fin 1) (Fin 1) ℂ)` (one-microstate pure state via `Matrix.PosSemidef.one` + `Matrix.trace_one`) + an
  `example` firing `area_floor_vonNeumann` on it (`S_vN = 0 ≤ log 1`) — completes M-7's Shannon-only witness with the
  honest von Neumann side. (A first attempt with the maximally-mixed `I/d` was reverted — ℂ-order/PosSemidef
  plumbing; the `Fin 1` identity is the clean route. Needed `open scoped ComplexOrder` since ℂ's order is scoped.)
  Green, standard 3, budget 0, full `QIQTH` green; wired into `AxiomAudit.lean`. The checklist + bonus are now done;
  the genuine open frontier is Route 1 / Gap-2 (a separate plan).

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
