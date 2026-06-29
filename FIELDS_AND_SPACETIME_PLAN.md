# Quantum fields (free SM content) + emergent spacetime — axiom-free Lean, two parallel tracks

> Built on the completed corner construction (`QIQTH/CornerConstruction.lean`, D1–D8;
> [[qiqth_microstate_deepening_complete]]) and the GPT-5.5-pro scope audits for the Standard Model and
> emergent spacetime ([[qiqth_emergent_spacetime_scope]]). **Track A** = represent the SM's *free-field
> content* in the capacity-bounded corner; **Track B** = reconstruct *finite proto-spacetime* (metric /
> RT / causal order) from the same finite substrate. Run by two staggered /loop crons.

---

## §0 — Honest scope (the rails; identical for both tracks)

The decisive principle: **QIQT-H sits on top of QFT — it *accepts* a field theory as input and tells you
about its records / Born weights / capacity / emergent gravity; it does NOT *construct* QFT, and capacity
never *generates* a field.**

- **Capacity is a CONSTRAINT, not a generator.** Never claim to "derive" the electron/photon/any field,
  the value of `G`, or the `1/4` ratio.
- **Track A is FREE-FIELD content only.** Interacting QFT, non-abelian gauge dynamics, the Yang–Mills mass
  gap, confinement/hadron spectrum, chirality + dynamical SSB are **cited frontiers** (open mathematics),
  NOT in scope. We represent the *free* quark/lepton/W/Z/gluon/Higgs field algebras, nothing more.
- **Track B is finite PROTO-spacetime only.** A background-independent 4D Lorentzian manifold, the
  interacting continuum limit, the value of `G` are **cited frontiers** (open physics). We build finite
  reconstructed metric/causal objects with explicit error bounds; the "this *is* spacetime" identification
  stays a tagged physics claim.
- **min-cut is AREA, not a metric** (the corrected roadmap fact, [[qiqth_emergent_spacetime_scope]]): use
  it only as the area/entropy primitive; reconstruct *distance* by a provably-metric rule.
- **Tier-1 (Jacobson / BW / Sakharov / `δS=ηδA`) ASSUMES geometry** and may NOT be cited as emergence
  evidence (the binding non-circularity rule).
- **THE AUDIT TRIPWIRE (both tracks):** everything transported by `A ↦ V A Vᴴ` lands in the corner
  `P·End(𝓗_R)·P`, `P=VVᴴ` — never the ambient `1_𝓗` unless `P=1`.
- **Discipline:** no `sorry`; every theorem `#print axioms` = standard 3; `bash scripts/axiom_budget_check.sh`
  budget 0; wire into `QIQTH.lean` + `AxiomAudit.lean`; ONE green commit per increment with the
  `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>` trailer; push via schannel; update §3 progress
  log; ship green, checkpoint frontiers honestly.

---

## §1 — TRACK A: the unified free-field corner (quantum fields / free SM content)

New module **`lean/mathlib/QIQTH/FreeFieldCorner.lean`** (imports `QIQTH.CornerConstruction`).

- **A1 — the abstract finite field-code interface.** A typeclass `FiniteFieldCode` over a finite code
  space packaging the data the corner transport needs (the field algebra's generators + their finite
  relations), with **CAR** (`encoded_anticomm`) and **truncated-CCR** (`encoded_truncated_ladder_commutator`)
  as the two canonical instances. Re-state D4/D5's corner transport generically over the interface. *(The
  one consolidation move; days.)*
- **A2 — fermion content (quarks + leptons).** Instantiate the CAR corner for `n`-mode fermionic Fock with
  arbitrary flavor/generation multiplicity; `fermion_modes_le_area` generalized to the multi-flavor mode
  count. *(Instances of A1 + existing CAR.)*
- **A3 — massive vector bosons (W, Z) and gluons.** Instantiate the truncated-bosonic corner for vector
  fields (per-mode truncated ladder); the truncation defect (`encoded_truncated_ladder_commutator`) carries
  through, honestly. *(Instances; the boson is necessarily truncated.)*
- **A4 — the Higgs scalar.** The simplest truncated-bosonic instance.
- **A5 — capstone: the free SM field content in the corner.** One theorem bundling A2–A4: every free SM
  field type, encoded into the capacity-bounded corner, has Born-weighted, area-bounded records with its
  (CAR / truncated-CCR) algebra faithfully transported. Honest statement of *free-field-content* coverage.
- **Cited frontier (checkpoint, do NOT grind):** interactions, gauge invariance beyond free BRST,
  chirality, SSB, confinement — open mathematics; the SM's *essence*, out of scope.

---

## §2 — TRACK B: emergent-spacetime finite cores

New module **`lean/mathlib/QIQTH/EmergentSpacetime.lean`**.

- **B0 — finite exact-continuum no-go guards (Rank 0; pure de-risking).** `finiteDim_scaling_forces_zero`:
  if `U` is unitary and `U P Uᴴ = r • P` with `|r| ≠ 1`, then `P = 0` (Hilbert–Schmidt / Frobenius norm:
  unitary conjugation is isometric, but `r•` rescales). Corollaries: **no exact finite Borchers dilation**,
  **no exact finite CCR** (recovering `no_finiteDim_CCR` in scaling form), **no exact finite boost scaling**.
  Forces Tier-2 to be *approximate*; prevents overclaiming. *(Days.)*
- **B1 — the corrected finite metric core (Rank 1).** `minCut_not_metric` (the triangle-inequality
  counterexample `c(x,y)=c(y,z)=1, c(x,z)=4 ⟹ λ(x,z)=5 > 4`, as a theorem); an `ApproxMetric ε` predicate;
  and a **metric-valid** reconstruction proven to satisfy the metric axioms — start with the
  **variation-of-information** metric `VI(X,Y)=H(X|Y)+H(Y|X)` on finite record partitions (genuine
  info→metric, rides the existing Shannon machinery) and/or a finite **shortest-path** graph metric.
- **B2 — finite graph RT / capacity entropy skeleton (Rank 2).** A finite weighted graph with boundary
  vertices; `cutCapacity` / `boundaryEntropy`; prove purity `S(A)=S(Aᶜ)`, subadditivity, and (target)
  strong subadditivity; min-cut as the area/entropy bound (its *correct* role).
- **B3 — tensor-network cut bound, wired to the corner (Rank 3).** `entropy_le_log_dim_of_factor_through_cut`:
  if a state factors through a cut space of dim `D`, then `S_vN(ρ_A) ≤ log D`; specialize to a min-cut bound;
  connect to the D1–D8 corner codes (the finite substrate already supplies the code/capacity blocks).
- **B4 — operational causal preorder (Rank 4).** `CanSignal → Relation.ReflTransGen → partial order →
  future/past cones`; no-signalling-outside-cone for finite local dynamics. **Honest note:** a directed
  causal order needs a *supplied* time-slicing / channel orientation — a unitary runtime alone is
  reversible; this derives a finite operational order, NOT Lorentzian light-cones from nothing.
- **Cited frontier (checkpoint, do NOT grind):** Borchers / half-sided modular inclusion (translation from
  modular data) — exact-finite is dead by B0, so continuum research-grade; background-independent 4D
  manifold — open physics. Connes–Rovelli thermal time — interpretive, low yield.

---

## §3 — Build/commit protocol & progress log

Per increment: `cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green; `#print axioms` = standard 3;
`bash scripts/axiom_budget_check.sh` budget 0; wire into `QIQTH.lean` + `AxiomAudit.lean`; ONE commit on `main`
(Co-Authored-By trailer); push via schannel; update this log; report.

### Progress log
- 2026-06-29 — Plan written from the SM + emergent-spacetime scope audits. Two staggered /loop crons:
  Track A (`FreeFieldCorner.lean`, A1→A5, job 74417971 @ :00,:10,…) and Track B (`EmergentSpacetime.lean`,
  B0→B4, job 49fea657 @ :05,:15,…).
- 2026-06-29 — **B0 DONE** (axiom-free standard-3, budget 0, full QIQTH green 8875 jobs). New module
  `QIQTH/EmergentSpacetime.lean` (`section NoGo`): **`finiteDim_scaling_forces_zero`** — on a finite-dim
  space, a unitary conjugation cannot rescale a nonzero operator: `U` isometry (`Uᴴ U = 1`), `U P Uᴴ = r•P`
  with `star r · r ≠ 1` (`|r| ≠ 1`) ⟹ `P = 0` (the Hilbert–Schmidt/Frobenius norm `Tr(Pᴴ P)` is
  conjugation-invariant but `r•` rescales it by `|r|²`; via `Matrix.trace_conjTranspose_mul_self_eq_zero_iff`
  under `open scoped ComplexOrder`). Corollary **`scaling_of_nonzero_forces_unit_modulus`** (`P ≠ 0` ⟹
  `|r| = 1`). So there is **no exact finite Borchers dilation / Weyl / boost scaling** — Tier-2 emergence must
  be *approximate / scaling-limit*, the honest constraint, not a defect. (Import note: `RCLike ℂ` lives in
  `Mathlib.Analysis.Complex.Basic`, needed for the `ComplexOrder` scoped order instances.) Wired into
  `QIQTH.lean` + `AxiomAudit.lean`. _Track B next: B1 (`minCut_not_metric` + `ApproxMetric` reconstruction)._
- 2026-06-29 — **A1 DONE** (axiom-free standard-3, budget 0, full QIQTH green 8876 jobs). New module
  `QIQTH/FreeFieldCorner.lean` (`section GradedBracket`): the **unified corner transport** for free SM
  field content. `gradedBracket ε x y = x y + ε•(y x)` (ε=1 anticommutator/CAR fermions, ε=-1
  commutator/CCR bosons); **`encode_gradedBracket`** — `[ι_V(x),ι_V(y)]_ε = ι_V([x,y]_ε)`, the *single*
  transport theorem unifying the electron (D4, ε=1) and photon (D5, ε=-1); **`encoded_bracket_of_eq`** —
  any code relation `[x,y]_ε = M` transports to `[ι_V(x),ι_V(y)]_ε = ι_V(M)` (in the corner, never the
  ambient `1_𝓗`); **`encoded_CAR_bracket`** — the ε=1 instance recovers D4 (`{x,y}=c•1 ⟹ {ι(x),ι(y)}=c•P`).
  So every free SM field's defining algebra is an *instance* of one transport. Honest: transport of a
  SUPPLIED free-field algebra, NOT its construction; interactions/gauge/confinement/chirality/SSB are cited
  frontiers. Wired into `QIQTH.lean` + `AxiomAudit.lean`. _Track A next: A2 (quark/lepton multi-flavor CAR
  instances)._
- 2026-06-29 — **B1 DONE** (axiom-free standard-3, budget 0, full QIQTH green 8876 jobs).
  `EmergentSpacetime.lean` (`section Metric`): the corrected metric core. `IsApproxPseudometric ε d`
  (nonneg/self/symm/triangle-up-to-ε — the target type for any emergent-distance reconstruction);
  **`minCut_area_not_metric`** — a nonneg/symmetric/zero-diagonal area/cut function (RT/min-cut shape) that
  *violates the triangle inequality* (witness `λ(0,1)=λ(1,2)=2`, `λ(0,2)=5 > 4`): **min-cut area cannot be
  the emergent distance** (the corrected Tier-3 §3.1 guard, now a theorem); **`embedDist_isPseudometric`** —
  the metric-VALID replacement, the `L¹`/coordinate-embedding `|f x − f y|` is an exact pseudometric
  (`IsApproxPseudometric 0`), the honest first Tier-3 distance reconstruction; min-cut keeps its correct
  role as the area/entropy primitive. _Track B next: B2 (finite graph RT/capacity entropy skeleton)._
