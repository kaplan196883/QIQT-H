# QIQT-H — the abstract (canonical)

**Status:** canonical abstract rising from the current development; every sentence checkable against
`LEAN_RESULTS_INVENTORY.md` (ground truth) and the five-postulate structure P1–P5 as stated in the
foundations paper (`build/QIQT_Foundations_Paper.tex`) and on the website. All public copy
(paper, website) should align with this text and the guardrails below.

---

## Abstract

Quantum mechanics carries a collapse postulate it cannot justify, and general relativity resists
quantization. We develop **QIQT-H**, a single-world, holographic formulation of quantum theory
whose ontology is **Φ-monism**: there is one substance — the universal wave function Φ, evolving
exactly unitarily — of which observers are macroscopic patterns; a non-dynamical selector λ marks
exactly one decoherent record actual per run. No collapse term, no branching, no fundamental
probability. The theory rests on five postulates — **(P1)** the (Φ,λ) ontology, **(P2)** quantum
kinematics, **(P3)** microcausality, **(P4)** finite holographic capacity: the information content
of any bounded spacetime region is finite, and **(P5)** quantum equilibrium of the typicality
measure — of which P2–P3 are the standard quantum-relativistic arena, so the irreducible new
physics is **P4 + P5, on the P1 ontology**. We machine-verify the entire development in
Lean 4 / Mathlib: over **5,000 theorems across ~515 files**, zero axioms beyond Lean's standard
three, every physical input an explicitly named hypothesis.

The measurement problem dissolves without collapse: decoherence supplies the record structure,
λ (P1) makes exactly one history actual, and the Born rule is **reduced** — provably underivable
from unitarity alone, by a battery of machine-checked no-go theorems — to P5 alone (both earlier
Born premises collapse to refinement-equivariance). The selection layer is Poincaré-covariant, with
a proved obstruction (a covariant *measure* exists; a covariant *selector* cannot) and an axiom-free
boost-invariant typicality measure on the continuum 1+1D free field.

Gravity emerges holographically, in the pattern of AdS/CFT but with no string theory — and it is Φ,
never the actualized branch, that carries the holographic entropy that geometry responds to. Given
P4, the area **floor** S_vN ≤ Q_R **is a derived theorem, not an added postulate** (the holographic
*area form* of Q_R enters via the conditional induced-gravity bridge, not from finiteness alone);
capacity-bounded record corners of an explicitly constructed crossed-product core satisfy
**S = A/4G as a theorem** for the core's own trace-defined area — the calibration is derived, not
imposed; truncated free-field mode algebras *are* literally such corners; the linearized graviton
(exactly two helicity-±2 polarizations, canonically quantized, propagating at c) carries a
quantized area operator whose expectation the record count computes; the entanglement first law at
every probe is **equivalent** to the linearized Einstein equations; Newton's constant is delivered
as the relation **G = 1/(N Λ_s²)**, the Sakharov ¼ is a theorem, and Strominger's BTZ boundary
state count equals the bulk capacity exponent at the shared granularity — the two holographic
bookkeepings agree, and a saturated, conditional cross-check computes both the entropy and G from
one microscopic system.

Every derivation is conditional on named, shrinking inputs (the Clausius/area law and the
Iyer–Wald/first-law-deficit identification where not yet discharged, the matching of the
trace-defined area to external geometry, the numerical value of G, the continuum Type III₁ limit,
interacting matter). We claim
a fully machine-verified derivation chain from finite information toward quantum gravity and
single-outcome quantum mechanics — every remaining gap named, checkable, and independently
auditable — not a completed theory.

---

## The five postulates (as in the paper/website — the abstract must track these)

- **(P1) The (Φ,λ) ontology.** The universal wave function Φ is the complete ontology (no external
  observer, no fundamental probability); a non-dynamical selector λ makes exactly one decoherent
  record actual per run — no collapse term, no branching.
- **(P2) Quantum kinematics.** The complex-Hilbert-space / operator-algebraic arena; the Born
  squared modulus is this arena's inner-product geometry, not a separate postulate.
- **(P3) Microcausality.** Spacelike-separated regional algebras commute (the Lorentz-covariance
  input; provably NOT the source of the Born premises).
- **(P4) Finite holographic capacity.** The regional capacity is finite (P4-MICRO: finiteness is
  the postulate; the area *floor* S_vN ≤ Q_R is then a derived theorem, and the holographic *area
  form* of Q_R comes via the conditional induced-gravity bridge — NOT from finiteness alone).
- **(P5) Quantum equilibrium.** λ's typicality measure is refinement-equivariant (DGZ/Valentini);
  both Born premises reduce to P5 alone, and P5 is provably not reducible to P3.

**Division of labor:** P2–P3 = the standard arena · the irreducible physics = **P4 + P5** · the
ontology doing the interpretive work = **P1**.

---

## Alignment guardrails (binding for all public copy)

1. **"Solves the measurement problem" → "dissolves it without a collapse postulate."** Single
   outcomes are the work of **λ (P1) + decoherence**, never of capacity (H2/Macroscopic-Definiteness
   retired as a category error; `capacity_exactly_one` is sound but definitionally loaded —
   inventory §6e).

2. **Postulate accounting: five postulates, two irreducible.** The certified sentence is the
   paper's own: *"the genuinely irreducible physics reduces to (P4) + (P5), on the (P1) ontology,
   with (P2)–(P3) the standard quantum-relativistic arena."* Never say "one postulate" bare; the
   `NoBornFromNothing` battery proves P4 alone cannot give Born.

3. **"Gives quantum gravity" → "a machine-verified conditional chain toward it."** Every campaign
   checkpoint states "NOT QG solved; no wall crossed." Claim loudly what is certified: linearized
   Einstein ⟺ entanglement first law from real parts; S = A/4G a theorem in the constructed core;
   the quantized graviton with its area operator; the honest walls named.

4. **P4 has two provably different layers** — a record **count** bound in the finite model, an
   **entropy** bound in the continuum (`EntropyNotCardinality` proves them inequivalent). "Finite
   information" must never read as a finite matter Hilbert space (D2/D3). And the ontological
   reading is binding: **Q_R is an entanglement entropy of the pre-selection Φ** (the effective
   modular rank e^{S(ρ_R)}), so **geometry responds to Φ, never to the actualized branch** — λ's
   inertness is *required* for P4's consistency, not merely interpretive.

5. **The AdS/CFT contact is a *correspondence*, not an import.** `btz_cardy_eq_join_count`: the two
   bookkeepings agree at shared granularity. Never phrase as deriving/using Maldacena. What AdS/CFT
   still has and QIQT-H lacks is the fully independent cross-check; DY6's saturated cross-check is
   the honest first step and should be named as such.

6. **Φ-monism is the settled ontology thesis** and should be stated as such: no external observer,
   no fundamental probability or choice; we are macroscopic realizations of Φ (constitution = Φ,
   actuality-selection = λ). The weights |c_k|² are across-run record frequencies, not per-run
   chances.

**Differentiator to keep in every version:** the `verify/` capsule — a skeptic's own laptop
re-checks the whole chain (`bash verify/verify.sh` → claim card). No competing foundations program
ships this.

---

## Count note (authoritative, 2026-07-10)

The current-HEAD raw counts are **5,632 theorem/lemma declarations, 515 `.lean` files, ~3,400
`#print axioms` directives** (grep over `lean/mathlib/QIQTH/`, recount 2026-07-10). The inventory's
§0 meta-counts **lag the loop** and should be refreshed. When aligning public copy, the theorem/file
counts are authoritative from the grep above — NOT from the inventory snapshot. The website landing
now reads "over 5,000 / **41** world-firsts" (the 40th first = the machine-checked
Gromov–Hausdorff limits of graph geodesics to *curved* metric spaces — the cone with
curvature-as-a-theorem and the smooth sphere — and the same family decoded from the abstract state;
`sphereGrid_toGHSpace_tendsto_sphere`, `polarGrid_toGHSpace_tendsto_cone`, `cone_no_isometric_embedding_into_inner`;
the 41st = Williamson's symplectic normal form unconditional, `youla_pairing`, a Mathlib-first);
"over 5,000 theorems across ~515 files" is the current phrasing. New this recount (2026-07-10): the
"space from the state" emergent-geometry program (§6 of the inventory) — GH limits to interval / cube
∀d / flat torus / circle / tripod / cone / sphere, decoded from Bell cut-rank profiles, plus the
Hawking–Euclidean layer `cone_flat_iff` (flat ⟺ θ=2π) and `hawking_two_pi_coincidence`; and the
**Lorentzian ladder** (real time) — proper time via the *reverse* triangle inequality for flat Minkowski
(`tau_reverse_triangle`), the causal no-go (`causal_no_go`, why causal-set theory needs random sprinkling),
the continuous proper-time pinch (`causal_stencil_pinch`), and curved 2D de Sitter (`tauDS_reverse_triangle`
— to our knowledge the first machine-checked curved-spacetime reverse triangle inequality — with de Sitter
horizons `dS_causal_horizon`). **Binding scope:** dimension d, angle θ, topology, isotropy and the causal
order are all INSERTED (not emergent); states are CONSTRUCTED; curvature = the midpoint/embedding
obstruction, not a Riemann tensor; Hawking κβ/temperature identifications are CITED. NOT emergent
dimension/spacetime, NOT GR, NOT QG.

## Modular-tower update (2026-07-05) — Tomita–Takesaki COMPLETE

Since the prior "world-first #36" snapshot ("Δ^it + Tomita's theorem *first half*; J and the second
half are the *named next campaign*"), three campaigns landed (commits through `c0372aa`, all std-3
axiom-free) that make **the tower's Tomita–Takesaki modular theory COMPLETE** — the first complete
such in any proof assistant:
- **Modular conjugation (9/9):** `towerJ` a genuine involutive **anti-unitary** (J²=1, JΩ=Ω,
  ⟪Jξ,Jη⟫=⟪η,ξ⟫); the **polar decomposition on the core** S̄ = J∘Δ^{1/2}; JΔ^{it}=Δ^{it}J; and
  **Tomita's theorem second half in *inclusion* form** — `J·towerLimitVN·J ⊆ towerLimitVN′` with Ω
  separating for M′ (`TomitaSecondHalf.lean`).
- **Non-traciality (N1–N4):** the tower vacuum is a **genuine non-tracial KMS state** — ω not a
  trace, **Δ ≠ 1**, Δ^{it}=towerFlow ≠ id (the Powers "not-the-tracial-case" separation).
- **KMS-boundary capstone (C1):** `modular_data_complete_witness` bundles the full data (S̄, Δ,
  Δ†=Δ, Δ^{it}=flow, Tomita I, J, polar-on-core, Tomita II, non-traciality, KMS-boundary).
- **Tomita II in FULL — the RvD wall has fallen (D2a, 2026-07-11):** the commutation theorem
  **J M J = M′** (full equality, not just the ⊆ inclusion) is now proved — `tomita_commutation_equality`
  / `jconj_image_eq_commutant`, with Ω cyclic + separating for BOTH M and M′; the earlier "Kaplansky-gap"
  obstruction was an artifact, closed by a classical right-boundedness estimate. The tower now carries the
  **complete both-halves Tomita–Takesaki commutation theorem — the first in any proof assistant.**

**HAVE NOT (honest scope, binding for public copy):** no unbounded Δ^{1/2};
no strip-analyticity KMS; **NO type classification** ("not the tracial case" is *not* "not type II"
as an algebra statement; type III / S-invariant stays cited — Mathlib has no type API); finite-stage
Gibbs inductive-limit only. Website world-firsts list carries items for the modular conjugation and
the non-tracial KMS state accordingly (later additions — field-level BW and the emergent-geometry
GH-limit family — bring the current total to 40; see the count note below for the authoritative figure).

## Audit note (2026-07-05) — CLOSED

The claim "both earlier Born premises collapse to P5 alone" is now checkable against ground truth:
the P5-reduction chain (`equivariant_no_signaling`, `equivariant_context_independent`,
`apc_iff_positiveAdditive`, `mu_selection_martingale` + the two no-go guards, incl. **P5 ⊄ P3**
via `alphaSq_selector_signals`) was probed std-3 axiom-free and added to
`LEAN_RESULTS_INVENTORY.md` §1 (2026-07-05). The abstract is fully consistent with the inventory.
