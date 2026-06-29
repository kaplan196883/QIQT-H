# Emergent spacetime — Track C: entanglement → geometry, the AdS/CFT-borrowed finite core

> From the GPT-5.5-pro audits (2026-06-30): borrow AdS/CFT's **finite information-theoretic +
> inverse-problem** machinery, NOT its AdS boundary dictionary. Extends Track B
> (`QIQTH/EmergentSpacetime.lean`; [[qiqth_emergent_spacetime_scope]]). Most-tractable-first,
> axiom-free, each increment a self-contained green checkpoint.

---

## §0 — Honest invariants (enforced in EVERY increment)

- **min-cut / RT-AREA is never a distance** (`minCut_area_not_metric`). Reconstruct *distance* only by a
  provably-metric rule (L¹/Crofton, shortest-path); area stays the `cut`/entropy primitive.
- **A *directed* causal order needs a SUPPLIED orientation** — a unitary runtime is reversible; never claim
  to derive the time arrow.
- These are **finite proto-spacetime objects with explicit error tags**, NOT a background-independent 4D
  Lorentzian manifold (open physics, cited frontier). The "this is THE physical metric/causal structure"
  identification stays a **tagged physics claim**.
- **Weights/probes for any reconstructed metric must come from SUPPLIED entanglement/cut data** — else
  circular. The honest statement is conditional: *given the cut/entanglement data, a genuine metric is
  reconstructed.*
- Capacity is a **constraint, not a generator**.
- Discipline: no `sorry`; `#print axioms` = standard 3; `bash scripts/axiom_budget_check.sh` budget 0; wire
  into `QIQTH.lean` + `AxiomAudit.lean`; ONE green commit per increment with the `Co-Authored-By: Claude
  Opus 4.8 <noreply@anthropic.com>` trailer; push via schannel; update §3 log; checkpoint frontiers honestly.

Module: extend `lean/mathlib/QIQTH/EmergentSpacetime.lean`. A small shared predicate:
`structure IsFiniteMetric (d) : Prop := (toApprox : IsApproxPseudometric 0 d) (eq_of_dist_eq_zero : d x y = 0 → x = y)`.

---

## §1 — Increments (recommended build order; most-tractable-first)

- **C1 — the weighted cut / L¹-Crofton metric (BUILD FIRST; days).** `weightedCutDist (ω)(χ) x y = ∑ᵢ ω i ·
  |χ i x − χ i y|` (ω ≥ 0 weights, χ separating-cut/probe indicators). Prove `weightedCutDist_isPseudometric`
  (nonneg/self/symm/triangle — termwise `|a−c| ≤ |a−b|+|b−c|` ×ω, summed); `weightedCutDist_eq_zero_iff`
  (vanishes ⟺ all positive-weight probes agree); `weightedCutDist_isFiniteMetric_iff` (a genuine metric ⟺
  the probe family separates points, `WeightedProbesSeparate`); and `weightedCutDist_singleton_eq_embedDist`
  (recovers the B1 `embedDist`). **The honest entanglement → distance**: repairs `minCut_area_not_metric`,
  extends `embedDist_isPseudometric`. Rides `Finset.sum_nonneg/sum_le_sum`, `abs_sub_comm`, `abs_add`,
  `Finset.sum_eq_zero_iff_of_nonneg`.
- **C4 — CMI ≥ 0 / Markov-screening locality (day).** `cmi (S) A B C = S(A∪B)+S(B∪C)−S(B)−S(A∪B∪C)`;
  `cmi_nonneg_of_SSA` (from `StrongSubadditive S` as a hypothesis + `(A∪B)∩(B∪C)=B` for `Disjoint A C`);
  `MarkovLocality`/`GraphSeparatedBy` (graph-separation via `Reach (AvoidingRel sig B)`) ⇒
  `markov_screening_of_locality`. **Locality/connectivity from conditional independence** — proto-structure,
  not geometry; SSA is a supplied hypothesis (no quantum-SSA axiom).
- **C3 — flow weak duality `flowValue ≤ cutCapacity` (days).** `vertexExcess`, `flowValue f s`, `IsSTFlow`,
  `netAcross`/`outAcross`; `sum_vertexExcess_eq_netAcross` (internal C×C terms cancel by `Finset.sum_comm`) ⇒
  `flow_weak_duality` (`flowValue f s ≤ cutCapacity cap C` for `s∈C, t∉C`). The **easy half** of
  max-flow/min-cut; full duality = research-grade checkpoint. Extends `cut`.
- **C7 — abstract finite first-law inequality (<day).** `relEntFromModular S Kexp ρ σ = Δ⟨K⟩ − ΔS`;
  `deltaEntropy_le_deltaModular_of_relEnt_nonneg` (`0 ≤ relEnt ⇒ ΔS ≤ Δ⟨K⟩`, `linarith`). Reuses D6 modular
  machinery if concrete relEnt available; abstract version is pure algebra. Modular/thermodynamic, not geometry.
- **C5 — approximate modular no-go (generic: day; HS-matrix: week+).** Generic normed:
  `approx_scaling_gap_mul_norm_le` (`T : E →ₗᵢ E`, `‖T A − q•A‖ ≤ ε ⇒ |‖q‖−1|·‖A‖ ≤ ε` via
  `abs_norm_sub_norm_le`, `LinearIsometry.norm_map`, `norm_smul`) + `norm_le_div_of_approx_scaling_gap`. HS
  matrix instantiation (vectorize into `EuclideanSpace ℂ (n×n)`) later. Strengthens
  `finiteDim_scaling_forces_zero`: *approximate* nonunit-modulus scaling forces *small* norm.
- **C6 — Alexandrov intervals + longest-chain + capacity-volume (intervals/volume days; reverse-triangle
  week+).** `StrictReach`, `AlexandrovInterval sig x y = future(x) ∩ past(y)` (`mem_AlexandrovInterval`),
  `CausalChain`/`longestChainLen` (bounded by `card V`), `capacityVolume cap S = ∑_{v∈S} cap v` (nonneg,
  monotone). The **Lorentzian Tier-3 route** on the existing causal preorder — *supplied orientation* `sig`;
  `capacityVolume` is a volume *proxy/constraint*, not a generator. Optional research-grade
  `longestChainLen_reverse_triangle`.
- **C2 — finite shortest-path graph metric (week+; Mathlib gap).** `FinGraphLength`, `SimpleWalk` (finite,
  bounded by `card V`), `shortestPathDist = (simpleWalkCosts).min'`; pseudometric via reversal (symm) +
  append-and-loop-erase (triangle: `exists_simpleWalk_le_appendCost`), `IsFiniteMetric` under positive edge
  lengths. **Separates distance from cut-area.** Bespoke loop-erasure lemma — Mathlib has no shortest-path
  metric. Edge lengths must be supplied noncircularly (e.g. from C1).
- **C8 — reconstruction certificate `networkData ↦ ApproxMetric` (day, after C1/C2).** `ApproxMetric X`
  bundle with `source`/`status` provenance tags; `CroftonData.toApproxMetric`, `GraphMetricData.toApproxMetric`;
  `NetworkGraphData` with the **noncircularity guard** `length_from_crofton` (graph lengths tied to supplied
  C1 probes). Honest packaging, not new math.

**Start with C1 · C4 · C3.** Geometry-first alternative: C1 → C6(intervals) → C2.

**Cited frontiers (do NOT grind):** full max-flow/min-cut duality; the smooth 4D Lorentzian manifold
(background-independent); continuum Type-III modular; concrete quantum relative-entropy positivity;
manifold-learning convergence (finite metric → smooth metric). All AdS-unsolvable too.

---

## §2 — Build/commit protocol
Per increment: `cd lean/mathlib && ~/.elan/bin/lake build QIQTH.EmergentSpacetime` green; `#print axioms` =
standard 3; `bash scripts/axiom_budget_check.sh` budget 0; wire into `QIQTH.lean` (already) + `AxiomAudit.lean`;
ONE commit on `main` (Co-Authored-By trailer); push via schannel; update §3; report.

## §3 — Progress log
- 2026-06-30 — Plan written from the AdS/CFT-borrowings consult. Order: C1 → C4 → C3 → C7 → C5 → C6 → C2 → C8.
  Loop: job 94ed5364, every 10 min.
- 2026-06-30 — **C1 DONE** (axiom-free standard-3, budget 0, full QIQTH green 8876 jobs). `EmergentSpacetime.lean`
  (`section CroftonMetric`): the honest **entanglement → distance**. `IsFiniteMetric` (a `0`-pseudometric that
  separates points); **`weightedCutDist ω χ x y = ∑ᵢ ωᵢ·|χᵢ x − χᵢ y|`** (the cut-cone / L¹-Crofton rule);
  `weightedCutDist_isPseudometric` (nonneg/self/symm/triangle for ω≥0); `weightedCutDist_eq_zero_iff` (vanishes
  ⟺ all positive-weight probes agree); capstone **`weightedCutDist_isFiniteMetric_iff`** (a genuine finite
  *metric* ⟺ the probe family **separates points**, `WeightedProbesSeparate`); and
  `weightedCutDist_singleton_eq_embedDist` (recovers B1's `embedDist`). **Repairs `minCut_area_not_metric`**:
  min-cut area is never a distance, but a separating family of weighted cut/entanglement probes reconstructs a
  provable metric. Honest: weights/probes from SUPPLIED entanglement data (else circular); a finite
  proto-distance, NOT the physical metric. Wired into `AxiomAudit.lean`. _Next: C4 (CMI≥0 + Markov screening)._
- 2026-06-30 — **C4 DONE** (axiom-free standard-3, budget 0, full QIQTH green 8876 jobs). `EmergentSpacetime.lean`
  (`section MarkovLocality`): locality/connectivity from conditional independence. `StrongSubadditive S`
  (submodularity, a *hypothesis* — no quantum-SSA axiom); `cmi S A B C = S(A∪B)+S(B∪C)−S(B)−S(A∪B∪C)`;
  **`cmi_nonneg_of_SSA`** — `I(A:C|B) ≥ 0` for disjoint `A,C` (via `union_inter_union_eq_middle_of_disjoint`:
  `(A∪B)∩(B∪C)=B`); `AvoidingRel`/`GraphSeparatedBy` (separation by chains avoiding `B`, riding
  `Relation.ReflTransGen`); `IsMarkovScreen`/`MarkovLocality`; capstone **`markov_screening_of_locality`** — a
  graph-separating `B` screens `A` from `C` (`0 ≤ I(A:C|B) ≤ δ`), i.e. a separator in the *supplied* signalling
  graph is an approximate Markov blanket. Honest: reconstructs proto-structure (locality/patch-gluing), NOT a
  metric or manifold; `sig` and SSA are supplied. Wired into `AxiomAudit.lean`. _Next: C3 (flow weak duality)._
- 2026-06-30 — **C3 DONE** (axiom-free standard-3, budget 0, full QIQTH green 8876 jobs). `EmergentSpacetime.lean`
  (`section Flow`): the easy half of max-flow/min-cut, extending the B2 `cut`. `cutCapacity = cut`,
  `outAcross`/`inAcross`/`netAcross`, `vertexExcess`, `flowValue`, `IsSTFlow` (nonneg + capacity + conservation);
  **`sum_vertexExcess_eq_netAcross`** (∑_{u∈C} excess = net flow across ∂C — internal flow cancels by
  `Finset.sum_comm`); `flowValue_eq_netAcross_of_isSTFlow` (conservation kills interior vertices); capstone
  **`flow_weak_duality`** — `flowValue f s ≤ cutCapacity cap C` for `s∈C, t∉C` (net ≤ out ≤ cut capacity). Honest:
  the **inequality only**; full max-flow=min-cut duality is the cited research-grade frontier (no Mathlib
  max-flow). Wired into `AxiomAudit.lean`. _Next: C7 (abstract finite first-law ΔS ≤ Δ⟨K⟩)._
- 2026-06-30 — **C7 DONE** (axiom-free standard-3, budget 0, full QIQTH green 8876 jobs). `EmergentSpacetime.lean`
  (`section FirstLaw`): the finite entanglement first law. `delta F ρ σ = F ρ − F σ`; `relEntFromModular S Kexp
  ρ σ = Δ⟨K⟩ − ΔS`; **`deltaEntropy_le_deltaModular_of_relEnt_nonneg`** — `D(ρ‖σ) ≥ 0 ⟹ ΔS ≤ Δ⟨K⟩` (entropy
  change bounded by modular energy; positivity of `D` is the *supplied* input, Klein /
  `QuantumEntropy.relEntropy_nonneg`); and **`deltaEntropy_le_eta_deltaArea`** — with `K ∝ area` (`Kexp =
  η·Area`), `D ≥ 0 ⟹ ΔS ≤ η·ΔA`, the entropy–area variation underlying Jacobson. A finite thermodynamic
  inequality, conditional on `D ≥ 0` + the area identification; NOT a geometry reconstruction. Wired into
  `AxiomAudit.lean`. _Next: C5 (approximate modular no-go, generic normed)._
