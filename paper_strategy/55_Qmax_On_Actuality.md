# 55 — Q_max constrains ACTUALITY (λ), not the wavefunction (Φ) (2026-06-14)

**The reframing (Pawel).** The finite holographic capacity Q_max is NOT a constraint on the quantum state Φ
— we proved it can't be (a superposition of records is one vector sharing the same Hilbert dimension;
`RankCountNoGo`; "two records ≠ two capacities"). Instead Q_max constrains the **actuality** structure λ:
Φ evolves exactly unitarily and keeps all branches; λ assigns, per region, the set of ACTUAL (realized,
classical, definite) records; actual records are distinguishable/classical so their costs ADD; Q_max bounds
the total actual cost ⇒ at most one actual macro-record; λ supplies ≥1 ⇒ exactly one. Single outcome, no
collapse of Φ.

## Re-audit (Lean = ground truth): the reframing is what's already PROVEN

Read `CapacityModel.lean` and `CoreNoCollapse.lean` line by line:
- `CapacityModel`: every theorem counts members of an **orthonormal family** of distinguishable records and
  the dimensions they consume (`capacity_total ≤ finrank`, `macroscopic_subsingleton`, `capacity_exactly_one`).
  No superposition, no Φ, anywhere — purely the distinguishable-record (actuality) layer.
- `CoreNoCollapse`: `Coactual.active` = *"records simultaneously **actual**"*; cost **adds** over actual
  records; `Selection` = *"the actuality selector λ"*; `exactly_one_actual` is **Φ-independent** (ψ enters only
  the separate Born-weight `FinPVM` block); its docstring already says *"the state never collapses — purely the
  capacity bound + λ."*

**Verdict: "Q_max bounds actuality λ, not Φ" is literally what the machine-checked theorems prove.** The only
error was ever the *gloss* ("forbids multi-record states [in Φ]"). The additivity that is FALSE for quantum
superpositions is TRUE here, because these are actual, distinguishable records. Nothing to re-prove.

## Stress-test (pro, checked vs the Lean + standard physics): consistent, not fatally flawed

1. **No hidden collapse.** Φ stays `U(t)Φ(0)`; λ marks the actual record; unselected branches remain in Φ.
   Effective/epistemic collapse only (branch-relative state for prediction), like a Bohmian conditional
   wavefunction — not physical pruning.
2. **Additivity under entanglement.** Naive additivity is unsafe (entangled records are subadditive), BUT the
   robust theorem — monotone joint cost + **pairwise overflow** (two distinct rival actual macro-configs
   jointly exceed Q_max) ⇒ ≤1 — is sound (= our `joint_coactual_subsingleton`). Pairwise-overflow is the
   minimal physical input.
3. **No-signaling.** Consistent if λ's per-region marginals are Born (our `equivariant_marg_invariant`); λ must
   be contextual (Bell/CHSH guardrail, machine-checked) — inherits the usual Bell nonlocality burden, no
   operational signaling.
4. **Global consistency of λ — the genuine hard problem.** Per-region "exactly one" is clean; stitching
   per-region actualities into one globally-consistent, Lorentz-covariant λ over entangled/overlapping regions
   (the gluing / global-section / OP3b problem) is unsolved. No KS contradiction (λ assigns only actual
   decohered records in actual contexts, not noncontextual values for all observables); no Bell contradiction
   (no local factorizability demanded); Lorentz covariance is the sharpest pressure (preferred foliation
   easiest but not covariant; block/all-at-once λ clean but hard).

**Two reading-constraints the stress-test pins down (both consistent with the Lean):**
- **(A)** the capacity premise applies to **rival, mutually-exclusive complete macro-configurations of one
  region's DOF** — NOT arbitrary records (else "cost > Q_max/2" is empirically dead: compatible records
  coexist). Sharpens the file's `active_macroscopic_subsingleton`.
- **(B)** **recoherence:** unactual branches must remain able to influence future λ-statistics whenever
  standard QM restores interference, else collapse is smuggled in operationally (= the recoherence-stability
  open item).

## Net

**Q_max is load-bearing again — on the right layer.** "Q_max constrains actuality, not Φ" gives Q_max a real
job (the reason actuality is single-record), avoids collapse, and matches theorems already machine-checked. It
is a genuine improvement over the dead "capacity forbids superpositions" gloss, and is not fatally flawed.

Open pieces (none NEW — all pre-existing, now sharply located):
- the actual-record cost / pairwise-overflow principle for rival macro-configs (the I₀≈Q_R calibration),
  justified non-circularly;
- the **global, covariant λ-construction** over entangled regions (gluing/OP3b) — the genuine frontier;
- Born typicality for histories (the separate irreducible posit);
- no-signaling Born marginals (have the selector-level pieces; need the global version).

The program is, honestly, a **contextual single-world hidden-actuality theory** in which Q_max bounds
actuality and λ selects — with the unfinished core being the global covariant λ plus the cost principle. This
is the sharper, defensible, and better statement of QIQT-H.

**Propagation TODO:** bring the headline thesis (foundations paper, `/idea` `/theory` `/selection`, memory)
into line: *"Q_max does not constrain the wavefunction (it can't — superpositions are free); it constrains
actuality: λ has finite capacity, which is why exactly one macroscopic record is realized."*
