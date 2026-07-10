# RC campaign — boundary dynamics rungs a + b: the E4 join and the unraveling

## STATUS: CAMPAIGN COMPLETE (2026-07-10) — all three bricks landed FULL, axiom-free std-3, budget 0

- **RC1 DONE** — `73fd89c4` `RecordChannel.lean` (57 decls): the record-dephasing semigroup — records
  FORM, entropy monotone, Lyapunov, commutes with the free flow, equivariant.
- **RC2 DONE** — `ef64ea39` `RecordEquilibrium.lean` (10 decls, green first build): the second law
  WITH RIGIDITY (production zero ⟺ record, via Klein faithfulness; flow never reaches equilibrium at
  finite time) + THE E4 JOIN (`boundary_dynamics_equilibria_are_geometry`: stationary ∧
  Lyapunov-stable ∧ linearized-Einstein). Honesty finding: `hEq` is labelling inside E4's proof; the
  genuine dynamical links are the stationarity + Lyapunov-stability theorems.
- **RC3 DONE** — `a63c9b73` `RecordUnraveling.lean` (29 decls): THE EXACT UNRAVELING
  (`unraveling_exact` — candidate 6 = E_λ[candidate 3] as a theorem; λ = the jump time + selected
  record), a genuine probability law, Chapman–Kolmogorov, the Born reading via the held `bornW`, and
  **BORN FORCED** (`unraveling_weights_unique`, no PSD hypothesis needed) — the finite answer to the
  SelectionDynamics circularity risk: at this channel the jump law is forced, not chosen (forced
  GIVEN the channel; the non-circularity question moves one level up, documented).
- Commits LOCAL, unpushed. The firewall below is binding and restated in every header + audit pin.

**Date:** 2026-07-10. **Parent:** `BOUNDARY_DYNAMICS_CANDIDATES.md` (RC1 = `RecordChannel.lean`
`73fd89c4` DONE). **User directive:** "a and b in the loop."

## RC2 — `RecordEquilibrium.lean` (rung a: the E4 join + the second law with rigidity)

- **Rigidity / the equality case (the second law for the record channel):**
  `entropy_production_zero_iff` — `S(dephase A) = S(A) ⟺ dephase A = A` (via `crossEntropy_dephase`
  + the held faithfulness `relEntropy_eq_zero`-style rigidity): entropy strictly increases UNLESS the
  state is already a record. `Tsem_record_iff` — `dephase (Tsem s A) = Tsem s A ⟺ dephase A = A`
  (off-diagonals scale by `e^{−s} ≠ 0`): the flow never creates or destroys equilibrium at finite
  time. Strict forms where cheap.
- **THE JOIN `record_dynamics_einstein`:** instantiate `code_equilibrium_einstein` (E4) with the
  per-ray references `ρt v 0` required to be **fixed points of `Tsem`** (records, by
  `Tsem_fixed_iff`) — "equilibrium" upgraded from a bare stationarity hypothesis to a DYNAMICAL
  notion (attractor of the RC1 semigroup). E4's other carried data (paths, BW, derivative data,
  Iyer–Wald) stay carried, honestly. Conclusion: linearized vacuum Einstein — **the boundary
  dynamics' equilibria ARE geometry**, as one composed named theorem.

## RC3 — `RecordUnraveling.lean` (rung b: the jump-process unraveling + Born forced)

- **The exact unraveling:** the RC1 channel unravels EXACTLY as (Poisson-1 jump time, Born-selected
  record): `unraveling_exact` — `Tsem s ρ = e^{−s}·ρ + Σ_n (1−e^{−s})·(ρ n n)·recordState n` with
  the weights a genuine probability law (`jumpWeight_nonneg` via PSD diagonal, `jumpWeight_sum` via
  trace 1, no-jump weight `e^{−s}`). Candidate 6 = E_λ[candidate 3] as a theorem.
- **Chapman–Kolmogorov / consistency:** the two-time composition of the jump law reproduces the
  one-time law (diagonal entries are `Tsem`-invariant; the finite `CoarseGrainNaturality` shape).
- **The Born reading:** conditioned on jumping, the record distribution IS the Born law of the
  record POVM (`bornW`-compatible).
- **BORN FORCED (the finite circularity answer):** `unraveling_weights_unique` — ANY record-diagonal
  unraveling of `Tsem` must use exactly the Born weights `(1−e^{−s})·ρ_nn` (diagonal-entry match).
  HONEST framing: Born is forced GIVEN the channel (which was built in the record basis); the
  non-circularity question moves one level up (why this channel) — documented, not hidden.
- **Equivariance transfer:** permutation relabeling pushes the jump law forward (Gate-3 at path
  level).

## IC1 — `InteractingChannel.lean` (rung c, added 2026-07-10: EINSELECTION DERIVED — delete RC1's input)

The pure-dephasing (measurement-limit) model, exactly solvable, finite: system ι × environment κ,
monitored observable `A = diagonal a`, environment `B = diagonal b`, environment state `ω = diagonal w`
(probability weights), interaction `H = A ⊗ B`; the dynamics is the diagonal phase unitary
`U_t = diagonal (e^{−it·a n·b k})` (house pattern — no Stone, no Matrix.exp). Deliverables:
- `reduced_dynamics_entry`: `ρ_S(t) n m = γ_{nm}(t)·ρ n m` with `γ_{nm}(t) = Σ_k w k·e^{−it(a n−a m)b k}`
  (via the held `partialTraceRight`); `gamma_diag = 1` (the ledger conserved BY THE INTERACTION),
  `gamma_abs_le_one`; trace/PSD preservation (held partial-trace theorems).
- **THE EINSELECTION CAPSTONE `timeAvg_reduced_tendsto_dephase`**: under the gaps-resolved hypothesis
  (`∀ n ≠ m, ∀ k, (a n − a m)·b k ≠ 0`), the Cesàro time average `(1/T)∫₀ᵀ ρ_S(t) dt → dephase ρ`
  entrywise as `T → ∞` — **the time-averaged interacting reduced dynamics IS RC1's dephase channel, in
  the eigenbasis of the coupling**: the record/pointer basis DERIVED from `H_int`, not inserted.
- `invariant_iff_record`: the states invariant under the interacting reduced dynamics at all times are
  exactly the records (einselection uniqueness, via the time-average limit).
- The necessity guard `no_resolution_no_einselection`: with `b = 0` (decoupled environment) nothing
  dephases — the gaps-resolved hypothesis is load-bearing, machine-checked.
- HONEST: finite environment ⟹ recurrences (the repo's own gate C) — pointwise `t → ∞` dephasing is
  IMPOSSIBLE; the derived statement is the Cesàro/time-averaged einselection (the honest
  finite-dimensional Zurek statement, cited); pure-dephasing limit (system self-Hamiltonian competition
  = named follow-on); environment spectrum/state are inputs; deletes RC1's pointer-basis input AT THE
  TIME-AVERAGED LEVEL only.

## HONEST scope firewall (binding, both bricks)

Record/pointer basis an INPUT; E4's ray-path/BW/Iyer–Wald data stay CARRIED (structure fields,
never axioms); PosDef per held conventions; finite single corner; the unraveling is the finite
two-time law, not a continuum stochastic process (no filtration/SDE); Born forced GIVEN the
channel, not derived ab initio; NOT bulk reconstruction, NOT the strong holographic principle,
NOT QG.

## Discipline

Unchanged: ONE bg fable subagent per brick (own module, NO git); independent verification (rebuild +
scratchpad `#print axioms` std-3 + no-sorry grep); wire `QIQTH.lean`; AxiomAudit pins; full budget
check (LONG ~420000ms, budget 0); commits LOCAL ONLY — DO NOT PUSH; explicit git paths; NO sorry;
hypotheses never axioms; checkpoint at genuine walls; RC2 then RC3 sequentially (shared build tree).
