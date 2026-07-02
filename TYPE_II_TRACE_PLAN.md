# THE WALL — the Type II dual-weight trace (τ∘θ_s = e^{−s}τ), the tractable ladder

**Status:** ACTIVE (2026-07-02). **GPT-5.5-pro-DESIGNED ladder (consult 2026-07-02) — its corrections are
BINDING.** **Goal:** construct the crossed-product dual-weight trace on an honest algebraic core — the object
whose renormalized entropy discharges the carried calibration toward a continuum count. This is wall #1 of QG in
QIQT-H.

## Binding corrections (from the consult — never violate)
- **The weight density lives on the LOG-CLOCK `L` (λ_t = e^{itL}), NOT the clock position `X`.** The dual action
  θ_s = Ad(V_s)⁻¹ (modulation conjugation) fixes `π(a)`, phases `λ_t ↦ e^{ist}λ_t`, and SHIFTS `f(L) ↦ f(L+s)`;
  the CPW `e^x` is against the spectral variable of `L`. A `[t=0]·∫e^x f(X)`-style functional proves INVARIANCE,
  not `e^{−s}` scaling — forbidden.
- **The ℤ-clock model:** the genuine dual action of `M⋊ℤ` is CIRCLE-valued and leaves `Tr(e^N ·)` INVARIANT;
  the `e^{−1}` scaling comes from the SHIFT (the discrete log-clock translation), not the dual action. Label
  accordingly; domain needs clock cutoffs `f(N)` (finitely supported) or an ℝ≥0∞ weight.
- **Test functions:** bounded measurable with COMPACT SUPPORT (`ExpTest`), not Schwartz (`∫e^x|f|` must converge).
- **The full CPW normal-semifinite-faithful vN trace** (normal weights, affiliated operators, extension from the
  core) is the CARRIED `DualWeightTraceExtension` hypothesis — never claimed, never an axiom.

## Increments (the reordered ladder)
- [x] **W1 ✅ LANDED (`QIQTH/DualAction.lean`, [AF] std-3, wired+pinned, budget 0) — the dual action.** `dualAction s := Ad(modulationUnitary s)⁻¹` on `B(H_tot)`:
  `dualAction_matter` (fixes `π(a)`), `dualAction_clock` (`λ_t ↦ e^{ist}λ_t` — LITERALLY the proven Weyl
  relation), `dualAction_add` (group law). Package as *-automorphisms.
- [x] **W1.5 ✅ LANDED (`QIQTH/LogClockWeight.lean`, [AF] std-3, wired+pinned, budget 0) — the log-clock + the scaling integral.** `logClock L` with `λ_t = e^{itL}` (Stone uniqueness + FC);
  `dualAction_logClock_fc`: `θ_s(f(L)) = (x ↦ f(x+s))(L)`. `ExpTest` structure; `Iexp f := ∫ e^x f x dx`;
  **`Iexp_dualShift`: `Iexp(f(·+s)) = e^{−s}·Iexp f`** — the exact scaling, clock-only.
- [x] **W2 ✅ LANDED (`QIQTH/ZClockRegression.lean`, [AF] std-3, wired+pinned, budget 0) — the ℤ weighted shift.** `zWeight A := ∑ e^n⟨e_n, A e_n⟩` on the
  finite-support core: `zWeight_shift_quasiInvariant` (`= e^{−1}·`, the SHIFT = discrete log-clock translation)
  AND `zWeight_dualCircle_invariant` (the TRUE ℤ-dual action leaves it invariant) — the distinction machine-checked.
- [ ] **W3a — the monomial trace formula.** On core elements `π(a)·λ_t·f(L)` (`f : ExpTest`):
  `tauMonomial a t f := ω(a)·∫ e^x e^{itx} f(x) dx`; **`tauMonomial_dual`: `τ₀(θ_s(·)) = e^{−s}·τ₀(·)`** —
  Weyl + change of variables, exact.
- [ ] **W3b — the modular eigen-core.** `ModEigen κ` (σ_t-eigenoperators `σ_t(a) = e^{itκ}a`); `EigenTerm`
  (`κ, a, F`) with `rep := π(a)·f(L)`, `mul`/`star`/`theta`/`tau`; theorems `eigen_rep_mul`, `eigen_rep_star`,
  **`eigen_tau_dual`** (`e^{−s}` scaling), **`eigen_tau_trace`** (traciality — via the KMS eigen lemma
  `ω(ab) = e^{κ}ω(ba)` + the `∫e^x` shift identity: the factors cancel), **`eigen_tau_star_mul_nonneg`**
  (positivity — frequency blocks are ω-orthogonal, `omega_eigen_zero`).
- [ ] **W4 — the payoff.** `CoreDensity` (positive, mass-one, log-closed); `SrenCore` (the τ₀-relative entropy on
  the core); **instantiate `TraceCapacity`/`Phase5Master` for the eigen/coherent core with the CONSTRUCTED
  trace** — the FQ-bound interface fed by a built object, non-vacuous. The full vN extension stays the carried
  `DualWeightTraceExtension` + `EntropyCoreApproximation` typeclasses (explicit hypotheses, never axioms).

## Discipline (every increment)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green; `#print axioms` std-3; budget 0; AxiomAudit
pins; wire QIQTH.lean; ONE commit + `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`; push schannel;
update this checklist + `LEAN_RESULTS_INVENTORY.md`. Honest scope: core/algebraic level; the vN closure and the
continuum count stay carried; NEVER claim the wall crossed or QG solved. Consults: `mcp__OpenAI__ask`
gpt-5.5-pro.

## Progress log
- **2026-07-02** — plan created from the GPT-5.5-pro ladder consult (W1 RECOMMEND; W2 redirected to honest
  shift-vs-dual regression; W3 redirected to the log-clock normal form — the X-position formula FORBIDDEN;
  W4 core-instantiation + carried extension). NEXT → W1.
- **2026-07-02 — W1 ✅ LANDED**: dualPhase V_s (fiberwise phase unitary on L²(ℝ;H), group law + inverse) + dualAction θ_s = Ad(V_s)⁻¹: dualAction_matter (fixes π(a)), dualAction_clock (θ_s(λ_t)=e^{ist}λ_t — the vector-valued Weyl relation), dualAction_add, dualAction_mul. NEXT → W1.5 (logClock + Iexp scaling).
- **2026-07-02 — W1.5 ✅ LANDED**: ExpTest (compact-support log-clock symbols; dualShift + modMul closure), expTest_integrable, Iexp = ∫e^x f, and THE EXACT SCALING Iexp_dualShift (= e^{−s}·Iexp, pure change of variables) + the modulated W3a form. NEXT → W2 (ℤ shift-vs-dual regression).
- **2026-07-02 — W2 ✅ LANDED**: the ℤ regression on banded kernels — zWeight_shift_quasiInvariant (= e^{−1}·, the SHIFT/discrete log-clock translation) AND zWeight_dualCircle_invariant (the TRUE ℤ-dual action leaves the weight invariant) + positivity + window stability. The shift-vs-dual distinction is machine-checked. NEXT → W3a (the monomial trace formula).
