# GR track — interpreted state report

**Track:** `gr` — *QIQT-H gives the GR field equations (Jacobson route, free KG field).*
Generated from `reports/gr/agent_summary.json` (tool commit `d76cb2a`). Machine facts:
[`report.machine.md`](report.machine.md). Provenance badges are mandatory: `[L]` Lean/kernel
fact, `[P]` Lean-checked prober, `[D]` deterministic post-processing, `[C:rule]` curation rule in
`tracks/gr.toml`, `[AI]` my semantic judgment.

## Provenance summary

- `[L]` 7/7 spine theorems present; all `kind = thm`.
- `[L]` **0 project-specific axioms** across the whole spine (`project_axioms: []`).
- `[L]` Every theorem is **`policy_clean`** (depends only on the allowed axioms `propext`,
  `Classical.choice`, `Quot.sound`) but **not** `axiom_free_literal` — i.e. they *do* use
  `Classical.choice`/`propext`, so the honest phrase is **"policy-clean (standard axioms only),
  not literally axiom-free."**
- `[L]` **0 packed Prop fields** (`n_packed = 0`) anywhere — no assumptions are hidden inside
  data-structure arguments; the surface hypotheses are the whole assumption surface.
- `[P]` **0 auto-dischargeable** surface hypotheses (`dischargeable: []` on every theorem) and
  **0 vacuous/`falseProvable`** contexts. No no-go (`isFalse`) theorems here.
- `[P]` Caveat (honesty contract): "not auto-dischargeable" means *not closed by the prober's
  tactics*, a lower bound on redundancy — **not** "proven necessary."

## Capstone assumption surface (headline)

The capstone is `[C:role]` **`QIQTH.WedgeKMSToGR.qiqt_gr_freefield`** — the free-field
instantiation. `[L]` It carries **29 propositional hypotheses, 0 packed**, and `uses_spine`
`qiqt_gr_from_flux_complete`. `[AI]` This is the right headline: it is the most-downstream theorem
whose conclusion is the Einstein field equations, and (unlike the abstract spine member) it does
**not** assume an abstract flux hypothesis — it has pushed that down to the one-particle modular
objects (`hTkk`, `hbridge`). Deduplicated piles, by the `[C]` curation rules:

### PHYSICS — genuine inputs (8) `[C:physics-floor]`
| binder | type (verbatim `[L]`) | `[AI]` reading |
|---|---|---|
| `hbound` | `BL(g x) v = 0 → ∀ᶠ t in 𝓝 0, Sf x v t ≤ η·A x v t` | capacity bound $S\le\eta A$ |
| `hsat` | `… → Sf x v 0 = η·A x v 0` | saturation at the reference |
| `hDnn` | `… → ∀ t, 0 ≤ KE x v t − Sf x v t` | Klein positivity (relative-entropy ≥ 0) |
| `hD0` | `… → KE x v 0 − Sf x v 0 = 0` | Klein equality at the reference |
| `hFocus` | `… → ad x v = BL(ricci g gi) v` | Raychaudhuri focusing $\dot A = R_{kk}$ |
| `hKG` | `boxField φ g gi x = m²·φ x` | Klein–Gordon matter equation of motion |
| `hTkk` | `… = (−2π ∫ \overline{ff}·ff')·\mathrm{im}` | stress-energy ↔ boost/modular-flux component (Bisognano–Wichmann, one-particle) |
| `hbridge` | `HasDerivAt (⟨ff, modUnitary(niceWedge…) t · ff⟩) (i·kd) 0` | the modular-flow ($\Delta^{it}$) generator at the boost |

### SETUP — per-generator kinematics (3) `[C:setup]`
`hS`, `hK`, `hA` — existence of the entropy / modular-energy / area derivatives along each null
generator (`HasDerivAt … 0`).

### REGULARITY / BACKGROUND (18) `[C:regularity]`
Metric symmetry & inverse & smoothness (`hsymm`, `hsymm_gi`, `hinv`, `hCg`, `hCgi`); constants and
field smoothness (`hbar0`, `heta`, `ha = 2π/(ℏη)`, `hφ`); frame/congruence (`hPP`, `hPP'`,
`hcong`); and the localization-mode analytic data (`hmw`, `hf2`, `hf_int`, `hfd`, `hf'_meas`,
`hB`).

`[L]` 8 + 3 + 18 = 29 = `n_prop`. `[AI]` So the genuine *physical* assumption surface of the
machine-checked free-field Einstein result is the 8 PHYSICS binders; the other 21 are kinematic
setup and regularity/background.

## Spine notes (the other capstone-style members)

- `[L]` `qiqt_bekenstein_gives_gr` (abstract core, 23 hyps) and `qiqt_gr_from_flux_complete`
  (23 hyps) assume the **abstract** boost-flux input `hFlux`/`hflux`
  (`kd = (2π/ℏ)·BL(T)·v`) plus `conserv` (∇·(aT)=0) and `hreg`. `[C]` These flux binders come back
  **uncurated** (`curation: null`) — the `gr.toml` `name_regex` set omits `hFlux`/`hflux`/`hKMS`
  (the same gap I fixed earlier in `list_hypotheses.lean`). `[AI]` They are PHYSICS inputs; see
  `reports/gr/curation.suggestions.toml` for a proposed rule (not auto-applied).
- `[L]` The one-particle-BW spine — `oneParticleBW_niceWedge_unconditional` (2 hyps: `hm: 0<m`,
  `hVboost`: `V t = boostUnitary(2π t)`), `freeField_oneParticle_hFlux` (7 hyps) and
  `freeField_component_hFlux` (8 hyps, produces `hbridge`+`hTkk`) — `[AI]` is exactly the machinery
  that **discharges** the capstone's `hTkk`/`hbridge` down to `0 < m`, the boost identification, and
  ordinary $L^2$ analytic regularity of the wedge mode. This is the live research frontier.

## Current state — proven / conditional / open `[AI]`

- **Proven (machine-checked, policy-clean, 0 project axioms):** the entire deductive chain from the
  29 hypotheses to the Einstein field equations $a\,T_{\mu\nu}=G_{\mu\nu}+\Lambda g_{\mu\nu}$ —
  including the differential geometry (Bianchi, $\nabla^\mu G_{\mu\nu}=0$, null-cone→tensor, constant
  $\Lambda$). Nothing here is vacuous and nothing is auto-dischargeable.
- **Conditional on (the scope still assumed):** the 8 PHYSICS binders — the Clausius/area-saturation
  floor (`hbound`/`hsat`/`hDnn`/`hD0`, the QIQT-H capacity postulate), Raychaudhuri focusing
  (`hFocus`, cited geometry), the matter EOM (`hKG`), and the boost/modular-flux objects
  (`hTkk`/`hbridge`).
- **Open / research frontier:** (i) finish discharging `hTkk`/`hbridge` to the genuine one-particle
  Bisognano–Wichmann property — the `Fock.*_hFlux` spine reduces them to `0<m` + boost +
  $L^2$ regularity, so what remains is wiring that into the capstone in place of the assumed pair;
  (ii) the capacity/area floor (`hbound`/`hsat`) is the framework's **physical postulate**, not a
  theorem, and is out of scope for formal discharge. Raychaudhuri (`hFocus`) is a cited theorem of
  Lorentzian geometry, assumed here.
