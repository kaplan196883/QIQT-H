# Route 1 — the free-field modular-energy bound (the honest core of "deriving holography")

**Status:** ACTIVE (2026-07-01). **Origin:** the GPT-5.5-pro expert scoping consult on "Route 1" (turning the
holographic capacity bound from a postulate into a theorem via the JLMS modular identity).

## ⚠ HONEST REFRAMING (the load-bearing verdict — read first)

**"Derive the holographic `A/4G` for the free field" is NOT achievable — and this plan does NOT attempt it.**
GPT-5.5-pro (expert): for a fixed-background *free scalar* on a Rindler wedge, `K_{∂R} = A/4G + K_bulk` with a
genuine `A/4G` is **not a theorem** — the free scalar has **no Newton constant `G`** and **no geometric area
operator**; wedge entropy is Type III/infinite and, cut off, has a **matter/cutoff-dependent coefficient**, not
universally `1/4G`; and the `δA/4G = 2π∫δT_kk` step **uses the Einstein equations**, not pure Bisognano–Wichmann
kinematics. So BW gives the Unruh `2π` but **not** the `1/4G` **along this modular route**. The `A/4G`
identification remains a *gravitational input / normalization* here, and the continuum Type III₁→II crossed-product
**dual-weight trace** stays a **multi-year cited frontier** (Mathlib's vN-algebra support is not close).

**⚠ DO NOT misread this as "the 1/4 is not derived."** This is a statement about the **JLMS free-field modular
route only**. The Bekenstein–Hawking `1/4` ratio **IS** derived — as a machine-checked Lean theorem — but through
the **separate Sakharov / induced-gravity bridge** (`SakharovRatio.sakharov_ratio`: `S_ent·G_ind/A = (4π)/(16π) =
1/4`, matter- and regulator-independent, circularity-clean; the **P4-MICRO** story: finiteness postulated, area
floor + form derived, `1/4` ratio derived). That is a *different mechanism* from the free-field modular identity.
What *neither* derives is the **value of `G`** (carried). Keep "the `1/4` ratio (derived, Sakharov)" · "the modular
route (this plan; does not touch `A/4G`)" · "the value of `G` (open)" strictly separated.

**What IS genuinely derivable (this plan's real goal):** the **free-field modular-energy bound** — the Casini /
first-law inequality `ΔS ≤ Δ⟨K_W⟩ = 2π Δ⟨B_boost⟩` from relative-entropy positivity + the (already machine-checked)
one-particle Bisognano–Wichmann `K_W = 2π B_boost`. This turns the *modular pieces* of the carried `Phase5Master`
hypothesis into **theorems**, and is honest, real, publishable **formalized modular QFT** — advertised as exactly
that, **never** as deriving the holographic `A/4G` bound.

**Honest invariants (enforce every increment):** NO `sorry`; `#print axioms` std-3; budget 0. NEVER claim this
derives `A/4G`, "holography", QG, or the value of `G`; the `A/4G`/area identification stays a *gravitational
input*, the continuum Type II dual-weight trace stays a *cited multi-year frontier*, and the Fock lift is a
labelled follow-on. Advertise the deliverable as **formalized modular free-field QFT**, not a holographic-bound
derivation. Cite the GPT-5.5-pro verdict.

---

## Track A — the honesty guardrail (docs)

State consistently across inventory §2/§3, ledger, website (`open-problems`/`formalization`), paper §1.1a:

> *"Route 1" (deriving the capacity law via JLMS) is **reframed**: the `A/4G` area identification is **not**
> derivable from the free field (no `G`, no area operator, cutoff-dependent coefficient; the `δA/4G=2π∫δT_kk` step
> needs the Einstein equations). What IS derived is the free-field **modular-energy bound** `ΔS ≤ 2π Δ⟨B_boost⟩`
> (Casini/first law, from relative-entropy positivity + one-particle BW) — turning `Phase5Master`'s modular pieces
> into theorems. The `A/4G` identification stays a gravitational input; the continuum Type II dual-weight trace
> stays a multi-year cited frontier.*

PASS = every surface states the reframing; "modular QFT, not `A/4G`" explicit; the continuum Type II trace labelled frontier.

---

## Track B — Lean (`QIQTH/ModularEnergyBound.lean`)

Finite-dim / Type-I corner first (the honest shadow, as with P4-MICRO). Reuse `relEntropy`, `relEntropy_nonneg`
(Klein), `vonNeumannEntropy`, `crossEntropy`, `matLog`, `cfc_trace` — all already in the repo. GPT-5.5-pro's
recommended order:

### B1 — the Umegaki relative-entropy identity  `D(ρ‖σ) = Δ⟨K_σ⟩ − ΔS`
`finiteCorner_relEnt_eq_modEnergy_sub_entropy`: for finite-dim densities `ρ, σ` (`σ` faithful),
`D(ρ‖σ) = (⟨K_σ⟩_ρ − ⟨K_σ⟩_σ) − (S(ρ) − S(σ))`, with the **modular Hamiltonian** `K_σ = −log σ`. A pure
rearrangement of `relEntropy`/`vonNeumannEntropy`/`crossEntropy` — highly tractable.

### B2 — the Casini bound  `ΔS ≤ Δ⟨K_σ⟩`
`finiteCorner_entropy_le_modularEnergy`: `S(ρ) − S(σ) ≤ ⟨K_σ⟩_ρ − ⟨K_σ⟩_σ`, immediate from B1 + `relEntropy_nonneg`
(Klein positivity, already proved). **This is the real near-term theorem** — the modular-energy bound.

### B3 — the Bisognano–Wichmann rewrite  `K_σ = 2π K_boost + c·1  ⟹  ΔS ≤ 2π Δ⟨K_boost⟩`
`finiteCorner_wedge_Casini_BW`: given the (finite-corner) BW/KMS identification of the modular Hamiltonian with the
compressed boost generator (a hypothesis discharged by the repo's one-particle BW transport where applicable),
the entropy variation is bounded by **boost energy** (the Unruh `2π`). Caveat (enforce in the statement): the
corner must be modular-invariant / the transported KMS dynamics must be exactly the compressed BW flow — a generic
projection does not preserve BW flow; carry that as an explicit hypothesis, not a silent assumption.

### B4 — the first law  `δS = 2π ⟨δρ · K_boost⟩`
`finiteCorner_wedge_firstLaw_BW`: differentiating `S(ρ_t)` at `ρ_0 = σ` (traceless perturbation) gives the
entanglement first law with `K = 2π K_boost`. From B3 + the derivative of `S`.

### B5 — wire-in + audit + Track-A docs → theorem names
`QIQTH.lean` import, `AxiomAudit.lean` pins (std-3), `axiom_budget_check.sh` budget 0; point the guardrails at the
built theorems.

### Follow-ons (labelled, NOT this campaign's deliverable)
- **Fock lift** of one-particle BW: `K_{A(W),Ω} = dΓ(K_{V(W)}) = 2π dΓ(B_W)` — genuine 6–18 month modular-QFT
  campaign; needs bosonic Fock/CCR infrastructure. Cited follow-on.
- **Clock-dressed modular split** `K̃ = A_edge ⊗ 1 + 1 ⊗ K_W` as a theorem of *product standard subspaces* (real
  only if `A_edge`/the dressed subspace is defined *independently*, not by declaring the answer). Cited follow-on.
- **Continuum Type III₁→II crossed product + dual-weight trace + Takesaki duality** — multi-year Mathlib-gap
  frontier; NOT attempted. The `A/4G` area identification lives here + gravitational constraints.

PASS = B1–B4 proved axiom-free (the free-field modular-energy bound + first law are theorems, `Phase5Master`'s
modular pieces upgraded from carried to derived); docs state the reframing; `A/4G` + continuum trace stay frontiers.

---

## Verification (per increment)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.ModularEnergyBound` green; `#print axioms` std-3;
`bash scripts/axiom_budget_check.sh` budget 0; ONE commit per increment with the `Co-Authored-By: Claude Opus 4.8
<noreply@anthropic.com>` trailer; push via schannel; update the Progress log. Website edits build green (66 pages).
NO `sorry`. NEVER claim `A/4G` / holography / QG / the value of `G` are derived.

## Honest scale
B1–B2 are days (rearranging existing entropy lemmas + Klein). B3–B4 are days–weeks (the BW-transport hypothesis +
differentiation). The Fock lift is the genuine 6–18 month modular-QFT campaign; the continuum Type II trace is
multi-year. **This plan delivers the free-field modular-energy bound + first law as theorems — real formalized
modular QFT — and honestly checkpoints `A/4G` as the gravitational input it is.** It does NOT derive holography.

## Progress log
- **2026-07-01** — plan created from the GPT-5.5-pro Route-1 consult; goal REFRAMED (A/4G not free-field-derivable;
  deliver the modular-energy bound instead).
- **2026-07-01 — Track A (core) ✅.** Added the Route-1 reframing to the authoritative sources: paper §1.1a (appended
  to the "Route 1 next target" sentence) and inventory §2 — "the `A/4ℓ_P²` term is NOT free-field-derivable (no `G`,
  no area operator, cutoff-dependent coefficient, the `δA/4G=2π∫δT_kk` step uses the Einstein equations); BW gives
  the Unruh `2π` not the `1/4G`; the honest deliverable is the free-field modular-energy bound `ΔS ≤ 2π Δ⟨B_boost⟩`
  (formalized modular QFT, NOT a holographic-`A/4G` derivation); the continuum Type II trace stays a multi-year
  frontier." **NEXT → finish Track A (website `open-problems`/`formalization` + ledger), then Track B (B1 Umegaki
  identity → B2 Casini bound → B3 BW rewrite → B4 first law → B5 wire-in).**
- **2026-07-01 — B1+B2 ✅ DONE** (`QIQTH/ModularEnergyBound.lean`, axiom-free std-3, wired into `QIQTH.lean` +
  `AxiomAudit.lean`, budget 0). Turned out the repo already had every ingredient (the Donald identities +
  Klein), so this is a clean assembly: `modHam K_σ = −log σ` + `modEnergy ⟨K_σ⟩_ρ = crossEntropy`; **B1
  `modular_relEnt_identity`** `D(ρ‖σ) = (⟨K_σ⟩_ρ − ⟨K_σ⟩_σ) − (S(ρ)−S(σ))` (Umegaki, from
  `relEntropy_eq_crossEntropy_sub_entropy` + `crossEntropy_self`); **B2 `modular_casini_bound`** (the real
  Route-1 content) `S(ρ)−S(σ) ≤ ⟨K_σ⟩_ρ − ⟨K_σ⟩_σ` from `relEntropy_nonneg` (Klein) — with one-particle BW
  `K_σ=2π B_boost` this is `ΔS ≤ 2π Δ⟨B_boost⟩`, the Unruh modular bound. Formalized modular QFT; the `A/4G`
  identification is NOT claimed (gravitational input). **NEXT → B3 `finiteCorner_wedge_Casini_BW` (substitute
  `K_σ = 2π K_boost + c·1`, carry the modular-invariant-corner caveat as an explicit hypothesis) → B4 first law →
  finish Track A (website/ledger) → B5.**
- **2026-07-01 — B3 ✅ DONE** (the BW modular-energy bound). Built `boostEnergy ⟨K_boost⟩_ρ`, `modEnergy_of_BW`
  (under `K_σ = 2π·K_boost + c·1` the modular energy is `2π⟨K_boost⟩ + c`, the `c` shifting by `tr ρ = 1`), and
  **`finiteCorner_wedge_Casini_BW`**: `S(ρ)−S(σ) ≤ 2π(⟨K_boost⟩_ρ − ⟨K_boost⟩_σ)` — the Unruh `2π` modular bound,
  with the BW/KMS identification (`K_σ = 2π K_boost + c·1`) carried as an **explicit hypothesis** (a generic corner
  does NOT preserve BW flow — the modular-invariant-corner caveat lives there, not silently). Axiom-free std-3,
  pinned, budget 0. **NEXT → B4 `finiteCorner_wedge_firstLaw_BW` (differentiate `S(ρ_t)` at `ρ_0=σ`, traceless
  perturbation ⟹ `δS = 2π⟨δρ·K_boost⟩`) → finish Track A (website/ledger) → B5 wire-in.**
- **2026-07-01 — B4 ✅ DONE** (the entanglement first law). Built **`finiteCorner_firstLaw`**: along any
  differentiable family of states `ρ_t` through the reference `ρ_0`, the relative entropy `D(ρ_t‖ρ_0)` is
  **stationary** at `t=0` (`D' = 0`). The honest, tractable form: rather than differentiate the von Neumann
  entropy directly (eigenvalue perturbation — genuinely hard), use that `D(ρ_t‖ρ_0) ≥ 0 = D(ρ_0‖ρ_0)` makes
  `t=0` a minimum, so a differentiable function's derivative vanishes there (`IsLocalMin.hasDerivAt_eq_zero`).
  Since `D = ⟨K_σ⟩ − S` (B1), that stationarity **IS** the first law `δS = δ⟨K_σ⟩` — the entropy variation
  equals the modular-energy variation at the reference (with BW, `δS = 2π δ⟨K_boost⟩`). The differentiability
  of `D` is the analytic input, carried as an explicit hypothesis. Axiom-free std-3, pinned, budget 0.
  **The four mathematical rungs B1–B4 are now all theorems** — the free-field modular-energy chain (Umegaki
  identity → Casini bound → BW rewrite → first law) is fully machine-checked, upgrading `Phase5Master`'s modular
  pieces from a carried hypothesis to derived results. Formalized modular QFT; NO `A/4G`, no gravity, no `G`.
  **NEXT → B5 finish: point Track-A docs (website `open-problems`/`formalization`, ledger) at the built theorems
  (QIQTH.lean import + AxiomAudit pins already done for B1–B4).**
- **2026-07-01 — B5 ✅ DONE + CAMPAIGN COMPLETE.** Wired the whole campaign into the public surfaces, pointing every
  Track-A guardrail at the four built theorems: (i) `QIQTH.lean` import + `AxiomAudit.lean` std-3 pins (B1–B4, done
  incrementally); (ii) **website `open-problems`** — a new "Route 1 reframed" note (the `A/4G` is not
  free-field-derivable — no `G`/area operator, cutoff-dependent coefficient, the `δA/4G=2π∫δT_kk` step needs the
  Einstein equations — and what IS machine-checked is the modular-energy bound `ΔS ≤ 2π Δ⟨B_boost⟩`, naming
  `modular_relEnt_identity`/`modular_casini_bound`/`finiteCorner_wedge_Casini_BW`/`finiteCorner_firstLaw`); (iii)
  **website `formalization`** — a new "free-field modular-energy bound" subsection with the four-theorem table;
  (iv) **`CLAIMS_LEDGER.md`** row **E7** (`[AF]`+`[frontier]`), formalized modular QFT NOT `A/4G`. Website builds
  green (66 pages). **All of Track A + B (B1–B5) DONE.** The deliverable: the free-field modular-energy chain
  (Umegaki identity → Casini bound → BW rewrite → first law) is a fully machine-checked axiom-free theorem set,
  upgrading `Phase5Master`'s modular pieces from a carried hypothesis to derived results — **formalized modular
  QFT, honestly NOT a derivation of the holographic `A/4G` bound**. Follow-ons stay labelled cited frontiers: the
  Fock lift of one-particle BW, the clock-dressed product-standard-subspace split, and the continuum Type III₁→II
  crossed-product dual-weight trace (multi-year, where `A/4G` lives).
- **2026-07-01 — B4′ ✅ DONE (post-campaign sharpening to B4's originally-targeted form).** Built
  **`finiteCorner_firstLaw_boostEnergy`**: the *explicit* boost-energy first law `δS = 2π·δ⟨K_boost⟩`. B4 proved the
  stationarity form (`D' = 0`); this sharpens it to the `HasDerivAt` form GPT-5.5-pro originally targeted. Key
  tractability insight — it needs **no matrix-normed-space calculus**: carry the two genuine analytic inputs
  (differentiability of `S(ρ_t)` and of `⟨K_boost⟩_{ρ_t}`) as **explicit scalar-derivative hypotheses**, then derive
  the *relation* between their derivatives entirely in `ℝ→ℝ` calculus — the modular energy is `2π·⟨K_boost⟩ + c`
  (BW, `modEnergy_of_BW`) so its derivative is `2π·B'`; B1 (`modular_relEnt_identity`) gives `D = ⟨K⟩ − S` pointwise
  so `D' = 2π·B' − S'`; B4 stationarity forces `D' = 0`; hence `S' = 2π·B'`. Axiom-free std-3, pinned, budget 0.
  This closes B4 to its full targeted form. Formalized modular QFT; no `A/4G`, no gravity, no `G`. The campaign
  deliverable now includes both the stationarity AND the explicit boost-energy first law.
- **2026-07-01 — B6 + B6′ ✅ DONE (saturation / rigidity — completes the bound with its tightness case).** Built
  **`modular_casini_saturation`**: the Casini bound `ΔS ≤ Δ⟨K_σ⟩` is **saturated iff `ρ = σ`** — equality holds
  *only* at the modular reference. Forward: equality ⟹ `D(ρ‖σ) = 0` (B1) ⟹ `ρ = σ` by **faithfulness** of the
  relative entropy (the repo's axiom-free `relEntropy_eq_zero`, Klein's equality case); reverse via `relEntropy_self`
  + the identity. And **`finiteCorner_wedge_saturation_BW`**: the BW form `ΔS = 2π Δ⟨K_boost⟩ ⟺ ρ = σ` (the Unruh
  bound is tight only at the reference vacuum), by rewriting the K_σ saturation through `modEnergy_of_BW`. Both
  axiom-free std-3, pinned, budget 0. This gives the modular-energy bound its **rigidity** companion — the bound
  AND exactly when it is an equality. Formalized modular QFT; no `A/4G`, no gravity. **Track-B tractable rungs now
  fully exhausted** (B1–B6 + B4′ + B6′); only the labelled multi-year cited frontiers remain.
- **2026-07-01 — B7 ✅ DONE + CAMPAIGN COMPLETE (capstone; tractable surface expert-confirmed exhausted).**
  Consulted GPT-5.5-pro on whether any tractable in-scope lemma remained: verdict = *substantive surface exhausted*,
  with one genuinely-useful capstone worth adding (the exact-deficit / bundled citable theorem). Built it:
  **`finiteCorner_wedge_BW_deficit_eq_relEntropy`** (B7a) — the *exact deficit* `2π·Δ⟨K_boost⟩ − ΔS = D(ρ‖σ)`
  (the sharpest form: the Unruh-bound slack IS the Umegaki relative entropy); **`finiteCorner_wedge_Casini_BW_strict`**
  (B7b) — strict bound `ΔS < 2π·Δ⟨K_boost⟩` off the reference (B3 + B6′); and the campaign capstone
  **`freeField_modularEnergyBound_finiteCorner_BW`** — a single citable statement bundling *bound ∧ exact-deficit ∧
  rigidity*. All axiom-free std-3, pinned, budget 0; capstone surfaced on the website `formalization` page (green,
  66 pages). **THE CAMPAIGN IS COMPLETE.** The free-field modular-energy bound is a fully machine-checked, axiom-free
  theorem set — identity (B1) → bound (B2) → BW/Unruh rewrite (B3) → first law, stationarity + explicit (B4, B4′) →
  rigidity (B6, B6′) → exact-deficit + bundled capstone (B7) — upgrading `Phase5Master`'s modular pieces from a
  carried hypothesis to derived results. Honest deliverable: **formalized modular free-field QFT, NOT a derivation
  of the holographic `A/4G` bound**. The `A/4G`/area identification stays a gravitational input; the labelled
  multi-year cited frontiers (Fock lift of one-particle BW, clock-dressed product-standard-subspace split, continuum
  Type III₁→II crossed-product dual-weight trace where `A/4G` lives) are the only remaining work and are OUT of this
  campaign's scope. **Next ROUTE1 fires: no tractable in-scope item remains — the honest state is CHECKPOINTED COMPLETE.**
