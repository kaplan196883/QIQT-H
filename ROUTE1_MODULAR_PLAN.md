# Route 1 — the free-field modular-energy bound (the honest core of "deriving holography")

**Status:** ACTIVE (2026-07-01). **Origin:** the GPT-5.5-pro expert scoping consult on "Route 1" (turning the
holographic capacity bound from a postulate into a theorem via the JLMS modular identity).

## ⚠ HONEST REFRAMING (the load-bearing verdict — read first)

**"Derive the holographic `A/4G` for the free field" is NOT achievable — and this plan does NOT attempt it.**
GPT-5.5-pro (expert): for a fixed-background *free scalar* on a Rindler wedge, `K_{∂R} = A/4G + K_bulk` with a
genuine `A/4G` is **not a theorem** — the free scalar has **no Newton constant `G`** and **no geometric area
operator**; wedge entropy is Type III/infinite and, cut off, has a **matter/cutoff-dependent coefficient**, not
universally `1/4G`; and the `δA/4G = 2π∫δT_kk` step **uses the Einstein equations**, not pure Bisognano–Wichmann
kinematics. So BW gives the Unruh `2π` but **not** the `1/4G`. The `A/4G` identification remains a *gravitational
input / normalization*, and the continuum Type III₁→II crossed-product **dual-weight trace** stays a **multi-year
cited frontier** (Mathlib's vN-algebra support is not close).

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
  deliver the modular-energy bound instead). NEXT → Track A guardrail, then Track B (B1 Umegaki identity → B2 Casini
  bound → B3 BW rewrite → B4 first law → B5 wire-in).
