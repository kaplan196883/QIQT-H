# The graviton/dynamics wall — attacking the mechanism gap (a conditional finite skeleton, NOT solved QG)

**Status:** SCOPED (2026-07-01), pending GPT-5.5-pro verification before the loop starts. **Origin:** the GPT-5.5-pro
"be brave, crush the wall" mechanism consult, cross-checked against `LEAN_RESULTS_INVENTORY.md`.

## ⚠ HONEST SCOPE (read first — the load-bearing verdict)

This is the **attack on the mechanism gap** — the graviton/dynamics wall that keeps QIQT-H from being a quantum
gravity theory. **It does NOT solve quantum gravity.** What is grindable now (G1–G7) is a **finite, conditional,
algebraic skeleton** of the Faulkner–Guica–Hartman–Myers–Van Raamsdonk (FGHMVR) "entanglement first law ⟹ linearized
Einstein" logic, plus a QIQT-H-native finite **null-focusing** route. The decisive continuum physics (G8–G12) — the
CFT ball modular Hamiltonian, the RT/extremal-area identification, Iyer–Wald geometry, and the actual (non-linear,
self-interacting, quantized) graviton — is **real open research**, exactly the frontier the inventory (§8) already
cites. Every rung is labelled tractable-now vs research-open.

**★ THE SINGLE MOST IMPORTANT GUARD (GPT-5.5-pro verification, 2026-07-01).** The loop must **NEVER** turn
`hAK : δA = 8πG·K` into a *derived* theorem from packing / first law / min-cut. That hypothesis is **exactly where the
Einstein-equation content enters**. Packing/area-law alone does **not** derive it. G6 may only prove *conditional
bookkeeping*: assuming the area–modular/stress link, the finite second-difference equation follows. Any run that
"derives" this link is a soundness/overclaim failure — stop and flag it.

**⚠ Factor convention (avoid a silent `2π` error).** Disambiguate the modular vs boost kernel: if `K = Kmod` includes
the BW `2π` (`K_W = 2π B_boost`), the link is `δA = 4G·δKmod`; if `K = Kboost` excludes the `2π`, it is
`δA = 8πG·δKboost`. G1 uses modular `K`; G3/G6 use the **boost/tail** kernel `Kboost` (`8πG`). State which in every rung.

**Four non-negotiable honesty rails (enforce in every theorem):**
1. **Conditional, not derived.** The step `δA = 8πG·K` **carries the Einstein-equation content** — the inventory
   says verbatim (§2): "the `δA/4G = 2π∫δT_kk` step *uses the Einstein equations*." So G6 carries that link as an
   **explicit hypothesis on a supplied area–stress correspondence**, never derived (packing/area-law alone does not
   give it). Same discipline as `qiqt_gr_freefield`'s carried `hFlux`/`hTkk`.
2. **Linearized ≠ full.** G7/G11 reach at most **linearized** spin-2 kinematics (a conditional formal theorem). The
   **full nonlinear/self-interacting/quantized graviton (G12) is a research checkpoint — NEVER marked solved by the
   linearized rung.**
3. **Toy ≠ background-independent.** G4's refinement invariance earns only a *toy quotient* "not-a-fixed-graph"
   statement — NOT continuum background independence.
4. **`G` relation ≠ `G` value.** G5 generates `Λ_s` non-circularly as a *relation* (dimensional transmutation); it
   still needs a reference unit and does NOT compute the numerical `G`.

**Honest invariants (every increment):** NO `sorry`; `#print axioms` std-3; budget 0. NEVER claim QG solved / the
mechanism gap closed / a real graviton / background independence / the value of `G`. The `δA=8πG K` link is a carried
conditional. Advertise the deliverable as a **finite conditional skeleton of emergent (linearized) dynamics**, with
the continuum modular/RT/Iyer–Wald/nonlinear-graviton walls cited as open research. Cite the GPT-5.5-pro verdict.

---

## Foundations REUSED (confirmed present in `LEAN_RESULTS_INVENTORY.md`)

The program plugs into existing machine-checked results — it does not rebuild them:
- **First law** `δS = δ⟨K⟩` — `ModularEnergyBound.finiteCorner_firstLaw` / `finiteCorner_firstLaw_boostEnergy`
  (`δS = 2π δ⟨K_boost⟩`); Casini `ΔS ≤ Δ⟨K_σ⟩`; Track C's finite first law. ⚠ These are the **finite/wedge modular**
  first law — they justify the finite modular *pattern*; the `∀ B` all-probe family is a **separate explicit
  hypothesis** (continuum CFT balls = G8, not supplied).
- **`T_kk` (defined) + boost-charge = horizon stress flux** — `wedge_boostCharge_eq_neg_stressFlux` (§6d) — the
  anchor for the null kernel (G3). ⚠ **KG / free-field only**, with a **sign/orientation** caveat (`= −stressFlux`);
  the continuum `hTkk` localization/smearing map and interacting matter are **frontiers**, not supplied.
- **Raychaudhuri focusing** `dθ/dλ = −R_kk` — `raychaudhuri_focusing_at_equilibrium` [AF] (§3). ⚠ Background only —
  G6's `RkkDisc := Δ²(δA)` is a **discrete curvature proxy**, NOT the geometric Ricci contraction unless extra
  geometry/sign/normalization hypotheses are supplied.
- **RT / min-cut** — Track C `EmergentSpacetime.flow_weak_duality`, `EmergentSpacetime.entropy_le_cut` (both
  grep-confirmed); `QIQTH.ScreenCode.mincut_area_law` (namespace confirmed). Toy/finite/supplied-data.
- **Capacity / packing** — `HolographicScreenCode` (`area_law_of_packing`, saturation, load-bearing).
- **`G = 1/(N Λ_s²)`** — `InducedNewtonConstant` (for G5's RG rung).

---

## Track B — the grindable rungs (Lean; `QIQTH/EmergentDynamics.lean`, namespace `QIQTH.GravDyn`)

Single growing file, one commit per rung, most-tractable-first. GPT-5.5-pro supplied the theorem skeletons; use them.

### G1 — the FGHMVR logical skeleton (all-probes first law ⟺ residual = 0)  *[grindable now]*
`Separating (P : Ball → E →ₗ[ℝ] ℝ) := ∀ e, (∀ B, P B e = 0) → e = 0`. Then, with a carried Iyer–Wald-shaped identity
`iw : ∀ B, δK B − δS B = P B residual`:
`allBall_firstLaw_iff_residual_zero (sep) (iw) : (∀ B, δS B = δK B) ↔ residual = 0`. The exact formal core of
"first law at every probe ⟺ the linearized field equation." Pure linear algebra. ⚠ The *existing* finite/wedge
first-law theorems justify the finite modular *pattern*, but the `∀ B` all-probe family and the Iyer–Wald-shaped
`iw` identity are **explicit carried hypotheses** here — the inventory supplies **neither** continuum CFT balls
(= G8) nor Iyer–Wald geometry (= G10). Use `Kboost` (the `8πG` convention) consistently with G3/G6.

### G2 — finite Radon / decoder (all probes vanish ⟹ the field vanishes)  *[grindable now]*
`eq_zero_of_decoder (measure : Probe → (Cell → ℝ) → ℝ) (decode) (hdecode : ∀ f i, f i = ∑ p, decode i p · measure p f)
(hzero : ∀ p, measure p f = 0) : f = 0`. The finite model of "all ball integrals of `f` vanish ⟹ `f = 0`" — the
`Separating` instance G1 needs, made concrete on a finite cell/probe grid.

### G3 — the discrete null modular kernel  `Δ²K = T`  *[grindable now; anchors to existing `T_kk`]*
`tailK N T c = ∑ i∈Icc c N, (i−c)·T i`; `secondDiff A c = A(c−1) − 2·A c + A(c+1)`;
`secondDiff_tailK_eq : secondDiff (tailK N T) c = T c` (for `0 < c < N`). The finite version of the null modular
shape derivative `δ²K_V/δV² = 2π T_kk` — connecting to the *existing* `T_kk` / `wedge_boostCharge_eq_neg_stressFlux`.

### G4 — dynamic-screen refinement invariance (toy background independence)  *[grindable now]*
`EdgeRefinement` (a surjection `π : E' → E` with **fiberwise-additive** `logDim`/`areaWt`); `refinement_preserves_area_and_capacity`
(`codeCap`/`screenArea` descend along refinements); `regional_bound_invariant_under_refinement` (packing bound
descends); `property_preserved_along_moves` (invariance along `Relation.ReflTransGen` of a move relation). Earns the
**toy** "capacity/area live on the quotient of graph configurations, not a fixed graph" statement. ⚠ **Requires an
explicit cut/region correspondence** — an edge surjection *alone* does NOT give min-cut invariance (a refinement can
introduce new cuts and change the min); carry the pullback/weight-preserving cut map as a hypothesis. ⚠ **NOT
continuum background independence** — only invariance for *supplied finite* graph/cut data.

### G5 — discrete RG dimensional transmutation (`Λ_s` non-circular)  *[grindable now]*
`uFlow`, `muFlow`, `LambdaRG b u μ = μ·exp(−u/2b)`; `LambdaRG_invariant : LambdaRG b (uFlow …) (muFlow …) = LambdaRG b u0 μ0`
(the one-loop RG invariant); `InducedG_pos`. Then `Λ_s = μ0·exp(−1/(2b g0²))`, `G = 1/(N Λ_s²)` — `Λ_s` generated from
*dimensionless* data `{b, g0}`, not from `G`. ⚠ Still needs a reference unit; does NOT compute the value of `G`.

### G6 — ★ the QIQT-H-native finite null-focusing theorem (the bold bet)  *[grindable now, CONDITIONAL BOOKKEEPING]*
`secondDiff_of_area_firstLaw (κ) (hAK : ∀ c, δA c = κ·Kboost c) (hKT : ∀ c, secondDiff Kboost c = T c) : ∀ c,
secondDiff δA c = κ·T c`. Instantiate `κ = 8πG`, `Kboost` = the G3 boost/tail kernel (`Δ²Kboost = T_kk`), define the
**discrete curvature proxy** `RkkDisc := Δ²(δA)`. Conclusion: **`RkkDisc = 8πG·T_kk`** on the finite substrate.
⚠⚠ **CONDITIONAL BOOKKEEPING, NOT a derivation of Einstein.** The `hAK : δA = 8πG·Kboost` link **carries the
Einstein-equation content** (inventory §2) and is an **explicit carried hypothesis on a supplied area–stress
correspondence** — it is **NOT** derived from packing/first-law/min-cut (the single most important guard, above).
Work with **variations `δA`** (not absolute area — affine zero-modes/signs/normalization acknowledged); `RkkDisc` is
a **discrete proxy, NOT geometric Ricci** absent extra geometry. Optional λ-variant
`selector_zero_defect_implies_constraints` (a finite defect functional minimized to zero ⟹ constraints hold) recasts
λ as a variational selector — a bookkeeping device, not a derivation of the action.

### G7 — null equations for all directions ⟹ linearized Einstein up to Λ  *[split; fixed 4D]*
- **G7a** *[grindable now]* — `symForm_proportional_to_minkowski_of_null_quad_zero (S : Matrix (Fin 4) (Fin 4) ℝ)
  (hSym) (hNull : ∀ k, minkowskiQuad k = 0 → quadForm S k = 0) : ∃ φ, S = φ • minkowskiMetric`. Pure finite-dim
  tensor algebra, explicit coordinate proof on rational null vectors (no algebraic-geometry machinery).
- **G7b** *[conditional]* — removing `φ` via (discrete) Bianchi/conservation + a boundary condition `φ = 0` (or `φ` =
  a cosmological-constant mode) to give the **linearized** Einstein residual — only insofar as it uses the *existing*
  formal Bianchi/conservation theorems; **no PDE/QFT graviton claim**.
⚠ **Linearized only** (the residual is a first-order tensor equation); the propagating/quantized spin-2 graviton is
G11/G12 (frontier), NEVER reached here.

### G-wire — audit + inventory
Wire into `QIQTH.lean` + `AxiomAudit.lean` (std-3 pins); add a LOUDLY-LABELLED `LEAN_RESULTS_INVENTORY.md` entry:
"conditional finite skeleton of emergent (linearized) dynamics — FGHMVR + null-focusing; the `δA=8πG K` link is a
carried Einstein-content hypothesis; linearized ≠ full graviton; NOT solved QG."

---

## Frontier walls — G8–G12 (cited, NOT this plan; = inventory §8 frontiers)
- **G8** — continuum ball modular Hamiltonian `K_B = 2π∫_B (R²−r²)/2R · T_00`: conformal-QFT / Type III input, a
  library gap (carried as an interface hypothesis only).
- **G9** — RT / extremal-area identification `δS_B = δA_B/4G` for an *emergent extremal surface* (not a pre-existing
  screen charge): research checkpoint.
- **G10** — Iyer–Wald formal Lorentzian geometry (`dχ = −2ξ^a E_ab ε^b`): a major Mathlib formalization project.
- **G11** — the linearized graviton PDE/QFT (`□h̄ = −16πG T`, TT polarizations, spin-2): partially algebraic later.
- **G12** — the **full nonlinear/self-interacting/quantized graviton**: real research. NEVER marked solved by G7/G11.
- **Also on the research side (GPT-5.5-pro verification):** the continuum **`hTkk` localization/smearing** map; the
  continuum **Type III/vN relative-entropy** inputs for *actual* ball modular Hamiltonians; the **interacting-matter /
  SM stress tensor**; genuine **RT/area-law emergence** (`S∝A` scaling, an emergent extremal surface — not a supplied
  screen charge); and the **numerical value of `G` / species accounting**. The *physical instantiations* of G1, G6,
  G7 live here; only their **finite conditional algebraic forms** are grindable now.

---

## Verification (per increment)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.EmergentDynamics` green; `#print axioms` std-3;
`bash scripts/axiom_budget_check.sh` budget 0 (from `lean/mathlib`); ONE commit per rung with the `Co-Authored-By:
Claude Opus 4.8 <noreply@anthropic.com>` trailer; push via schannel; update the Progress log. NO `sorry`. NEVER claim
QG solved / real graviton / background independence / value of `G`; the `δA=8πG K` link is a carried conditional.

## Honest scale
G1–G7 are hours–days each (finite algebra / linear algebra / Finset sums). They deliver a **conditional finite
skeleton** of emergent linearized dynamics — genuinely new, inventory-grounded, and honestly NOT quantum gravity.
G8–G12 are multi-year research + major Mathlib formalization. The wall becomes real research exactly at G8 (continuum
modular Hamiltonians, emergent metric, Iyer–Wald), as the inventory §8 already marks.

## Progress log
- **2026-07-01** — scoped from the GPT-5.5-pro mechanism consult, cross-checked against the inventory (first law /
  `T_kk` / stress flux / Raychaudhuri / RT foundations confirmed present; the `δA=8πG K` Einstein-content conditional
  confirmed by §2; G8–G12 = the §8 cited frontiers).
- **2026-07-01 — VERIFIED (GPT-5.5-pro), verdict "YES WITH REQUIRED EDITS → GO."** Both the full plan and the full
  `LEAN_RESULTS_INVENTORY.md` were sent verbatim for verification. Applied all 8 required edits: (1) added the
  factor-convention `Kmod` (`4G`) vs `Kboost` (`8πG`) disambiguation + the **single most important guard** (never
  derive `hAK`); (2) G1 marks the `∀ B` all-probe family + Iyer–Wald `iw` as explicit carried hypotheses (continuum
  balls = G8, Iyer–Wald = G10); (3) `T_kk`/stress-flux marked KG/free-field-only + sign/orientation caveat + `hTkk`
  frontier; (4) name-checks confirmed (`entropy_le_cut`, `flow_weak_duality` in `EmergentSpacetime`;
  `QIQTH.ScreenCode.mincut_area_law`); (5) G4 requires an explicit cut/region correspondence (edge surjection alone
  ≠ min-cut invariance); (6) G6 rewritten with `δA`/`Kboost`/`RkkDisc`, `hAK` the carried Einstein-content
  hypothesis, `RkkDisc` a discrete proxy not Ricci; (7) G7 split into G7a (pointwise algebra) + G7b (conditional
  φ-removal, no graviton claim); (8) frontier list extended (`hTkk` localization, continuum modular/vN, interacting
  matter, RT emergence, numerical `G`). **NEXT → G1 (`allBall_firstLaw_iff_residual_zero`).**
- **2026-07-01 — G1 ✅ DONE** (`QIQTH/EmergentDynamics.lean`, namespace `QIQTH.GravDyn`, [AF] std-3, wired into
  `QIQTH.lean` + `AxiomAudit`, budget 0). The **FGHMVR logical skeleton**: `Separating` probe families +
  `residual_eq_zero_of_firstLaw` + **`allBall_firstLaw_iff_residual_zero`** — given a separating probe family and a
  **carried** Iyer–Wald identity `iw : ∀ B, δK B − δS B = P B residual`, the first law `∀ B, δS B = δK B` **⟺**
  `residual = 0`. Pure linear algebra; the `∀ B` all-probe family + `iw` are explicit carried hypotheses (continuum
  balls = G8, Iyer–Wald = G10 — NOT supplied); NOT a physical derivation of Einstein. **NEXT → G2
  (`eq_zero_of_decoder`: a finite decoder identity ⟹ `Separating`).**
