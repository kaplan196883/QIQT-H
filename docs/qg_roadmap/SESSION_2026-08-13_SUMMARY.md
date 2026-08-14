# Session 2026-08-13 — Terminal Synthesis (J4-686 … J4-739)

> ⚠ **HONEST FIREWALL (read first).** Nothing in this session proved `a₁ = R/6`. The whole arc
> below either (a) *discharges conditional analytic inputs* of the CURVED heat-kernel capstone down
> to smaller/named inputs, or (b) *characterizes a genuine wall*. `whiteU1(0) = R/6` is still a
> labelled carrier of the curved chain. `R/6` **is** a proven identity in the older **flat**
> `A1R6FromLabelled` chain — but that chain itself carries an unclosed labelled `hGauss` (see §3f), so
> "the flat chain proves R/6" is a *conditional* theorem, not an unconditional one. Do not upgrade
> either statement past what is written here.

This document consolidates the ~55 ledger entries **J4-686 … J4-739** of `JET4_TOWER_PLAN.md`
into one top-level summary, so future sessions do not (a) re-derive already-proven things or
(b) overclaim. Every claim carries an exact decl name + file path so it is independently checkable.
For the fine-grained per-brick record of Arc A see `WHITENED_CAMPAIGN_TERMINAL.md` §1–8 (this doc
supersedes nothing there; it adds Arcs B/C, the two honest corrections, and the full remaining map).

---

## 1. The three major arcs of this session

### Arc A — the whitened `hInnerCont` continuity campaign (J4-686 → J4-735)

**What it is.** The curved heat-kernel capstone needs the whitened Levi-series inner-pairing
*interior-time continuity* at the concrete curved witness (`n=2`, `κ=−1`, fat gate
`Kset = closedBall 0 2`). It opened (J4-686) carrying a **~40-member** analytic/structural/
measurability/domination/jet/induction/gate/geometry list.

**Trajectory (~35 bricks; full table in `WHITENED_CAMPAIGN_TERMINAL.md` §2).**
- ~40 carries → **one** named analytic input `hflowData` (J4-722,
  `white_final8_joint_witness_sharp`, `QIQTH/WhiteFinal8SharpWitness.lean`), with the reach triple
  discharged by the sharp reach `uniformFlowExp_sharp_reach`.
- `hflowData` was then found to be a **satisfiability wall** at the z₀-independent solver (its
  clause (i) demanded a *global* contraction of the untruncated flow — unprovable). Pivot to the
  **z₀-dependent truncated solver** (J4-732, `hsolveFlow_of_truncatedContractionData`,
  `QIQTH/WhiteHsolveFlowTruncated.lean`), yielding the *satisfiable* feed
  `white_hInnerCont_closed_final9`.
- Final unbundling (J4-735, `white_hInnerCont_final10_conditional`,
  `QIQTH/WhiteHflowTruncConditional.lean`): the opaque bundle → **three transparent, individually
  satisfiable geometric hypotheses**:
  - **`hcontrLip`** — fixed-radius contraction smallness `M < 1` on the truncation window (its
    `O(‖v‖)` linear rate now exposed at the type level via
    `baseFlow_hder_family_fixedRadius`, `QIQTH/BaseFlowHderFamilyFixedRadius.lean`);
  - **`hvLip`** — the uniform v-slot Lipschitz *width* modulus (J4-676's honest, un-removable
    WIDTH WALL — σ-interior-of-`Kset` geometry);
  - **`hfrontImg`** — the null-frontier → sphere-image containment (set-theoretic core banked as
    `frontier_image_ball_subset_image_sphere`, `QIQTH/ImageAnnulusFrontier.lean` — **no injectivity
    needed**).

**Terminal status.** The whitened tower is a machine-checked **conditional entailment on exactly
three named geometric hypotheses** `{hcontrLip, hvLip, hfrontImg}` at the concrete curved witness.
Per strategic review (gpt-5.6-sol) the `hflowData` thread **STOPS** at J4-735 — the residue is three
individually-tractable hypotheses, each with its banked discharge tool identified, not an opaque
bundle. All decls std-3 (`propext`, `Classical.choice`, `Quot.sound`); budget raw 0.

**~8 proved impossibility / vacuity certificates found along the way** (the honesty ledger —
these are *theorems* or Sol-confirmed verdicts that a tempting shortcut is genuinely dead, from
`WHITENED_CAMPAIGN_TERMINAL.md` §3):

| Certificate | File / decl | Proves impossible |
|---|---|---|
| ε₀/τ no-uniform-majorant | J4-685 verdict (`JET4_TOWER_PLAN.md`) | no uniform-in-τ majorant for the width-2 center envelope |
| off-gate hardwiring unsat at fat gate | J4-701 / J4-708 | off-gate vanishing at the general integration variable is unsat at a *fat* gate |
| "w=0 thin wrapper" does not exist | J4-708 support brick | the succ branch uses `hEoffFirst` at the general `w` |
| ∀-radius geometry unsat at bounded gate | `white_hbase_cover_gap` (`WhiteHBaseProducer.lean`) | `hballS ∧ all-R' off-gate cover → False` |
| box-uniform a.e.-`w` slot unsat | `WhiteHtermBoxWGlue.lean` (J4-711 crux) | bad-`w` set has *positive* measure; null-boundary cannot repair the box-uniform interface |
| all-R' off-gate cover ⊥ in-gate reach | J4-709 / J4-711 | reach-alignment obstruction between `htermBox` all-R' and flow-ball chart reach |
| uniform reach bound unsat | J4-711 / J4-701 | no single uniform continuity radius covers all levels |
| `forcedCollar` reach coupling | `white_final8_forcedCollar_reach_gt` (`WhiteFinal8JointWitness.lean`) | crude banked reach `R ≤ (1−c_lin)c/2 < c/2` violates hardcoded `b=c/2` (resolved by the J4-722 *sharp* reach) |
| curved capstone antecedents jointly unsat | `CurvedA1FarConsumeCheck.lean` (cp466, Sol-confirmed) | the earlier "curved-satisfiable a₁=R/6 capstone" is **vacuous** (`hframeK ≡ δ-on-K` forces `K={0}`) |

Plus two center-chart verdicts grounded as theorems (J4-717): `whiteUnvel_center_apply`
(`whiteUnvel κ 0 = id`) and `whiteInvChart_center_eq` (center chart = the genuine inverse chart
`E.symm`).

### Arc B — the R/6 pivot (J4-736 → J4-737)

**The discovery (user-prompted, NOT self-caught — stated honestly).** At J4-735→736 the plan
proposed treating `whiteU1(0) = R/6` as the next grind target. The user's steering note flagged the
**don't-undercredit correction**: `R/6 = ∑ᵢ ricci(0)/6` is **already a proven identity** in the
older *flat* `A1R6FromLabelled` chain — specifically
`VanVleckCancellation.transportCoeff_vanVleck_one_diag` (and the `_infty` sibling
`OmegaHsrcC4cAudit.transportCoeff_vanVleck_one_diag_infty`), conditional on that chain's labelled
`hGauss`. Only the *whitened* chain still assumed `R/6`. This was not caught by the agent's own
search first.

**The discharge (J4-736, `97991704`, `QIQTH/WhiteU1R6Conditional.lean`, 2 decls, std-3).**
- `whiteU1_eq_ricci6_of_smooth` — ★ the whitened `hu1` REDUCED to exactly **three smoothness
  hypotheses**: `{hgTop : ContDiff ℝ ⊤ whiteMetric, hgiTop : ContDiff ℝ ⊤ whiteMetricInv,
  hsrc : ContDiff ℝ ∞ (transport source)}`. Six of the seven gauge/2-jet hypotheses were banked
  from already-proven `whitePullbackMetric_*` theorems (`hg0/hgi0/hdg0/hgsymm/htr/hGauss`, the last
  via the proven `whiteGauss_discharged`, J4-641); `hΓ` derived from `hdg0`.
- `whiteChartKernel1_diagonal_a1_discharged` — the diagonal-a1 theorem with `hu1` supplied.
- Value proven = `(∑ᵢ ricci ĝ_q ĝ⁻¹_q i i 0)/6 = R` (since `ĝ_q(0)=δ`).

**The wall characterization (J4-737, scoping only, no Lean).** The three residual hypotheses are
**GENUINE, not stale**: `hgTop`/`hgiTop` demand `ContDiff ℝ ⊤` where `⊤ : WithTop ℕ∞` is the
**ANALYTIC level ω** (confirmed by the repo's own `OmegaHsrcC4cAudit.lean:280` "the unreachable
analytic ⊤" + the J4-639 note). Both consumers
(`NCRiemannTwoJet.htr_from_hGauss`,
`OmegaHsrcC4cAudit.transportCoeff_vanVleck_one_diag_infty`) require an **analytic** metric, not
merely `C^∞`. The `C⁵` tower built this session
(`ExpMapContDiffFive.expMap_contDiffOn_five` → pointwise `ContDiffAt 4` for the whitened metric via
`WhiteW1.white_metric_entry_contDiffAt4_of_chartC5`) is **infinitely far below** this: closing it
needs Cauchy–Kovalevskaya-class analytic-ODE dependence theory, **absent from Mathlib and the repo**,
and the alternative (finite-order rebasing of the `transportCoeff_vanVleck_one_diag` consumer chain
down from `⊤`) is a large multi-lemma rewrite that would *still* need a global (not pointwise-at-0)
finite-order metric-smoothness bound not currently banked. J4-639's "genuinely open" framing is
confirmed, if anything understated (analytic, not just global `C^∞`).

### Arc C — the mass pre-ρ carrier unification (J4-738 → J4-739)

The center-branch `hmassone` (`curved_hmassone_final_at_gate`) carried the mass pre-ρ pile
`{rS, hKball, hSact, hWslice, hDom}` on a **different gate family** (van-Vleck / `constGate`, not the
flow-ball gate of Arc A). This session collapsed it:

- **J4-738 (`68eae3dd`, `QIQTH/CurvedA1HmassoneReach.lean`, 3 decls, std-3).**
  `curved_hmassone_final_from_reach` — reproduces the `hmassone` limit with **both `hSact` and
  `hWslice` discharged from ONE origin-reach input** (`hSact` = `constGate` membership,
  definitionally = reach, via `constGate_zero_mem_iff_reach`; `hWslice` via the banked carry-free
  `curvedRNC_hWslice_carryFree`). Also noted: Option B (the `K1TransportBudgetW` order-1 `t²` shape
  wall) was scoped and found **ALREADY CLOSED** by `white_K1BudgetW_unconditional_curvedWitness`
  (J4-664) — no live wall there.
- **J4-739 (`96ec59cd`, `QIQTH/CurvedA1HmassoneMassUnified.lean`, 4 decls, std-3).**
  `curved_hmassone_mass_unified` — `hDom` REPLACED by two **already-banked** reach-family facts:
  `hMod` (`curvedRNC_moduli_bound`, J4-532, compact chart-reach) and `hPhase`
  (`curvedRNC_phase_transfer`, J4-533, near-isometry collar), assembled via
  `curvedRNC_baseWitness_dom` (J4-531).

**Final unified mass carrier list:** `{origin-reach (2 radii, J4-738), rS/hKball (trivially fat),
hMod (BANKED), hPhase (BANKED), κ<0 fat base}`. `hDom` is **gone**. ⚠ Honest caveat: `hDom` rests on
the chart-image reach of `uniformInverseChart` — a **distinct** reach-family object from the flow-exp
origin-reach — so the mass pile collapses to **two** distinct banked reach-family inputs, not one
shared input. Satisfiable, but not yet literally instantiated end-to-end into a single closed witness.

---

## 2. The two "don't-undercredit" corrections this session

Both were **prompted by the user pushing back, not self-caught.** This is a recurring failure
pattern (see MEMORY `feedback_dont_undercredit_repo`): grep `QIQTH/` + the AxiomAudit BEFORE
declaring something missing or building a brick.

1. **The fixed-radius phase-ball trick + the abstract flow-derivative theorem already existed.**
   During Arc A's J4-735 sprint the fixed-radius smallness re-derivation was nearly rebuilt from
   scratch before the coordinator escalation surfaced that the technique was already banked as
   `UniformFlowJacobianBound.uniformFlowExp_fderiv_uniform_bound` (the single compact phase-ball
   `S = closedBall (c₀,0) (C₀·ρ_K + Rwin + σ)` sized from `K`/`ρ_K`/`C₀` *before* picking `v`), and
   the generic abstract flow-derivative theorem existed as
   `UniformFlowSecondFDeriv.autonomousFlow_endpoint_hasFDerivAt_window_exists`. The correct move was
   to *reuse* them. Honest sub-verdict recorded (J4-735, `WHITENED_CAMPAIGN_TERMINAL.md` §8.2): the
   abstract theorem supplies only first-jet **existence**, not the near-identity **magnitude** bound
   `‖L − id‖ ≤ Dc·e^K` — that bound still requires the field-specific Grönwall step
   `jacobiEndpoint_base_near_id_bound`, correctly bundled by the banked
   `baseFlow_endpoint_fderiv_near_id_window`. So the reuse is real *and* its limits are characterized.

2. **The "R/6 is never derived" claim was overbroad.** As detailed in Arc B: `R/6` **is** a proven
   identity in the flat `A1R6FromLabelled` chain (`transportCoeff_vanVleck_one_diag`). The correct
   honest statement is narrower: `R/6` is proven in the **flat** chain (conditional on that chain's
   own labelled `hGauss`); only the **whitened** chain still assumed it (now discharged to the
   analytic-smoothness wall, J4-736). Do **not** re-record "R/6 is nowhere derived."

---

## 3. The honest full remaining map for `a₁ = R/6`

Every item below is a *real* residue with its obstruction named. None is closed.

- **(a) Whitened tower's 3 hypotheses** `{hcontrLip, hvLip, hfrontImg}` (J4-735,
  `WhiteHflowTruncConditional.white_hInnerCont_final10_conditional`). Individually satisfiable, each
  with a banked discharge tool identified; **not yet instantiated end-to-end**. `hvLip` is the honest
  un-removable WIDTH WALL (J4-676).
- **(b) The analytic-smoothness wall for `whiteU1 = R/6`** `{hgTop, hgiTop, hsrc}`
  (`WhiteU1R6Conditional.whiteU1_eq_ricci6_of_smooth`, J4-736). **Genuinely hard**: needs
  analytic (ω-level) metric smoothness, i.e. Cauchy–Kovalevskaya-class analytic-ODE dependence theory
  absent from Mathlib and the repo (J4-737). Not a near-term target.
- **(c) The two mass-side reach-family inputs** — origin-reach (2 radii) + chart-image reach
  (J4-738/739). **Satisfiable but not literally instantiated** end-to-end; they live on a different
  gate family from (a).
- **(d) The Duhamel / heatOp / Levi domination pile beyond `hmassone`** — the `{h0, h1, hΔ}`
  discharge, Duhamel-split integrability, and the remaining fat-K carrier piles + capstone
  co-instantiation (flagged in J4-736's own honest residue line). Orthogonal to (a)/(b).
- **(e) The capstone arrow census** (~31 arrows; full census in `A1_R6_RESIDUE_STATUS.md`). Reduced
  hard through J4-311/312/313 (`hDuhamel`, `hDConv`, and all three inner CConv-facade arrows are now
  theorems), but **`hCConv` is walled at the `hEgrad` third-jet layer**: the field-slot chart is only
  `C²`, and `hCConv` at full strength wants a `C¹→C²` step on the **third** jet — a genuine 3–5-brick
  development (`A1_R6_RESIDUE_STATUS.md` §hCConv; `WHITENED_CAMPAIGN_TERMINAL.md` §4d). This is the
  capstone-side analog of the *same* regularity-order wall Arc A and Arc B both hit.
- **(f) `R/6` itself** — **PROVEN in the flat chain**
  (`VanVleckCancellation.transportCoeff_vanVleck_one_diag`), but that chain carries its **own**
  unclosed labelled `hGauss`. ⚠ Do **not** call the flat chain unconditional either. The curved
  witness carries `whiteU1(0) = R/6` as a labelled input, discharged in J4-736 only *down to* the
  analytic-smoothness wall (b).

**Recurring structural theme.** Walls (a)-`hcontrLip`, (b), and (e)-`hEgrad` are the *same*
phenomenon at three sites: the machinery delivers **first-order base regularity at a point**, and
each capstone arrow wants **one order higher / uniform-over-a-set / analytic** smoothness. This is the
single mathematical shape blocking the curved `a₁ = R/6`.

---

## 4. So — is `a₁ = R/6` done? (plain-language skim)

**No.** For a *general curved* metric, `a₁ = R/6` is **not** proven and is not claimed. What is true,
stated precisely and without inflation:

- The **flat** heat-kernel tower derives `a₁ = R/6` (conditional on a labelled Gaussian input in that
  chain), and `R/6 = ∑ᵢ ricci(0)/6` is a genuine proven identity there.
- The **curved** capstone is a *conditional* theorem: it would entail `a₁ = R/6` at the concrete
  curved witness **given** a handful of named analytic inputs. This session did honest, real work
  shrinking those inputs — a ~40-member continuity carry list down to three explicit geometric
  hypotheses, the `R/6` carrier down to three smoothness hypotheses, and the mass pile down to two
  banked reach-family facts — and, just as importantly, **characterized precisely why the last steps
  are hard**: they need smoothness one order higher (up to full analyticity) than anything the tower
  banks, and Mathlib simply does not contain the analytic-ODE-dependence and joint `C²`-in-basepoint
  theory required. So the curved result is a well-mapped conditional entailment with its remaining
  inputs named and its hardest wall (analytic smoothness) identified as needing new, Mathlib-absent
  foundational theory — **not** a finished theorem, and not a short hop from one.

---

*Ledger: J4-740 (this writeup). Docs only; no Lean; nothing committed; nothing wired into
`QIQTH.lean`/`AxiomAudit`. Sources: `JET4_TOWER_PLAN.md` J4-686…J4-739,
`WHITENED_CAMPAIGN_TERMINAL.md` §1–8, `A1_R6_RESIDUE_STATUS.md`, `WHERE_WE_ARE.md`.
⚠ NOT `a₁ = R/6`.*
