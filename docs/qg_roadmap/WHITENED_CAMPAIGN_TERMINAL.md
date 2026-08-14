# The Whitened `hInnerCont` Campaign — Terminal Writeup (J4-723)

> ⚠ **HONEST FIREWALL (read first).**  This document, and the entire whitened `hInnerCont`
> campaign it summarizes, is **NOT** `a₁ = R/6` and proves **nothing** about `R/6`.  `R/6`
> remains a **labelled carrier** (`whiteU1(0) = R/6`), untouched.  The **flat** heat-kernel tower
> that establishes `a₁ = R/6` is non-vacuous; the **curved** capstone chain is **CONDITIONAL** —
> it carries labelled analytic inputs, of which the whitened-continuity campaign was one, and now
> discharges that one down to a **single** named base-varying-flow contraction input, `hflowData`.
> **An `R/6` carrier is not an `R/6` proof.**  The result below is a *conditional entailment*:
> *given* `hflowData` (a genuine, un-banked analytic regularity fact about the curved geodesic
> flow), the whitened inner-pairing interior-time continuity holds at the concrete curved witness.

This is the terminal ledger for the `hInnerCont` sub-tower of the Jet-4 curved heat-kernel program
(ledger entries **J4-686 … J4-722** in `JET4_TOWER_PLAN.md`).  It records: (1) the result; (2) the
arc of ~35 bricks that took the carry list from ~40 members to 1; (3) the proved
impossibility/vacuity certificates (the honesty ledger); (4) the honest remaining-gap map; and
(5) the `hflowData`/J3 scoping verdict with the cheapest honest route.

---

## 1. The Result

Two theorems, both **std-3** (`propext`, `Classical.choice`, `Quot.sound`), no `sorry`, no new
axioms, no `:= True`, no vacuous/unsatisfiable hypothesis, both wired into
`QIQTH.lean` + pinned in `AxiomAudit.lean` (std-3 verified in the mainline build):

- **`white_hInnerCont_closed_final8`** — `QIQTH/WhiteHsolveFlowContraction.lean` (J4-720).
  The whitened inner-pairing interior-time continuity, gate-parametric, with the Lipschitz-solver
  residual `hsolveFlow` **dissolved** (discharged internally by a fully proven Banach fixed point,
  `hsolveFlow_of_contractionData`).  **Zero analytic residuals beyond the single honest input
  `hflowData`.**

- **`white_final8_joint_witness_sharp`** — `QIQTH/WhiteFinal8SharpWitness.lean` (J4-722).
  The reach-discharged **joint cp466 witness**: at the **concrete curved witness**
  (`n = 2`, `κ = −1`, fat gate `Kset = closedBall 0 2`, flow-ball gate `S`, collar `a = c/4`,
  `b = c/2`, shared radius `c` shrunk into a common small-`c` window), *all* the standard carries
  are co-instantiated with **no conflict** and the reach triple `{R, hballS, hballC, hbR}` is
  **discharged internally** via the sharp reach.  The strengthened witness carries **ONLY**
  `hflowData`.  Conclusion is non-vacuous (nonempty time window `Ioc 0 1`).

**The exact shape of `hflowData`** (verbatim from `WhiteHsolveFlowContraction.lean`), for
`φ_w := uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKfat w` (the
base-`w` geodesic-flow / exp-map endpoint):

```
∀ z₀, ∃ (Kc Cv : ℝ≥0), Kc < 1 ∧
  -- (i) uniform-over-w CONTRACTION in the base slot, one constant Kc < 1 for every sphere direction v:
  (∀ v ∈ sphere 0 c, ContractingWith Kc (fun w => z₀ - φ_w v + w)) ∧
  -- (ii) uniform LIPSCHITZ-in-direction v of the flow image, one modulus Cv over all bases w:
  (∀ v v' ∈ sphere 0 c, ∀ w, dist (φ_w v) (φ_w v') ≤ Cv * dist v v') ∧
  -- (iii) frontier → sphere-image containment (the null-frontier is a C¹ sphere image):
  {w | z₀ ∈ frontier (S w)} ⊆ {w | ∃ v ∈ sphere 0 c, φ_w v = z₀}
```

The Banach solver turns `hflowData` into `hsolveFlow` by `H v := ContractingWith.fixedPoint
(w ↦ z₀ − φ_w v + w)`: the fixed-point equation gives the solver `φ_{H v} v = z₀`;
`fixedPoint_lipschitz_in_map` makes `H` Lipschitz with constant `Cv/(1−Kc)`; uniqueness lands the
bad base set inside `H '' sphere`, which is null (Lipschitz image of a sphere).

---

## 2. The Arc — from a ~40-member carry list to 1

The `hInnerCont` sub-tower opened (J4-686) needing the whitened Levi-series inner-pairing time
continuity with **every** structural, measurability, domination, jet-regularity, induction, gate,
and geometry input carried.  ~35 bricks later the carry list is a single analytic input.  The
major discharges, in order:

| # | Brick / decl | What it discharged |
|---|---|---|
| J4-686 | route (β) reconciliation | whitened↔van-Vleck dom-pkg reconciliation |
| J4-687 | `white_hBdom` (all-rows) | whitened Bochner domination |
| J4-688 | `curved_hInnerCont_of_dominations` | width/witness-generic `hInnerCont` **builder** |
| J4-689 | `white_hWdom` | whitened value-kernel Gaussian domination |
| J4-690 | `white_gate_package_combined` | **co-emitting gate discharger** (one gate `S` emits all suppliers) |
| J4-691 | `S1` (whitened-defect `tripleHEmeas`) | joint measurability; carries → `{hmeas, hcont}` |
| J4-692 | convergence trio | `LeviSeriesLocalData`/`hFsum` extraction |
| J4-693 | `hcont` witness factor | Levi time-continuity witness factor; carry → `hJoint` |
| J4-694 | width-generic Levi **M-test** | `htermBox` termwise joint continuity replay |
| J4-695 | `hmajor` + `hbase` split | τ-gate affine dissolution of the majorant |
| J4-696 | `white_hRepCont` | indicator collapse + chart-continuity composition |
| J4-697 | `white_hVcont` | flow-ball `ContinuousAt` export; `hLcont` → jets |
| J4-698 | `white_hGradCont`, `white_hHessCont` | first/second spatial-jet joint continuities; `hbase` Δ_z side fully discharged |
| J4-699 | `hEmeas` + `hmajor` | `hInnerCont` → single carry `htermBox` |
| J4-700 | `white_htermBox_of_flowBall_hcont` | `htermBox` measurability + bound carries; sole carry `hcont` |
| J4-701 | gate-vanishing extension | reach-alignment killed (kernel ≡ 0 off gate) |
| J4-702 | Gap-A | base-`w` whitened kernel continuity |
| J4-703 | Gap-A a.e.-`w` assembly | `hcontE` slot at the whitened kernel |
| J4-704 | S-dom + Gap-B | per-level `hcont` assembled |
| J4-705 | `hjoint` induction tie | closed the Nat.rec fixpoint (rescaled-window monotonicity) |
| J4-706 | `white_hInnerCont_of_geometry` | gate-threading (internal gate instantiation) |
| J4-707 | ∃-shape wrapper | supplier co-instantiation at internal radius `c` |
| J4-708 | cp466 correction + support brick | fixed the w=0-restriction error; support brick |
| J4-709 | per-level stitch | three-route verdict, per-level continuity radius |
| J4-710 | `..._of_flowBall_at_set` | **set-generic** locality (the `closedBall 0 R` was a wrapper artifact) |
| J4-711 | vanishing-leg glue | pointwise null-frontier interface (the crux interface theorem) |
| J4-712 | glue wired into level induction | `white_htermBox_unconditional_k_cover` (cover induction) |
| J4-713 | `hInterior` | strict non-circular Nat.rec recursion; `hInterior` closed |
| J4-714 | `white_hlegA_of_reach` | leg-(a) reparam family (neighborhood transfer from `_at_set`) |
| J4-715 | `white_hbase_producer` | `hbase` producer + **width-wall gap** certificate |
| J4-716 | cutoff-collar | `whiteDefectKernel_collar_vanishing_open`; width wall closed |
| J4-717 | combined route + junk verdict | `whiteInvChart_center_eq`; reroute to on-gate collar |
| J4-718 | `white_hgateCollar_of_reach` | **on-gate collar discharge**; sole residual `{hnull}` |
| J4-719 | `hnull` reduction | codim-1 null-image core (`dimH_sphere` built); `hnull` → `hsolveFlow` |
| J4-720 | `hsolveFlow_of_contractionData` | **Banach solver**; sole input `hflowData` |
| J4-721 | `white_final8_joint_witness` | joint cp466 audit; carries `{hflowData, reach triple}` |
| J4-722 | `uniformFlowExp_sharp_reach` | **sharp reach**; reach triple discharged; carries ONLY `hflowData` |

The pivotal structural moves: **J4-711** (the *pointwise* null-frontier interface —
`continuousWithinAt_of_dominated` with `z₀` fixed makes `{w | z₀ ∈ frontier(S w)}` null, repairing
the box-uniform quantifier order that was genuinely unsatisfiable); **J4-710** (the locality
insight that killed the finite-cover machinery); **J4-719** (building `dimH_sphere` from scratch to
get "Lipschitz image of a sphere is volume-null"); **J4-720** (the Banach fixed point that turned
the last inverse-solvability question into named contraction data).

---

## 3. The Honesty Ledger — proved impossibility / vacuity certificates

Each of these is a **theorem** (or a Sol-confirmed scoping verdict) establishing that a *tempting
shortcut is genuinely dead*, not merely unattempted.  They are the load-bearing evidence that the
surviving `hflowData` input is real and not an artifact of a mis-stated hypothesis.

| Certificate | File / decl | What it proves impossible |
|---|---|---|
| ε₀/τ no-uniform-majorant | (J4-685 verdict, `JET4_TOWER_PLAN.md`) | no uniform-in-τ majorant exists for the width-2 center envelope; no sound absorption |
| off-gate hardwiring unsat at fat gate | J4-701 / J4-708 | hardwiring off-gate vanishing at the general integration variable is unsat at a **fat** gate |
| all-`w` `hEoffFirst` ⊥ `hcover` | J4-708 support brick | the "w=0 thin wrapper" does **not** exist; the succ branch uses `hEoffFirst` at the general `w` |
| ∀-radius geometry unsat at bounded gate | `white_hbase_cover_gap` (`WhiteHBaseProducer.lean`) | `hballS ∧ all-R' off-gate cover → False` (a sup-norm-R point sits in `S 0 ⊆ closure(S 0)`) |
| box-uniform a.e.-`w` slot unsat | `WhiteHtermBoxWGlue.lean` (J4-711 crux verdict) | for `K ⊇ gate frontiers` the bad-`w` set has **positive measure**; the null-boundary fact cannot repair the box-uniform interface |
| all-R' off-gate cover ⊥ in-gate reach | J4-709 / J4-711 | reach-alignment obstruction: `htermBox` all-R' vs flow-ball chart reach are incompatible |
| uniform reach bound unsat | J4-711 / J4-701 | no single uniform continuity radius covers all levels; killed by the pointwise interface instead |
| `forcedCollar` reach coupling | `white_final8_forcedCollar_reach_gt` (`WhiteFinal8JointWitness.lean`) | the value supplier hardcodes `b=c/2` ⟹ `hbR` forces `R>c/2`; the *crude* banked reach delivers only `R ≤ (1−c_lin)c/2 < c/2` (resolved by the J4-722 **sharp** reach, not a contradiction) |
| curved capstone antecedents jointly unsat | `CurvedA1FarConsumeCheck.lean` (cp466, Sol-confirmed) | the earlier "curved-satisfiable a₁=R/6 capstone" is **vacuous** at the genuinely-curved witness (`hframeK ≡ δ-on-K` forces `K={0}`); see MEMORY `qiqth_jet4_tower_complete` |

Two further *center-chart* verdicts (grounded as theorems, J4-717): `whiteUnvel_center_apply`
(`whiteUnvel κ 0 = id`) and `whiteInvChart_center_eq` (center chart = the genuine uniform inverse
chart `E.symm`) — the "all-beyond-R `hcollar`" is genuinely **undecidable** at the concrete chart
outside the reach image (junk far-field), which is why the discharge had to reroute to the *on-gate*
collar.

---

## 4. The Remaining Map (honest)

### 4a. `hflowData` — the J3 base-varying contraction blocker (the ONE surviving input)

**State** (from `WhiteHsolveFlowContraction.lean` §1, the w-regularity verdict).  The solver needs a
**uniform-over-base-`w`, Lipschitz-in-`w` contraction** of `w ↦ z₀ − φ_w v + w` with constant
`< 1`, plus **Lipschitz-in-direction-`v`** of `φ_w`, plus the **frontier→sphere-image** containment.
What is **banked** is only *pointwise-at-the-centre first-order* base-varying data:

- `BaseVaryingIFTPackage.baseVaryingChart_hasFDerivAt_center` — `fderiv Wbv 0 = -id` for the
  base-slot inverse chart, from the base-`0` displacement bank (**unconditional**);
- `BasepointFDeriv.geodesicBasepoint_endpoint_hasFDerivAt_exists` — the base-point **first**-order
  Fréchet derivative of the flow endpoint **at the centre**, with quadratic remainder;
- `BaseVaryingIFTPackage.baseVaryingIFTPackage` — the full change-of-variables bundle, but
  **CONDITIONAL** on the un-banked base-slot `C²` input `hbaseC2 : ContDiffAt ℝ 2 Wbv 0` (the
  recognized "J3 blocker").

A uniform-over-`w`, `<1`-contraction bound is **not** banked and **not** cheaply derivable from
pointwise-at-centre data.  The two undischarged sub-inputs are:

- **`hbaseC2`** (`BaseVaryingIFTPackage`) — `C²` of the base-slot inverse chart at `0`;
- **`hFoplip`** (`BasepointJetLipschitz`) — the concrete flow-side operator `q`-Lipschitz bound
  `‖fderiv²(Fam q) v − fderiv²(Fam q') v‖ ≤ Λ·dist(q,q')` (the second-order weld residual).

See §5 for the scoping verdict and cheapest route.

### 4b. Mass pre-ρ carriers (different gate family)

Pile 2 (`curved_hmassone_final_at_gate`): the mass pre-ρ carriers `{rS, hKball, hSact, hWslice,
hDom}` remain **open** — entangled quantifiers on a **different gate family** (van-Vleck /
`constGate`, not the flow-ball gate of the `hInnerCont` chain).  Nothing cheap; not on the
`hInnerCont` critical path.

### 4c. `K1TransportBudget` — the k=1 shape wall

Pile 3: the order-0 witness is an `O(t)` ceiling; the required `t²` is **provably out of reach** for
the current shape.  The fix is a `p`-dependent transported `u₁` (**J4-636**, transported first heat
coefficient) — out of scope of this campaign.

### 4d. The capstone arrows census — `hCConv` third-jet wall

From `A1_R6_RESIDUE_STATUS.md`: the curved-`a₁=R/6` capstone `a1_R6_of_residue` chain has its
`hCConv` reduced through L1 layers `{D, hConvDeriv, hConvD1}` (J4-155/158) down to *gcoef
dominated-convergence continuity + the C4b s-domination bundle*, but the underlying **`hEgrad`
third-jet layer** is a genuine 3–5-brick development: the field-slot chart is currently only `C²`,
and `hCConv` at full strength wants a `C¹→C²` step on the **third** jet.  This is the capstone-side
analog of the same regularity wall the `hInnerCont` campaign hit — smooth dependence one order
higher than what is banked.

### 4e. `a₁ = R/6` itself — the labelled carrier

`whiteU1(0) = R/6` is carried as a **labelled input**, not derived at the curved witness.  The
**flat** heat-kernel tower establishing `a₁ = R/6` is **non-vacuous**.  The **curved** capstone
chain is **CONDITIONAL**: it entails `a₁ = R/6` *given* its labelled analytic inputs, of which the
whitened continuity was one (now reduced to `hflowData`).  **The campaign closed one conditional
arrow to a single named input; it did not prove `a₁ = R/6`.**

---

## 5. `hflowData` / J3 Scoping Verdict

**Files read:** `GeodesicSmoothDep.lean` (451L), `BasepointSmoothDep.lean` (256L),
`BaseVaryingIFTPackage.lean` (236L), `BasepointFDeriv.lean` (260L), `BasepointJetLipschitz.lean`
(170L), `ExpMapContDiffFive.lean` (132L), `CurvedRNCGaussWitness.lean` (metric def).

### What exists (banked)

- **First-order base-point smooth dependence, DERIVED.**  `BasepointSmoothDep` /
  `BasepointFDeriv`: for a linearly base-perturbed geodesic family, the flow endpoint `δ ↦ W δ t`
  has a genuine **Fréchet derivative** at the base point equal to the endpoint Jacobi map `L`
  (`geodesicBasepoint_endpoint_hasFDerivAt_exists`), with a **quadratic** remainder
  `‖W δ t − W 0 t − V δ t‖ ≤ C‖δ‖²`.  This is `o(‖δ‖)` — genuine C¹-in-base regularity — carrying
  only geometric inputs (`S` convex, field `C²` bound `‖∂²F‖ ≤ M₂` on `S`, field Lipschitz,
  Jacobi-coefficient bound `‖DF‖ ≤ K`, tube containment, supplied Jacobi solution).
- **Two-point Grönwall Lipschitz-in-base.**  `geodesic_twopoint_gronwall`:
  `‖Y s t − Y 0 t‖ ≤ C_L·|s|` — a Lipschitz-in-base bound *already exists* along the tube.
- **`C⁵`-in-direction of the exp map.**  `ExpMapContDiffFive.expMap_contDiffOn_five`: `exp_p` is
  `ContDiffOn ℝ 5` on the injectivity ball — **but only in the direction slot `v`, at fixed base
  `p`.**  Gives the Lipschitz-in-`v` half of `hflowData` (ingredient (ii)) essentially for free.
- **The metric is polynomial in the coordinates.**  `curvedRNCMetric K x i j =
  δ_{ij} − (K/3)(‖x‖²δ_{ij} − x_i x_j)` is `C^∞` (`curvedRNCMetric_contDiff`), and `curvedRNCInv`,
  `curvedRNC_hChr` are smooth in the coordinates.  So there is **no metric-smoothness obstruction**;
  the geodesic *field* `F(x,ẋ)` is `C^∞` jointly in position and velocity.
- **Frontier→sphere-image (ingredient (iii)).**  Already available in spirit from J4-717/718:
  `frontier(S w) ⊆ φ_w '' sphere 0 c` at the flow-ball gate `S w = φ_w '' ball 0 c` (openness of the
  flow image on the reach); this is the containment `hflowData` (iii) demands.

### What is missing (the gap)

The blocker is **not** smoothness of the metric or of the flow in the *direction* slot — both are
banked.  The gap is exactly two facts, both about **base-slot** (starting-point `w`) regularity
uniform over a *range* of bases (not just at the centre):

1. **`hbaseC2 : ContDiffAt ℝ 2 Wbv 0`** (`BaseVaryingIFTPackage`) — `C²` of the base-slot inverse
   chart.  The banked base facts are `C¹`-at-the-centre (fderiv `= -id`, quadratic remainder); the
   IFT bundle needs one derivative more, **in the base slot**.
2. **`hFoplip`** (`BasepointJetLipschitz`) — the concrete flow-side operator `q`-Lipschitz bound on
   the **second** derivative, uniform over the base set.  This is the second-order weld residual
   `‖fderiv²(Fam q) v − fderiv²(Fam q') v‖ ≤ Λ·dist(q,q')`.

Both are the *same order-mismatch* seen throughout the tower: the machinery delivers first-order
base regularity at a point; `hflowData`'s uniform contraction wants second-order / uniform-over-a-set
base regularity.  A uniform-over-`w` contraction with constant `< 1` is precisely a *uniform* bound
on `‖∂_w(φ_w v − w)‖ < 1` over the base ball — which needs `C²`-in-base (to control how `∂_w φ_w`
varies) plus the concrete `hFoplip`.

**Does a C² joint smoothness of `(w,v) ↦ φ_w v` exist anywhere?**  **No — not banked.**
`ExpMapContDiffFive` gives `C⁵` **in `v` at fixed base**.  `GeodesicSmoothDep`/`BasepointFDeriv`
give `C¹` **in `w` at the centre** (with a quadratic remainder, i.e. the *existence* of the
first base-derivative, not a `C²` joint statement).  The **joint** `(w,v)` `C²` regularity — the
object that would immediately yield `hflowData` — is exactly the un-banked statement, blocked at
`hbaseC2`/`hFoplip`.

### The cheapest honest route

The geodesic field `F` is `C^∞` **jointly** in `(x, ẋ)` because the metric is polynomial
(`curvedRNCMetric_contDiff`) and the Christoffel symbols are rational in smooth data with nonvanishing
denominator near `0`.  The standard ODE fact — *the flow of a `C^k` vector field is jointly `C^k` in
`(time, initial condition)`* — is **exactly** what closes the gap, but it is the primitive Mathlib
lacks (only Picard–Lindelöf **Lipschitz**-in-IC is available; the repo built the `C¹` layer by hand
via Grönwall residuals).  The cheapest honest route, in increasing cost:

1. **Discharge `hbaseC2` directly from the polynomial field** by lifting the existing
   `geodesicVariation_residual_bound` machinery **one order**: the repo already proves the
   *first-order* uniform field remainder (`geodesicField_uniform_C1_remainder`) and carries the
   *second-order* remainder `‖F a − F b − DF(b)(a−b)‖ ≤ M‖a−b‖²` as the labelled gap
   (`GeodesicSmoothDep` honest checkpoint).  Because `F` is **polynomial-smooth**, that second-order
   uniform Taylor remainder is *provable* (finite-degree Taylor with explicit remainder on a convex
   compact set) — this is the single missing lemma named in `GeodesicSmoothDep`.  Proving it
   discharges `hbaseC2` and, with `jacobiSol_unique` (linearity engine, already banked), lifts
   `BasepointFDeriv` to a **second**-order base jet.
2. **From the second-order base jet, assemble the uniform contraction** by a mean-value bound:
   `∂_w(φ_w v − w) = D_w φ_w v − Id`, and near the centre `D_w φ_w v ≈ Id + O(‖v‖ + ‖w‖)` (the
   Jacobi map is `Id` at `v=0`), so a small-radius window makes `‖∂_w(φ_w v − w)‖ ≤ Kc < 1` uniformly
   — the same small-`c` window already used for the sharp reach (`ρwin` in
   `WhiteFinal8SharpWitness.lean`).  This is a Grönwall/MVI argument on top of step 1, not new
   geometry.
3. **`hFoplip`** (`BasepointJetLipschitz`) is only needed for the *full joint 2-jet continuity*
   route; the contraction bound of step 2 does **not** require it if the window is taken small enough
   that the first-order base jet plus its quadratic remainder already give `< 1`.  So the *minimal*
   path is **step 1 (the uniform C² field remainder) → step 2 (the small-window MVI contraction)**,
   bypassing `hFoplip`.

**Verdict:** `hflowData` is **not** an intractable wall — it is the *one-order-up* lift of the
already-banked base-point first-order smooth-dependence machinery, and the missing lemma (the uniform
**second-order** Taylor remainder of the polynomial geodesic field on a convex compact) is explicitly
named and *provable in principle* from the polynomial structure of `curvedRNCMetric`.  It is a
genuine multi-brick development (the C²-in-base ODE smooth-dependence Mathlib lacks), not a
`Classical.choose`-blocked or provably-vacuous obstruction.  It is honestly one analytic input, and
the cheapest route is the two-step lift above.

---

## 6. Bottom line

- **What landed:** the whitened `hInnerCont` interior-time continuity is fully audited at the
  concrete curved witness (`white_hInnerCont_closed_final8` + `white_final8_joint_witness_sharp`),
  carrying **exactly one** analytic input, `hflowData`, with every other structural, measurability,
  domination, jet, induction, gate, reach, and null-frontier input **discharged** — and a matching
  **honesty ledger** of eight+ proved impossibility/vacuity certificates showing the shortcuts are
  genuinely dead.
- **What it is not:** it is **not** `a₁ = R/6`.  `R/6` is a labelled carrier; the flat tower is
  non-vacuous; the curved capstone chain is **CONDITIONAL** and, beyond `hflowData`, still carries
  the mass pre-ρ pile, the `K1Transport` k=1 shape wall, and the `hCConv`/`hEgrad` third-jet wall.
- **The one input, scoped:** `hflowData` is the base-varying-flow uniform contraction — a
  one-order-up lift of the banked base-point first-order smooth-dependence, closable via the named
  (and structurally provable) uniform second-order Taylor remainder of the polynomial geodesic field.

*Ledger: J4-723 (this writeup).  std-3 throughout; budget raw 0; nothing committed here; nothing
wired into `QIQTH.lean`/`AxiomAudit`.*
