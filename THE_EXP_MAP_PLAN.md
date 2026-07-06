# THE EXPONENTIAL MAP — `HasStrictFDerivAt exp_p id 0` via the equilibrium two-point Grönwall (dodges the C¹-flow gap)

**Status:** CLOSED (S1–S6 all DONE, [AF] std-3, budget 0). **Track:** QG / curved-G.
**Commits LOCAL ONLY** (session no-push). **User explicitly authorized this multi-increment effort.**

## Binding verdict (GPT-5.5-pro's route — the key improvement)
The RNC-existence gate is `exp_p` a local C¹ diffeo at `0`, which needs `HasStrictFDerivAt exp_p id 0` (the inverse
function theorem needs a STRICT derivative — Fréchet-at-a-point is NOT enough: `O(‖v‖²)` does not give the two-point
`o(‖v−w‖)`). **The direct strict-derivative route reaches this WITHOUT the general variational/C¹-flow theorem that
Mathlib lacks** (no Jacobi equation, no global linear existence). Construction at the equilibrium `e=(p,0)`
(`F(e)=0`, `A:=DF(e)`, `A(ξ,η)=(η,0)`, `A²=0`): `ℓ_d(t):=(1+tA)i(d)` is an EXPLICIT linear comparison (`i(v)=(0,v)`);
for `Y_v(t):=φ(t,e+i(v))`, `d:=v−w`, the residual `r(t):=Y_v(t)−Y_w(t)−ℓ_d(t)` solves `r'=A·r+R` with
`R=F(Y_v)−F(Y_w)−A(Y_v−Y_w)`; strict estimate for `F` (`‖F(y)−F(z)−A(y−z)‖≤ε‖y−z‖` near `e`, from bilinearity of
the `Γ(x)(u,u)` term + local Lipschitz/boundedness of `Γ`) × Lipschitz flow dependence (`‖Y_v−Y_w‖≤L‖v−w‖`, PRESENT)
give `‖R‖≤εL‖v−w‖`; **inhomogeneous Grönwall** (`norm_le_gronwallBound_of_norm_deriv_right_le`, PRESENT with the `δ,K,ε`
signature) gives `‖r(1)‖≤Cε‖v−w‖`; projecting `exp_p(v)−exp_p(w)−(v−w)=π₁r(1)` gives `HasStrictFDerivAt exp_p id 0`.
Then `HasStrictFDerivAt.to_localInverse` ⟹ `exp_p` a local diffeo ⟹ normal coordinates exist.

## HONEST HAVE-NOT (binding)
Reaching `exp_p` a local C¹ diffeo is the crux gate — but it is NOT yet the full RNC gauge. Deriving `g(0)=δ`,
`∂g(0)=0`, `∂_{(l}Γ_{jk)}(0)=0` IN the normal coordinates still needs the metric-in-normal-coordinates change of
variables (the 3rd-order geodesic expansion → `∂∂g↔R`). And numerical-G stays gated on `N` (species), `Λ_s` (scale),
`E/ξ` regardless. Never claim numerical-G, the full gauge derived, or a curved heat kernel from this campaign.

## Mathlib inventory (verified, both consults)
PRESENT: `norm_le_gronwallBound_of_norm_deriv_right_le` (inhomogeneous, `Gronwall.lean:134`), `ODE_solution_unique_of_mem_Ioo`
(`:330`), Picard–Lindelöf local existence (`PicardLindelof.lean:834`), Lipschitz-in-IC (`:757`), joint flow continuity
(`:791`), C¹ remainder `norm_image_sub_le_of_norm_fderiv_le'` (`MeanValue.lean:527/550`), `ContDiff.continuous_fderiv`,
`hasFDerivAt_iff_isLittleO`, `HasStrictFDerivAt.to_localInverse`/`ContDiffAt.to_localInverse`, `taylor_mean_remainder_bound`.
Repo: `QIQTH/Geodesic.lean` (`geodesicField`, `contDiff_geodesicField`, `geodesic_local_existence`, `geodesic_local_unique`).
ABSENT: variational/Jacobi flow-in-IC differentiability, global linear-ODE existence, exp-map/RNC — all DODGED by this route.

## Increments (the direct strict-derivative track)
- [x] **S1 — geodesic rescaling `γ_{p,sv}(t)=γ_{p,v}(st)` — DONE (`ExpMap.geodesic_rescale`, 2026-07-06, [AF] std-3).**
  Landed FLOW-FREE (cleaner than planned): stated as a property of ANY integral curve of `F`, not the `Classical.choose`
  flow. `HasDerivAt γ (F(γ t)) t` on `(a,b)` ⟹ `HasDerivAt (τ↦(γ(sτ).1, s•γ(sτ).2)) (F(rescaleCLM s (γ(st)))) t`,
  via the chain rule (`HasDerivAt.scomp` + `HasFDerivAt.comp_hasDerivAt` through `rescaleCLM = fst.prod (s•snd)`) and
  `rescale_field_eq : L_s(s•F w)=F(L_s w)` (quadratic homogeneity of the acceleration, `smul_smul_accel`).
- [x] **S2 — the STRICT derivative of `F` at `e=(p,0)` — DONE (`ExpMap.hasStrictFDerivAt_geodesicField`, 2026-07-06,
  [AF] std-3).** `HasStrictFDerivAt (geodesicField g gi) linF (p,0)` with `linF (ξ,η)=(η,0)` (`= snd.prod 0`) `= DF(e)`.
  Route (cleaner than the ε-δ estimate): `F` is `C^∞` ⟹ `ContDiffAt.hasStrictFDerivAt'` upgrades its Fréchet derivative
  to STRICT; and the Fréchet derivative at `e` is `linF` because the nonlinear part `(x,u)↦Γ(x)(u,u)` is bilinear in
  `u` with `u=0` at `e` (triple-product-vanishing lemma + `hasFDerivAt_pi''`/`.fun_sum`/`.neg`). This IS the strict
  estimate for `F` the plan asked for, in the packaged `HasStrictFDerivAt F A e` form. `exp_p`/`expMap` also DEFINED
  (scaffolding, see below) though not via the ε-δ nbhd.
- [x] **Scaffolding — `geodesicSol` (function) + `expMap` — DONE (2026-07-06, [AF] std-3).** `geodesicSol` = a genuine
  integral curve as a total function (`Classical.choose` of `geodesic_local_existence`) + spec lemmas
  `geodesicSol_zero`/`geodesicSol_hasDerivAt`; `expMap p v := (geodesicSol (p,v) 1).1`. HONEST: the chosen curve solves
  the ODE only on `(−ε,ε)`; `expMap`'s geodesic meaning at `t=1` holds only for small `v` (needs S1 + existence-on-[0,1]).
- [x] **S3 — Lipschitz flow dependence — DONE on the PL interval (`ExpMap.geodesicField_flow_lipschitz`, 2026-07-06,
  [AF] std-3).** Instantiates `IsPicardLindelof.of_contDiffAt_one` on the `C^∞` field at `e=(p,0)` +
  `exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`: a local flow `α` on `closedBall e r` with
  `α x 0 = x`, `α x' = F(α x)`, that is `L'`-Lipschitz in the IC `x`, uniformly for `t∈[-ε,ε]`. HONEST: this is the
  Lipschitz-in-IC on the Picard–Lindelöf interval `[-ε,ε]` — reaching the *unit* interval `[0,1]` for all small `v,w`
  is the tube-management bookkeeping, NOT discharged here.
- [x] **S4 (ODE algebra) — the residual solves `r'=A·r+R` — DONE (`ExpMap.residual_hasDerivAt`, 2026-07-06, [AF]
  std-3).** For any two integral curves `Y₁,Y₂` of `F`, `r(τ)=Y₁τ−Y₂τ−(τ•d,d)` has `HasDerivAt r (A·r(t)+R(t)) t`
  with `A=linF`, `R=F(Y₁)−F(Y₂)−A(Y₁−Y₂)` (from `Y'=F(Y)`, `(τ•d,d)'=(d,0)`, `A·(τ•d,d)=(d,0)`). Flow-independent.
- [x] **S4 (crux, CONDITIONAL) — the two-point Grönwall estimate — DONE (`ExpMap.residual_gronwall`, 2026-07-06, [AF]
  std-3).** Given the integral-curve property of `Y₁,Y₂` on `[0,1]`, `Y₁0−Y₂0=(0,d)`, and a uniform remainder bound
  `‖R(t)‖≤C` on `[0,1]`, `norm_le_gronwallBound_of_norm_deriv_right_le` (δ=0, K=‖A‖, inhomog `C`) gives
  `‖Y₁1−Y₂1−(1•d,d)‖ ≤ gronwallBound 0 ‖A‖ C 1`. With `C=εL‖v−w‖` this is `O(ε)‖v−w‖`. CONDITIONAL on its tube
  hypotheses (the `[0,1]` integral-curve property + the uniform `C`).
- [x] **S4 (existence-on-`[0,1]` half of the tube) — DONE (`ExpMap.geodesicSol_rescale_unit_existence`, 2026-07-06,
  [AF] std-3).** For every direction `v` there is a scale `s=ε/2>0` and a genuine integral curve `γ` with
  `γ 0=(p, s•v)` solving the geodesic ODE on `(-1,2)⊇[0,1]` — `geodesicSol_hasDerivAt` rescaled by `geodesic_rescale`.
  Discharges the existence-on-`[0,1]` half FLOW-FREE (short geodesics `s•v`). HONEST: NOT the uniform-over-a-ball tube.
- [x] **S4′ (unconditional) — the common-tube crux CLOSED: BOTH halves, uniform over a ball — DONE (2026-07-06,
  [AF] std-3).** The flagged reconciliation is now discharged unconditionally over a whole ball via a cleaner route
  than PL re-timing (direct Grönwall + geodesic rescaling on the *uniform* existence ball). Five new theorems in
  `QIQTH/ExpMap.lean`:
  - `geodesicField_equilibrium` — `e=(p,0)` is a zero of `F`.
  - `geodesic_twopoint_gronwall` — the direct two-point bound `dist(Y₁ t)(Y₂ t) ≤ dist(Y₁ 0)(Y₂ 0)·e^{Kt}` on `[0,1]`
    for two curves in a `K`-Lipschitz set `S` (Mathlib `dist_le_of_trajectories_ODE_of_mem`). *This replaces the
    interval-mismatched S3 flow-Lipschitz — Grönwall directly on `[0,1]`, no PL re-timing.*
  - `geodesic_apriori_bound` — the a-priori confinement `dist(Y t) e ≤ dist(Y 0) e·e^{Kt}` (two-point bound against
    the constant equilibrium curve).
  - **`geodesic_unit_tube_existence`** — the EXISTENCE half, UNIFORM over a ball: `∃ρ>0, ∀‖v‖≤ρ`, a genuine integral
    curve through `(p,v)` on `(-2,2)⊇[0,1]`. Uses `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt`
    (UNIFORM existence time `ε` at `e`, no shrinkage over the ball) + rescaling `s=ε/2` stretching `(-ε,ε)` to `(-2,2)`.
    *This is the key: the uniform-`ε` PL ball dissolves the `[-ε,ε]`-vs-`[0,1]` mismatch.*
  - **`geodesic_apriori_confinement`** — the CONFINEMENT half, UNIFORM over a ball: `∃ρ,C₀`, the tube through `(p,v)`
    stays `‖Y t − e‖ ≤ C₀‖v‖` on `[0,1]` (so `Y_v(t)→e` uniformly as `v→0`). The flow's equilibrium trajectory is
    CONSTANT (`α e = e`, by ODE uniqueness against the constant curve on the flow's compact range where `F` is
    Lipschitz), so its Lipschitz-in-IC bounds the rescaled tube. *This dodges the a-priori-bound clopen circularity.*
  **Both halves of the flagged crux (existence + confinement) are now UNCONDITIONAL over a ball.**
- [x] **S5 — `HasStrictFDerivAt exp_p id 0` — DONE (`ExpMap.hasStrictFDerivAt_expMap`, 2026-07-06, [AF] std-3).**
  `HasStrictFDerivAt (expMap g gi hC p) (ContinuousLinearMap.id ℝ (Point n)) 0`. **Definitional bridge fixed via route
  (a):** `expMap` is now DEFINED from the confined `[0,1]` tube — `exists_confined_tube_family` skolemizes
  `geodesic_apriori_confinement`'s per-velocity tube into ONE tube-valued function `expTube` (choice over the guarded
  existential, junk outside the ball), `expMap p v := (expTube p v 1).1`, with `expTube_spec` giving the genuine
  geodesic endpoint for `‖v‖ ≤ expRho`. **`isLittleO` assembly:** for `c>0`, `η := c/(M+1)` with `M = e^{K}·β`,
  `β = gronwallBound 0 ‖A‖ 1 1` (via `gronwallBound_zero_linear`, the `ε`-linearity of the bound); the confinement puts
  `Y_v(t),Y_w(t)` in the S2 `η`-nbhd, the S2 strict remainder (`hasStrictFDerivAt_geodesicField`) gives `‖R‖≤η‖Y_v−Y_w‖`,
  `geodesic_twopoint_gronwall` gives `‖Y_v−Y_w‖≤e^{K}‖v−w‖`, `residual_gronwall` gives `‖r(1)‖≤c‖v−w‖`, and the position
  projection `π₁ r(1) = exp_p v − exp_p w − (v−w)` closes the two-point `o(‖v−w‖)`.  Two mechanical hazards handled:
  the `Classical.choose`-heavy `expTube` is made `irreducible` + fixed as opaque locals (`set … ; clear_value`) so
  `whnf`/`isDefEq` never expand it, and the S2 estimate is unpacked to a bare-point two-argument form so pair
  projections never meet `geodesicField`/`christoffel`'s `whnf`.
- [x] **S6 — `exp_p` local C¹ diffeo at 0 — DONE (`ExpMap.expMap_localInverse`, 2026-07-06, [AF] std-3).**
  `HasStrictFDerivAt.toOpenPartialHomeomorph` (with `id = ↑(ContinuousLinearEquiv.refl …)` invertible) ⟹ an
  `OpenPartialHomeomorph φ` with `⇑φ = expMap`, `0 ∈ φ.source`, and a continuous local inverse `φ.symm` whose strict
  derivative at `expMap 0` is again `id` (via `to_localInverse` + `localInverse_def` + `refl_symm`/`coe_refl`).  `φ.symm`
  IS the normal-coordinate chart. **← the RNC local-diffeo gate, CLOSED.**  HONEST: this reaches a local C¹ diffeo
  ⟹ normal coordinates EXIST as a chart; it does NOT derive the RNC gauge in those coordinates, NOT a curved heat
  kernel, NOT numerical-G.

## Verbatim HAVE / HAVE-NOT
- **HAVE:** "The geodesic exponential map `exp_p` has `HasStrictFDerivAt exp_p id 0` and is a local C¹ diffeomorphism
  at `0` — via a two-point Grönwall estimate at the equilibrium that dodges the (Mathlib-absent) variational/C¹-flow
  theorem. Normal coordinates exist as a chart. Axiom-free std-3."
- **HAVE NOT:** "This is `exp_p`'s strict derivative + local-diffeo only. It does NOT yet derive the RNC gauge in the
  normal coordinates (`g(0)=δ`, `∂g(0)=0`, `∂_{(l}Γ_{jk)}(0)=0` still need the metric-in-normal-coordinates change of
  variables), does NOT build a curved heat kernel, and does NOT move numerical-G (N, Λ_s, E/ξ remain)."

## Failure modes
- **Common-tube management over `[0,1]`** (both consults' #1 stall risk): the flow, `S2`'s nbhd, and `S3`'s Lipschitz
  set must be reconciled on one interval for all small `v,w`. If it resists, land S1–S3 green + checkpoint S4 with the
  exact tube goal. Do NOT force.
- If `norm_le_gronwallBound_of_norm_deriv_right_le`'s hypotheses (right-derivative form) mismatch `r`'s regularity,
  adapt via the `HasDerivWithinAt` form; checkpoint if a genuine regularity gap appears.
- Do NOT attempt the general C¹-flow / Jacobi theorem (G1–G4) — the direct route dodges it; that's the research-grade gap.

## Discipline (every increment)
`lake build QIQTH.<module>` green; `#print axioms` std-3; budget 0; AxiomAudit pins; wire QIQTH.lean; ONE commit
LOCAL ONLY (no push) with the Co-Authored-By trailer; update this plan + inventory. NO `sorry`; NEVER claim
numerical-G, the full gauge, or a curved heat kernel.

## Progress log
- **2026-07 (scoped):** fable consult mapped the targeted T-track (Fréchet only) + general G-track (research-grade).
  **GPT-5.5-pro consult (high) corrected the target:** Fréchet-at-a-point does NOT feed the IFT; the DIRECT
  strict-derivative route (two-point Grönwall at the equilibrium, `A²=0` explicit comparison) reaches
  `HasStrictFDerivAt exp_p id 0` → `to_localInverse` WITHOUT the Mathlib-absent C¹-flow theorem. Crux = S4 (two-point
  Grönwall) + tube management. Increments S1–S6.
- **2026-07-06 (first bricks LANDED):** `QIQTH/ExpMap.lean`, all [AF] std-3, budget 0, wired into `QIQTH.lean` +
  `AxiomAudit.lean`. **S2 CLOSED** (`hasStrictFDerivAt_geodesicField`: `HasStrictFDerivAt (geodesicField g gi) linF
  (p,0)`, `linF (ξ,η)=(η,0)` — via `ContDiffAt.hasStrictFDerivAt'` on the `C^∞` field + the bilinear-vanishing Fréchet
  derivative). **S1 CLOSED** flow-free (`geodesic_rescale` + `rescale_field_eq` + `smul_smul_accel`). **Scaffolding
  CLOSED** (`geodesicSol` function + spec lemmas + `expMap`). Remaining: **S3 (Lipschitz flow dep), S4 (the two-point
  Grönwall crux + common-tube management over [0,1]), S5 (`HasStrictFDerivAt exp_p id 0`), S6 (`to_localInverse` diffeo)
  — all CHECKPOINTED, not started.** S2's `linF` IS the linear comparison `A` that S4/S5 consume. HONEST: this is the
  strict derivative of the ODE FIELD + rescaling + scaffolding — NOT yet `exp_p`'s strict derivative, NOT the diffeo,
  NOT the RNC gauge, NOT numerical-G.
- **2026-07-06 (S3 + S4 LANDED, crux CHECKPOINTED):** `QIQTH/ExpMap.lean`, all [AF] std-3, budget 0. **S3 CLOSED on the
  PL interval** (`geodesicField_flow_lipschitz`: PL flow Lipschitz-in-IC on `closedBall e r` over `[-ε,ε]`, via
  `IsPicardLindelof.of_contDiffAt_one` + `…lipschitzOnWith`). **S4 ODE algebra CLOSED** (`residual_hasDerivAt`:
  `r'=A·r+R`). **S4 crux CLOSED CONDITIONALLY** (`residual_gronwall`: `‖r(1)‖≤gronwallBound 0 ‖A‖ C 1` given the `[0,1]`
  integral-curve property + uniform `‖R‖≤C`; with `C=εL‖v−w‖` this is `O(ε)‖v−w‖`). **Existence-on-`[0,1]` half CLOSED
  flow-free** (`geodesicSol_rescale_unit_existence`: for each `v` a genuine integral curve through `(p,s•v)` on
  `(-1,2)⊇[0,1]`, `s=ε/2`). **CHECKPOINTED — S5 unconditional two-point estimate:** needs the common-tube reconciliation
  over `[0,1]` for a whole ball (one radius `ρ` giving integral-curve-on-`[0,1]` + S2-nbhd containment + S3 Lipschitz
  simultaneously for all `v,w∈ball 0 ρ`; the PL interval is `[-ε,ε]` not `[0,1]`, bridging needs a uniform re-timing).
  Flagged #1 stall risk; validly checkpointed. HONEST: NOT `exp_p`'s strict derivative, NOT the diffeo, NOT the RNC
  gauge, NOT numerical-G.
- **2026-07-06 (S4′ — the common-tube crux CLOSED, both halves):** `QIQTH/ExpMap.lean`, five new theorems, all [AF]
  std-3, budget 0. The flagged #1 stall (common-tube reconciliation over `[0,1]` for a whole ball) is DISCHARGED
  UNCONDITIONALLY via a cleaner route than PL re-timing. **Existence half** (`geodesic_unit_tube_existence`): the
  `C¹` local-existence lemma gives a UNIFORM existence time `ε` over a ball at the equilibrium; rescaling `s=ε/2`
  stretches `(-ε,ε)` to `(-2,2)⊇[0,1]` — dissolving the `[-ε,ε]`-vs-`[0,1]` interval mismatch. **Confinement half**
  (`geodesic_apriori_confinement`): the flow's equilibrium trajectory is constant (`α e = e` by ODE uniqueness
  against the constant curve on its compact range), so Lipschitz-in-IC gives `‖Y_v(t) − e‖ ≤ C₀‖v‖` on `[0,1]` —
  the a-priori boundedness, dodging the clopen circularity. Plus the two Grönwall estimates (`geodesic_twopoint_gronwall`,
  `geodesic_apriori_bound`) via Mathlib `dist_le_of_trajectories_ODE_of_mem`, and `geodesicField_equilibrium`.
  **CHECKPOINTED — S5:** now PURE ASSEMBLY (no missing Mathlib theorem): definitional bridge (pin `expMap` to the
  confined tube endpoint) + the `isLittleO` `η`-juggling feeding confinement + S2 remainder + two-point Grönwall +
  `residual_gronwall`. HONEST: NOT yet `exp_p`'s strict derivative, NOT the diffeo, NOT the RNC gauge, NOT numerical-G.
- **2026-07-06 (S5 + S6 — the exp-map campaign CLOSED):** `QIQTH/ExpMap.lean`, seven new declarations, all [AF] std-3,
  budget 0, pinned in `AxiomAudit.lean`. **Definitional bridge (route a):** `expMap` REDEFINED from the confined `[0,1]`
  tube — `exists_confined_tube_family` skolemizes `geodesic_apriori_confinement` into the tube function `expTube`
  (`expRho`/`expConst`/`expTube` selectors + `expTube_spec`), `expMap p v := (expTube p v 1).1` (the old
  `geodesicSol`-based scaffolding `expMap` was deleted; `geodesicSol` + its lemmas remain). **S5**
  (`hasStrictFDerivAt_expMap`): `HasStrictFDerivAt (expMap g gi hC p) (ContinuousLinearMap.id ℝ (Point n)) 0`, assembled
  through `hasStrictFDerivAt_iff_isLittleO`/`isLittleO_iff` from the S2 strict field remainder + `geodesic_twopoint_gronwall`
  + `residual_gronwall` + `gronwallBound_zero_linear` (new: `ε`-linearity of the Grönwall bound). **S6**
  (`expMap_localInverse`): `HasStrictFDerivAt.toOpenPartialHomeomorph` gives an `OpenPartialHomeomorph φ`, `⇑φ = expMap`,
  `0 ∈ φ.source`, and `HasStrictFDerivAt φ.symm id (expMap 0)` — normal coordinates EXIST as a chart. Two mechanical
  hazards solved: `expTube` (a `Classical.choose` chain) made `irreducible` + fixed as opaque locals via `set`+`clear_value`
  so `whnf`/`isDefEq` never expand it; and the S2 little-o unpacked to a bare-point two-argument form so pair projections
  never trip `geodesicField`/`christoffel`'s `whnf`. **HONEST:** local C¹ diffeo ⟹ normal-coordinate CHART exists; NOT the
  RNC gauge in those coordinates (still needs the metric-in-normal-coordinates change of variables), NOT a curved heat
  kernel, NOT numerical-G (N, Λ_s, E/ξ remain).
