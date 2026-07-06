# THE EXPONENTIAL MAP — `HasStrictFDerivAt exp_p id 0` via the equilibrium two-point Grönwall (dodges the C¹-flow gap)

**Status:** SCOPED (fable + **GPT-5.5-pro** consults, verified against pin v4.30.0). **Track:** QG / curved-G.
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
- [ ] **S1 — geodesic rescaling `γ_{p,sv}(t)=γ_{p,v}(st)` (std-3).** From `geodesic_local_unique` + chain rule
  (`γ''(st)·s² = −Γ(γ)(sγ',sγ') = −s²Γ(γ)(γ',γ')`). (Handles negative `s` via a small interval around 0.) Green.
- [ ] **S2 — `exp_p` def + the strict estimate for `F` at `e` (std-4).** `exp_p(v):=π₁(φ(1,(p,v)))`; prove
  `∀ ε>0, ∃ nbhd of e, ∀ y z in it, ‖F(y)−F(z)−A(y−z)‖ ≤ ε‖y−z‖` from bilinearity of `(x,u)↦Γ(x)(u,u)` + local
  boundedness/Lipschitz of `Γ` (via `contDiff_geodesicField`/`hC`). `A(ξ,η)=(η,0)` is `DF(e)`.
- [ ] **S3 — Lipschitz flow dependence `‖Y_v(t)−Y_w(t)‖≤L‖v−w‖` on `[0,1]` (std-3/4).** Instantiate Mathlib's
  `IsPicardLindelof…lipschitzOnWith` on the common tube (joint continuity gives the tube for small `v,w`).
- [ ] **S4 — the two-point Grönwall estimate (std-5, THE CRUX).** `r=Y_v−Y_w−ℓ_d`, `r(0)=0`, `r'=A·r+R`,
  `‖R‖≤εL‖v−w‖` (S2×S3); `norm_le_gronwallBound_of_norm_deriv_right_le` (δ=0, K=‖A‖, inhomog `εL‖v−w‖`) ⟹
  `‖r(1)‖≤Cε‖v−w‖`. Crux risk: **common-tube management over `[0,1]`** (both consults flag this as the stall risk).
- [ ] **S5 — `HasStrictFDerivAt exp_p (id) 0` (std-4).** Project `exp_p(v)−exp_p(w)−(v−w)=π₁ r(1)` ⟹ two-point
  `o(‖v−w‖)` ⟹ strict derivative (`hasStrictFDerivAt` via the `isLittleO` two-point characterization).
- [ ] **S6 — `exp_p` local C¹ diffeo at 0 (std-4).** `HasStrictFDerivAt.to_localInverse` (id invertible) ⟹ a
  `PartialHomeomorph` inverse `exp_p⁻¹` = the normal-coordinate chart. **← the RNC local-diffeo gate.**

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
