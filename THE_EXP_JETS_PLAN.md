# THE EXP-MAP HIGHER JETS — discharge the RNC gauge via equilibrium-anchored finite-order jets (NOT the general smooth-dependence theorem)

**Status:** SCOPED (**GPT-5.5-pro** consult, high — overturns the prior "gated on general smooth-dependence" verdict).
**Track:** QG / curved-G. **Commits LOCAL ONLY** (session no-push). **User explicitly authorized the bold effort.**

## Binding verdict (GPT-5.5-pro — the correction)
Discharging the RNC campaign's carried gauge (`g̃(0)=δ`, `∂g̃(0)=0`, `∂_{(l}Γ̃^i_{jk)}(0)=0` in the exp-map normal
coordinates) needs only the FINITE Taylor coefficients of the pullback metric `g̃(y)=g(exp_p y)·D exp_p(y)·D exp_p(y)`
at `y=0` — i.e. finitely many jets of `exp_p` at the SINGLE point 0. These are reachable by the SAME equilibrium
two-point-Grönwall technique that already proved `HasStrictFDerivAt exp_p id 0` (`ExpMap.lean`), extended one/two
orders up — **NOT** the general variational/C¹-flow theorem Mathlib lacks (that is overkill). The equilibrium
structure (`A=DF(e)`, `A²=0`, confinement `‖Y_v(t)−e‖≤C₀‖v‖`) anchors every estimate at `e`. **HONEST HAVE-NOT:**
discharging `hgauge` makes `κ=1/6` unconditional GIVEN the metric — it does NOT reach numerical-G (`N`, `Λ_s`, `E/ξ`
remain). Never claim numerical-G or a curved heat kernel.

## The concrete route (GPT-5.5-pro)
- **Value 2-jet:** second difference `Δ_{v,w}(t)=z_{v+w}−z_v−z_w` (`z_v:=Y_v−e`), state 2-jet `B_t` (`B'=AB+H(L_tv,L_tw)`,
  `H=D²F(e)`, `π₁B_1(v,w)=−Γ_p(v,w)`, `L_tv=(tv,v)`), residual `q=Δ−B_t`: `q'=Aq+E`, `‖E‖≤Cε‖v‖‖w‖+Cδ‖q‖` (2nd-diff
  Taylor bound of `F` at `e` + confinement + the 1-jet), inhomog Grönwall ⟹ `q(1)=o` ⟹
  `exp_p(v)=p+v−½Γ_p(v,v)+o(‖v‖²)` (`D²exp_p(0)=−Γ_p` by polarization from the radial 2-jet, already proven).
- **Value 3-jet:** state 3-jet `C_t` (`C'=AC+K(L_tv,…)+H(B_t,L_t·)` terms, `K=D³F(e)`), diagonal residual
  `r_3=z_v−L_tv−½B_t−⅙C_t`, `‖error‖≤Cε‖v‖³+Cδ‖r_3‖`, Grönwall ⟹ `r_3(1)=o(‖v‖³)`.
- **Jacobian field expansion (the genuine subtlety — `g̃` uses `fderiv exp_p y`):** `DF(e+z)=A+H(z,·)+½K(z,z,·)+o(‖z‖²)`;
  the localized first-variation `HasFDerivAt (v↦Y_v(t)) (J_t(v)) v` for `v` near 0 (`J'=DF(Y_v)J`, `J(0)=(0,h)`), then
  `J_t(v)h=L_th+B_t(v,h)+½C_t(v,v,h)+o(‖v‖²)‖h‖` — again equilibrium Grönwall. `⚠ fderiv` may be junk off the
  differentiability set — establish local differentiability FIRST.

## Increments
- [x] **EXP-JET1 — the value 2-jet (GPT-5.5-pro: "very tractable"). DONE 2026-07-06.**
  `exp_p(v)−p−v+½Γ_p(v,v)=o(‖v‖²)` — proved as `ExpMap.lean`'s `expMap_value_two_jet` ([AF] std-3, budget 0), the FULL
  vector (uniform-over-directions) 2-jet: `(fun v => expMap g gi hC p v − p − v + ½·Γ_p(v,v)) =o[𝓝 0] (fun v => ‖v‖²)`.
  Route (diagonal form, as scoped): explicit model curve `M(t)=(p+t·v−½t²·Γ_p(v,v), v−t·Γ_p(v,v))`, residual `q=Y−M`
  with `q'(t)=((q t).2, Γ_p(v,v)−Γ_{(Y t).1}((Y t).2,(Y t).2))` (identity computed directly — no abstract `H=D²F(e)`
  needed), the crux bound `‖q'(t)‖≤(1+Bcoef‖v‖)‖q t‖+Acoef‖v‖³` via the a-priori confinement + the LOCAL Christoffel
  value/Lipschitz bounds on `closedBall p (C₀·expRho)` (the base-point Lipschitz `christoffel_quad_diff_bound` is what
  yields `O(‖v‖³)`, hence `o(‖v‖²)`), then the inhomogeneous Grönwall (`norm_le_gronwallBound_of_norm_deriv_right_le` +
  new helper `gronwallBound_zero_one_le_exp`) + position projection. New reusable lemmas: `christoffel_bilin_bound`,
  `christoffel_quad_diff_bound`, `gronwallBound_zero_one_le_exp`. HONEST: the Fréchet value 2-jet of `exp_p` at 0 — does
  NOT discharge `hgauge`, NOT build the pullback metric, NOT move numerical-G.
- [x] **EXP-JET2 — the value 3-jet** (`r_3(1)=o(‖v‖³)`). **DONE 2026-07-06** — proved as `ExpMap.lean`'s
  `expMap_value_three_jet` ([AF] std-3), the FULL vector little-o
  `(fun v => exp_p v − p − v + ½·Γ_p(v,v) − ⅙·a₃(v)) =o[𝓝 0] (fun v => ‖v‖³)`. The cubic coefficient is the honest
  `γ'''(0)`: `a₃(v)_i = −∑_{jkl} ∂_l Γ^i_{jk}(p) v_j v_k v_l + ∑_{jk} Γ^i_{jk}(p)(Γ_p(v,v)_j v_k + v_j Γ_p(v,v)_k)`
  (= the prompt's `2∑ Γ Γ_p(v,v) v` form exactly when the metric is symmetric, `christoffel_symm`). Route (as scoped):
  cubic model curve `M(τ)=(p+τv−½τ²Γv+⅙τ³a₃, v−τΓv+½τ²a₃)` (`expJet2_model_hasDerivAt`), residual `r₃=Y−M` with
  `r₃'=A·r₃+Err` (`Err=Γv−t·a₃−Γ_{(Y t).1}((Y t).2,(Y t).2)`, `expJet2_residual_deriv_eq`); the exact
  O(‖v‖³)-cancellation regroups `Err = [−t²Γ_p(Γv,Γv)] + [t·∂Γ(v,v,v)−∂Γ(u*,u*,X−p)] − Rem + [Γ_X(u*,u*)−Γ_X(U,U)]`
  via three new sum-algebra helpers — `bilin_sub_smul_expand`, `tri_shared_telescope`, `bilin_taylor_repack` — with the
  cheap confinement-derived tube first-order bounds `‖(Y t).2−v‖`, `‖(Y t).1−p−t·v‖ = O(‖v‖²)` (MVT via
  `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`) feeding the `∂Γ` cancellation, and `christoffel_taylor_bound`
  (the SECOND-order Christoffel Taylor remainder) as the new analytic ingredient. Result
  `‖Err(t)‖ ≤ Acoef·‖v‖⁴ + Bcoef·‖v‖·‖r₃‖`; the inhomogeneous Grönwall
  (`norm_le_gronwallBound_of_norm_deriv_right_le` + `gronwallBound_zero_one_le_exp`) gives `‖r₃ 1‖ ≤ Cfinal·‖v‖⁴`, and the
  position projection closes the `o(‖v‖³)`. GREEN supporting lemmas: `fderiv_apply_eq_sum_pd`, `christoffel_pd_contDiff`,
  `christoffel_taylor_bound`, `christoffel_pd_trilin_bound`, `bilin_sup_bound`, `expJet2_model_hasDerivAt`,
  `expJet2_residual_deriv_eq`, `bilin_sub_smul_expand`, `tri_shared_telescope`, `bilin_taylor_repack`. **HONEST**: the
  Fréchet value 3-jet of `exp_p` at 0 — does NOT discharge `hgauge`, NOT build the pullback metric, NOT move
  numerical-G (`N`, `Λ_s`, `E/ξ` remain).
- [ ] **EXP-JET3 — the Jacobian field expansion to order 2** (`fderiv exp_p y = 1 + B(y,·) + ½T(y,y,·) + o(‖y‖²)`),
  via the localized first-variation. Moderate/high; the `fderiv`-differentiability caveat is the crux.
- [ ] **EXP-JET4 — the pullback metric `g̃` Taylor coefficients at 0** from EXP-JET1–3: `g̃(0)=δ` (needs an orthonormal
  frame at `p`, or state relative to `g(p)`), `∂g̃(0)=0`, `∂∂g̃(0)↔R`.
- [ ] **EXP-JET5 — discharge `hgauge`** (`∂_{(l}Γ̃^i_{jk)}(0)=0` in the normal coords) ⟹ instantiate
  `RNCExpansion.heat_a1_of_gauge` at `g:=g̃` ⟹ **`κ=1/6` UNCONDITIONAL given the metric** (the carried gauge retired).

## Verbatim HAVE / HAVE-NOT
- **HAVE (target):** "The exp-map normal coordinates satisfy the RNC gauge — `g̃(0)=δ`, `∂g̃(0)=0`,
  `∂_{(l}Γ̃_{jk)}(0)=0` — derived from the exp map's finite jets at 0 (equilibrium-anchored Grönwall, no general
  smooth-dependence theorem), discharging the carried `hgauge` ⟹ `κ=1/6` unconditional given the metric. Axiom-free."
- **HAVE NOT:** "This makes `κ=1/6` unconditional GIVEN the metric; it does NOT give numerical-G (`N`, `Λ_s`, `E/ξ`
  remain), does NOT build a curved heat kernel, and does NOT build the general smooth-dependence-on-IC theorem."

## Failure modes
- The `fderiv exp_p y`-as-a-field (EXP-JET3) genuinely needs local differentiability near 0 first — if it resists,
  land EXP-JET1/2 (value jets) green + checkpoint EXP-JET3 with the exact goal; do NOT fake `fderiv` off the
  differentiability set.
- The `B_t`/`C_t` state-jet algebra (`H=D²F(e)`, `K=D³F(e)` for the geodesic field) is the bookkeeping bulk — verify
  `H((ξ,η),(ξ',η'))=(0,−2Γ_p(η,η'))` etc. concretely.
- Do NOT build the general variational/C¹-flow theorem — the targeted finite-order jets suffice (GPT-5.5-pro).

## Discipline (every increment)
`lake build QIQTH.ExpMap` green; `#print axioms` std-3; budget 0; AxiomAudit pins; ONE commit LOCAL ONLY (no push)
with the Co-Authored-By trailer; update this plan + inventory. NO `sorry`; NEVER claim numerical-G or a curved heat
kernel; the metric-orthonormal-frame `g(p)=δ` assumption (for `g̃(0)=δ`) is a carried frame choice, stated honestly.

## Progress log
- **2026-07 (scoped):** GPT-5.5-pro (high) overturned the prior "gated on general smooth-dependence" verdict: the
  pullback metric's finite Taylor coefficients at 0 need only finite jets of `exp_p` at 0, reachable by the
  equilibrium two-point-Grönwall technique (value 2-/3-jet + localized Jacobian expansion) — NOT the general theorem.
  Concrete second-/third-difference residual estimates + the `fderiv`-field caveat given. Start EXP-JET1 (value 2-jet).
