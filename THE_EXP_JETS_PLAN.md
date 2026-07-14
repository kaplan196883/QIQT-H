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
- [~] **EXP-JET3 — the Jacobian field expansion to order 2** (`fderiv exp_p y = 1 + B(y,·) + ½T(y,y,·) + o(‖y‖²)`),
  via the localized first-variation. Moderate/high; the `fderiv`-differentiability caveat is the crux.
  - [x] **EXP-JET3a — SETUP for the localized first-variation / operator-valued fundamental solution. DONE 2026-07-07.**
    **KEY FINDING:** Mathlib's Picard–Lindelöf `IsPicardLindelof f t₀ x₀ a r L K` is ALREADY nonautonomous
    (`f : ℝ → E → E`; `Mathlib/Analysis/ODE/PicardLindelof.lean`); the autonomous corollaries wrap `(fun _ ↦ f)`
    via `IsPicardLindelof.of_contDiffAt_one`. So GPT-5.5-pro's flagged crux ("Mathlib PL is autonomous-only, must
    augment time") is FALSE — the nonautonomous fundamental solution `Φ_v` (field `Ψ_v t M = (DF(Y_v t)).comp M`,
    linear ⇒ globally Lipschitz in `M`, continuous in `t`) is NOT blocked by a missing theorem; building it is a
    large instantiation + assembly effort, not an infra gap. Green setup landed in `ExpMap.lean` ([AF] std-3,
    budget 0): `expJetIota` (`ι h = (0,h)`, `inr`), `expJetPi` (`π (x,u) = x`, `fst`),
    `geodesicField_differentiable` / `hasFDerivAt_geodesicField_fderiv` (`DF = fderiv F` exists everywhere ⇒ the
    Jacobi coefficient `A_v(t)=DF(Y_v(t))` is honest, never junk `fderiv`),
    `expJet_linVariation_residual_deriv` (the residual identity `R' = DF(Y₁)·R + N`,
    `N = F(Y₂)−F(Y₁)−DF(Y₁)(Y₂−Y₁)`, for `R = (Y₂−Y₁) − J` and ANY Jacobi solution `J`, pure calculus + `DF`
    linearity), and the analytic ingredient `geodesicField_uniform_C1_remainder` (UNIFORM first-order Taylor/C¹
    remainder of `F` on any convex compact `S`: `∀ε>0 ∃δ>0`, `‖F a − F b − DF(b)(a−b)‖ ≤ ε‖a−b‖` for `a,b∈S`,
    `‖a−b‖<δ`; Heine–Cantor uniform continuity of `fderiv F` + `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`
    on the segment).
  - [~] **EXP-JET3b — operator field `Ψ_v` + PL data + LOCAL fundamental solution. PARTIAL 2026-07-07.**
    Landed green in `ExpMap.lean` ([AF] std-3, budget 0): the operator-valued Jacobi field
    `expJetPsi` (`Ψ_v t M = DF(Y_v t) ∘ M` on `State →L State`), its linearity data
    `expJetPsi_norm_sub_le` (`‖Ψ_v t M − Ψ_v t N‖ ≤ ‖DF(Y_v t)‖·‖M − N‖`) / `expJetPsi_norm_le`
    (operator-norm submultiplicativity), `expTube_continuousOn` (the tube is continuous on `[0,1]`),
    the uniform Jacobi bound `expJet_fderiv_tube_bddAbove` (`‖DF(Y_v t)‖ ≤ KdF` on `[0,1]`, compactness
    of `fderiv F ∘ Y_v`), the time-continuity `expJetPsi_continuousOn` (right-composition CLM), and
    **`expJetFund_local`** — the LOCAL operator-valued fundamental solution `Φ_v` on a short `[0,T]`,
    `Φ_v 0 = 1`, `Φ_v' t = Ψ_v t (Φ_v t)`, via the FULL operator-normed `IsPicardLindelof` instantiation
    (`a=1, r=0, L=2·KdF, K=KdF, T=min 1 (1/(2(KdF+1)))`). **THE INTERVAL OBSTRUCTION (the exact
    checkpoint):** Mathlib's PL carries `mul_max_le : L·max(tmax−t₀, t₀−tmin) ≤ a − r`; for the LINEAR
    operator ODE the field bound is `L = KdF·(1+a)` (linear growth), so reaching `t=1` in ONE
    application needs `KdF < 1` — FALSE for the general tube. A single application only reaches
    `T ≲ 1/KdF`; extending to `[0,1]` requires CONCATENATING `≈⌈KdF⌉` local solutions (Grönwall-glued
    continuation), for which Mathlib has NO ready theorem (no global/continuation existence for
    globally-Lipschitz fields; time-rescaling scales `KdF` by the same factor). **Still CHECKPOINTED:**
    the `[0,1]` fundamental solution `Φ_v(1)` (the concatenation) and the first-variation residual
    Grönwall `HasFDerivAt (expMap g gi hC p) (L v) v`, `L v := π ∘ (Φ_v 1) ∘ ι` (set `J_k := Φ_v(·)(ι k)`,
    run inhomog Grönwall on `R_k` with `‖Z_k‖ ≤ Ctw‖k‖`, `‖N_k‖ ≤ εCtw‖k‖`, project with `π`).
    HONEST: operator field + PL data + LOCAL Φ_v — does NOT reach `Φ_v(1)`, NOT the localized first
    variation, NOT the pullback metric, NOT numerical-G.
  - [~] **EXP-JET3b (global scaffolding) — the SHIFTED normalized local propagator (concatenation brick). PARTIAL
    2026-07-07.**  Landed green in `ExpMap.lean` ([AF] std-3, budget 0): `expJetFund_shifted` — for a `[0,1]`-uniform
    Jacobi bound `KdF` threaded EXTERNALLY (so one `N` with `2(KdF+1)≤N` fixes the step) and ANY subinterval
    `[t₀,t₀+T] ⊆ [0,1]` with `2·KdF·T ≤ 1`, the NORMALIZED propagator `U_j` (`U_j(t₀)=1`, `U_j'=Ψ_v·U_j` on `[t₀,t₀+T]`)
    via the SHIFTED operator-normed `IsPicardLindelof` centred at the identity on `closedBall(1,1)` (`expJetFund_local`
    is the `t₀=0` case); and `expJetFund_shifted_integral` — the same with interval-continuity AND the LOCAL INTEGRAL
    EQUATION `U_j(t)=1+∫_{t₀}^t Ψ_v(s)(U_j s) ds` (from the derivative law by FTC-2, integrand continuous via
    `ContinuousOn.clm_comp`), the exact brick the global integral-equation gluing consumes.  **KEY:** this discharges
    the earlier "Mathlib has NO continuation theorem" checkpoint into a pure ASSEMBLY — every `[τ_j,τ_{j+1}]` is a
    normalized `U_j`; glue by right-multiplication `M_{j+1}:=U_j(τ_{j+1})∘M_j`, `seg_j:=U_j∘M_j` (inherits the shifted
    integral eq via `ContinuousLinearMap.integral_comp_comm`), prove the GLOBAL integral equation
    `Φ_v(t)=1+∫_0^t Ψ_v(s)(Φ_v s) ds` on `[0,τ_j]` by induction on `j`
    (`intervalIntegral.integral_add_adjacent_intervals` + `intervalIntegral.integral_congr`), then FTC on `[0,1]`.
    ⚠ **CHECKPOINTED (the remaining EXP-JET3b work):** that partition induction (piecewise `glued`/`Φ_v`, ℕ/ℝ
    partition arithmetic `τ(j+1)=τj+h`, `τN=1`), `Φ_v(1)`, `L v := expJetPi∘(Φ_v 1)∘expJetIota`, and the first-variation
    residual Grönwall `HasFDerivAt (expMap g gi hC p) (L v) v` (set `J_k:=Φ_v(·)(ι k)`, run inhomog Grönwall on `R_k` with
    `‖N_k‖≤εCtw‖k‖` via `geodesicField_uniform_C1_remainder`+`geodesic_twopoint_gronwall`, project with `π`).
    HONEST: the concatenation building block (one subinterval, differential + local integral form) — does NOT reach
    `Φ_v(1)`, NOT the localized first variation, NOT the pullback metric, NOT numerical-G.
  - [x] **EXP-JET3b STEP A — the `[0,1]` fundamental solution `Φ_v`. DONE 2026-07-07.**  Landed green in
    `ExpMap.lean` ([AF] std-3, budget 0): **`expJetFund`** — the `[0,1]` operator-valued fundamental solution `Φ_v`
    with `Φ_v 0 = 1`, `ContinuousOn Φ_v [0,1]`, the GLOBAL integral equation `Φ_v t = 1 + ∫₀ᵗ Ψ_v s (Φ_v s) ds` on
    `[0,1]`, AND the derivative law `HasDerivWithinAt Φ_v (Ψ_v t (Φ_v t)) (Icc 0 1) t` for every `t ∈ [0,1]`.
    Route (as scoped): the concatenation is a finite induction (`expJetFund_glue`, private) on the partition
    `τ j = j/N` (step `h = 1/N`, `N ≥ 2(KdF+1)` from `exists_nat_ge` so each subinterval has `2·KdF·h ≤ 1`); the glued
    curve on `[0,τ_{j+1}]` is `Φ_{j+1}(t) = if t ≤ τ_j then Φ_j t else U_j(t) ∘ Φ_j(τ_j)` (`U_j` from
    `expJetFund_shifted_integral`), and the GLOBAL integral equation is pasted from the sub-interval one by
    `intervalIntegral.integral_add_adjacent_intervals` + `integral_congr` + right-composition/integral commutation
    (`ContinuousLinearMap.intervalIntegral_comp_comm` with `RM = (compL).flip (Φ_j τ_j)`); continuity glues by
    `ContinuousOn.union_of_isClosed` over `Icc 0 τ_j ∪ Icc τ_j τ_{j+1}`.  The partition arithmetic (`τ(j+1)=τj+1/N`,
    `τN = N/N = 1`, `Nat.cast` bookkeeping) is discharged by `push_cast; ring` + `div_self`/`div_le_one`.  The
    derivative law comes from the integral equation by FTC-1 (`intervalIntegral.integral_hasDerivWithinAt_right`,
    using the `FTCFilter t (𝓝[Icc 0 1] t)` instance from `Fact (t ∈ Icc 0 1)`) + `.const_add` + `.congr`.  New
    reusable lemma `expJetPsi_comp_continuousOn` (integrand continuity on any `A ⊆ [0,1]`).  **KEY:** this discharges
    the "Mathlib has NO continuation theorem" checkpoint into a completed ASSEMBLY.  HONEST: the `[0,1]` fundamental
    solution — a step toward the localized first variation `HasFDerivAt exp_p (L v) v` (EXP-JET3, still CHECKPOINTED).
    It does NOT yet give the first variation, NOT the Jacobian 2-jet expansion, NOT the pullback metric, NOT
    numerical-G (`N`, `Λ_s`, `E/ξ` remain).
  - [x] **EXP-JET3b STEP B — the localized first variation `HasFDerivAt exp_p (L v) v`. DONE 2026-07-07.**  Landed
    green in `ExpMap.lean` ([AF] std-3, budget 0): **`hasFDerivAt_expMap`** — for `‖v‖ < expRho`,
    `HasFDerivAt (expMap g gi hC p) (expJetPi.comp ((Φ_v 1).comp expJetIota)) v` with `Φ_v` THE `[0,1]`
    fundamental solution (`expJetFund`), stated existentially in `Φ_v` (it is not canonically named).  Route (as
    scoped): the Jacobi field `J_k(t) = Φ_v(t)(0,k)` (`HasDerivWithinAt.clm_apply` on the `Φ_v` derivative law +
    `expJetPsi_apply`, `J_k 0 = (0,k)`) transports the first variation; the residual `R_k = (Y_{v+k} − Y_v) − J_k`
    has `R_k 0 = 0` and `R_k' = DF(Y_v)·R_k + N_k` (built inline from `Y_{v+k}' − Y_v' − J_k'` + `map_sub`/`abel`),
    with the two-point separation `‖Y_{v+k} − Y_v‖ ≤ ‖k‖·Ctw` (`geodesic_twopoint_gronwall`, `Ctw = e^{Ktube}` on a
    fixed convex-compact ball `S = closedBall((p,0), expConst(‖v‖+1)+1)`) and the C¹ remainder
    `‖N_k(t)‖ ≤ ε·‖Y_{v+k}−Y_v‖ ≤ ε·Ctw·‖k‖` (`geodesicField_uniform_C1_remainder` on `S`); the inhomogeneous
    Grönwall (`norm_le_gronwallBound_of_norm_deriv_right_le`, `Icc→Ici` right-derivatives via
    `mono_of_mem_nhdsWithin`) gives `‖R_k 1‖ ≤ ε·Ctw·β'·‖k‖ ≤ c·‖k‖` (`gronwallBound_zero_linear`, ε tolerance).
    Finally `exp_p(v+k) − exp_p(v) − L v·k = expJetPi(R_k 1)` (since `expJetPi(J_k 1) = L v·k`) + `‖expJetPi z‖ ≤ ‖z‖`
    closes the `isLittleO`.  HONEST: the localized first variation (the genuine subtlety of EXP-JET3).  Does NOT yet
    give the full Jacobian 2-jet expansion `fderiv exp_p y = 1 + B(y,·) + …`, NOT the pullback metric, NOT
    numerical-G (`N`, `Λ_s`, `E/ξ` remain).
  - [x] **EXP-JET3c (STEP 0) — the closed-form Fréchet derivative of the geodesic field. DONE 2026-07-07.**  Landed
    green in `ExpMap.lean` ([AF] std-3, budget 0): **`geodesicField_fderiv_apply`** — the honest closed form of the
    Jacobi coefficient `A_v(t)=DF(Y_v t)`:
    `DF(x,u)(ξ,η) = (η, i ↦ −∑_{jk}[(∑_l ∂_l Γ^i_{jk}(x)·ξ_l)·u_j·u_k + Γ^i_{jk}(x)·η_j·u_k + Γ^i_{jk}(x)·u_j·η_k])`.
    Route: per-term product rule `HasFDerivAt.mul` on `q ↦ Γ^i_{jk}(q.1)·q.2 j·q.2 k` (position factor via
    `.comp hasFDerivAt_fst`, velocity factors via `(proj·).comp snd`), assembled over `j,k` (`HasFDerivAt.fun_sum`),
    `i` (`hasFDerivAt_pi.2`) + the velocity slot (`hasFDerivAt_snd.prodMk`); `HasFDerivAt.fderiv` reads off the fderiv,
    `fderiv_apply_eq_sum_pd` turns `fderiv Γ x ξ` into `∑_l ∂_l Γ·ξ_l`.  Specialising `(x,u)=(p,0)` recovers
    `A₀=DF(e)=linF` (every acceleration term carries a factor `u=0`).  **KEY:** this is the STEP-0 analytic foundation
    for the uniform `DF(Y_y t) = A₀ + A₁(t,y) + A₂(t,y) + o(‖y‖²)` expansion (identify `A₁`, `A₂` by composing this
    closed form with the tube's value 2-jet `Y_y(t)−e = S₁+S₂+o(‖y‖²)`).  ⚠ **STILL CHECKPOINTED (the EXP-JET3c bulk):**
    the uniform order-2 `DF` expansion (operator norm, uniform in `t∈[0,1]`); the model Jacobian `K_y=K₀+K₁+K₂` from the
    triangular ODEs (explicit closed forms since `A₀²=0`); the residual operator Grönwall
    `‖(Φ_y 1)∘ι − K_y(1)‖ ≤ C‖y‖²`; and the projected 2-jet `L y = 1 − Γ_p(y,·) + ½T(y,y,·) + o(‖y‖²)`.
    HONEST: the pointwise closed-form Jacobi coefficient — does NOT give the uniform order-2 expansion, NOT the Jacobian
    2-jet, NOT the pullback metric, NOT numerical-G (`N`, `Λ_s`, `E/ξ` remain).
  - [x] **EXP-JET3c (STEP 1 ingredient) — the uniform-in-`t` tube value 2-jet. DONE 2026-07-07.**  Landed green in
    `ExpMap.lean` ([AF] std-3, budget 0): **`expTube_value_two_jet`** — for `‖v‖ ≤ ρ` the WHOLE confined tube
    `Y_v(t)=expTube p v t` (not just its position endpoint at `t=1`, as `expMap_value_two_jet` exposed) is
    `O(‖v‖³)`-close, UNIFORMLY in `t∈[0,1]`, to the model curve `M(t)=(p+t·v−½t²Γ_p(v,v), v−t·Γ_p(v,v))`:
    `‖Y_v(t) − M(t)‖ ≤ C·‖v‖³` on `[0,1]`.  This is the tube 2-jet `Y_v(t)−e = S₁(t,v)+S₂(t,v)+O(‖v‖³)`,
    `S₁=(t·v,v)`, `S₂=(−½t²Γ_p(v,v),−t·Γ_p(v,v))` — the value-jet input the uniform `DF(Y_v t)` expansion consumes
    (compose `geodesicField_fderiv_apply` at `(x,u)=Y_v(t)` with this).  Route (as scoped): the SAME
    equilibrium-anchored residual-ODE + inhomogeneous Grönwall as `expMap_value_two_jet` (`q=Y−M`, `q 0 = 0`,
    `‖q'‖ ≤ (1+Bcoef‖v‖)‖q‖ + Acoef‖v‖³` via confinement + `christoffel_quad_diff_bound`), but the Grönwall is applied
    at EVERY `t∈[0,1]` (not just `t=1`) and BOTH phase components are exposed (no position projection).  New reusable
    helper **`gronwallBound_zero_le_exp`** (`gronwallBound 0 K ε t ≤ ε·e^K` uniformly in `t∈[0,1]`, generalizing
    `gronwallBound_zero_one_le_exp` to arbitrary `ε` and interior times).  ⚠ **STILL CHECKPOINTED (the EXP-JET3c bulk):**
    the operator-norm `DF(Y_y t) = A₀+A₁(t,y)+A₂(t,y)+o(‖y‖²)` expansion (plug this tube 2-jet into
    `geodesicField_fderiv_apply` and bound the operator-norm remainder via `christoffel_taylor_bound` — this is the
    remaining analytic bulk); the model Jacobian `K_y=K₀+K₁+K₂`; the residual operator Grönwall; and the projected
    `L y = 1 − Γ_p(y,·) + ½T(y,y,·) + o(‖y‖²)`.  HONEST: the uniform-in-`t` full-phase-vector value 2-jet of the tube —
    does NOT give the operator `DF` expansion, NOT the Jacobian 2-jet, NOT the pullback metric, NOT numerical-G
    (`N`, `Λ_s`, `E/ξ` remain).
  - [x] **EXP-JET3c (STEP 1 core) — the operator-norm `‖DF(x,u) − A₀‖` bound (`A₀` is leading). DONE 2026-07-07.**
    Landed green in `ExpMap.lean` ([AF] std-3, budget 0): **`geodesicField_fderiv_sub_linF_opNorm_le`** — given
    `|Γ^i_{jk}(x)| ≤ Mc` and `|∂_l Γ^i_{jk}(x)| ≤ Nc`, the OPERATOR-NORM bound
    `‖DF(x,u) − A₀‖ ≤ Nc·n³·‖u‖² + 2·(Mc·n²)·‖u‖` (`A₀ = linF = DF(e)`).  Route: `(DF(x,u)−A₀)(ξ,η) = (0, Acc)` (the
    velocity slots cancel), `Acc = −∑_{jk}[(∑_l ∂_lΓ·ξ_l)u_j u_k + Γ·η_j u_k + Γ·u_j η_k]` split into the
    ∂Γ-trilinear form (`christoffel_pd_trilin_bound`, `≤ Nc·n³·‖u‖²·‖ξ‖`) and two Γ-bilinear forms
    (`christoffel_bilin_bound`, `≤ Mc·n²·‖u‖·‖η‖` each), `‖ξ‖,‖η‖ ≤ ‖(ξ,η)‖`, then `ContinuousLinearMap.opNorm_le_bound`.
    Composed with `expTube_value_two_jet` (`‖u‖ = ‖(Y_v t).2‖ = O(‖v‖)`) this is the ORDER-0 remainder
    `‖DF(Y_v t) − A₀‖ ≤ C·‖v‖` of the uniform `DF(Y_v t)` expansion.  ⚠ **STILL CHECKPOINTED (the EXP-JET3c bulk):**
    identifying the order-1/2 coefficients `A₁(t,y)`, `A₂(t,y)` (the linear/quadratic-in-`y` operator terms) and the
    operator-norm `o(‖y‖²)` remainder — i.e. the FULL uniform order-2 `DF(Y_y t)` expansion; the model Jacobian
    `K_y=K₀+K₁+K₂` from the triangular ODEs (`A₀²=0`); the residual operator Grönwall `‖(Φ_y 1)∘ι − K_y(1)‖ ≤ C‖y‖²`;
    and the projected `L y = 1 − Γ_p(y,·) + ½T(y,y,·) + o(‖y‖²)`.  HONEST: the operator-norm "`A₀` is leading" bound —
    does NOT identify `A₁, A₂`, NOT the full Jacobian 2-jet, NOT the pullback metric, NOT numerical-G.
  - [x] **EXP-JET3c (STEP 1, order-0 composed) — the uniform-in-`t` order-0 `DF` expansion along the tube. DONE
    2026-07-07.**  Landed green in `ExpMap.lean` ([AF] std-3, budget 0): **`expJet_fderiv_tube_order0`** — the ORDER-0
    (leading `A₀`) term of the uniform `DF(Y_v t)` expansion, now a theorem: `∃ ρ>0, ∃ C≥0, ∀ ‖v‖≤ρ, ∀ t∈[0,1],
    ‖DF(Y_v t) − A₀‖ ≤ C·‖v‖` (`A₀=linF=DF(e)`, `Y_v=expTube p v`).  Route (as scoped): compose the pointwise
    `geodesicField_fderiv_sub_linF_opNorm_le` with the a-priori confinement `expTube_spec` (`‖(Y_v t).2‖ ≤ C₀‖v‖`,
    `(Y_v t).1 ∈ closedBall p (C₀ρ)`); the Christoffel value bound `Mc` and `∂Γ` value bound `Nc` are uniform over the
    compact confinement ball (`christoffel_pd_contDiff` → continuity → `subset_closedBall` bound), and
    `Nc·n³‖u‖²+2Mc·n²‖u‖ ≤ C·‖v‖` via `‖u‖≤C₀‖v‖≤C₀ρ` (`C=Nc·n³·C₀²·ρ+2·Mc·n²·C₀`).  ⚠ **STILL CHECKPOINTED (the
    EXP-JET3c bulk):** the ORDER-1 coefficient `A₁(t,y)` (linear-in-`y`; anchored — `A₁` is `t`-independent, the
    order-1 part of `DF(p,y)−A₀`, `= (0, i↦−∑_{jk}Γ^i_{jk,p}(η_j y_k + y_j η_k))`) with the operator remainder
    `‖DF(Y_y t)−A₀−A₁‖ ≤ C‖y‖²` (needs the tube 2-jet `‖(Y_y t).2 − y‖=O(‖y‖²)` from `expTube_value_two_jet` +
    Christoffel/∂Γ Lipschitz `christoffel_quad_diff_bound`); the ORDER-2 coefficient `A₂(t,y)` (quadratic-in-`y`;
    `t`-dependent — the ∂Γ-trilinear `(∂Γ_p ξ)y_j y_k` + the `t·∂Γ_p·y` Γ-cross-terms); the model Jacobian
    `K_y=K₀+K₁+K₂` from the triangular ODEs (`A₀²=0` ⟹ `K₀(t)=1+tA₀`, `K₁(t)=∫₀ᵗ(1+(t−s)A₀)A₁(s)K₀(s)ds`, `K₂`
    analogously); the residual operator Grönwall `‖(Φ_y 1)∘ι − K_y(1)‖ ≤ C‖y‖²`; and the projected
    `L y = 1 − Γ_p(y,·) + ½T(y,y,·) + o(‖y‖²)`.  HONEST: the order-0 remainder — does NOT identify `A₁, A₂`, NOT the
    Jacobian 2-jet, NOT the pullback metric, NOT numerical-G.
  - [x] **EXP-JET3c (STEP 1, order-1 anchoring) — the tube Jacobi coefficient is `O(‖v‖²)`-close to the fixed
    `DF(p,v)`. DONE 2026-07-07.**  Landed green in `ExpMap.lean` ([AF] std-3, budget 0): **`expJet_fderiv_tube_order1`**
    — `∃ ρ>0, ∃ C≥0, ∀ ‖v‖≤ρ, ∀ t∈[0,1], ‖DF(Y_v t) − DF(p,v)‖ ≤ C·‖v‖²` (`Y_v=expTube p v`).  This ANCHORS the
    order-1 coefficient: `DF(Y_v t) = DF(p,v) + O(‖v‖²)` UNIFORMLY in `t`, so the FIXED `t`-independent operator
    `DF(p,v)` carries the order-1 part `A₁` (`= DF(p,v) − A₀` up to its own order-2 ∂Γ piece), reducing the remaining
    work to expanding the single fixed `DF(p,v)` — no more tube/`t` dependence.  Route: a new pointwise two-point
    operator-norm bound **`geodesicField_fderiv_two_pt_opNorm_le`** (`‖DF(x,u) − DF(x',u')‖ ≤ Nc·n³(‖u‖²+‖u'‖²) +
    2(Mc·n²‖u−u'‖ + Dc·n²‖u'‖)`: velocity slots cancel, ∂Γ block by `christoffel_pd_trilin_bound` at each point, the
    two Γ-bilinear blocks by the new generic **`bilin_two_pt_diff_bound`**) applied at `(Y_v t)` vs `(p,v)`, fed the
    confinement (`‖(Y_v t).2‖≤C₀‖v‖`, `(Y_v t).1∈closedBall p (C₀ρ)`), the Christoffel value/Lipschitz/∂Γ bounds on
    the ball, the Christoffel Lipschitz `Dc = Lc·‖x−p‖ = O(‖v‖)`, and the tube 2-jet `‖(Y_v t).2 − v‖ ≤ D₂‖v‖²`
    (`expTube_value_two_jet` + `christoffel_bilin_bound`).  ⚠ **STILL CHECKPOINTED (the remaining EXP-JET3c bulk):**
    expand the single fixed `DF(p,v) = A₀ + A₁ + (order-2 ∂Γ)` to read off `A₁`, `A₂` as CLM coefficients; the model
    Jacobian `K_y=K₀+K₁+K₂` from the triangular ODEs (`A₀²=0` ⟹ `K₀(t)=1+tA₀`, `K₁(t)=∫₀ᵗ(1+(t−s)A₀)A₁K₀(s)ds`,
    `K₂` analogously — now with `A₁` `t`-independent and `A₂` the residual order-2 term); the residual operator Grönwall
    `‖(Φ_y 1)∘ι − K_y(1)‖ ≤ C‖y‖²`; and the projected `L y = 1 − Γ_p(y,·) + ½T(y,y,·) + o(‖y‖²)`.  HONEST: the order-1
    anchoring — does NOT give `K_y`, the residual Grönwall, the projected Jacobian 2-jet, the pullback metric, or
    numerical-G (`N`, `Λ_s`, `E/ξ` remain).
  - [x] **EXP-JET3c (STEP 1, coefficient identification) — the anchored order-2 decomposition
    `DF(p,v) = A₀ + A₁(v) + A₂(v)`. DONE 2026-07-07.**  Landed green in `ExpMap.lean` ([AF] std-3, budget 0):
    **`geodesicField_fderiv_anchored_eq`** — the fixed `t`-independent Jacobi coefficient at the base point splits
    EXACTLY (a degree-≤2 polynomial in `v`, NO remainder) as `linF + expJetA1 g gi p v + expJetA2 g gi p v`, with
    `A₀=linF=DF(e)`, `A₁(v)(ξ,η)=(0,i↦−∑_{jk}Γ^i_{jk}(p)(η_j v_k+v_j η_k))` (velocity-bilinear Γ part, **`expJetA1`**),
    `A₂(v)(ξ,η)=(0,i↦−∑_{jk}(∑_l ∂_lΓ^i_{jk}(p) ξ_l)v_j v_k)` (∂Γ-trilinear part, **`expJetA2`**); and the composed
    **`expJet_fderiv_tube_order2`** — `∃ ρ>0, ∃ C≥0, ∀ ‖v‖≤ρ, ∀ t∈[0,1], ‖DF(Y_v t) − (linF+A₁+A₂)‖ ≤ C·‖v‖²`, the
    uniform-in-`t` order-2 expansion with IDENTIFIED coefficients (order-1 anchoring + the exact decomposition).  New
    reusable CLM building block **`matVecCLM`** (`η ↦ (i↦∑_j c_ij η_j)` on `Point n`, from `proj j`) + helper
    `pd_trilin_reorder` (∂-index reorder).  Route: read off `geodesicField_fderiv_apply` at `(p,v)`, regroup the
    acceleration double-sum into the three coefficient arrays (`ContinuousLinearMap.ext` → `Prod.ext` → per-`i` Finset
    sum algebra; the ∂Γ block via `pd_trilin_reorder`, the two Γ blocks combined into `c₁` via `Finset.sum_comm` +
    `Finset.sum_neg_distrib`, closed by `linarith`).  ⚠ **STILL CHECKPOINTED (the EXP-JET3c bulk):** the model Jacobian
    `K_v=K₀+K₁+K₂` from the triangular ODEs (`A₀²=0` ⟹ `K₀(t)=1+tA₀`, `K₁(t)=∫₀ᵗ(1+(t−s)A₀)A₁K₀(s)ds`, `K₂` analogously);
    the residual operator Grönwall `‖(Φ_y 1)∘ι − K_y(1)‖ ≤ C‖y‖²`; and the projected
    `L y = 1 − Γ_p(y,·) + ½T(y,y,·) + o(‖y‖²)`.  HONEST: the `A₁,A₂` coefficient identification + uniform order-2
    expansion — does NOT give `K_v`, the residual Grönwall, the projected 2-jet, the pullback metric, or numerical-G.
  - [~] **EXP-JET3c (STEP 2, order-0 model propagator `K₀`) — PARTIAL 2026-07-07.**  Landed green in `ExpMap.lean`
    ([AF] std-3, budget 0): **`linF_comp_linF`** (`A₀²=0`, `linF.comp linF = 0` — the equilibrium linearization is
    nilpotent, so `exp(t·A₀)` truncates to `1 + t·A₀`), the model propagator **`expJetK0`** (`K₀(t) = 1 + t·A₀`) with
    `expJetK0_zero` (`K₀(0)=1`), `expJetK0_hasDerivAt` (`K₀'=A₀`), `linF_comp_expJetK0` (`A₀·K₀(t)=A₀`), and
    **`expJetK0_hasDerivAt_ode`** — `K₀` solves the equilibrium operator ODE `K₀' = A₀·K₀`.  The exact order-0 brick
    of the model Jacobian `K_v = K₀ + K₁ + K₂`.  ⚠ **STILL CHECKPOINTED (the EXP-JET3c bulk):** the order-1/2
    corrections `K₁(t) = ∫₀ᵗ(1+(t−s)A₀)·A₁·K₀(s)ds`, `K₂(t) = ∫₀ᵗ(1+(t−s)A₀)(A₁·K₁(s)+A₂·K₀(s))ds` (operator-valued
    Bochner integrals + FTC/Leibniz derivative laws); the residual operator Grönwall `‖(Φ_y 1)∘ι − K_y(1)‖ ≤ C‖y‖²`;
    and the projected `L y = 1 − Γ_p(y,·) + ½T(y,y,·) + o(‖y‖²)`.  HONEST: the order-0 model propagator + nilpotency —
    does NOT give `K₁,K₂`, the residual Grönwall, the projected 2-jet, the pullback metric, or numerical-G.
  - [x] **EXP-JET3c (STEP 2, order-1/2 model propagators + toolkit) — DONE 2026-07-07** (commits e14fb66, 7628bd7):
    closed-form `expJetK1`/`expJetK2` + `expJetK*_hasDerivAt_ode`, `expJetA1`/`expJetA2` + `_opNorm_le`, the anchored
    identity `geodesicField_fderiv_anchored_eq` (`DF(p,v)=A₀+A₁(v)+A₂(v)` EXACT), `expJet_fderiv_tube_order2`,
    `expJet_residual_identity`, `linF_comp_linF` (A₀²=0), `expJetA1_comp_linF` (A₁A₀=0). All [AF] std-3, budget 0.
  - [x] **EXP-JET3c (STEP 3a — small-context Grönwall helper) — DONE 2026-07-07** (commit 50e8972): `expJet_residual_gronwall`
    (`E:ℝ→F` any normed `ℝ`-space, `E 0=0`, `‖E'‖≤K‖E‖+C` on `[0,1)` ⟹ `‖E 1‖≤C·e^K`).  Abstracted over `F` to dodge
    the 32M-heartbeat CLM-Banach whnf/instance explosion the monolithic operator-Grönwall triggered.  [AF] std-3.
  - [x] **EXP-JET3c (STEP 3b — the Jacobian 1-jet) — DONE 2026-07-07** (commits 2f39d90, 26c86c5; [AF] std-3, budget 0).
    **`hasFDerivAt_expMap_jacobian_one_jet`**: `(fun v => fderiv exp_p v − (id + expJetOneJetModel v)) =O[𝓝 0] (‖v‖²)`,
    with `expJetOneJetModel v = ½·matVecCLM c₁ = −Γ_p^sym(v,·)` — i.e. `fderiv exp_p v = id − Γ_p^sym(v,·) + O(‖v‖²)`.
    Route (as scoped): uniform-in-`v` `‖DF(Y_v t)‖≤Kstar` (`expJet_fderiv_tube_bddAbove_unif`, confinement into a fixed
    compact phase-space ball ⟹ `e^{Kstar}` Grönwall factor uniform ⟹ genuine `IsBigO` over `𝓝 0`); operator residual
    `E_v=Φ_v−(K₀+K₁)` obeying `E'=DF∘E+N` (`expJet_residual_identity`), `‖N‖≤Cconst‖v‖²` (via `expJet_fderiv_tube_order2`
    + `expJetA2_opNorm_le` + `expJetA1/K1_opNorm_le`), `expJet_residual_gronwall` ⟹ `‖E_v 1‖≤Cconst‖v‖²·e^{Kstar}`;
    projected exact model identity `expJet_proj_model_one` (`π∘(K₀(1)+K₁(1))∘ι = id + expJetOneJetModel v`); residual
    `fderiv exp_p v − (id+model) = π∘(E_v 1)∘ι`, `‖·‖≤‖E_v 1‖`. **KEY compile fix:** the capstone whnf-exploded even at
    4M heartbeats (CLM-space instance/whnf blowup); offloading every heavy CLM-algebra step into 5 small-context
    helpers (`expJet_recompose`, `expJet_DA1_norm_le`, `expJet_N_norm_le`, `expJet_Ederiv_norm_le`,
    `expJet_pi_comp_iota_norm_le`) — same technique as `expJet_residual_gronwall` — brought it to 1.6M heartbeats.
    This delivers **TWO of three gauge conditions**: `g̃(0)=δ`, `∂g̃(0)=0`.  HONEST: the Jacobian 1-jet — does NOT give
    the Jacobian 2-jet (`½T` term; anchored A₂ is t-dependent-wrong there — see the FINDING below), NOT the pullback
    metric, NOT the gauge discharge, NOT numerical-G.
- [x] **EXP-JET3c (STEP 3 — HONEST MATH FINDING, GPT-5.5-pro-confirmed 2026-07-07).** The ANCHORED fixed `A₂(v)` reaches
  the Jacobian 1-JET exactly but is WRONG at order 2: the true order-2 Jacobi coefficient `Ã₂(t,v)` is genuinely
  `t`-DEPENDENT (tube drift `Y_v(t)≈(p+tv,v−tΓv)` feeds `∂Γ` a `t·v`), and the missing forcing SURVIVES the `π∘·∘ι`
  projection (explicit 1-D check: `(Γ²−∂Γ)/3·v²k`).  So the full Jacobian 2-jet needs `Ã₂(t,v)` + a `t`-dependent
  `K̃₂(t)` + a little-o (not `≤C‖v‖²`) C²-operator Taylor Grönwall.  Route (b) — differentiating the value 3-jet — is
  NOT Lean-sound (a Peano value remainder `o(‖v‖³)` does NOT give a derivative remainder `o(‖v‖²)`; counterexample
  `x⁴sin(1/x²)`); it would need a full `HasFTaylorSeriesUpTo`/`ContDiffAt 3` object, which we do not have.
- **THE PIVOT — EXP-JET5 via the RADIAL GAUGE (GPT-5.5-pro, route (c)): BYPASSES the Jacobian 2-jet entirely.**
  The symmetrized gauge condition `∂_{(l}Γ̃^i_{jk)}(0)=0` follows from radial-geodesic straightness WITHOUT any
  Jacobian 2-jet.  Chain: (1) `exp_p(s·v) = (Y_v s).1` (radial lines ↦ geodesics, ODE-rescaling uniqueness);
  (2) `Γ̃` = the pullback-metric Christoffel field via the transform `Dexp_p(y)(Γ̃ y a b) = D²exp_p(y)[a,b] +
  Γ(exp_p y)(Dexp_p(y)a, Dexp_p(y)b)` (metric-compatibility / local-isometry — the HEAVY lemma; its ONLY use of
  `∂g̃` is to identify `Γ̃` as `g̃`'s Christoffel, NOT to compute `∂Γ̃` from the metric expansion); (3) radial
  geodesic ⟹ `Γ̃(s·v)(v,v)=0` near `s=0`; (4) `d/ds|₀` ⟹ `DΓ̃₀(v)(v,v)=0 ∀v` (chain rule); (5) polarize the cubic
  diagonal `T(v,v,v)=0` ⟹ full symmetrization `∑_{σ}T=0`, i.e. `∂_{(l}Γ̃_{jk)}(0)=0`.  Concrete Lean lemmas:
  `exp_scale_eq_tube` (Lemma 1, ODE-rescale), `pullback_christoffel_transform` (Lemma 2, heaviest),
  `normal_ray_christoffel_zero` (Lemma 3), `DGamma_diag_zero_of_normal_rays` (Lemma 4, `HasFDerivAt` + homogeneity),
  `trilinear_diag_zero_fullSymm` (Lemma 5, pure polarization `P(x)=T x x x` inclusion–exclusion).  Lemma 5 is
  standalone algebra (start there); Lemma 2 is the real work.  This is the classical textbook RNC-gauge proof and is
  MUCH lighter in Lean than the `t`-dependent 2-jet.
  - [x] **Lemma 5 `trilinear_diag_zero_fullSymm` — DONE 2026-07-07** (`QIQTH/Polarization.lean`, [AF] std-3, budget 0):
    `(∀x, T x x x=0) ⟹ ∑_{σ∈S₃} T aσ bσ cσ = 0` via `sixSym_eq_incl_excl` (`P(a+b+c)−P(a+b)−P(a+c)−P(b+c)+P(a)+P(b)+P(c)`,
    multilinearity + `abel`).  Standalone; wired into QIQTH.lean + AxiomAudit.
  - **⚠ ROUTE-C REVISION (GPT-5.5-pro consult 2026-07-07, component-framework specifics) — the honest cost of route (c).**
    In the COMPONENT framework `Γ̃ := christoffel g̃ g̃i` where `g̃ y i j := ∑_{ab} g(exp_p y)_{ab}·(fderiv exp_p y e_i)^a·
    (fderiv exp_p y e_j)^b` (the pullback metric). Feeding the EXISTING `RNCExpansion.heat_a1_of_gauge` — which reads the
    LITERAL `pd (christoffel g̃ g̃i) l 0` — SECRETLY REQUIRES a controlled C³/HESSIAN jet of `exp_p` at 0 (`pd(pd exp)`),
    i.e. the finite-jet residue of smooth-dependence-of-`exp_p`-on-`v` (the Mathlib gap). My value 2/3-jets + Jacobian
    1-jet are INSUFFICIENT for the literal `christoffel g̃` (sanity: `r=x⁴sin(1/x)` has `r=o(x³)`, `r'=O(x²)`, but `r''`
    oscillates — value-3-jet + Jacobian-1-jet do NOT determine `pd(christoffel g̃)`). **So route (c) is NOT automatically
    cheaper via the literal pullback Christoffel.**  THE GENUINELY LIGHT ROUTE = **refactor the consumer to a finite
    GaugeJet interface**: (i) define the FORMAL RNC-Christoffel linear coefficient `rncDΓ Γ0 Γ1 A3 l i j k := A3 i l j k
    + Γ1 l i j k − ∑_a Γ0 i a k·Γ0 a l j − ∑_a Γ0 i j a·Γ0 a l k` from data I HAVE (`Γ0=christoffel..p`, `Γ1=pd christoffel..p`,
    `A3`=the value-3-jet cubic `a₃`); (ii) prove the RADIAL DIAGONAL vanishes `dΓDiag(rncDΓ) v i := ∑_{ljk} rncDΓ l i j k v_l
    v_j v_k = 0` by matching the `t¹` coefficient in the geodesic equation for `exp_p(t•v)=(Y_v t).1` (uses the value 3-jet
    + geodesic ODE + `geodesic_rescale` — FINITE jets only, NO ContDiff exp_p); (iii) `gaugeJet_of_diag` via Polarization
    Lemma 5 ⟹ `GaugeJet(rncDΓ)` (the symmetrized gauge on the formal coefficients); (iv) refactor
    `heat_a1_of_gauge`→`heat_a1_of_gaugeJet dΓ (hgauge:GaugeJet dΓ)` reading `dΓ` directly. This DISCHARGES the gauge as a
    FORMAL-JET THEOREM with no smooth-dependence. **HONEST remaining gap (clearly labelled):** the bridge
    `rncDΓ = pd(christoffel g̃ g̃i) 0` (`rnc_christoffel_linearJet`) — proving the formal coefficients ARE the literal
    pullback-Christoffel jet — is the finite-jet pullback-transform and STILL needs the controlled C³/Hessian jet of `exp_p`
    (the smooth-dependence residue). Deferred, honestly cited.
  - [x] **Lemma 5→gauge: `gaugeJet_of_diag` — DONE 2026-07-07** (`QIQTH/RNCGauge.lean`, commit 1b09321, [AF] std-3,
    budget 0): `(∀ v i, dGammaDiag dΓ v i = 0) ⟹ GaugeJet dΓ` via Polarization Lemma 5. Packages the per-`i` cubic form as
    the trilinear CLM `gaugeTri` (`proj`/`smulRight`), with `gaugeTri_apply` (triple-contraction eval), `gaugeTri_diag`
    (`= dGammaDiag`), `gaugeTri_basis` (basis-coefficient readout); `gaugeJet_of_diag` reads Lemma 5 at the basis triple.
    Generic in `dΓ` — the radial-identity ⟹ symmetrized-gauge step, presuming the radial identity `dGammaDiag=0` as INPUT.
  - [ ] **`rncDΓ` + `expMap_rncDΓ_diag_zero` — SCOPED (GPT-5.5-pro 2026-07-07, PURE ALGEBRA, no ODE).** The geodesic
    content is ALREADY BANKED in the value-3-jet cubic `a₃` (`expMap_value_three_jet`), so the radial identity
    `dGammaDiag(rncDΓ) v i = 0` is a pure `Finset` cancellation — NO geodesic-equation t¹-extraction. Exact spec:
    with `Γ i j k := christoffel g gi i j k p`, `dΓ∂ l i j k := pd (christoffel g gi i j k) l p`,
    `SA i l j k := ∑ a, Γ i a k * Γ a l j`, `SB i l j k := ∑ a, Γ i j a * Γ a l k`, the raw contraction-representative
    `A3raw i l j k := −dΓ∂ l i j k + SA i l j k + SB i l j k` has `∑_{ljk} A3raw i l j k v_l v_j v_k = a₃(v)_i` EXACTLY.
    ⚠ **VACUITY TRAP (must avoid):** `rncDΓraw := A3raw + dΓ∂ − SA − SB` is POINTWISE ZERO (A3raw was built to cancel),
    so `GaugeJet(rncDΓraw)=GaugeJet(0)` is VACUOUS — NOT a real gauge discharge. **Use the SYMMETRIZED coefficient**
    `A3sym i l j k := (1/6)(A3raw i l j k + A3raw i l k j + A3raw i j l k + A3raw i j k l + A3raw i k l j + A3raw i k j l)`
    (the canonical Taylor coeff), `rncDΓ := A3sym + dΓ∂ − SA − SB` (NOT pointwise zero). Then `dGammaDiag(rncDΓ) v i = 0`
    via: `dGammaDiag(A3sym)=a₃(v)_i` (symmetrization preserves the v³-contraction — a lemma), `dGammaDiag(dΓ∂)=∂Γ(v³)`,
    `dGammaDiag(SA)=`term-A, `dGammaDiag(SB)=`term-B, and `a₃ = −∂Γ + termA + termB` (its def) ⟹ sum = 0. Delicate steps
    = three `Finset.sum_comm`/reindex lemmas (∂: `j,k,l→l,j,k`; termA: `l,j,k,a→a,k,l,j`; termB: `l,j,k,a→j,a,l,k`),
    each a proved helper (NOT blind simp). Then `gaugeJet_of_diag` ⟹ `GaugeJet(rncDΓ)` — the NON-vacuous formal gauge.
    Then **`heat_a1_of_gaugeJet`** (consumer refactor) → assemble κ=1/6 given the FORMAL gauge.
  - [x] **Abstract algebraic core — DONE 2026-07-07** (`QIQTH/RNCGauge.lean`, commit 2da77e5, [AF] std-3, budget 0):
    `christSqA`/`christSqB`/`a3rawArr`/`a3symArr`/`rncDΓ` (abstract Γ, dΓ1), the crux `sum3_sym_contract` (the diagonal
    contraction `∑ f_{ljk} v³` is invariant under permuting f's 3 lower args — via 2 transposition helpers +
    `Finset.sum_comm`/`sum_congr`/`ring` composed over the 6 perms), `dGammaDiag_a3sym_eq_raw`, `expMap_rncDΓ_diag_zero`
    (`dGammaDiag(rncDΓ)=0`, tautology), and **`rncGaugeJet : GaugeJet (rncDΓ Γ dΓ1)`** via `gaugeJet_of_diag`. Non-vacuous
    (symmetrized A3sym, not the pointwise-zero raw). HONEST: the abstract algebraic core — does NOT yet GROUND `rncDΓ` in
    the exp map's actual `a₃` (fact B below), NOT the pullback metric, NOT numerical-G.
  - [x] **fact B — GROUND `rncDΓ` in the exp 3-jet — DONE 2026-07-07** (`QIQTH/RNCGaugeExp.lean`, commit 692d6b4, [AF]
    std-3, budget 0): **`a3rawArr_contract_eq_a3`** — `∑_{ljk} a3rawArr Γ dΓ1 i l j k v_l v_j v_k = a₃(v)_i` for
    `Γ:=christoffel..p`, `dΓ1:=pd(christoffel..)..p`, matching the EXACT inlined cubic of `expMap_value_three_jet`
    verbatim (∂Γ + χ²-A + χ²-B), via the three `Finset` reindex matchings (private `reindex_A`/`reindex_B`, `sum_comm`/
    `sum_congr`/`ring`, no Christoffel symmetry used); and **`exp_rncGaugeJet : GaugeJet (rncDΓ [true exp jet])`** —
    `rncGaugeJet` specialized to the genuine exp-value-3-jet-derived formal Christoffel jet. **Route-c's algebraic side is
    now COMPLETE and grounded in the actual exp map.** HONEST: does NOT reach κ=1/6 for the pullback metric (the bridge
    `rncDΓ=pd(christoffel g̃)(0)` + `ContDiff exp_p` remain — see the HONEST FINDING below), NOT numerical-G.
  - **⚠ HONEST FINDING (2026-07-07) — route-c reduces but does NOT eliminate the smooth-dependence gap.** The algebraic
    side of route-c is DONE (`rncGaugeJet`: the RNC-Christoffel linearization satisfies the gauge) and the gauge⟹κ=1/6
    side is DONE (`heat_a1_of_gauge`). But CONNECTING them for the actual exp normal coordinates is still blocked on
    `ContDiff exp_p`: (i) `heat_a1_of_gauge`'s `hgauge` is about the LITERAL `pd(christoffel g gi)(0)`, so discharging it
    at `g:=g̃` needs `rncDΓ = pd(christoffel g̃ g̃i)(0)` (the bridge — the finite-jet pullback-Christoffel transform,
    needing the Hessian-exp jet); AND (ii) merely INSTANTIATING `heat_a1_of_gauge` at `g̃` needs `hg : ContDiff ℝ ⊤ g̃`,
    hence `ContDiff exp_p` (since `g̃ y = g(exp_p y)(D exp_p y ·)(D exp_p y ·)`), which is exactly the smooth-dependence-
    of-`exp_p`-on-`v` theorem Mathlib LACKS (only pointwise `HasFDerivAt exp_p` near 0 is proved). So the HONEST endgame
    of route-c: the gauge is discharged AS A PROVEN ALGEBRAIC IDENTITY grounded in the exp value-3-jet (`rncGaugeJet` +
    fact B), but the metric-instantiation (κ=1/6 for the ACTUAL pullback metric) reduces to the single cited frontier
    `ContDiff exp_p` (smooth dependence on the initial velocity). NEVER claim κ=1/6 is unconditional for the pullback
    metric until `ContDiff exp_p` lands. Candidate future attack: does the operator fundamental solution `Φ_v`
    (`expJetFund`) depend smoothly on `v` (a second-order equilibrium-Grönwall), giving `ContDiff exp_p`? — open.
  - **⚠ ContDiff-`exp_p` VERDICT (GPT-5.5-pro consult 2026-07-07) — REACHABLE finite tower, but a 4–8 WEEK effort; CHECKPOINT.**
    Mathlib v4.30.0 genuinely LACKS C^k-dependence-of-ODE-flow-on-IC (no shortcut API; implicit-function route is CIRCULAR —
    IFT needs `exp_p` already C¹). `ContDiff k exp_p` IS reachable via the FINITE AUGMENTED JET-ODE TOWER (not a general
    smooth-dependence theorem): solve enlarged Picard–Lindelöf systems on `Phase × (Phase→L Phase) × …`. **Jet₁**
    `(Y,P)'=(F Y, DF(Y)∘P)`, IC `(p,v),1,0` — PL Lipschitz-dependence ⟹ `v↦(Y_v,P_v=Φ_v)` continuous ⟹ **ContDiff¹ exp_p**
    (needs `ContinuousOn (v↦Φ_v 1)` + `fderiv exp_p v = π Φ_v(1) ι` continuous). **Jet₂** adds `Q'(a,b)=DF(Y)Q(a,b)+D²F(Y)(P a)(P b)`,
    `Q(0)=0`, residual `S_h=P_{v+h}−P_v−Q_v(ιh,·)` Grönwall ⟹ o(‖h‖) ⟹ **ContDiff² exp_p** (`D²exp_p=π Q_v(1)(ιh,ιk)`).
    **Jet₃** adds `R'(a,b,c)=DF(Y)R+D²F(Y)(Pa)(Q(b,c))+…+D³F(Y)(Pa)(Pb)(Pc)` ⟹ **ContDiff³ exp_p**. ⚠ **DERIVATIVE-LOSS
    (new, binding):** the pullback loses one derivative (`D exp_p` appears in `g̃`), so `ContDiff² g̃` needs `ContDiff³ exp_p`
    — NOT C². Effort: C¹ ≈ days–1wk; C² ≈ 2–4wk; **C³ ≈ 4–8wk**; general C^∞ = multi-month Mathlib PR. **VERDICT: the RNC
    gauge is DISCHARGED as a proven algebraic identity (`exp_rncGaugeJet`, grounded in exp `a₃`); the κ=1/6 metric-
    instantiation reduces to the `ContDiff³ exp_p` tower — a genuine 4–8-week finite effort, the honest CITED FRONTIER.**
    Marginal value is modest (removes a carried gauge hyp; does NOT touch numerical-G or QG). Rung 1 (`ContDiff¹ exp_p` via
    the Jet₁ augmented ODE) is the available next brick if the tower is pursued — bounded, days-scale, strengthens the 1-jet
    from pointwise to continuous — but it does NOT by itself unlock κ=1/6 (needs all of C³). **ROUTE-C CHECKPOINTED HERE.**
  - [ ] **(deferred, honestly cited) `rnc_christoffel_linearJet`** — the bridge `rncDΓ = pd(christoffel g̃ g̃i) 0`; needs
    the controlled C³/Hessian jet of `exp_p` (smooth-dependence-on-`v` residue). NOT attempted until the jet exists.
- [ ] **EXP-JET4 — the pullback metric `g̃` Taylor coefficients at 0** from EXP-JET1–3: `g̃(0)=δ` (needs an orthonormal
  frame at `p`, or state relative to `g(p)`) + `∂g̃(0)=0` (from the 1-jet, EXP-JET3c STEP 3b).  `∂∂g̃(0)↔R` is NOT
  needed for the gauge if route (c) supplies `∂_{(l}Γ̃_{jk)}(0)=0` directly.
- [ ] **EXP-JET5 — discharge `hgauge`** (`∂_{(l}Γ̃^i_{jk)}(0)=0` in the normal coords) **via route (c) radial gauge
  (see the PIVOT above)** ⟹ instantiate `RNCExpansion.heat_a1_of_gauge` at `g:=g̃` ⟹ **`κ=1/6` UNCONDITIONAL given the
  metric** (the carried gauge retired).

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
- **2026-07-15 (PARAMETRIX P1 RUNG 1 — `ContDiff¹ exp_p` — DONE, PUSHED `4bc842dd`):** `ExpMapContDiff.lean` ([AF]
  std-3, budget 0). `expMap_contDiffOn_one` (`ContDiffOn ℝ 1 exp_p (ball 0 expRho)`) via `fderivExpMap_continuousOn`
  (continuous `v↦fderiv exp_p v`); crux `expFund_two_pt_diff` (`‖Φ_v 1 − Φ_w 1‖ ≤ C‖v−w‖`, the operator fundamental
  solution's Lipschitz dependence on the initial velocity) CLOSED via the operator two-point Grönwall on the Jet₁
  system (equilibrium technique, NOT the Mathlib-absent general C¹-flow theorem). Strengthens the Jacobian 1-jet
  pointwise→continuous.
- **2026-07-15 (PARAMETRIX P1 RUNG 2 — `ContDiff² exp_p` — PARTIAL / CHECKPOINT, PUSHED `30e8ef0d`):**
  `ExpMapContDiff2.lean` ([AF] std-3, budget 0). TWO green results, NOT the full `ContDiff²`:
  (i) `expMap_contDiffOn_two_of_fderiv_contDiffOn_one` — the PROVEN Rung-2 REDUCTION: `ContDiff¹ (fderiv exp_p)` on
  the ball ⟹ `ContDiff² exp_p` (Rung-1 differentiability + `fderivWithin=fderiv` on the open ball + Mathlib
  `contDiffOn_succ_of_fderivWithin`), isolating the exact remaining obligation "`Φ_v(1)` is `C¹` in `v`";
  (ii) the Jet₂ analytic ingredient `D²F = fderiv(fderiv F)` EXISTS and is `C^∞` (`contDiff_fderiv2_geodesicField`,
  `hasFDerivAt_fderiv_geodesicField`). ⚠ **STILL OPEN (the multi-week bulk, NOT a Mathlib gap):** the `D²F` closed
  form + the Jet₂ fundamental solution `Q_v` on `[0,1]` (a fresh bilinear-valued Picard–Lindelöf tower mirroring the
  `expJetFund` chain) + the parameter-residual Grönwall ⟹ `v↦Φ_v(1)` is `C¹`. `ContDiff² exp_p` is NOT yet
  unconditional. Next reachable brick: the `D²F` uniform operator-norm bound on the `[0,1]` tube (the Grönwall
  coefficient bound, analog of `expJet_fderiv_tube_bddAbove_unif`), the prerequisite for the `Q_v` PL construction.
- **2026-07-15 (RUNG 2 cont. — `D²F` uniform tube bound — DONE, PUSHED `bd159c11`):** `expJet_fderiv2_tube_bddAbove_unif`
  in `ExpMapContDiff2.lean` ([AF] std-3): `∃ Kstar≥0, ‖D²F(expTube p v t)‖ ≤ Kstar` uniformly over `‖v‖≤expRho`,
  `t∈[0,1]` — the `D²F` analog of `expJet_fderiv_tube_bddAbove_unif`. Confinement (`expTube_spec`) → fixed compact
  ball; `D²F` is `C^∞` (`contDiff_fderiv2_geodesicField`) → continuous; `IsCompact.exists_bound_of_continuousOn` on
  the ℝ-valued `q↦‖D²F q‖` (routing through the scalar norm dodges the nested-CLM `E→L E→L E` instance diamond).
  The Grönwall COEFFICIENT bound `Q_v` consumes. **STRATEGY NOTE (leaner path):** `Q_v` needs `D²F` as a BOUNDED +
  LIPSCHITZ field on the tube (the `LipschitzOnWith (fderiv F)` shape `expFund_two_pt_diff` already consumes for
  `DF`), NOT the giant `D²F` closed form — use the campaign's equilibrium-Grönwall technique. Remaining Rung-2
  bricks: (2) `D²F` Lipschitz-on-tube (`Convex.lipschitzOnWith_of_nnnorm_fderiv_le` on the confined ball, `D³F`
  bounded), (3) the `Q_v` Jet₂ fundamental-solution PL tower on `[0,1]` (mirror `expJetFund` local→shifted→glue —
  the multi-week bulk), (4) the parameter-residual Grönwall ⟹ `v↦Φ_v(1)` is `C¹` ⟹ discharge the reduction ⟹
  `ContDiff² exp_p`.
- **2026-07-15 (RUNG 2 cont. — `D²F` Lipschitz-on-ball — DONE, PUSHED `55a9f0ad`):** `expJet_fderiv2_lipschitzOnWith`
  in `ExpMapContDiff2.lean` ([AF] std-3): `∃ Ld2f, LipschitzOnWith Ld2f D²F (closedBall (p,0) (expConst·expRho))`
  — `D²F` is `C^∞`, so `ContDiffOn.exists_lipschitzOnWith` (Lipschitz-from-`C¹`-on-compact-convex) gives it directly,
  mirroring the `DF` `hLipDF` discharge (no CLM diamond here). The two `D²F` field-regularity inputs (bound +
  Lipschitz on the tube ball) `Q_v` consumes are now BOTH landed.
  **KEY STRUCTURAL INSIGHT for `Q_v`:** the Jet₂ second variation `Q^{hk}(t)` is **VECTOR-valued** (`Point n×Point n`),
  NOT CLM-valued — it solves the INHOMOGENEOUS linear ODE `Q'(t) = DF(Y_v t)·Q(t) + D²F(Y_v t)(P^h(t),P^k(t))`,
  `Q(0)=0`, whose HOMOGENEOUS part is exactly what the built `Φ_v` (`expJetFund`, coefficient `expJetPsi`)
  propagates. The inhomogeneous term `Θ^{hk}(t) = D²F(Y_v t)(Φ_v(t)(ι h), Φ_v(t)(ι k))` is continuous + bounded on
  `[0,1]` (D²F tube bound × `Φ_v` continuity²). So brick (3) decomposes: (3a) define `Θ^{hk}` + prove its `[0,1]`
  regularity (continuity + uniform bound) — the ODE well-posedness input, tractable; (3b) the inhomogeneous
  fundamental solution `Q^{hk}` on `[0,1]` (mirror `expJetFund` local→shifted→glue with a source term, or Duhamel
  against `Φ_v`) — the bulk; (3c/4) `(h,k)↦π∘Q^{hk}(1)` is the second Fréchet derivative via the residual Grönwall,
  + continuity in `v` ⟹ `ContDiff² exp_p`.
- **2026-07-15 (RUNG 2 cont. — 3a: the Jet₂ source `Θ` + regularity — DONE, PUSHED `7c5f8520`):** in
  `ExpMapContDiff2.lean` ([AF] std-3): `expJet2Rhs g gi hC p v Φ h k t := D²F(Y_v t)(Φ t (ι h))(Φ t (ι k))` (`Φ`
  abstract, mirrors `expFund_two_pt_diff`) + `expJet2Rhs_continuousOn` (`ContinuousOn.clm_apply` ×2 +
  `expTube_continuousOn` + `D²F` cont) + `expJet2Rhs_norm_le` (`‖Θ‖ ≤ Kstar·(Cphi‖h‖)·(Cphi‖k‖)`, `le_opNorm` ×2 +
  the `D²F` tube bound). The two ODE well-posedness inputs (continuity → local existence, bound → Grönwall) for the
  next brick. **3b next:** `expJet2Fund` = the `Q^{hk}` inhomogeneous fundamental solution on `[0,1]`
  (`Q(0)=0`, `Q(t)=∫₀ᵗ [DF(Y_v s)(Q s)+Θ(s)]ds`, `HasDerivWithinAt`) by mirroring `expJetFund_local→_shifted→_glue`
  with the `expJet2Rhs` source — the multi-week bilinear bulk; decompose (local→shifted→glue) + checkpoint.
- **2026-07-07 (EXP-JET3c STEP 2, operator-norm + residual-identity toolkit + TWO checkpoints):** landed green
  ([AF] std-3, budget 0) the reusable toolkit the operator residual Grönwall consumes: **`matVecCLM_opNorm_le`**
  (`‖matVecCLM c‖ ≤ n·b`), **`expJetA1_opNorm_le`** (`‖A₁‖ ≤ 2n²Mc‖v‖`, order-1), **`expJetA2_opNorm_le`**
  (`‖A₂‖ ≤ n³Nc‖v‖²`, order-2), **`expJetK0_opNorm_le`** / **`expJetK1_opNorm_le`** (`‖K₀‖,‖K₁‖` bounds on `[0,1]`),
  **`expJetPi_opNorm_le`** / **`expJetIota_opNorm_le`** (`‖π‖,‖ι‖ ≤ 1`), and **`expJet_residual_identity`** (the CLM
  ring identity `D·Φ−(A₀K₀+(A₀K₁+A₁K₀)) = D·(Φ−(K₀+K₁))+((D−(A₀+A₁))·(K₀+K₁)+A₁·K₁)`).
  ⚠ **TWO CHECKPOINTS discovered during the attempt (both blocking the projected 2-jet):**
  **(1) MATH GAP — the anchored model is only `O(‖v‖²)`-accurate, NOT `o(‖v‖²)`.**  The committed STEP-1 lemmas
  (`geodesicField_fderiv_anchored_eq`, `expJet_fderiv_tube_order2`) anchor the order-2 Jacobi coefficient to the FIXED
  `A₂ = expJetA2` (the ∂Γ-trilinear part only), giving `‖DF(Y_v t)−(A₀+A₁+A₂)‖ ≤ C‖v‖²` — a genuine Θ(‖v‖²), NOT
  little-o, because the true coefficient `Ã₂(t,v)` is `t`-DEPENDENT (the `t·∂Γ_p·v` Γ-cross-terms from the tube's
  position drift `p+tv` and velocity drift `−tΓv`, which the fixed anchor misses; the plan flagged this at STEP 1).
  Consequently the anchored model `K_v=K₀+K₁+K₂` reproduces the Jacobian's LINEAR term `−Γ_p^{sym}(v,·)` EXACTLY but its
  order-2 term is wrong — the projection `π∘K_v(1)∘ι` does NOT equal `id−Γ_p(v,·)+½T(v,v,·)` and the residual Grönwall
  yields only `O(‖v‖²)` (the strict Jacobian 1-jet), NOT the `o(‖v‖²)` 2-jet.  The honest 2-jet needs the `t`-dependent
  `Ã₂(t,v)` integrated against a `t`-dependent `K̃₂`, plus a little-o (not `≤C‖v‖²`) C²-operator Taylor remainder.
  **(2) COMPILE INTRACTABILITY — the monolithic operator Grönwall blows up.**  A fully-written `O(‖v‖²)` 1-jet theorem
  (`fderiv exp_p v = id−Γ_p^{sym}(v,·)+O(‖v‖²)`, TRUE and useful — it gives the RNC gauge `∂g̃(0)=0`) type-checks in
  pieces but the monolithic proof exceeds 32M heartbeats: the large local context (many `set`s + the `Φ` existential +
  `fderiv(geodesicField)` terms) makes instance-search/`whnf` in the CLM Banach space explode (the point-valued
  `hasFDerivAt_expMap` Grönwall compiles at 4M; the operator-valued one does not).  FIX = extract the operator Grönwall
  into a SMALL-context helper `expJet_residual_gronwall (Φ, scalar bounds) → ‖Φ 1 − (K₀ 1+K₁ 1)‖ ≤ Cε·exp KdF'` so
  instance-search sees a small context; the residual identity + opNorm toolkit above are the exact bricks it consumes.
  HONEST: the toolkit + the two precisely-scoped checkpoints — does NOT give the residual Grönwall, the 1-jet, the
  projected 2-jet, the pullback metric, or numerical-G.
- **2026-07-07 (EXP-JET3c STEP 2, order-1/2 model propagators K₁, K₂):** the closed-form order-1/2 model
  propagators `K₁`, `K₂` + their equilibrium ODEs — landed green ([AF] std-3, budget 0).  New in `ExpMap.lean`:
  the composition/nilpotency helpers **`expJetA1_comp_linF`** (`A₁A₀=0`), **`linF_comp_linF_comp`** (`A₀A₀X=0`),
  **`expJetA1_comp_linF_comp`** (`A₁A₀X=0`); the closed forms **`expJetK1`** (`K₁(t)=t·A₁+(t²/2)·A₀A₁`) with
  `expJetK1_zero`, `expJetK1_hasDerivAt` (polynomial deriv) and **`expJetK1_hasDerivAt_ode`** (`K₁'=A₀K₁+A₁K₀`);
  and **`expJetK2`** (`K₂(t)=t·A₂+(t²/2)·(A₁²+A₂A₀+A₀A₂)+(t³/6)·A₀(A₁²+A₂A₀)`) with `expJetK2_zero`,
  `expJetK2_hasDerivAt` and **`expJetK2_hasDerivAt_ode`** (`K₂'=A₀K₂+A₁K₁+A₂K₀`).  Route (as scoped): variation of
  constants collapses to POLYNOMIALS because `A₀²=0` (`linF_comp_linF`) and `A₁A₀=0` — so `K₁,K₂` are DEFINED as the
  explicit CLM polynomials and the ODEs are VERIFIED by differentiation (`hasDerivAt_pow`/`smul_const` for the
  polynomial deriv; the ODE-RHS `simp only [comp_add, comp_smul, comp_id, smul_add, <nilpotency collapses>]; abel`),
  bypassing the operator Bochner integral entirely.  This completes the model Jacobian `K_v = K₀+K₁+K₂` bricks.
  ⚠ CHECKPOINTED: the residual operator Grönwall `‖(Φ_v 1) − K_v(1)‖ ≤ C‖v‖²` (needs opNorm bounds on `A₁,A₂,K₁,K₂`)
  and the projected `L v = 1 − Γ_p(v,·) + ½T(v,v,·) + o(‖v‖²)` remain.
- **2026-07-07 (EXP-JET3c STEP 2, order-0 model propagator):** the order-0 model propagator `K₀(t)=1+t·A₀` +
  nilpotency `A₀²=0` — landed green ([AF] std-3, budget 0).  New in `ExpMap.lean`: **`linF_comp_linF`** (`A₀²=0`),
  **`expJetK0`** (`K₀(t)=1+t·A₀`), `expJetK0_zero`, `expJetK0_hasDerivAt` (`K₀'=A₀`), `linF_comp_expJetK0`
  (`A₀·K₀(t)=A₀`), and **`expJetK0_hasDerivAt_ode`** (`K₀'=A₀·K₀`).  The exact order-0 brick of the model Jacobian
  `K_v`.  ⚠ CHECKPOINTED: `K₁,K₂` (the order-1/2 operator-integral corrections), the residual operator Grönwall, and
  the projected `L y = 1 − Γ_p(y,·) + ½T(y,y,·) + o(‖y‖²)` remain.
- **2026-07-07 (EXP-JET3c STEP 1, coefficient identification):** the anchored order-2 decomposition
  `DF(p,v) = A₀ + A₁(v) + A₂(v)` — landed green ([AF] std-3, budget 0).  New in `ExpMap.lean`:
  **`geodesicField_fderiv_anchored_eq`** (the EXACT `DF(p,v) = linF + expJetA1 + expJetA2`, degree-≤2 polynomial in `v`,
  no remainder), the composed **`expJet_fderiv_tube_order2`** (`‖DF(Y_v t) − (linF+A₁+A₂)‖ ≤ C·‖v‖²` uniform in
  `t∈[0,1]`, from order-1 anchoring + the decomposition), the CLM coefficient operators **`expJetA1`** (order-1,
  velocity-bilinear Γ) / **`expJetA2`** (order-2, ∂Γ-trilinear), the generic building block **`matVecCLM`**, and helper
  `pd_trilin_reorder`.  This turns the previously only-anchored "fixed `DF(p,v)` carries the order-1 part" into the
  ACTUAL identified coefficients `A₀,A₁,A₂` (as CLMs) with a machine-checked exact decomposition — the coefficient
  input the model-Jacobian ODEs consume.  Route: `geodesicField_fderiv_apply` at `(p,v)`, `ContinuousLinearMap.ext` →
  `Prod.ext` → per-`i` Finset algebra (∂Γ block by `pd_trilin_reorder`; the two Γ blocks combined into `c₁` via
  `Finset.sum_comm`/`Finset.sum_neg_distrib`; `linarith`).  ⚠ CHECKPOINTED: the model Jacobian `K_v=K₀+K₁+K₂` from the
  triangular ODEs (`A₀²=0` ⟹ `K₀(t)=1+tA₀`, `K₁=∫₀ᵗ(1+(t−s)A₀)A₁K₀ds`, `K₂` analogously); the residual operator
  Grönwall `‖(Φ_y 1)∘ι − K_y(1)‖ ≤ C‖y‖²`; and the projected `L y = 1 − Γ_p(y,·) + ½T(y,y,·) + o(‖y‖²)` remain.
- **2026-07-07 (EXP-JET3c STEP 1, order-1 anchoring):** the tube Jacobi coefficient is `O(‖v‖²)`-close to the fixed
  `DF(p,v)` — landed green ([AF] std-3, budget 0).  New theorems in `ExpMap.lean`: **`expJet_fderiv_tube_order1`**
  (`∃ ρ>0, ∃ C≥0, ∀ ‖v‖≤ρ, ∀ t∈[0,1], ‖DF(Y_v t) − DF(p,v)‖ ≤ C·‖v‖²`), the pointwise engine
  **`geodesicField_fderiv_two_pt_opNorm_le`** (`‖DF(x,u) − DF(x',u')‖ ≤ Nc·n³(‖u‖²+‖u'‖²) + 2(Mc·n²‖u−u'‖ +
  Dc·n²‖u'‖)`), and the generic **`bilin_two_pt_diff_bound`** (two-point bilinear-difference bound, generalizing
  `christoffel_quad_diff_bound`).  This ANCHORS the order-1 coefficient: `DF(Y_v t) = DF(p,v) + O(‖v‖²)` UNIFORMLY in
  `t`, so the FIXED `t`-independent `DF(p,v)` carries the order-1 part `A₁`, reducing the remaining EXP-JET3c work to
  expanding the single fixed `DF(p,v) = A₀ + A₁ + (order-2 ∂Γ)`.  Route: the two-point opNorm bound at `(Y_v t)` vs
  `(p,v)` (velocity slots cancel, ∂Γ block by `christoffel_pd_trilin_bound` at each point, Γ-bilinear blocks by
  `bilin_two_pt_diff_bound`), fed the confinement, the Christoffel value/Lipschitz/∂Γ bounds on the ball, and the tube
  2-jet `‖(Y_v t).2 − v‖ ≤ D₂‖v‖²` (`expTube_value_two_jet` + `christoffel_bilin_bound`).  ⚠ CHECKPOINTED: read off
  `A₁, A₂` as CLM coefficients of the fixed `DF(p,v)`; the model Jacobian `K_y`; the residual operator Grönwall; and
  the projected `L y = 1 − Γ_p(y,·) + ½T(y,y,·) + o(‖y‖²)` remain.
- **2026-07-07 (EXP-JET3c STEP 1, order-0 composed):** the uniform-in-`t` order-0 `DF` expansion along the tube
  landed green ([AF] std-3, budget 0).  New theorem `expJet_fderiv_tube_order0` in `ExpMap.lean`:
  `∃ ρ>0, ∃ C≥0, ∀ ‖v‖≤ρ, ∀ t∈[0,1], ‖DF(Y_v t) − A₀‖ ≤ C·‖v‖` (`A₀=linF=DF(e)`, `Y_v=expTube p v`).  Composes the
  pointwise `geodesicField_fderiv_sub_linF_opNorm_le` with the a-priori confinement (`‖(Y_v t).2‖≤C₀‖v‖`,
  `(Y_v t).1∈closedBall p (C₀ρ)`, `expTube_spec`); `Mc` (Christoffel) and `Nc` (`∂Γ`) value bounds uniform over the
  compact confinement ball via `christoffel_pd_contDiff`→continuity→`subset_closedBall`, and
  `Nc·n³‖u‖²+2Mc·n²‖u‖ ≤ C·‖v‖` via `‖u‖≤C₀‖v‖≤C₀ρ`.  This turns the previously only-described order-0 (leading `A₀`)
  term of the uniform `DF(Y_y t)=A₀+A₁(t,y)+A₂(t,y)+o(‖y‖²)` expansion into an actual theorem.  ⚠ CHECKPOINTED: the
  order-1 coefficient `A₁` (t-independent, `= (0,i↦−∑_{jk}Γ^i_{jk,p}(η_j y_k+y_j η_k))`, with `o(‖y‖²)` operator
  remainder needing the tube 2-jet `‖(Y_y t).2−y‖=O(‖y‖²)` + Christoffel/∂Γ Lipschitz), the order-2 coefficient `A₂`
  (t-dependent), the model Jacobian `K_y`, the residual operator Grönwall, and the projected
  `L y = 1 − Γ_p(y,·) + ½T(y,y,·) + o(‖y‖²)` remain.
- **2026-07-07 (EXP-JET3c STEP 1 core):** the operator-norm "`A₀` is leading" bound landed green ([AF] std-3,
  budget 0).  New theorem `geodesicField_fderiv_sub_linF_opNorm_le` in `ExpMap.lean`: given `|Γ(x)| ≤ Mc`,
  `|∂Γ(x)| ≤ Nc`, `‖DF(x,u) − A₀‖ ≤ Nc·n³·‖u‖² + 2·(Mc·n²)·‖u‖` (`A₀=linF=DF(e)`).  The velocity slots of
  `(DF(x,u)−A₀)(ξ,η)` cancel, leaving `(0, Acc)`; `Acc` splits into a ∂Γ-trilinear form
  (`christoffel_pd_trilin_bound`) + two Γ-bilinear forms (`christoffel_bilin_bound`), bounded by `‖(ξ,η)‖` and closed
  by `ContinuousLinearMap.opNorm_le_bound`.  Composed with `expTube_value_two_jet` (`‖u‖=‖(Y_v t).2‖=O(‖v‖)`) this is
  the ORDER-0 remainder `‖DF(Y_v t) − A₀‖ ≤ C·‖v‖` of the uniform `DF(Y_v t)` expansion.  ⚠ CHECKPOINTED: the FULL
  order-2 expansion (identify `A₁(t,y)`, `A₂(t,y)` + the operator `o(‖y‖²)` remainder), the model Jacobian `K_y`, the
  residual operator Grönwall, and the projected `L y = 1 − Γ_p(y,·) + ½T(y,y,·) + o(‖y‖²)` remain.
- **2026-07-07 (EXP-JET3c STEP 1 ingredient):** the uniform-in-`t` tube value 2-jet landed green ([AF] std-3,
  budget 0).  New theorem `expTube_value_two_jet` in `ExpMap.lean`: for `‖v‖ ≤ ρ`, `∀ t∈[0,1]`,
  `‖expTube p v t − (p+t·v−½t²Γ_p(v,v), v−t·Γ_p(v,v))‖ ≤ C·‖v‖³` — the WHOLE confined tube's value 2-jet, uniform in
  `t` and exposing BOTH phase components (`expMap_value_two_jet` only projected the position endpoint at `t=1`).  This
  is exactly the tube 2-jet `Y_v(t)−e = S₁+S₂+O(‖v‖³)` the operator-valued Jacobian 2-jet's uniform `DF(Y_v t)`
  expansion consumes (compose `geodesicField_fderiv_apply` at `(x,u)=Y_v(t)` with it).  Route: the SAME
  equilibrium-anchored residual-ODE + inhomogeneous Grönwall as `expMap_value_two_jet`, but Grönwall applied at every
  `t∈[0,1]` (via the new reusable helper `gronwallBound_zero_le_exp`: `gronwallBound 0 K ε t ≤ ε·e^K` uniform in
  `t∈[0,1]`) and no position projection.  ⚠ CHECKPOINTED: the operator-norm `DF(Y_y t)` order-2 expansion (plug this
  into `geodesicField_fderiv_apply`, bound the remainder via `christoffel_taylor_bound`), the model Jacobian `K_y`,
  the residual operator Grönwall, and the projected `L y = 1 − Γ_p(y,·) + ½T(y,y,·) + o(‖y‖²)` remain.
- **2026-07-07 (EXP-JET3c STEP 0):** the closed-form Fréchet derivative of the geodesic field landed green
  ([AF] std-3, budget 0).  New theorem `geodesicField_fderiv_apply` in `ExpMap.lean`:
  `DF(x,u)(ξ,η) = (η, i ↦ −∑_{jk}[(∑_l ∂_l Γ^i_{jk}(x)·ξ_l)·u_j·u_k + Γ^i_{jk}(x)·η_j·u_k + Γ^i_{jk}(x)·u_j·η_k])`.
  Product rule (`HasFDerivAt.mul`) on the quadratic-in-`u` Christoffel-composed acceleration + `fderiv_apply_eq_sum_pd`
  for the `∂Γ` factor; assembled via `hasFDerivAt_pi.2`/`hasFDerivAt_snd.prodMk`, fderiv read off by `HasFDerivAt.fderiv`.
  This is the STEP-0 analytic foundation for identifying the order-0/1/2 coefficients (`A₀=DF(e)=linF`, `A₁`, `A₂`) of
  the uniform `DF(Y_y t)` expansion.  ⚠ CHECKPOINTED: the uniform order-2 `DF` expansion, the model Jacobian `K_y`, the
  residual operator Grönwall, and the projected 2-jet `L y = 1 − Γ_p(y,·) + ½T(y,y,·) + o(‖y‖²)` remain.
- **2026-07-07 (EXP-JET3b STEP B):** the localized first variation `HasFDerivAt exp_p (L v) v` landed green
  ([AF] std-3, budget 0).  New theorem `hasFDerivAt_expMap` in `ExpMap.lean`: for `‖v‖ < expRho`,
  `HasFDerivAt (expMap g gi hC p) (expJetPi.comp ((Φ_v 1).comp expJetIota)) v`, `Φ_v` the `[0,1]` fundamental
  solution (existential).  Jacobi field `J_k=Φ_v(·)(0,k)` (`clm_apply` on the Φ_v derivative law), residual
  `R_k=(Y_{v+k}−Y_v)−J_k` with `R_k'=DF(Y_v)R_k+N_k`, `‖N_k‖≤ε·Ctw·‖k‖` (C¹ remainder + two-point Grönwall on a
  fixed convex-compact ball), inhomogeneous Grönwall ⟹ `‖R_k 1‖=o(‖k‖)`, `expJetPi` projection closes the little-o.
  This CLOSES the checkpointed first variation; EXP-JET3 (full Jacobian 2-jet) and EXP-JET4/5 (pullback metric →
  `hgauge`) remain.
- **2026-07-07 (EXP-JET3b STEP A):** the `[0,1]` operator-valued fundamental solution `Φ_v` landed green
  ([AF] std-3, budget 0).  New lemmas in `ExpMap.lean`: `expJetPsi_comp_continuousOn` (integrand continuity on any
  `A ⊆ [0,1]`), `expJetFund_glue` (private — the partition-induction concatenation of the `N ≥ 2(KdF+1)` shifted
  normalized propagators, glued by right-composition `Φ_{j+1}(t)=if t≤τ_j then Φ_j t else U_j(t)∘Φ_j(τ_j)`, GLOBAL
  integral equation pasted by `integral_add_adjacent_intervals`/`integral_congr`/`intervalIntegral_comp_comm`,
  continuity by `union_of_isClosed`), and **`expJetFund`** — the `[0,1]` fundamental solution `Φ_v` with `Φ_v 0 = 1`,
  `ContinuousOn Φ_v [0,1]`, the GLOBAL integral equation, AND the derivative law
  `HasDerivWithinAt Φ_v (Ψ_v t (Φ_v t)) (Icc 0 1) t` on all `[0,1]` (FTC-1 via the `𝓝[Icc 0 1]` FTCFilter).  The
  partition arithmetic (`τN=1`), flagged as the stall risk, was discharged (`push_cast; ring` + `div_self`).  KEY:
  turns the prior "no Mathlib continuation theorem" checkpoint into a completed assembly.  The first-variation
  `HasFDerivAt exp_p (L v) v` (Step B) remains CHECKPOINTED.
- **2026-07-07 (EXP-JET3b global scaffolding):** the SHIFTED normalized local propagator landed green
  ([AF] std-3, budget 0). New lemmas in `ExpMap.lean`: `expJetFund_shifted` (the normalized propagator `U_j`
  on ANY `[t₀,t₀+T] ⊆ [0,1]` with `2·KdF·T ≤ 1`, `U_j(t₀)=1`, `U_j'=Ψ_v·U_j`, via the shifted operator-normed
  `IsPicardLindelof`; generalizes `expJetFund_local`) and `expJetFund_shifted_integral` (the same + interval
  continuity + the LOCAL INTEGRAL EQUATION `U_j(t)=1+∫_{t₀}^t Ψ_v(s)(U_j s) ds` by FTC-2, the gluing brick).
  KEY: this discharges the prior "no Mathlib continuation theorem" checkpoint into a pure ASSEMBLY (glue by
  `M_{j+1}:=U_j(τ_{j+1})∘M_j`, `seg_j:=U_j∘M_j`, global integral eq by induction on `j` +
  `integral_add_adjacent_intervals`/`integral_congr`, then FTC on `[0,1]`).  The partition induction, `Φ_v(1)`,
  and the first-variation `HasFDerivAt exp_p (L v) v` remain CHECKPOINTED.
- **2026-07-07 (EXP-JET3b):** the operator-valued Jacobi field `Ψ_v` + its Picard–Lindelöf data + the
  LOCAL fundamental solution `Φ_v` landed green ([AF] std-3, budget 0). New lemmas in `ExpMap.lean`:
  `expJetPsi` (`Ψ_v t M = DF(Y_v t) ∘ M`), `expJetPsi_norm_sub_le`, `expJetPsi_norm_le`,
  `expTube_continuousOn`, `expJet_fderiv_tube_bddAbove`, `expJetPsi_continuousOn`, `expJetFund_local`
  (the LOCAL short-interval fundamental solution via the full operator-normed `IsPicardLindelof`
  instantiation — the "main cost"). KEY FINDING / CHECKPOINT: the `[0,1]` fundamental solution is
  blocked at the PL `mul_max_le` interval bound — a single application reaches only `T ≲ 1/KdF` (linear
  field: `L=KdF(1+a)`, so `t=1` would need `KdF<1`); the `[0,1]` extension needs concatenating
  `≈⌈KdF⌉` local solutions, for which Mathlib has NO continuation theorem. `Φ_v(1)` + the
  first-variation residual Grönwall `HasFDerivAt exp_p (L v) v` remain CHECKPOINTED.
- **2026-07-07 (EXP-JET3a):** localized first-variation / operator-valued fundamental-solution SETUP landed green
  ([AF] std-3, budget 0). KEY FINDING: Mathlib's Picard–Lindelöf is ALREADY nonautonomous
  (`IsPicardLindelof f t₀ x₀ a r L K`, `f : ℝ → E → E`) — the "must augment time" worry is void. New lemmas in
  `ExpMap.lean`: `expJetIota`, `expJetPi`, `geodesicField_differentiable`, `hasFDerivAt_geodesicField_fderiv`,
  `expJet_linVariation_residual_deriv` (residual identity `R'=DF(Y₁)R+N`), `geodesicField_uniform_C1_remainder`
  (uniform C¹ Taylor remainder on a convex compact set). The `Φ_v` construction + the `HasFDerivAt exp_p (L v) v`
  little-o are CHECKPOINTED (EXP-JET3b) — no missing Mathlib theorem, a large assembly effort.
- **2026-07 (scoped):** GPT-5.5-pro (high) overturned the prior "gated on general smooth-dependence" verdict: the
  pullback metric's finite Taylor coefficients at 0 need only finite jets of `exp_p` at 0, reachable by the
  equilibrium two-point-Grönwall technique (value 2-/3-jet + localized Jacobian expansion) — NOT the general theorem.
  Concrete second-/third-difference residual estimates + the `fderiv`-field caveat given. Start EXP-JET1 (value 2-jet).
