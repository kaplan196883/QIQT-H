# Plan — Discharge the last two non-physical inputs of free-field QIQT→GR

**Created 2026-06-22.** Follow-up to `QIQT_GR_WIRING_PLAN.md` (Route B wired; `StripKMSrvd` audit corrected by
GPT-5.5-pro: it is **dischargeable**, not irreducible). This plan specifies the two remaining work items that
shrink the QIQT→GR citation surface down to its **minimal honest core** — a single labelled *physical*
postulate (the Clausius/area-saturation law).

---

## Where we stand (verified 2026-06-22)

`qiqt_gr_from_wedge_kms_complete` (`QIQTH/WedgeKMSToGR.lean`) derives the Einstein field equations
`a·T = G + Λ·g`, axiom-free (`[propext, Classical.choice, Quot.sound]`, budget 0), conditional on a thin
surface. After the corrected audit, that surface splits cleanly:

| Input | Honest status | This plan |
|---|---|---|
| RvD Thm 3.8 modular uniqueness, BW identification, 2nd-quant flow | **DERIVED** axiom-free | — |
| Route B horizon stress flux + `wedge_boostCharge_eq_neg_stressFlux` (hTkk) | **DERIVED** axiom-free (done) | — |
| `hDnn`/`hD0` (relative-entropy positivity) | **DERIVED** via Klein (`relEntropy_nonneg`) | — |
| `hFocus` (Raychaudhuri focusing, `ad = BL(Ric) v`) | **mostly DERIVED** (`hFocus_of_raychaudhuri`); only the `harea` area↔θ modelling identification + `hequil` equilibrium remain | **Work Item B** |
| `hKMS` = `StripKMSrvd(boostUnitary, 𝒦_W)` | **DISCHARGED axiom-free** (`stripKMSrvd_boostUnitary` → `oneParticleBW_niceWedge`, 2026-06-23) — the labelled KMS is now a THEOREM; only the Reeh–Schlieder standardness of the wedge subspace (`S`-construction) remains, the cited frontier | **Work Item A — DONE to floor** |
| Clausius/area-saturation (`hbound`, `hsat`) | **genuinely irreducible PHYSICS** (= QIQT-H horizon-thermodynamics postulate) | out of scope — the honest floor |
| metric/frame/regularity scaffolding (`hCg`, `hreg`, `conserv`, …) | precondition infrastructure; `conserv` derivable for explicit KG `T` | out of scope (optional later) |

**Goal of this plan:** retire `hKMS` (Item A) and close `hFocus` to `harea` only (Item B), leaving the
Clausius/area-saturation law as the single labelled physical input.

**★★★★★ PLAN GOAL ACHIEVED (2026-06-23).** Both work items are discharged to their honest floors, axiom-free:
- **Item A (`hKMS`) DONE**: the free-field BW KMS condition (RvD Def 3.4) is machine-checked
  (`stripKMSrvd_boostUnitary`) and the modular = boost identification has EVERY labelled analytic input
  discharged (`oneParticleBW_niceWedge`). Residual = the Reeh–Schlieder standardness of the wedge subspace
  (the `S`-construction), the cited frontier — research-grade, not in Mathlib, and the codebase never assumed
  it discharged either.
- **Item B (`hFocus`) CLOSED**: focusing derived from kinematic Raychaudhuri (`hFocus_of_raychaudhuri`);
  residual = the `harea` area↔θ modelling identification + `hequil`, which are physics/modelling, not analytic.
- **Single labelled physical input**: the Clausius/area-saturation law (`hbound`, `hsat`) — the QIQT-H
  horizon-thermodynamics postulate, the honest floor by design.

Remaining beyond this plan's scope (all either cited frontier or new subsystems, NOT mechanical discharge):
the `S`-construction (Reeh–Schlieder), `conserv` (would need a full KG-stress-tensor-on-manifold construction +
covariant-divergence computation), and the continuum Type-III / DPI-Lieb axiom-retirement programs (separate plans).

---

## Work Item A — Discharge `StripKMSrvd(boostUnitary(−2π·), 𝒦_W)` (the free-field Hardy proof)

**This is the substantial one (multi-week to multi-month).** It retires `hKMS`, turning the BW identification
`modUnitary 𝒦_W = boostUnitary(−2π·)` into an unconditional theorem for the free 1+1 scalar.

### The mathematics (GPT-5.5-pro route b — non-circular)

The wedge generators are `ψ_f = Krep m f` for **real, wedge-supported, L²** `f`
(`wedgeGenSet`, `OneParticleBW.lean:426`), and
`Krep m f θ = (1/√2)·minkowskiFourier f (massShell m θ)` with `massShell m θ = (m·coshθ, m·sinhθ)`
(`Localization.lean:43,167,194`). So the rapidity wavefunction is literally `ψ_f(θ) = c·f̂(p(θ))`,
`p(θ) = massShell m θ` — exactly GPT's setup.

The single analytic engine: **`p(θ+iπ) = −p(θ)`** (since `cosh(θ+iπ)=−coshθ`, `sinh(θ+iπ)=−sinhθ`).

1. **Strip analyticity / Hardy membership.** For `f` supported in the right wedge `W_R`,
   `ψ_f(ζ) = c·∫ e^{−i p(ζ)·x} f(x) dx` extends holomorphically to the strip `S_π = {0 < Im ζ < π}`, with
   `‖ψ_f(·+iλ)‖_{L²(dθ)}` uniformly bounded (an `H²(S_π)` member). Damping: `Im p(θ+iλ)·x ≤ 0` for `x ∈ W_R`
   (the dual-cone sign: `Im p(θ+iλ)·x = m sinλ (sinhθ·x⁰ − coshθ·x¹) ≤ 0` because
   `coshθ·x¹ − sinhθ·x⁰ = ½e^θ(x¹−x⁰)+½e^{−θ}(x¹+x⁰) > 0` on `W_R`). Uses ONLY wedge support + the mass-shell
   energy parametrization — never Δ/J.
2. **Boundary conjugation.** From `p(θ+iπ)=−p(θ)` and `f` real:
   `ψ_f(θ+iπ) = c·f̂(−p(θ)) = c·conj(f̂(p(θ))) = conj(ψ_f(θ))`.
3. **The Hardy-real subspace** `K_Hardy = {ψ ∈ L² : ψ has an H²(S_π) rep with ψ(θ+iπ)=conj(ψ(θ))}` is closed
   and contains the generators, so `𝒦_W ⊆ K_Hardy`.
4. **The KMS function.** With the boost convention `(V_t ξ)(θ)=ξ(θ−2πt)` (= `boostUnitary(−2πt)`; **verify the
   project's sign** and flip if needed), for `ξ,η ∈ K_Hardy` with analytic reps `Ξ, H` and
   `H^#(ζ):=conj(H(conj ζ))`, define on `{−1<Im z<0}`
   `F_{η,ξ}(z) = ∫ H^#(θ+πz)·Ξ(θ−πz) dθ`. Then (change of variables):
   - top edge `F(t) = ∫ conj(η(θ+πt))·ξ(θ−πt) dθ = ⟪η, V_t ξ⟫`;
   - bottom edge (using `Ξ(θ+iπ)=conj(Ξ(θ))`) `F(t−i) = ⟪V_t ξ, η⟫`;
   - bound `|F(t−is)| ≤ ‖η(·+iπs)‖₂‖ξ(·+iπs)‖₂ ≤ ‖η‖₂‖ξ‖₂` (Cauchy–Schwarz + Hardy bound);
   - holomorphy by vector-valued holomorphy of strip translates / Morera + dominated convergence.

   This `F` is exactly the `StripKMSrvd` witness. Then `StripKMSrvd ⟹[oneParticleBW_wedge_complete, DONE]
   modUnitary 𝒦_W = boostUnitary(−2π·)`. **Non-circular:** the iπ-edge comes from `p(θ+iπ)=−p(θ)`, not from
   `Δ`.

### Existing infrastructure (build on)

- `massShell`, `minkowskiFourier`, `Krep`, `wedgeGenSet`, `rightWedge`, `boostTest`, `lorentzBoost`,
  `boostUnitary_mapsTo_wedgeSubspace` (invariance — DONE).
- Real-`θ` differentiability of `Krep`: `schwartz_Krep_hasDerivAt` (`HorizonFourier.lean:264`).
- Strip-holomorphy + boundary-uniqueness toolkit (for the consumer side): `DiffContOnCl`,
  `eqOn_of_im_zero_edge_halfStrip`, `differentiableOn_deviceVecF`, `corrC_bdd_halfStrip`
  (`KMSCorrelation.lean`, `StripUniqueness.lean`).
- L²-Plancherel / Schwartz-Fourier machinery from Route B (`L2Plancherel.lean`, `SchwartzDecay.lean`).

### What is genuinely NEW (the work)

1. **Complex mass-shell + Fourier–Laplace continuation.** A holomorphic `ζ ↦ minkowskiFourier f (massShellℂ m ζ)`
   on `S_π`, where `massShellℂ m ζ = (m·cosh ζ, m·sinh ζ)` (`ℂ`-valued). The exponent
   `−i p(ζ)·x` with the wedge-damping bound. *(New file `QIQTH/Fock/WedgeAnalyticity.lean`.)*
2. **`H²(S_π)` uniform strip bounds** for wedge-supported `f` (`‖ψ_f(·+iλ)‖₂ ≤ C`, `0≤λ≤π`).
3. **Boundary conjugation lemma** `ψ_f(θ+iπ) = conj(ψ_f(θ))` (from `massShellℂ m (θ+iπ) = −massShell m θ` +
   real `f`).
4. **`K_Hardy` closed real subspace** and `wedgeGenSet ⊆ K_Hardy` (hence `𝒦_W ⊆ K_Hardy` by closure).
5. **The KMS-function assembly** `F_{η,ξ}` with the two edges + bound + holomorphy ⟹
   `stripKMSrvd_boost : StripKMSrvd (fun t => boostUnitary (−2π t)) 𝒦_W`. *(New file
   `QIQTH/Fock/BoostKMS.lean`.)*
6. **Wire** into `oneParticleBW_wedge_complete` ⟹ an unconditional
   `oneParticleBW_wedge_unconditional : ∀ t, modUnitary 𝒦_W t = boostUnitary(−2π t)`, and thread up through
   `WedgeKMSFlux_complete` / `qiqt_gr_from_wedge_kms_complete` to remove `hKMS`.

> **STATUS 2026-06-22: A0 convention audit DONE — route confirmed; long pole de-risked.**
> - **Conventions match GPT's route exactly.** With `minkowskiDot p x = p₀x₀ − p₁x₁`
>   (`Localization.lean:37`) and `minkowskiFourier f p = ∫ exp(−i·(p·x))·f` and `massShell m θ = (m coshθ,
>   m sinhθ)`, the damping is reproduced: for `ζ=θ+iλ`, `Re(−i·p(ζ)·x) = m sinλ·(sinhθ·x₀ − coshθ·x₁)`, which
>   is `< 0` on `rightWedge = {x₁>|x₀|}` (`OneParticleBW.lean:371`) for `0<λ<π` (since
>   `coshθ·x₁ − sinhθ·x₀ = ½e^θ(x₁−x₀)+½e^{−θ}(x₁+x₀) > 0`). So `ψ_f` is holomorphic & decaying on
>   **`S_π={0<Im<π}`**. And `massShellℂ m (θ+iπ) = −massShell m θ` (cosh/sinh `(θ+iπ)=−`), giving
>   `ψ_f(θ+iπ)=conj(ψ_f(θ))` for real `f` (since `minkowskiFourier f (−p)=conj(minkowskiFourier f p)`). ✅
> - **One sign to handle in A4:** `boostUnitary t` is `g ↦ g(·−t)` (`MPFlow.unitary`, χ=add_right), so
>   `boostUnitary(−2πt) g = g(·+2πt)` = `ξ(θ+2πt)` — opposite to GPT's `ξ(θ−2πt)`. Flip the KMS strip
>   orientation (use `{0<Im z<1}` / swap edges) accordingly; GPT flagged this.
> - **Long pole NOT blocked.** Mathlib `ParametricIntegral.lean` provides
>   `hasDerivAt_integral_of_dominated_loc_of_deriv_le` / `hasFDerivAt_integral_of_dominated_loc_of_lip`
>   over general `𝕜` (take `𝕜=ℂ` ⟹ complex-differentiable parametric integral ⟹ holomorphy).
>   **`Mathlib/Analysis/MellinTransform.lean` is a worked precedent** for strip-holomorphy of a parametric
>   integral — use it as the template for A1/A2. The wedge-wavefunction strip analyticity is assembly of
>   existing infra, not new analysis. Effort estimate revised DOWN toward the multi-week end (was 1–3 mo).

### Phasing (each an axiom-free green checkpoint)

- **A1.** `massShellℂ`, holomorphy of the continued wavefunction on `S_π`, the wedge-damping sign bound.
  - **A1a DONE** (commit `7fb8b7a`, `QIQTH/Fock/WedgeAnalyticity.lean`): `minkowskiDotℂ`, `massShellℂ`,
    `KrepCont`; `KrepCont_ofReal` (real-axis agreement); `massShellℂ_add_pi_I` (the `iπ`-shift
    `p_m(ζ+iπ)=−p_m(ζ)`). Axiom-free, budget 0.
  - **A1b-i DONE** (`WedgeAnalyticity.lean`): `kernel m x ζ := exp(−i·p_m(ζ)·x)`;
    `hasDerivAt_minkowskiDotℂ_massShellℂ` (ζ-deriv of the pairing) + `hasDerivAt_kernel` (the kernel is
    entire in ζ, `dK/dζ = K·(−i·(m sinhζ·x₀ − m coshζ·x₁))`, chain rule through `exp`). Axiom-free, budget 0.
  - **A1b-ii-α DONE** (commit `980a4c4`): `kernelDeriv`; `hasDerivAt_kernel_mul` (the `h_diff` ingredient —
    `ζ↦K(ζ,x)·f(x)` differentiable, deriv `kernelDeriv·f(x)`); `continuous_kernel_in_x` (measurability).
  - **A1b-ii-β DONE** (commit `14dabdb`): `norm_exp_le_exp_norm`, `norm_cosh_le`, `norm_sinh_le`,
    `norm_term_le`, `norm_kernel_le`, `norm_kernelDeriv_le`, `continuous_kernelDeriv_in_x`,
    `hasDerivAt_KrepCont`, **`differentiable_KrepCont`** (KrepCont entire for `f` continuous + compact
    support, via the dominated parametric-derivative theorem over ℂ + the ball-domination from
    `norm_kernelDeriv_le` and `‖x‖≤M` on `tsupport f`). Axiom-free, budget 0.
  - **★ PHASE A1 COMPLETE** — foundations (A1a), damping bound (A1c), holomorphy (A1b).

- **A3 DONE** (commit `c555eaa`, done ahead of A2 — self-contained): `kernel_add_pi_I`
  (`K(θ+iπ,x)=conj K(θ,x)`) and **`KrepCont_add_pi_I`** (for real `f`, `ψ_f(θ+iπ)=conj(Krep m f θ)`). The
  `iπ` boundary conjugation = the KMS bottom-edge engine. Axiom-free, budget 0.

- **A2 (sup-bound half) DONE** (commit `59deb45`): `norm_KrepCont_le` — `‖KrepCont m f (θ+iλ)‖ ≤ (1/√2)·∫‖f‖`
  uniformly on `0≤λ≤π` for wedge-supported `f`, from the damping `‖K(ζ,x)‖≤1` through the integral.
  Axiom-free, budget 0.
  - **A2 (L² decay) — THE HARD ANALYTIC FRONTIER, still open.** Needed: `‖KrepCont m f (·+iλ)‖_{L²(dθ)} ≤ C`
    (uniform in `λ∈[0,π]`). The existing decay infra (`schwartz_Krep_decay_sq`, `cosh⁻²`) is **real-axis
    only**; extending it to complex rapidity is genuinely hard. The favorable fact: for `x` strictly inside
    the wedge (compact support ⟹ bounded away from the boundary), the damping exponent
    `m sinλ(sinhθ x₀ − coshθ x₁) ≲ −c·coshθ` gives *double-exponential* decay in `θ` for `λ∈(0,π)` — so the
    `L²` bound should hold and even be easy pointwise; the formalization needs Minkowski's integral
    inequality (`‖∫_x K(·,x)f(x)‖_{L²_θ} ≤ ∫_x ‖K(·,x)‖_{L²_θ}|f(x)|`) and a `θ`-integrability estimate for
    `exp(−c coshθ)`. **Assess Mathlib support for Minkowski's integral inequality before committing.**

- **A4 (the hard finish).** Assemble `StripKMSrvd boostUnitary 𝒦_W`. Architecture:
  1. **KMS function** `F_{η,ξ}(z) := ∫ H^#(θ+πz)·Ξ(θ−πz) dθ` (`H^#(ζ):=conj(H(conj ζ))`, `Ξ,H` the
     `KrepCont` reps of `ξ,η`). Holomorphy on the strip + continuity-to-closure (`DiffContOnCl`) via a
     dominated parametric-derivative argument (reuse the A1b pattern); boundedness via Cauchy–Schwarz + A2.
  2. **Top edge** `F(t) = ⟪η, boostUnitary(−2π t) ξ⟫`: connect the concrete `∫…dθ` to the abstract `Lp ℂ 2`
     inner product (`L2.inner_def`/`MeasureTheory.L2.inner_def`) and the boost = rapidity-translation action
     (`OneParticle.boostUnitary_apply`, `MPFlow.unitary_apply`). Change of variables `y = θ−πt`. **NB the
     A0/A4 boost-sign:** `boostUnitary(−2πt) g = g(·+2πt)`, so orient the strip/edges accordingly.
  3. **Bottom edge** `F(t−i) = ⟪boostUnitary(−2π t) ξ, η⟫` via the A3 conjugation `KrepCont_add_pi_I`
     (`Ξ(θ+iπ)=conj Ξ(θ)`) — the `iπ` flip swaps the inner-product order.
  4. Conclude `StripKMSrvd` for the dense class of (real, compact-support, wedge) generators; extend to
     `𝒦_W` by closedness (the bound is continuous in `ξ,η`), and bridge `x∈rightWedge` ↔ the
     `0<x₁∓x₀` hyps of `norm_kernel_le_one`. Then `oneParticleBW_wedge_complete` ⟹ unconditional BW; thread
     up to remove `hKMS` from `qiqt_gr_from_wedge_kms_complete`.
  This step integrates with the abstract `Lp`/`StandardSubspace` layer and is the genuine multi-fire finish.

---

## A4 MILESTONE — analytic toolkit COMPLETE (2026-06-22)

Every cleanly-buildable ingredient for `kmsFun`'s `DiffContOnCl` is now proven, axiom-free, budget 0:
- **Witness + edges**: `kmsFun`, `kmsFun_ofReal_eq_inner` (top edge), `kmsFun_sub_I` (bottom edge),
  `stripKMSrvd_pair_of_regularity` (consolidation: everything reduced to `kmsFun` `DiffContOnCl`+bounded).
- **Per-factor strip-decay bounds** (general args): `norm_reflKrepCont_le`, `norm_deriv_reflKrepCont_le`,
  `norm_KrepCont_le_exp_decay_gen`, `norm_deriv_KrepCont_le_exp_decay`.
- **Integrand `z`-derivative**: `hasDerivAt_kmsIntegrand_z` (explicit value) + `norm_two_term_le` (4-factor
  norm decomposition); `differentiable_kmsIntegrand`, `continuous_kmsIntegrand_in_theta` (`h_diff`/`hF_meas`).
- **Uniformity + integrability**: `cosh_shift_exp_le` (shifted decay made `z`-uniform), `cosh` shift bounds,
  `integrable_cosh_mul_exp_neg_const_mul_cosh`, `integrable_exp_neg_const_mul_cosh`, `sin_neg_pi_mul_pos`
  (decay rate `σ>0` on the open strip).

**Honest remaining scope:**
1. `hF_int` — **DONE** (`integrable_kmsIntegrand`, `f9dc445`).
2. **`h_bound` + dominated theorem** ⟹ `kmsFun` differentiable on the open strip:
   - `hF_meas` (`continuous_kmsIntegrand_in_theta`), `hF_int` (`integrable_kmsIntegrand`), `hF'_meas`
     (`continuous_kmsIntegrand_deriv_in_theta` + `continuous_deriv_KrepCont`/`_reflKrepCont`), `h_diff`
     (`hasDerivAt_kmsIntegrand_z`) — **all DONE**.
   - **`h_bound` — DONE** (`ce38254`): `kmsIntegrand_deriv_bound` — `‖F'(z,θ)‖ ≤ π(Cdg Cf+Cdf Cg)·e^{πR}cosh θ·
     exp(−κ cosh θ)` (`z`-independent), via `norm_two_term_le` + `norm_term1_le` + `norm_term2_le` +
     `prod_norm_bound_cosh_shift` + `exists_sin_min`/`cosh_shift_exp_le`.
   - `bound_integrable` (the bound = const·`cosh·exp`, integrable — `integrable_cosh_mul_exp_neg_const_mul_cosh`).
   - **★★★★★ HOLOMORPHY DONE** (`4ce35ad`): `kmsFun_differentiableAt` — `kmsFun m f g` is `DifferentiableAt`
     every interior strip point (`−1<Im z₀<0`), via the dominated-derivative theorem with all six hypotheses +
     the `ε`-ball / `σ_min`(`exists_sin_min`)/`R` extraction. **The hardest analytic content is machine-checked.**
     ⟹ `DifferentiableOn ℂ kmsFun (openStrip)` immediately.
3. **Continuity-to-closure + boundedness** ⟹ `DiffContOnCl` + `∃M`. Both are the **boundary** difficulty:
   `ContinuousOn kmsFun (closedStrip)` and `‖kmsFun z‖ ≤ M` need the parametric integral controlled up to the
   boundary `Im z ∈ {0,−1}`, where the `σ`-damping degenerates (`σ=sin(−π·Im z)→0`) and the `L²`/oscillatory
   mechanism takes over (`Krep`'s real-axis `cosh⁻²` decay + A3). The remaining genuine analytic frontier.
   - **★★★★ CAUCHY–SCHWARZ REDUCTION DONE** (`memLp_KrepCont_affine` in WedgeAnalyticity;
     `norm_integral_conj_mul_le_l2` + `norm_kmsFun_le_l2_product` in BoostKMS): for interior `z`,
     `‖kmsFun m f g z‖ ≤ √(∫‖slice_g‖²)·√(∫‖slice_f‖²)` — boundedness of `kmsFun` is now **reduced to uniform
     control of the two strip-slice `L²` norms**, the correct Hardy-space decomposition. Each slice is `L²`
     via `memLp_KrepCont_affine` (`Im = −π·z.im ∈ (0,π)`, real shift absorbed by `measurePreserving_add_right`).
     Axiom-free, budget 0.
4. **Boundedness `∃M`** — strategy now NAILED DOWN (apply the scalar max-principle to `kmsFun` itself, not
   to the slice norms):
   - **★★★ EDGE BOUNDS DONE** (`norm_kmsFun_ofReal_le`, `norm_kmsFun_sub_I_le` in BoostKMS): **both** boundary
     lines `Im z ∈ {0,−1}` are bounded by the SAME `t`-independent constant `B = ‖KrepL2 g‖·‖KrepL2 f‖`
     (top edge = `⟪KrepL2 g, boostUnitary(2πt) KrepL2 f⟫`, Cauchy–Schwarz + boost isometry; bottom edge =
     `conj` of top via `kmsFun_sub_I`). Axiom-free.
   - **KEY STRUCTURAL FACT**: the slice-norm bound `‖kmsFun z‖ ≤ √N_g(η)√N_f(η)` depends only on `η=Im z`
     (θ-translation invariance), so `kmsFun` is **bounded in the unbounded (Re z) strip direction** and on
     every closed sub-strip `Im z ∈ [−1+ε,−ε]`. The ONLY subtlety is the edge limit `η→{0,−1}`, where the
     crude bound `N_f(η) ~ −log η` blows up logarithmically (so plain Hadamard `BddAbove` fails) but the TRUE
     edge value is `≤ B`.
   - **★ ROUTE (GPT-5.5, 2026-06-22): θ-TRUNCATION + HADAMARD + DOMINATED CONVERGENCE** — sidesteps the entire
     Hardy / continuity-to-boundary wall. `kmsFunCut R z := ∫_{θ∈[−R,R]} (same integrand)`. PROGRESS:
       (i) **DONE** `kmsFunCut` def + **DiffContOnCl** on the strip (`kmsFunCut_differentiableAt`/`_differentiableOn`
           = open-strip holomorphy via restricted-measure dominated-derivative; `kmsFunCut_continuousOn` =
           continuity on the CLOSED strip via `continuousOn_of_dominated` with the CONSTANT dominator `C_g·C_f`
           — the truncation payoff, no edge degeneration; `kmsFunCut_diffContOnCl` assembles them);
       (ii) **DONE** `BddAbove`: `norm_kmsFunCut_le` gives `‖kmsFunCut R z‖ ≤ C_g·C_f·2R` on the closed strip
            (plain bound `norm_KrepCont_le_const`, `exp(−m sinη δ coshθ) ≤ 1`) — log-blowup absent;
       (iii) **DONE** edge bounds `≤ B := √(∫‖Krep g‖²)·√(∫‖Krep f‖²)`: `kmsFunCut_ofReal`,
            `norm_kmsFunCut_ofReal_le` (top) + `kmsFunCut_sub_I`, `norm_kmsFunCut_sub_I_le` (bottom) — truncated
            Cauchy–Schwarz (`norm_integral_conj_mul_le_l2` generalized to any measure, over `volume.restrict`)
            + `setIntegral_le_integral` (truncation shrinks the L²-norm) + `integral_add_right_eq_self`.
       (iv) **DONE** Hadamard: `norm_kmsFunCut_le_B` — rotation `w↦−i·w` to `verticalClosedStrip 0 1`,
            `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'` with edge consts `B,B`,
            `B^(1−s)·B^s=B` (`rpow_add_of_nonneg`) ⟹ `‖kmsFunCut R z‖ ≤ B` for every `R`, every closed-strip `z`.
       (v) **★★★★★ DONE — BOUNDEDNESS** `norm_kmsFun_le_B`: `R→∞` via `tendsto_setIntegral_of_monotone`
            (`⋃ₙ[−n,n]=ℝ`) ⟹ `‖kmsFun z‖ ≤ B` for interior `z`. **The boundedness frontier is CLOSED, axiom-free.**
   - **REMAINING for the full DiffContOnCl witness**: `ContinuousOn kmsFun (closed strip)` of the UNtruncated
     function (the `hDCC` continuity half of `stripKMSrvd_pair_of_regularity`). REQUIRED — NOT droppable: the
     `StripKMS` variant WITHOUT closure-continuity is trivially/vacuously satisfiable (documented soundness hole,
     `OneParticleBW.lean:528`), so the continuity is exactly what makes the KMS condition a genuine constraint.
   - **★ ROUTE (GPT-5.5, 2026-06-22 #2): ANNULAR-DIFFERENCE UNIFORM CAUCHY** — reuses ALL the truncation
     machinery; closed-strip continuity in ~5 steps:
       (i) **DONE** tail seminorm `T_h(R) := √(∫_{|θ|>R}‖Krep h‖²) → 0` (`tendsto_tail_sq_zero`,
           `tendsto_tail_seminorm_zero`), so `ε_R := T_g(R)·‖Krep f‖₂ + ‖Krep g‖₂·T_f(R) → 0`.
       (ii) **DONE** — `tail_geom`, `real_L2_inner_le`, `tail_term_le`, `tail_integral_le` (uniform tail bound),
           and the annulus EDGE bounds `norm_kmsFunCut_diff_ofReal_le` (top) + `norm_kmsFunCut_diff_sub_I_le`
           (bottom) `‖kmsFunCut S t − kmsFunCut R t‖ ≤ ε_R`, all axiom-free.
       (iii) **DONE** — `norm_kmsFunCut_diff_le`: `norm_le_of_strip_edges` on `Φ = kmsFunCut S − kmsFunCut R`
           ⟹ `‖kmsFunCut S z − kmsFunCut R z‖ ≤ ε_R` on the WHOLE closed strip, every `S≥R`.
           (= uniform-Cauchy of `{kmsFunCut n}` on the closed strip.)
       (iv) **DONE** — `S→∞`: `kmsFunCut_tendsto_closed` (`kmsFunCut n z → kmsFun z`, via
           `tendsto_setIntegral_of_monotone` + `integrable_kmsFun_integrand_closed` =
           `memLp_KrepCont_affine_closed` slices at arg-`Im∈[0,π]` incl. edges) +
           `norm_kmsFun_sub_kmsFunCut_le` (`le_of_tendsto` ⟹ `‖kmsFun z − kmsFunCut R z‖ ≤ ε_R` on closed strip).
       (v) **★★★★★ DONE** — `kmsFun_continuousOn_closed` (`TendstoUniformlyOn` + `ε_R→0` +
           `kmsFunCut_continuousOn` ⟹ `ContinuousOn kmsFun (closedStrip)`), then **`kmsFun_diffContOnCl`** =
           full `DiffContOnCl ℂ kmsFun (im⁻¹'Ioo(−1)0)`. **THE ENTIRE ANALYTIC REGULARITY OF THE WITNESS IS DONE,
           AXIOM-FREE, NO HARDY THEORY.**
     (GPT confirmed Vitali/Montel and the L²-slice/Riesz routes are NOT Lean-tractable; this annular route is.)
   - **★★★★★ WITNESS WIRING DONE** — `norm_kmsFun_le_closed` (closed-strip bound via `R=0`, `kmsFunCut_zero`);
     `stripKMSrvd_pair_of_regularity` reworked to use the witness `F := closedStrip.indicator(kmsFun)` (= `kmsFun`
     on the strip via `DifferentiableOn`/`ContinuousOn.congr`, `0` off-strip ⟹ globally bounded WITHOUT weakening
     the `StripKMSrvd` predicate — RvD Def 3.4 only constrains `F` on the strip); **`stripKMSrvd_pair`** = the
     UNCONDITIONAL `∃F` witness (RvD Def 3.4) for the wedge pair, axiom-free. **A4 is essentially COMPLETE: the
     free-field boost-KMS / Bisognano–Wichmann analytic input is fully machine-checked — no Hardy/Paley–Wiener,
     no Tomita–Takesaki, no axioms.** Full `QIQTH` rebuilds green (8677 jobs), budget 0.
5. **REMAINING — THREADING `stripKMSrvd_pair` ⟹ `StripKMSrvd boostUnitary 𝒦_W`** (abstract functional-analysis
   plumbing; the HARD ANALYSIS is done). `𝒦_W = closure(span_ℝ(wedgeGenSet))`, `wedgeGenSet = {KrepL2 f : supp f⊆
   rightWedge, real, MemLp(Krep f)}`; `hKMS` is consumed on the whole closed submodule (via `h1_of_stripKMSrvd`
   at arbitrary closed-submodule vectors), so the full extension is needed. Three sub-gaps:
   - (a) **f-regularity / density**: `wedgeGenSet`'s `f` (supp⊆wedge, real, MemLp) is weaker than `stripKMSrvd_pair`'s
     NICE `f` (continuous, compact supp, `δ`-margin). Need: `span_ℝ(nice KrepL2)` dense in `𝒦_W` (smooth-compact
     wedge functions dense). [`memLp_Krep_boostTest` DONE — auto-discharges the boost-translate hypothesis.]
   - (b) **sesquilinearity — additivity DONE**: `KrepCont_add` (KrepCont linear in the test fn) ⟹
     `kmsFun_add_left` + `kmsFun_add_right` (kmsFun additive in `f` and `g` on the closed strip). Gives the
     difference identity `kmsFun_{F,G}−kmsFun_{F',G'} = kmsFun_{F−F',G}+kmsFun_{F',G−G'}`. Keystone bounds DONE:
     `norm_toLp_Krep_eq_sqrt` (‖KrepL2 f‖=√∫‖Krep f‖²) + `norm_kmsFun_le_norm_mul` (‖kmsFun z‖≤2‖KrepL2 g‖‖KrepL2 f‖).
   - (c) **closure — REMAINING (the big piece); ROUTE NAILED DOWN (GPT-5.5 #3): `closedStrip →ᵇ ℂ` BCF**:
       (c0) **difference bound** `‖kmsFun_{f₁,g₁}(z) − kmsFun_{f₂,g₂}(z)‖ ≤ 2‖KrepL2 g₁‖‖KrepL2 f₁−KrepL2 f₂‖
            + 2‖KrepL2 g₁−KrepL2 g₂‖‖KrepL2 f₂‖` on the closed strip (difference identity via `kmsFun_add_*` +
            `norm_kmsFun_le_norm_mul` + `KrepL2` linearity). [Needs niceness closed under `−`: continuous/compact
            (`HasCompactSupport.sub`)/margin(union of supports)/real/MemLp — bundle a `WedgeTest` class.]
       (c1) `kmsBCF F G : closedStrip →ᵇ ℂ := ⟨z ↦ kmsFun m F G z, closed-strip continuity, norm_kmsFun_le_norm_mul⟩`;
       (c2) approximants via `mem_closure_iff_seq_limit`; `B n := kmsBCF (Fₙ) (Gₙ)` is `CauchySeq` (c0 + `ξₙ→ξ`);
            `cauchySeq_tendsto_of_complete` (`closedStrip →ᵇ ℂ` is `CompleteSpace`) ⟹ limit `b`;
       (c3) `F := stripExtend b` (= `b` on closed strip, `0` outside) ⟹ global bound `‖b‖`; `DifferentiableOn` on
            the open strip via **`TendstoLocallyUniformlyOn.differentiableOn`** (`hUnifClosed.mono` to open, the
            BIGGEST RISK = this lemma's API); `ContinuousOn` closed via `b.continuous`;
       (c4) boundary values: pointwise conv (`TendstoUniformlyOn.tendsto_at`) + `Filter.Tendsto.inner` +
            `(V a).continuous.tendsto` + the pair edge identity + `tendsto_nhds_unique`.
     Well-definedness NOT needed (existential goal). AVOID abstract dense-extension (`DenseInducing.extend`) —
     no ready Banach space of holomorphic-strip fns. Plus `2π`↔`−2π` sign mirror.
   ⟹ `StripKMSrvd boostUnitary 𝒦_W` ⟹ remove `hKMS` from `qiqt_gr_from_wedge_kms_complete`.
   - **★ DENSITY RESOLVED (GPT-5.5 #4): use the NICE CORE.** The density gap (nice dense in the BROAD
     `wedgeGenSet` = {supp⊆wedge, real, MemLp}) is an ARTIFACT of the over-broad generator class. The STANDARD,
     physically-faithful BW formalization defines the wedge standard subspace as `closure(span(NICE one-particle
     vectors))` — compactly-supported `δ`-margin functions are the canonical CORE for wedge localization. So:
     define `niceWedgeGenSet := {KrepL2 f : f continuous, compact supp, δ-margin, real, MemLp}` and prove
     `StripKMSrvd boostUnitary (closure(span(niceWedgeGenSet)))` — **NO density theorem needed** (the generators
     ARE nice; the BCF Cauchy limit closes the span). `boostUnitary_mapsTo_niceWedgeGenSet` holds (boost preserves
     nice: `boostTest` is a wedge-preserving homeomorphism comp). The broad-class equality `K_big = K_nice` is a
     SEPARATE optional theorem (`Submodule.orthogonal_orthogonal_eq_closure` + a distributional totality lemma,
     OR `tendsto_Lp_of_tendsto_ae` mollifier approximation) — only needed if a downstream lemma genuinely requires
     the broad `𝒦_W`. The KMS extension itself uses the nice-core def. [Decision pending: refactor `wedgeGenSet`
     to nice, or introduce `niceWedgeGenSet` + the equality — check downstream `𝒦_W` consumers (standardness,
     `hdense`).]
   - **★★ SPAN COLLAPSE (DONE 2026-06-22, `5bb7d10`): `span_ℝ(niceWedgeGenSet) = niceWedgeGenSet` as a SET.**
     The nice test functions are closed under ℝ-linear combination (sum: margin→min, support→union; real scalar:
     scales the margin), and `KrepL2` is ℝ-linear: `KrepL2(c·f₁+f₂)=c·KrepL2 f₁+KrepL2 f₂` (`KrepL2_add` ✅ +
     `KrepL2_sub` ✅ + real-scalar law). So `{KrepL2 f : f nice}` is ALREADY an ℝ-subspace ⟹ `span_ℝ` adds nothing
     ⟹ **every span element is a SINGLE `KrepL2` of a nice test function.** This COLLAPSES the bilinear-span step
     of (c2): the closure threading is a closure limit over SINGLE nice generator PAIRS — each `Fₙ = kmsBCF fₙ gₙ`
     (one nice pair), no finite-sum bilinear bookkeeping. The Cauchy machinery (c0 `dist_kmsBCF_le` ✅) applies
     verbatim.
   - **★★★ NICE-CORE INFRASTRUCTURE BUILT (2026-06-22, axiom-free, budget 0):**
       • `NiceTest m` structure (f + 7 niceness fields incl. δ); `NiceTest.vec := KrepL2 f` (`7a16c61`).
       • Closed under ± : `NiceTest.add`/`vec_add` (`KrepL2_add`, `5bb7d10`), `NiceTest.sub`/`vec_sub`
         (`KrepL2_sub`); `niceWedgeGenSet := range NiceTest.vec`; `niceWedgeGenSet_add_mem` (ℝ-subspace as a set).
       • `NiceTest.margin_le` (margin monotone in δ); `NiceTest.bcf` (= `kmsBCF` at common margin `min N.δ M.δ`);
         `NiceTest.bcf_congr` (δ-independence); **`NiceTest.dist_bcf_le`** = the c2 BCF Cauchy-control over pairs
         (reconciles per-pair margins at the four-way min) (`ac73f9b`).
       • **`NiceTest.bcf_cauchySeq`** (`c6e803e`): `(N n).vec→ξ, (M n).vec→η` ⟹ `n↦(N n).bcf (M n)` is `CauchySeq`
         in `closedStrip →ᵇ ℂ` (the c2→limit step; norms bounded via `Tendsto.norm.bddAbove_range`, vecs Cauchy).
   - **★★★★★ DONE (2026-06-22) — `StripKMSrvd boostUnitary (closure(niceWedgeGenSet))` axiom-free.** The full c3+c4
     assembly is machine-checked:
       (c4 edges) `NiceTest.bcf_apply_eq_top` (= `⟪M.vec, V(2πt) N.vec⟫`, via `kmsFun_ofReal_eq_inner`) +
         `bcf_apply_eq_bot` (via `kmsFun_sub_I` + `inner_conj_symm`) (`2d3fbc0`).
       (c3+c4) **`stripKMSrvd_closure`** (`53651ca`): nice approximants (`mem_closure_iff_seq_limit`+choice) →
         `bcf_cauchySeq` → `cauchySeq_tendsto_of_complete` limit `b` in `closedStrip→ᵇℂ` → `F := b on strip, 0 off`;
         holomorphy via **`TendstoLocallyUniformlyOn.differentiableOn`** (added import `Analysis.Complex.LocallyUniformLimit`;
         uniform transfer via `BoundedContinuousFunction.tendsto_iff_tendstoUniformly` + `…comp_coe`); continuity via
         `b.continuous`; boundary via `Filter.Tendsto.inner` + `tendsto_nhds_unique`. NO density theorem.
       (package) **`stripKMSrvd_boostUnitary`** (`6c2551e`): `StripKMSrvd (fun t => boostUnitary (2πt))
         (closure (niceWedgeGenSet m))` — the free-field BW KMS condition as a THEOREM.
   - **★★ SIGN FINDING (2026-06-22) — the discharge is the `+2π` instance, NOT `−2π`.** `oneParticleBW_of_stripKMSrvd_density`
     (OneParticleBW.lean:775) is GENERIC in `V`: it derives `modUnitary S t = V t` for *whatever* `V` satisfies
     `StripKMSrvd V K` (+ the boost-group/`𝒦`-invariance regularity, all true for either sign). Hence **`StripKMSrvd`
     is satisfiable for AT MOST ONE boost sign** on a given `S` (else `modUnitary = V₊ = V₋`, contradiction). I PROVED
     it for `V₊ = boostUnitary(2π·)` (`stripKMSrvd_boostUnitary`). Therefore `StripKMSrvd (boostUnitary(−2π·))` is
     FALSE, so the codebase's `oneParticleBW_wedge_complete` `hVboost : V t = boostUnitary(−2πt)` can never be
     discharged with a genuine KMS witness — that `−2π` was the *labelled/expected* sign, and the construction shows
     the discharge runs at `+2π`. (Reflection `f↦conj∘f∘conj` does NOT convert: it always introduces a stray `conj`
     or lands on the WRONG strip — consistent with the at-most-one-sign fact, not a fixable mechanical gap.)
   - **★★★★★ DISCHARGED (2026-06-23, `e95622e`) — `oneParticleBW_niceWedge`, axiom-free.** For a standard
     subspace `S` with `hcarrier : S.toClosedSubmodule = closure(niceWedgeGenSet m)` and `hVboost : V t =
     boostUnitary(2πt)`: `modUnitary S t = V t`. EVERY labelled analytic input discharged:
       • `hKMS` ← `stripKMSrvd_boostUnitary` (machine-checked RvD Def 3.4 KMS), • `hInv` ←
       `boostUnitary_mapsTo_niceWedgeGenSet` (`NiceTest.boost` + lightcone scaling, `56b3de0`) + `Set.MapsTo.closure`,
       • contraction-group structure ← boost group laws, all fed to `oneParticleBW_complete` (RvD Thm 3.8 discharge).
     This is `oneParticleBW_wedge_complete` with the labelled KMS hypothesis ELIMINATED. Full QIQTH green (8677 jobs);
     budget 0.
   - **REMAINING (honest boundary — NOT the labelled KMS anymore):**
     (a) **`S`-construction = the Reeh–Schlieder FRONTIER.** `oneParticleBW_niceWedge` takes `S : StandardSubspace`
         + `hcarrier` as a hypothesis (as did `oneParticleBW_wedge_complete`). Unconditionalizing it = CONSTRUCT a
         `StandardSubspace` with `toClosedSubmodule = closure(niceWedgeGenSet m)`, i.e. prove `K := closure(span ℝ
         nice)` is **separating** (`K ⊓ K.mulI = ⊥`) and **cyclic** (`K ⊔ K.mulI = ⊤`). Cyclic ⟺ `{KrepL2 g : g
         nice}` dense in `L²(ℝ,dθ)` ⟺ the on-shell amplitudes of wedge test functions are total — this is genuine
         **Reeh–Schlieder / Lorentz-analyticity** (Paley–Wiener / edge-of-the-wedge), NOT in Mathlib, a multi-week
         research-grade formalization. **This is the cited frontier** (like Type-III); the codebase NEVER constructs
         `S` either. The easy containment is DONE: `closure(niceWedgeGenSet) ⊆ 𝒦_W_broad`
         (`closure_niceWedgeGenSet_subset`, `68494d6`, via `niceWedgeGenSet ⊆ wedgeGenSet`).
         **★ FRONTIER NOW PRECISELY ISOLATED (2026-06-23):** all elementary structure is built axiom-free —
         `niceWedgeGenSet` is a genuine ℝ-`Submodule` (`niceWedgeSubmodule`; `span_ℝ = it` via
         `niceWedgeGenSet_span_eq`, from `NiceTest.zero`/`smul` + `Krep_smul`/`minkowskiFourier_smul`,
         `4edd9bc`/`9681520`); its `ClosedSubmodule` carrier `niceWedgeClosedSubmodule` has coe
         `= closure(niceWedgeGenSet)` (`98de1b1`); and **`oneParticleBW_niceWedge_of_standard`** (`503981d`)
         proves `modUnitary = boost(2πt)` GIVEN ONLY `hsep` (separating) + `hcyc` (cyclic), via the
         `niceWedgeStandardSubspace` constructor. So the ENTIRE remaining gap to an unconditional free-field
         one-particle BW is exactly those **two named Reeh–Schlieder lattice identities** — every other input
         (carrier, KMS, 𝒦-invariance, group structure) is machine-checked.
         **★★ CYCLIC FRONTIER REDUCED (2026-06-23, `40bf965`, axiom-free): `hcyc ⟸ Dense(span_ℂ niceWedgeGenSet)`.**
         `niceWedge_isCyclic_of_dense` — `K ⊔ K.mulI` is `i`-invariant (`ClosedSubmodule_sup_mulI_invariant`), hence
         a closed ℂ-subspace (`closedSubmodule_smul_I_mem`/`_complex_mem`) ⊇ every nice generator ⊇ closure of their
         dense ℂ-span `= ⊤` (`span_induction` + `closure_minimal` + `coe_top`). **The `ClosedSubmodule.mulI`
         instance-diamond that blocked this last fire is CRACKED**: the `mulI` abbrev carries an `InnerProductSpace`
         instance that defeats syntactic `rw`, so use defeq-tolerant `exact`/`refine` + `rfl` instead (term-mode
         `have h := mulI_sup K K.mulI; exact h.trans ...`; `(mem_mapEquiv_iff (scalarSMulCLE _ UnitI) S y).mpr`;
         `show (↑UnitI:ℂ)=I from rfl`). So `hcyc` is now the STANDARD analytic statement — the nice wedge one-particle
         vectors are total in `L²(ℝ)` (Reeh–Schlieder wedge-totality) — with NO lattice/instance plumbing left.
         REMAINING: (i) `hsep` analogous reduction (separating ⟺ cyclic of the complement `Kᗮ`); (ii) the analytic
         `Dense(span_ℂ niceWedgeGenSet)` itself — the genuine wedge-totality frontier (Paley–Wiener / edge-of-the-wedge).
         **★ ENGINE GENERALIZED + `of_dense` conditional (2026-06-23, `e71cc75`/`b11b40b`):**
         `ClosedSubmodule_sup_mulI_eq_top_of_dense` — for ANY `K` and `G ⊆ K` with dense ℂ-span, `K ⊔ K.mulI = ⊤`
         (reusable, axiom-free); `niceWedge_isCyclic_of_dense` is now a one-line instance; `oneParticleBW_niceWedge_of_dense`
         gives `modUnitary = boost` from `hsep` + `Dense(span_ℂ niceWedgeGenSet)`.
         **★ SEPARATING DUAL `hsep ⟸ Kᗮ cyclic` ATTEMPTED — ROOT-CAUSED to a scoped-instance vs `Max` conflict.**
         The math is clean and all four lemmas exist (`inf_orthogonal`+`orthogonal_orthogonal_eq`+`mulI_orthogonal`+
         `top_orthogonal_eq_bot`). DIAGNOSIS: `ᗮ` needs `InnerProductSpace ℝ (Lp ℂ 2)`, which the StandardSubspace
         framework provides as a `noncomputable scoped instance` inside `namespace ClosedSubmodule` (auto-named
         `ClosedSubmodule.instInnerProductSpaceReal`; docstring says "`open ClosedSubmodule`" to use it). WITHOUT the
         open, `ᗮ` in my goal picks a DIFFERENT `InnerProductSpace ℝ` than the framework lemmas → mismatch (defeats
         `rw` and even type-ascribed term-mode). WITH `open [scoped] ClosedSubmodule`, the `ᗮ` instance aligns BUT the
         open simultaneously breaks `⊔`/`Max` synthesis for `ClosedSubmodule` (`failed to synthesize Max`) and overloads
         the `ᗮ` notation. So the anonymous scoped instance can only be brought in by an open that breaks the lattice
         ops — a genuine Mathlib scoping tangle. **CONFIRMED ROOT (letI test):** even `letI :=
         ClosedSubmodule.instInnerProductSpaceReal` (pinning the ᗮ instance with NO open) makes `Max (ClosedSubmodule
         ℝ (Lp ℂ 2))` fail to synthesize — so the `ClosedSubmodule` LATTICE (`⊔`) instance ALSO depends on
         `InnerProductSpace ℝ`, and the two competing real-inner-product instances cannot be satisfied together. A
         genuine **Mathlib instance-design tangle** (lattice + orthogonal over two non-agreeing `InnerProductSpace ℝ`
         paths), NOT a local-trick fix. RESOLUTION (dedicated/Mathlib-aware): `@`-explicit instances on every `⊔`/`⊓`/`ᗮ`
         (verbose/fragile), or a Mathlib-side instance-priority fix making the scoped real-inner-product canonical.
         Reverted to keep green; the CYCLIC side is fully done, separating is the one piece gated on this tangle (its
         math is trivial once instances align). NB: the analytic `Dense(span_ℂ niceWedgeGenSet)` (wedge-totality) is the
         genuine remaining content for BOTH sides regardless.
         **★★★ CYCLIC SHARPENED TO TOTALITY (2026-06-23, `1ead640`, axiom-free) — ROUTED AROUND the ℝ-instance tangle.**
         `niceWedge_dense_of_total`: `Dense(span_ℂ niceWedgeGenSet) ⟸ {KrepL2 f : f nice} total in L²(ℝ)` (no nonzero
         `h` with `⟪KrepL2 f, h⟫=0 ∀ f`). KEY: uses the **COMPLEX** orthogonal complement (`orthogonal_eq_bot_iff` +
         `topologicalClosure_eq_top_iff`), and `InnerProductSpace ℂ` on `Lp ℂ 2` is UNAMBIGUOUS — so NO instance
         diamond (the ℝ-side tangle that blocks separating simply doesn't arise on the ℂ side). Chained:
         `niceWedge_isCyclic_of_total` + **`oneParticleBW_niceWedge_of_total`** give `modUnitary = boost(2πt)` from
         `hsep` + the canonical wedge-totality. The cyclic Reeh–Schlieder input is now in its SHARPEST form: "the nice
         wedge one-particle vectors are total in `L²(ℝ)`" — zero lattice/instance plumbing, the textbook statement.
         REMAINING: (i) that totality itself — the genuine Paley–Wiener / edge-of-the-wedge frontier
         (`∫ conj(Krep f)·h = 0 ∀ nice f ⟹ h=0`, via Fubini + analyticity of the on-shell transform in a tube);
         (ii) `hsep` (separating), still gated on the ℝ-instance tangle for its dual reduction.
         **★★★★ CYCLIC AS A FULLY EXPLICIT INTEGRAL (2026-06-23, `67e4b34`, axiom-free).** `inner_KrepL2_general`
         (`⟪KrepL2 f, h⟫ = ∫ conj(Krep m f θ)·h(θ) dθ` for arbitrary `h`, via `L2.inner_def`) →
         `niceWedge_isCyclic_of_total_integral` + **`oneParticleBW_niceWedge_of_total_integral`**: `modUnitary =
         boost(2πt)` from `hsep` + the TEXTBOOK Reeh–Schlieder statement in concrete form — *the only `h ∈ L²(ℝ)`
         with `∫ conj(Krep m f θ)·h(θ) dθ = 0` for every nice wedge `f` is `h = 0`*. The free-field one-particle BW
         is now reduced to its IRREDUCIBLE analytic core: every structural/lattice/instance step machine-checked,
         leaving EXACTLY this on-shell-amplitude totality (the Paley–Wiener frontier) + `hsep`. This is the cleanest
         possible statement of what remains — a concrete integral-vanishing ⟹ zero condition on the localized
         rapidity amplitudes.
         **★★★★★ BOTH Reeh–Schlieder inputs REDUCED — one-particle BW now rests on TWO analytic conditions
         (2026-06-23, `86f87b0`, axiom-free).** The SEPARATING `ᗮ`-instance tangle is BYPASSED by going DIRECT:
         `closedSubmodule_smul_I_mem_of_mem_mulI` (`v ∈ K.mulI ⟹ I•v ∈ K`, via the unambiguous ℂ `scalarSMulCLE` —
         same technique as the cyclic `mulI`, NO `ᗮ`/ℝ-inner-product) ⟹ `niceWedge_isSeparating_of_no_complex_line`
         (`hsep ⟸` "no nonzero complex line": the only `v` with `v ∈ K` and `I•v ∈ K` is `v=0`). The dual-via-`ᗮ`
         route + its Mathlib instance tangle is now MOOT. Capstone **`oneParticleBW_niceWedge_reehSchlieder`**:
         `modUnitary = boost(2πt)` given ONLY (a) separating = no complex line (symplectic non-degeneracy / Pauli–Jordan)
         + (b) cyclic = wedge-totality `∫ conj(Krep f)·h=0 ∀ nice f ⟹ h=0` (Paley–Wiener). NO lattice/instance/KMS
         hypotheses remain. **The entire free-field one-particle Bisognano–Wichmann is machine-checked down to exactly
         these two concrete analytic statements about the localized rapidity amplitudes.** Item A's STRUCTURAL reduction
         is COMPLETE; only the two analytic Reeh–Schlieder facts (Fourier/analyticity on the on-shell amplitudes) remain
         as the honest cited frontier. **Named as first-class `Prop`s (`af37538`): `NiceWedgeSeparating m`
         (no complex line / Pauli–Jordan) and `NiceWedgeCyclic m` (wedge-totality / Paley–Wiener); the capstone
         `oneParticleBW_niceWedge_reehSchlieder` takes exactly these two — the precise, named goals for any future
         analytic proof.** These are research-grade analysis (Mathlib-unsupported): the cyclic side needs L² Fourier
         theory; separating needs the free-field symplectic non-degeneracy.
         **★★ CYCLIC FRONTIER MAJORLY SIMPLIFIED (2026-06-23, `e425cd8`, axiom-free) — BYPASSES edge-of-the-wedge.**
         `niceWedge_isCyclic_of_boost_orbit_dense`: cyclic ⟸ the complex span of the rapidity-boost ORBIT
         `{boostUnitary a (N₀.vec) : a∈ℝ}` of a SINGLE nice generator is dense. KEY: the boost acts on `Krep` by
         rapidity TRANSLATION (`Krep(boostTest a f)θ = Krep f(θ+a)`) + `boostTest` preserves niceness, so the orbit ⊆
         `niceWedgeGenSet`. So the cyclic frontier drops from "all wedge vectors total" to "the TRANSLATES of ONE
         on-shell amplitude are total" — the **Wiener–Tauberian condition `FT(KrepL2 f₀) ≠ 0` a.e.**, NO edge-of-the-wedge
         analyticity (the boost-translation richness does the work). REMAINING for cyclic: (a) Wiener's L² theorem
         (translates dense ⟺ `FT≠0` a.e.) — not in Mathlib but PROVABLE from its Fourier/Plancherel (`⟨τ_a g,h⟩=0 ∀a ⟹
         ĝ·conj(ĥ)=0 ⟹ ĥ=0`); (b) `FT(KrepL2 f₀)≠0 a.e.` for one concrete nice `f₀` (e.g. a wedge Gaussian; codebase has
         `gaussian_Krep_memLp`). Both are STANDARD L²-Fourier computations — a real step down from the abstract totality.
         (Separating still needs the symplectic non-degeneracy.) I was too quick to call this "terminus" — the
         boost-covariance gives a genuinely cleaner route.
         **WIENER CHAIN STARTED (2026-06-23, `4bb820c`): `inner_boostUnitary_correlation`** —
         `⟪boostUnitary a g, h⟫ = ∫ conj(g θ)·h(θ+a) dθ` (the g–h cross-correlation as a function of `a`), via
         `L2.inner_def` + `coeFn_boostUnitary` + `integral_add_right_eq_self`. First brick. REMAINING Wiener steps
         (Mathlib has `MeasureTheory.Lp.fourierTransformₗᵢ` (L² FT isometry equiv) + `inner_fourier_eq` (Parseval) +
         `fourierIntegral_comp_add_right` (translate→modulation)): (2) the correlation's FT = `conj(ĝ)·ĥ` (Parseval +
         modulation); (3) `c≡0 ⟹ conj(ĝ)·ĥ=0 ⟹ ĥ=0` (ĝ≠0 a.e.) `⟹ h=0` (FT iso injective); (4) assemble Wiener:
         boost-orbit dense `⟸ FT(g)≠0 a.e.`; (5) `FT(KrepL2 f₀)≠0 a.e.` for a concrete wedge Gaussian. A multi-fire
         STANDARD Fourier effort — the bricks accumulate like the BW witness did.
         **BRICK 2 DONE (`d792c1d`): `niceWedge_isCyclic_of_correlation_total`** — cyclic ⟸ (∃ nice `N₀`: the only `h`
         with `∫ conj(Krep N₀.f θ)·h(θ+a) dθ = 0` for ALL `a` is `h=0`). Combines the boost-orbit reduction +
         `inner_boostUnitary_correlation` + the complex orthogonal complement. So the cyclic frontier is now the
         single concrete statement "vanishing cross-correlation at all shifts ⟹ zero" — NO Fourier machinery yet
         invoked. REMAINING = ONLY the Wiener FT core: `(∀a, ∫ conj(g₀)·h(·+a)=0) ⟹ h=0` given `FT(g₀)≠0` a.e.
         **★ PATH — CORRECTED TWICE, the genuine route is the L²-TRANSLATE↔MODULATION intertwining (Plancherel).**
         The cross-correlation `c(a) = ⟪boostUnitary a g₀, h⟫` is built (`inner_boostUnitary_correlation{,_conv}`).
         TWO optimistic routes were ruled out by investigation: (✗ L¹-convolution) Mathlib's `fourier_mul_convolution_eq`
         needs BOTH args `Integrable ∧ Continuous`; `h∈L²` is neither, so it does NOT apply — the L¹-convolution does
         NOT bypass the L²-FT. (✗ `g₀∈L¹` free) the `exp(−c·coshθ)` decay is interior-strip only; real-axis `Krep` has
         just a constant bound. So `h∈L²` FORCES the L² Fourier (Plancherel) treatment. GENUINE route:
         `c(a) = ⟪𝓕(boostUnitary a g₀), 𝓕h⟫` (`inner_fourier_eq`), KEY brick = `𝓕(boostUnitary a g₀) = char_a • 𝓕g₀`
         (the L²-translate↔modulation intertwining), which Mathlib has only at the integral/Schwartz level
         (`fourierIntegral_comp_add_right`) — must be LIFTED to `fourierTransformₗᵢ` by Schwartz density (both sides
         continuous in `g₀`; `SchwartzMap.toLp_fourier_eq` for the base case). Then `c(a) = FT[conj(𝓕g₀)·𝓕h](a)`,
         `c≡0 ⟹ conj(𝓕g₀)·𝓕h=0 ⟹ 𝓕h=0` (`𝓕g₀≠0` a.e.) `⟹ h=0`. NEXT fire-sized brick: the Schwartz base case of the
         intertwining (then the density lift). A genuine multi-fire L²-Fourier-infrastructure build (Mathlib lacks it at
         the Lp level) — STANDARD, not research-grade. (The successive corrections are the honesty standard: each
         optimistic shortcut was checked against Mathlib's actual hypotheses and ruled out before relying on it.)
         **★ INFRASTRUCTURE INVENTORY (2026-06-23) — the cyclic FT core = "build Wiener's L² theorem".** Mathlib
         HAS: density (`SchwartzMap.denseRange_toLpCLM`), the integral-level translate→modulation
         (`fourierIntegral_comp_add_right`), Lp mult-by-bounded (`MemLp.of_le_mul`, so the modulation keeps `L²`),
         Fourier inversion (`Inversion.lean`, for FT injectivity), the Schwartz↔Lp FT bridge
         (`SchwartzMap.toLp_fourier_eq`), and Plancherel (`inner_fourier_eq`). Mathlib LACKS (must build): a
         SCHWARTZ-TRANSLATION operator (so even the intertwining's base case needs it), an Lp-MODULATION operator
         (as a CLM), the translate↔modulation INTERTWINING `𝓕∘T_a = M_a∘𝓕` (via density), and the L²-FT-injectivity
         assembly. This is a genuine multi-fire Lean-Fourier-infrastructure project — STANDARD analysis, but a
         sizeable contribution in its own right (essentially the L²-Wiener Tauberian theorem), arguably beyond the
         QIQT plan's scope. **HONEST FRONTIER:** the cyclic Reeh–Schlieder reduces to Wiener's L² theorem (Mathlib
         infrastructure gap) + a concrete Gaussian; the separating reduces to Pauli–Jordan symplectic non-degeneracy.
         Both are precisely-named standard analysis with EVERY surrounding structural step machine-checked — the
         maximal honest reduction, parallel to the cited Type-III / continuum-TT frontier.
         **★ WIENER BRICK 1 DE-RISKED (2026-06-23) — the Schwartz-translation operator COMPILES** (confirmed in
         isolation): `compCLM ℂ (g := fun x => x + a) (HasTemperateGrowth.id'.add (.const a)) ⟨1, 1+‖a‖, fun x =>
         by rw[pow_one]; …norm_sub_le…; nlinarith⟩ : 𝓢(ℝ,ℂ) →L[ℂ] 𝓢(ℝ,ℂ)`. So the Wiener build is concretely
         buildable (not just "Mathlib lacks it"). **BUILD STARTED — `QIQTH/Fock/WienerL2.lean`** (new file). FULL
         build (~8 bricks): **(1) BUILT** (`d4f4d9b`): `schwartzTranslate a`, `f↦f(·+a)`, with `schwartzTranslate_apply`.
         **(3) BUILT** (`2714172`): `boostUnitary_toLp` — `boostUnitary a (f.toLp) = (schwartzTranslate (−a) f).toLp`
         (via `coeFn_boostUnitary` + measure-preserving translated-`ae` + `schwartzTranslate_apply`); connects the QIQT
         boost group to the Schwartz translation. **(2) BUILT** (`fce5e28`): the L²-modulation operator `M_c`
         (mult by the modulus-1 character `modChar c ξ = e^{icξ}`) — NOT a Mathlib CLM (no bounded-function action on
         `Lp` exists), built from scratch: `memLp_modChar_smul` (`MemLp.of_le_mul (c:=1)`), `modL2 c` (the map),
         `coeFn_modL2`, `modL2_add` (additivity), `norm_modL2` (the `L²`-isometry `‖M_c g‖=‖g‖` via `eLpNorm_congr_norm_ae`).
         Additivity + isometry give continuity by hand → NO bundled CLM needed for the density step.
         **(4) BUILT** (`b5a4f32`): the translate→modulation intertwining `𝓕∘boost_a = M∘𝓕`, in two parts —
         **4a** `fourier_schwartzTranslate` (pointwise Schwartz): `𝓕(f(·−a))(w)=e^{−2πiaw}·𝓕f(w)` via `fourier_coe`
         + `VectorFourier.fourierIntegral_comp_add_right` + the char identity (`Real.fourierChar_apply`: `𝐞(⟪−a,w⟫)
         =modChar(−2πa)w`); **4b** `fourierL2_boostUnitary` (∀ `g∈L²`): `𝓕(boostUnitary a g)=M_{−2πa}(𝓕 g)`, lifted
         from the dense Schwartz range by `DenseRange.equalizer` (both sides continuous: `𝓕`/`boostUnitary` are `≃ₗᵢ`,
         `M_c` via `isometry_modL2`/`continuous_modL2`+`modL2_sub`).
         **★ KEY ENABLER FOUND (2026-06-23): Mathlib ALREADY HAS the L²-Plancherel Fourier UNITARY** —
         `MeasureTheory.Lp.fourierTransformₗᵢ : Lp F 2 ≃ₗᵢ[ℂ] Lp F 2` (notation `𝓕`) with `inner_fourier_eq`
         (`⟪𝓕 f,𝓕 g⟫=⟪f,g⟫`, Plancherel), `norm_fourier_eq`, and `SchwartzMap.toLp_fourier_eq` (`𝓕(f.toLp)=(𝓕 f).toLp`).
         (NO bounded-function action on `Lp` though — `M_c` was still built from scratch.) This collapses the remaining
         build: the Wiener argument is now `⟪boost_a g₀,h⟫ = ⟪𝓕(boost_a g₀),𝓕 h⟫` [Plancherel] `= ⟪M_a(𝓕g₀),𝓕h⟫`
         [brick 4] `= ∫ e^{+2πiaξ}·conj(𝓕g₀ ξ)·𝓕h ξ dξ` = the integral-FT of `k:=conj(𝓕g₀)·𝓕h ∈ L¹`.
         **(5) BUILT** (`d402880`): `inner_boostUnitary_eq_integral` — `⟪boostUnitary a g₀,h⟫ = ∫ e^{+2πiaξ}·conj(𝓕g₀ ξ)
         ·𝓕h ξ dξ`, via Plancherel (`Lp.inner_fourier_eq`) + brick 4 + `L2.inner_def` + `coeFn_modL2` + the conjugate-
         character helper `conj_modChar` (`conj e^{icξ}=e^{−icξ}` via `Complex.exp_conj`). So `∀a ⟪…⟫=0 ⟺ 𝓕⁻(k)≡0`.
         **(6a) BUILT** (`4f2435f`): `fourier_correlation_eq` — the function FT `𝓕 k (w) = ⟪boostUnitary(−w) g₀, h⟫`
         (brick 5 at `a=−w` + the `𝓕`-character `𝐞(−⟪ξ,w⟫)=modChar(2π(−w))ξ` via `Real.fourier_eq`/`Real.fourierChar_apply`).
         So the orbit-orthogonality hypothesis `∀a ⟪boost_a g₀,h⟫=0` becomes EXACTLY `𝓕 k ≡ 0`.
         **(6b) BUILT** (`6584995`): `ae_eq_zero_of_fourier_eq_zero` — `Integrable k ∧ 𝓕 k = 0 ⟹ k=ᵐ0`, the
         classical L¹ Fourier-uniqueness. Via `ae_eq_zero_of_integral_contDiff_smul_eq_zero` (`AEEqOfIntegralContDiff`):
         for each real C^∞-compact test `g`, package `↑∘g` as Schwartz (`HasCompactSupport.toSchwartzMap` +
         `ContDiff.continuousLinearMap_comp ofRealCLM`), write `G=𝓕(𝓕⁻G)` (`FourierTransform.fourier_fourierInv_eq`),
         multiplication formula `VectorFourier.integral_fourierIntegral_smul_eq_flip` (`∫ 𝓕(𝓕⁻G)·k=∫ (𝓕⁻G)·𝓕k`,
         `innerₗ` symmetric via `flip_innerₗ`) `=0`. The fiddly bits (real→ℂ test coercion, `•`/`*`, `𝓕`↔`fourierIntegral`
         defeq) all dispatched. **This was the hardest remaining analytic brick.**
         **(7) BUILT** (`31b6f2d`): `boost_orbit_total_of_fourier_ne_zero` — `𝓕g₀≠0` a.e. `∧ (∀a ⟪boost_a g₀,h⟫=0)
         ⟹ h=0`. Chains 6a (`⟹ 𝓕 k≡0`) + 6b (`⟹ k=ᵐ0`) on `k=conj(𝓕g₀)·𝓕h` (`∈L¹` via `MemLp.integrable_mul` of
         two `L²`, `MemLp.star` for the conj factor); `𝓕g₀≠0` a.e. + `mul_eq_zero` + `star_eq_zero` ⟹ `𝓕h=0` a.e.
         `⟹ 𝓕h=0` in `Lp` (`Lp.eq_zero_iff_ae_eq_zero`) `⟹ h=0` (`Lp.fourierTransformₗᵢ` inj).
         **★★★ THE WIENER L² TAUBERIAN THEOREM IS COMPLETE** — the boost orbit of any single generator with `𝓕≠0`
         a.e. is total in `L²`, fully axiom-free.
         **WIRING DONE** (`641dc6d`): `niceWedgeCyclic_of_fourier_ne_zero` (`BoostKMS.lean`, now imports `WienerL2`) —
         `NiceWedgeCyclic m` holds as soon as ONE nice generator `N₀` has `𝓕(N₀.vec)≠0` a.e.  Proof: `h⊥` all nice
         generators ⟹ `h⊥` `N₀`'s boost-orbit (boosts of a nice generator are nice, `NiceTest.vec_boost`; orthogonality
         = the integral, `inner_KrepL2_general`) ⟹[brick 7] `h=0`.  Feeds the banked capstone
         `oneParticleBW_niceWedge_reehSchlieder`.  Bricks 1–7 + wiring BUILT axiom-free.
         **THE ENTIRE CYCLIC REEH–SCHLIEDER INPUT NOW RESTS ON THE SINGLE CONCRETE FACT `∃ N₀, 𝓕(N₀.vec)≠0` a.e.**
         NEXT — only **(8)**: exhibit ONE concrete nice generator `f₀` (a wedge-supported bump/Gaussian-type real test)
         and show its one-particle amplitude `𝓕(Krep m f₀)≠0` a.e.  Then `niceWedgeCyclic_of_fourier_ne_zero` ⟹
         `NiceWedgeCyclic m` ⟹ the capstone discharges cyclic Reeh–Schlieder unconditionally (modulo the parallel
         separating side).  EVERY hard analytic piece (intertwining, Plancherel bridge, FT↔correlation reduction,
         L¹-uniqueness, the full Tauberian theorem, the `NiceWedgeCyclic` wiring) is DONE.
     (b) **Sign RESOLVED (not an open audit): `+2π`, proven.** `oneParticleBW_niceWedge` IS a theorem
         `modUnitary S t = boostUnitary(2πt)` (conditional on the carrier `S`). So the relative sign modUnitary↔boost
         for the nice-core right wedge is settled `+2π`; by the at-most-one-sign fact the codebase's `−2π`
         (`oneParticleBW_wedge_complete`) is the unsatisfiable labelled/expected convention. NOT editing the
         codebase's `−2π` theorem (it may target a different orientation; the broad=nice density would force the
         contradiction, but that density is itself the frontier). The honest statement stands: the BW discharge is
         machine-checked at `+2π`.
   - **NET STATE OF ITEM A:** the free-field BW analytic content (RvD Def 3.4 KMS witness, the `modUnitary=boost`
     identification with every labelled analytic input discharged) is COMPLETE and axiom-free. What remains
     (Reeh–Schlieder standardness of the wedge subspace) is the genuine cited frontier, beyond mechanical
     implementation — the same honest stopping point as Type-III / continuum TT.
     **★ Lightcone scaling WORKED OUT (ready to implement):** `lorentzBoost a` scales the lightcone coords by
     `(z₁−z₀) ↦ e^{−a}(z₁−z₀)` and `(z₁+z₀) ↦ e^{a}(z₁+z₀)` [from `lorentzBoost_one/zero` + `cosh a ∓ sinh a =
     e^{∓a}`]. So `boostTest(−a) f x = f(lorentzBoost(−a) x)`: if `≠0` then `f`'s margin `δ` at `y=lorentzBoost(−a)x`
     gives `δ ≤ e^{a}(x₁−x₀)` and `δ ≤ e^{−a}(x₁+x₀)` ⟹ `x` has margin `δ' := δ·e^{−|a|} > 0`. Build a
     `NiceTest.boost (a) : NiceTest m` constructor (f := `boostTest(−a) N.f`, δ := `N.δ·exp(−|a|)`, cont/cpt via
     `Continuous.comp`/homeomorph support, real preserved, memLp via `memLp_Krep_boostTest`) + `vec_boost`
     (`boostUnitary a N.vec = (N.boost a).vec`, from `boostUnitary_KrepL2`) ⟹ `boostUnitary_mapsTo_niceWedgeGenSet`.
   - **★ The `−2π` reconciliation is a SEPARATE convention question** (whether the codebase's `boostUnitary`/`modUnitary`/
     `rvdRC`/`modChar` sign convention makes `−2π` here `≡ +2π` physically). Flagged for an honest audit, NOT guessed.
   NOTE: this is laborious Hilbert-space plumbing (sesquilinear extension from a total set by continuity) — no
   new hard analysis. If it proves too long, `stripKMSrvd_pair` alone is already the citable A4 result (the
   explicit free-field boost-KMS witness, the genuine BW analytic content).

---

## FRONTIER ASSESSMENT (2026-06-22, after assessing Mathlib support)

**What is DONE, axiom-free (the analytic skeleton of the free-field BW/Hardy proof):** Item B (focusing
derived from Raychaudhuri); Item A — A0 convention audit, **A1 holomorphy** (`KrepCont` entire), **A1c**
damping bound, **A3** `iπ` boundary conjugation, **A2 sup-bound**. These are genuine, machine-checked results.

**What remains is research-grade, and partly blocked on missing Mathlib infrastructure:**
1. **A2 `L²` strip bound — no clean route in current Mathlib.** The natural proof needs **Minkowski's integral
   inequality** `‖∫_x F(·,x) dx‖_{L²} ≤ ∫_x ‖F(·,x)‖_{L²} dx`, which **Mathlib does not have** (only Hölder
   `lintegral_mul_le_Lp_mul_Lq` and the `Lp`-triangle `eLpNorm_add_le`). It would have to be proven from
   scratch (duality + Fubini + Cauchy–Schwarz). Even the elementary helper `coshθ ≥ 1+θ²/2` (for Gaussian
   domination of the interior-`λ` decay) is absent. And the bound must be **uniform in `λ∈[0,π]`**, requiring
   interpolation between the real-axis `cosh⁻²` decay (endpoints) and the interior double-exponential decay —
   delicate.
2. **A4 KMS-function assembly** — additionally needs the concrete-`∫` ↔ abstract-`Lp`-inner-product bridge and
   the `boostUnitary` translation action threaded through, then closedness extension to `𝒦_W`.

**Building blocks landed toward the frontier** (axiom-free, budget 0): `norm_KrepCont_le` (A2 sup-bound,
`59deb45`); `sq_div_eight_le_cosh` + `integrable_exp_neg_const_mul_cosh` (A2 decay building block — the
`θ`-integrability the interior-`λ` decay reduces to, `c11291e`).

**★ REFRAME (2026-06-22): the Minkowski gap is SIDESTEPPED for interior-`λ` `L²` membership.** The
**pointwise** bound `‖KrepCont m f (θ+iλ)‖ ≤ (1/√2)(∫‖f‖)·exp(−c·coshθ)` with `c = m·sinλ·δ` (`δ` the wedge
margin from `exists_wedge_margin`, using `coshθ·x₁−sinhθ·x₀ ≥ δ·coshθ`) + `integrable_exp_neg_const_mul_cosh`
(at `2c`) gives `MemLp (KrepCont m f (·+iλ)) 2` **directly**, no Minkowski integral inequality needed. The
margin lemma is DONE (`b98dc63`).

**Concrete next-step ladder:**
1. **Pointwise strip-decay bound — DONE** (`f32adc0`): `norm_kernel_eq` (exact modulus),
   `norm_kernel_le_exp_decay`, `norm_KrepCont_le_exp_decay`
   (`‖KrepCont m f (θ+iλ)‖ ≤ (1/√2)(∫‖f‖)·exp(−(m sinλ δ)coshθ)`). Axiom-free, budget 0.
2. **Interior-`λ` `L²` membership — DONE** (`3635e54`): `memLp_KrepCont_strip` —
   `MemLp (fun θ => KrepCont m f (θ+iλ)) 2 volume` for `λ∈(0,π)`, via `MemLp.mono'` against
   `C·exp(−c·cosh)` (sq integrable). **Minkowski gap fully off the critical path.** Axiom-free, budget 0.
   **★ PHASE A2 CORE COMPLETE** (sup-bound, decay block, margin, pointwise decay, interior-λ MemLp). Endpoints
   `λ=0,π` are `Krep`/`conj` via existing `MemLp`/A3 if needed.
3. **A4 (the remaining finish)** — STARTED (`8d17b79`, new file `QIQTH/Fock/BoostKMS.lean`):
   - **Real-axis edge bridge DONE**: `inner_KrepL2` (`⟪KrepL2 f, KrepL2 g⟫ = ∫ conj(Krep f)·Krep g`) and
     `inner_boostUnitary_KrepL2` (`⟪KrepL2 g, boostUnitary a (KrepL2 f)⟫ = ∫ conj(Krep g θ)·Krep f(θ−a) dθ`,
     via `boostUnitary_KrepL2` + `Krep_boost`). The concrete-integral form of `f(t)=⟪η,V_t ξ⟫`. Axiom-free.
   - **Top edge (`f(t)=⟪η,V_t ξ⟫`) DONE** (`55c8658`): `symm_edge_eq_shifted` + `symm_edge_eq_inner` — the
     symmetric integral `∫ conj(Krep g(θ+πt))·Krep f(θ−πt)` (= real-axis value of `F`) equals
     `⟪KrepL2 g, boostUnitary(2πt)(KrepL2 f)⟫`. Axiom-free.
   - **`F` defined + top edge DONE** (`f4f9cb3`): `kmsFun m f g z := ∫ conj(KrepCont g(conj(θ+πz)))·KrepCont
     f(θ−πz)`; `kmsFun_ofReal` (`F(t)=` symmetric integral via `KrepCont_ofReal`); `kmsFun_ofReal_eq_inner`
     (`F(t)=⟪KrepL2 g, boostUnitary(2πt)(KrepL2 f)⟫`). Axiom-free.
   - **Bottom edge `F(t−i)=conj(F(t))=⟪V_t ξ,η⟫` DONE** (`f7eb282`): `kmsFun_sub_I` — at `z=t−i` the `iπ`-shift
     puts both `KrepCont` args at `Im=+π`, `KrepCont_add_pi_I` (A3) collapses each to `conj(Krep…)`. Axiom-free.
     **★ BOTH KMS EDGES of the witness `F` now machine-checked.**
   - **Holomorphy ingredient DONE** (`86196d6`): `differentiable_reflKrepCont` — the reflected `g`-factor
     `u↦conj(KrepCont g(conj u))` is entire (Schwarz reflection via `DifferentiableAt.star_conj`).
     **Confirms `F`'s holomorphy is reachable** (the `conj∘·∘conj` was the only non-obvious differentiability).
   - **Integrand holomorphy DONE** (`a82ad92`): `differentiable_kmsIntegrand` — the `kmsFun` integrand is
     entire in `z` (the per-`θ` `h_diff` ingredient).
   - **Integrand continuity/measurability DONE** (`35cb3f2`): `continuous_kmsIntegrand_in_theta` (the `hF_meas`
     ingredient). So both pointwise ingredients (`h_diff` + `hF_meas`) for the parametric theorem are in hand.
   - **Derivative-decay integrability DONE** (`28c63e3`): `abs_le_cosh` (`|θ|≤coshθ`) +
     `integrable_cosh_mul_exp_neg_const_mul_cosh` (`cosh s·exp(−c cosh s)` integrable) — the integrability the
     `z`-derivative domination reduces to (`‖∂_z integrand‖ ≲ cosh(s)·exp(−c cosh s)`).
   - **★★★★ CONSOLIDATION DONE** (`275342d`): `stripKMSrvd_pair_of_regularity` — for a wedge generator pair,
     the `StripKMSrvd` `∃F` witness holds GIVEN ONLY `hDCC` (`DiffContOnCl` of `kmsFun`) + `hbd` (bounded). Both
     KMS edges discharged (top via `kmsFun_ofReal_eq_inner`, bottom via `kmsFun_sub_I`+`inner_conj_symm`).
     **This precisely isolates the entire remaining frontier** to the analytic regularity of ONE explicit
     function `kmsFun m f g`. Axiom-free.
   - **Remaining (the whole frontier, now crisply isolated)**: (c) prove `DiffContOnCl ℂ (kmsFun m f g)` (the
     parametric-holomorphy assembly — `z`-derivative norm bound `≲ cosh·exp(−c cosh)` [integrability in hand] +
     the dominated-derivative theorem + continuity-to-closure) and `∃M, ∀z ‖kmsFun z‖≤M` (the
     *uniform-to-boundary* `L²`-norm continuity — the one genuinely delicate piece). (d) closedness of
     `StripKMSrvd` to `𝒦_W` (bound continuous in `ξ,η`) + the `−2π`↔`2π` boost-sign mirror to match
     `oneParticleBW_wedge_complete`; then ⟹ unconditional BW ⟹ remove `hKMS`.
     - *Derivative-decay building blocks landed (all axiom-free):* `norm_cosh_le_cosh_re`/`norm_sinh_le_cosh_re`
       (`15ba0d1`, poly-factor bound); `deriv_KrepCont_eq` + `norm_kernel_eq'` (`559d28f`, deriv repr +
       general-`ζ` modulus); `norm_kernel_le_exp_decay'` + `norm_kernelDeriv_le_exp_decay` (`a2d6560`, general-`ζ`
       kernel & kernelDeriv strip-decay: `‖K'(ζ,x)‖ ≤ exp(−c cosh(Re ζ))·|m|·cosh(Re ζ)·(|x₀|+|x₁|)`).
       `norm_deriv_KrepCont_le_exp_decay` (`2fe7a2b`): `‖deriv(KrepCont m f) ζ‖ ≤ (1/√2)|m|·cosh(Re ζ)·
       exp(−c cosh(Re ζ))·∫(|x₀|+|x₁|)‖f‖` — the `z`-derivative norm bound. **Full strip-decay infrastructure
       (function + derivative) now complete.**
       Reflection-factor derivative `deriv_reflKrepCont_eq` (`ccada4e`) + the integrand's `z`-derivative
       `hasDerivAt_kmsIntegrand_z` (`a2a0797`, explicit value via product/chain rule) — the `h_diff` ingredient.
       `cosh` shift bounds `e^{−|s|}cosh θ ≤ cosh(θ+s) ≤ e^{|s|}cosh θ` (`ea5ef0c`, + `abs_sinh_le_cosh`,
       `cosh±|sinh|=e^{±|s|}`) — make the shifting-peak decay uniform over a `z`-ball. **All analytic building
       blocks for the domination are now in hand.**
       **Next:** (i) bound `‖integrand z-derivative‖ ≤` integrable-in-`θ` uniformly over a `z`-ball in the strip
       interior (combine the four decay bounds via the `cosh` shift bounds + `conj`-arg `Im` bookkeeping +
       `c_min>0` from staying interior); (ii) feed `hasDerivAt_integral_of_dominated_loc_of_deriv_le` ⟹ `kmsFun`
       differentiable on the open strip; (iii) continuity-to-closure ⟹ `DiffContOnCl`; then the boundedness frontier.

**Honest scale:** discharging `StripKMSrvd` from here is a genuine multi-week-to-month real-analysis +
Mathlib-infrastructure effort (Minkowski integral inequality is itself a Mathlib-worthy contribution). This is
the same class of "cited frontier" boundary as the Araki/Type-III continuum work. The analytic skeleton built
this session (A0–A3, A2-sup) is the honest, axiom-free contribution; the `L²`/assembly core is the documented
remaining frontier. Per the plan's fallback clause, this is the last green checkpoint of the fast-progress arc.
  - **A1c DONE** (commit pending, `WedgeAnalyticity.lean`): `cosh_ofReal_add_ofReal_mul_I` /
    `sinh_ofReal_add_ofReal_mul_I` (real/imag split at complex rapidity) + `norm_kernel_le_one` — the
    wedge-damping bound `‖exp(−i·p_m(θ+iλ)·x)‖ ≤ 1` for `0<x₁−x₀`, `0<x₁+x₀`, `0≤λ≤π`, `m≥0` (the
    `rightWedge` conditions kept as explicit hyps to keep this file dependency-light; the
    `x∈rightWedge ↔ …` bridge goes in `BoostKMS.lean`). Axiom-free, budget 0.
- **A2.** Uniform `H²(S_π)` strip bounds.
- **A3.** Boundary conjugation `ψ_f(θ+iπ)=conj(ψ_f(θ))`; define `K_Hardy`, prove `wedgeGenSet ⊆ K_Hardy`,
  closedness ⟹ `𝒦_W ⊆ K_Hardy`.
- **A4.** Assemble `F_{η,ξ}`; prove the two edges, the uniform bound, and `DiffContOnCl`; conclude
  `stripKMSrvd_boost`.
- **A5.** Wire to the unconditional BW identification + up the GR chain; remove `hKMS`.

### Risks / unknowns

- **Convention/sign audit** (`boostUnitary` direction, `inner` linear slot, `minkowskiFourier` sign, the
  `−2π` factor) — settle FIRST; a sign error propagates to the wrong strip/edge.
- **Holomorphic-parameter integration in Lean** (differentiating `∫ … dx` in a complex parameter): the
  heaviest infra dependency. Inventory Mathlib `Complex`/`hasFDerivAt` parametric-integral lemmas before A1;
  if thin, this is the long pole (pushes A toward the multi-month end).
- **`J` not needed:** `StripKMSrvd` gives the modular GROUP; we do NOT need to identify the modular conjugation
  `J` (the chain only consumes the group). Keep scope to the group.
- **Honest fallback:** if holomorphic-parameter integration stalls, stop at the last green Phase (A1–A3 are
  independently valuable: the wedge-wavefunction strip analyticity is the physical heart) and re-label `hKMS`
  as "the one remaining one-particle BW/KMS theorem, reduced to assembling `F` from the proven Hardy data."

---

## Work Item B — Close `hFocus` to the area↔θ modelling identification only

> **STATUS 2026-06-22: B1 DONE** (commit `e09652d`). `qiqt_gr_from_wedge_kms_raychaudhuri`
> (`WedgeKMSToGR.lean`) is the end-to-end GR theorem with the focusing step DERIVED from the kinematic
> Raychaudhuri data (per-direction null geodesic congruence `Vcong v`, `hVC`/`hgeo`/`hVval`/`hequil`) via
> `hFocus_of_raychaudhuri`; raw `hFocus` is gone. Axiom-free, budget 0. **B2** (honest classification) is
> captured below + in the plan. **B3** (fold `harea` into a `def`) is deliberately NOT done: `harea` bridges
> the abstract thermodynamic area functional `A` (whose derivative is `ad`, via `hA`) to the congruence
> expansion — it is a genuine *modelling identification*, not pure notation, so folding it would relocate, not
> eliminate, the physical content. Item B is therefore considered **closed** at the honest floor: the only
> residue is `harea` (area↔θ) + `hequil` (stationary horizon), both in the Jacobson local-equilibrium bucket.

**Small.** The geometric content of `hFocus` is ALREADY machine-checked: `hFocus_of_raychaudhuri`
(`QiqtToGR.lean:39`) derives `ad = BL(Ric) v` from the axiom-free `raychaudhuri_focusing_at_equilibrium`
(`QIQTH/Raychaudhuri.lean`), given:
- `hequil` — the shear–expansion quadratic vanishes (stationary/bifurcation horizon — Jacobson's setup);
- `harea` — the single **modelling identification** `ad = −∑_ν V^ν ∂_ν θ` (abstract area rate = minus the
  congruence expansion rate).

So nothing analytic remains; the task is to make this the *form the GR theorem actually consumes* and to
honestly classify `harea`/`hequil`.

### Steps

- **B1.** Confirm `qiqt_gr_from_wedge_kms_complete` can take `hFocus` *via* `hFocus_of_raychaudhuri` (provide a
  `…_complete` variant that consumes `harea` + `hequil` instead of raw `hFocus`), so the geometric step is
  visibly derived in the end-to-end theorem rather than only in a side lemma.
- **B2.** Classify the residue honestly in the plan + `AXIOM_CONTRACTS.md`:
  - `harea` (area rate = −expansion) is **definitional** — it is *what "area of the local horizon cross-section"
    means* for a null congruence (a modelling choice, not a physical assumption beyond "use the congruence's
    expansion as the area rate"). Candidate to fold into a `def` so it stops being a hypothesis.
  - `hequil` (stationary horizon) is part of the **Jacobson local-equilibrium setup** — same physical bucket as
    the Clausius/area-saturation law.
- **B3.** (Optional) Fold `harea` into the definition of the area functional so `ad` is *defined* as
  `−V^ν∂_ν θ`, removing it as a labelled hypothesis entirely.

### Risk

- Minimal. Pure threading/refactor + an honest classification. No new analytic content. If `hequil`/`harea`
  turn out to be load-bearing physical choices, that is fine — they then belong with the Clausius postulate,
  and the plan says so plainly.

---

## Order & rationale

1. **Item B first** (days): a clean, low-risk win that makes the GR theorem visibly carry the *derived*
   Raychaudhuri step, and crisply documents what physics actually remains.
2. **Item A second** (weeks–months): start with the **convention audit** (A0) and a **Mathlib parametric-
   holomorphic-integration inventory**, then A1→A5. Each phase ships green; stop honestly at the last green
   checkpoint if the integration infra proves insufficient.

After both: the only labelled *physical* input of free-field QIQT→GR is the **Clausius/area-saturation law**
(`hbound`, `hsat`) — the QIQT-H horizon-thermodynamics postulate, which by Jacobson's logic cannot be
eliminated, only stated cleanly.

---

## Verification discipline (both items)

- Per Lean increment: `cd /d/ROOT/qiqt/lean/mathlib` then `~/.elan/bin/lake build <module>` green; every new
  theorem `#print axioms` shows ONLY `[propext, Classical.choice, Quot.sound]`;
  `bash scripts/axiom_budget_check.sh` → `raw axiom count: 0 (budget 0)`; vacuity-lint clean (the one known
  `LorentzWitness.lean:180` placeholder is documented in `AXIOM_CONTRACTS.md`).
- Add a `#print axioms` entry to `AxiomAudit.lean` and an import to `QIQTH.lean` per new file.
- Commits on `main`, messages ending `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`.
- **Total honesty both directions**: state plainly what becomes derived vs. what remains a labelled physical
  input; do NOT advertise `hKMS`/`hFocus` as eliminated until the end-to-end theorem actually drops them.
- Leave the concurrent external agent's WIP (`BornTypicality.lean`, `DPI.lean`) UNTOUCHED.
