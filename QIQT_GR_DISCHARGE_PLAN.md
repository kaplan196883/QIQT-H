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
| `hKMS` = `StripKMSrvd(boostUnitary, 𝒦_W)` | **dischargeable theorem** (free-field Hardy proof), currently labelled | **Work Item A** |
| Clausius/area-saturation (`hbound`, `hsat`) | **genuinely irreducible PHYSICS** (= QIQT-H horizon-thermodynamics postulate) | out of scope — the honest floor |
| metric/frame/regularity scaffolding (`hCg`, `hreg`, `conserv`, …) | precondition infrastructure; `conserv` derivable for explicit KG `T` | out of scope (optional later) |

**Goal of this plan:** retire `hKMS` (Item A) and close `hFocus` to `harea` only (Item B), leaving the
Clausius/area-saturation law as the single labelled physical input.

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
