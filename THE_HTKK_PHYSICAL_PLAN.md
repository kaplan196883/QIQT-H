# THE hTkk PHYSICAL-LOCALIZATION PLAN — turn `hTkk` from a calibrated ansatz into a physical theorem

**Status:** SCOPED (dual consult: GPT-5.5-pro high + Fable Lean-audit, 2026-07-08). **Track:** QG / free-field induced gravity.
**Commits LOCAL ONLY (no push).**

## Binding verdict (both consults, independent, converging)
The existing `hTkk` discharge (`LocalizedMode.localized_mode_hTkk` + `GaussianMode.gaussMode_calibration` ⟹
`qiqt_gr_freefield_gaussian`/`_complete`, all [AF] std-3, no sorry) is a **calibration-hiding rank-one ANSATZ, not a
physical derivation** of the localization map. It sets `ff x v θ := (∑ᵦ vᵦ ∂ᵦφ(x))·g₀(θ)` (amplitude × universal profile)
and *chooses* `g₀`'s normalization so the boost charge equals `2π/ℏ·T_kk`.
- **GENUINELY DERIVED (keep):** (i) amplitude law `ff ∝ ∂_v φ`; (ii) quadratic `(∂φ)²` null-energy scaling; (iii) the
  per-generator family collapses to ONE universal scalar; (iv) the BW/Hilbert-space fact that the modular-energy rate of
  `D·g₀` is `i·D²·(2π/ℏ)` via genuine (axiom-free) modular flow.
- **NOT ESTABLISHED (the real physics):** that `ff = D·g₀` is the field's ACTUAL one-particle wedge mode, and that the
  coefficient `2π/ℏ` comes from the KMS temperature (β=2π) / KG symplectic norm of the genuine wedge excitation rather than
  a tuned normalization. Fable: the mode SHAPE/WIDTH is free (`GaussianModeFamily` — every width calibrates); only the
  **unit phase `−iθ`** carries `2π/ℏ`, and it is INSERTED. The `nullEnergy` docstring already concedes the wedge-smearing
  construction is "the cited frontier."
- The paper's "localization map is provably not dischargeable by analysis" is therefore **correct against the Gaussian
  discharge** — no contradiction. Honest status: `hTkk` is **REDUCED, not DERIVED**.

## The genuine target (GPT-5.5-pro, known flat-space free-field AQFT — Rindler modular Hamiltonian)
Derive `ff` from the field and fix `2π/ℏ` from Bisognano–Wichmann + the stress-tensor Noether charge, NOT a fitted `g₀`:
1. KG field → one-particle Hilbert space; positive-frequency projection of a smearing of `∂_v φ` near the generator `(x,v)`.
2. BW: wedge modular generator = Lorentz boost (ALREADY unconditional: `freeField_secondQuant_BW_unconditional`, `m>0`).
3. Noether: `K_W = (2π/ℏ)∫_{x¹>0,t=0} x¹ T₀₀ d³x  =  (2π/ℏ)∫_{H⁺} λ·T_kk dλ d²y` (boost charge = horizon `T_kk` integral).
4. Match to the one-particle rapidity boost charge `Q[f_phys] = (−2π∫ conj(f)·f').im` for `f_phys` = the transform of the
   ACTUAL horizon data (shape determined, not guessed).
5. **Local limit** (GPT-5.5-pro honesty correction): the POINTWISE `hTkk` is "too sharp" — QFT gives distributions. Prove a
   SMEARED version first, then a regulated approximate-identity local limit `χ_ε → δ_{(x,v)}` ⟹ pointwise `hTkk` as a
   corollary. Coefficient `2π/ℏ` fixed by BW + stress-tensor normalization.
Territory: Rindler modular Hamiltonian; Casini–Huerta half-space modular H; Ceyhan–Faulkner (QNEC/ANEC). Known physics,
hard formalization — the corpus's own docstring flags the mode-expansion as "beyond current Mathlib reach."

## Honest difficulty (binding — do NOT over-promise)
This is a research-grade, possibly multi-week formalization; the one-particle wedge mode-expansion + KG two-point
infrastructure is largely absent from Mathlib and only partially in QIQTH (Fock/StandardSubspace machinery exists). Expect
to CHECKPOINT at the mode-expansion wall. The near-term, genuinely-landable value is Stages 0–2 (honesty + the CLASSICAL
boost-charge identity + the KMS coefficient), which are real and tighten the story even if Stage 3 (the physical mode)
stalls. NEVER claim the physical localization map is discharged until `f_phys` is built from φ with the coefficient derived.

## The plan (sequenced, axiom-free, ship-green; new file `QIQTH/HTkkPhysical.lean` unless noted)

- [x] **HT0 — HONESTY RELABEL + INTERFACE — DONE 2026-07-08** (commit ca896d7, [AF] std-3, budget 0): `calibrated_rank_one_hTkk`
  alias + honest ⚠-scope docstring on `localized_mode_hTkk` (calibrated rank-one ansatz, coefficient `2π/ℏ` calibrated not
  derived, mode shape free); the non-vacuous frontier predicate `IsPhysicalWedgeMode physWedge m φ x v ff := physWedge m φ x v ff`
  (carries the smearing requirement as a passed-in predicate field, threading `m`; NOT `:= True`); inventory + `docs/G_SCOPE_AUDIT.md`
  F7 note. Capstones (`QiqtGrGaussian`/`QiqtGrComplete`) still build — non-breaking. Verified std-3.
- [ ] **HT0 (orig) — HONESTY RELABEL + INTERFACE (tractable NOW; soundness fix).** In `LocalizedMode.lean`/`GaussianMode.lean`:
  rename/alias the Gaussian result to **`calibrated_rank_one_hTkk`** with a docstring stating it is a calibrated rank-one
  ANSATZ realizing the `(∂φ)²` scaling + single-scalar calibration, NOT the physical KG localization map. Introduce a named
  predicate **`IsPhysicalWedgeMode m φ x v ff : Prop`** (the mode is the positive-frequency wedge smearing of `∂_v φ`, to be
  defined) so the frontier is an EXPLICIT Prop, not a hidden ansatz. Update `LEAN_RESULTS_INVENTORY.md` + the `nullEnergy`
  scope note: `hTkk` is REDUCED (scaling+scalar), the physical map is the cited frontier. [AF] std-3. Small, high-value.
- **HT1 — the CLASSICAL boost-charge ↔ horizon-`T_kk` identity — SCOPED (GPT-5.5-pro 2026-07-08; TARGET CORRECTED).**
  ⚠ The naive future-only identity `∫_{x¹>0,t=0} x¹ T₀₀ = ∫_{H⁺} λ T_kk` is **FALSE** without a no-flux condition (1+1
  massless counterexample: `φ=F(t−x)` ⟹ horizon integral 0 but boost charge `∫x(F')²>0`). The HONEST identity carries the
  explicit outer null-infinity flux `N_+`: `K₀(R) = H_+(R) + N_+(R)`, with (signature −+++, `U=x−t,V=x+t`, `k=∂_t+∂_x`,
  `T_kk=4T_VV`, `V=2λ`) `N_+(R) = ∫₀^R∫_{ℝ²}[U(∂_UΦ)² + (R/4)(|∇_yΦ|²+m²Φ²)]_{V=R}`. The future-only theorem holds only in
  the limit `N_+(R)→0` (a STATED falloff hypothesis — NEVER hidden). Derivation = the boost current `J^a=T^a_b χ^b` (χ the
  boost Killing field), `∂_a J^a=0` (the ONE EOM/conservation step), rewritten in null coords + a triangular FTC/Fubini on
  `0≤U≤V≤R`. HT1 fixes the boost-charge↔null-energy STRUCTURE; it does NOT fix `2π/ℏ` (that is BW/modular normalization = HT2).
  On the critical path, one brick. Sub-bricks (new file `QIQTH/HTkkPhysical.lean`):
  - [x] **HT1a (the honest core — pure calculus) — DONE 2026-07-08** ([AF] std-3, budget 0, no sorry).
    `QIQTH/HTkkPhysical.lean` → `QIQTH.HTkkPhysical.nullTriangle_ftc`: for `A B dA dB : ℝ→ℝ→ℝ` jointly-continuous
    (`Continuous (uncurry ·)`), `HasDerivAt`-parametrised partials (`dA=∂_U A`, `dB=∂_V B`), and `∂_U A + ∂_V B = 0`
    pointwise, `∫₀^R (A s s − B s s) ds = ∫₀^R A 0 V dV − ∫₀^R B U R dU`. Proof = two FTC applications
    (`intervalIntegral.integral_eq_sub_of_hasDerivAt`, once per variable) + ONE triangular Fubini swap (private
    `triangle_swap`: diagonal-truncated integrand `if U<V then dA U V else 0` on the square, integrable via a compact
    `IsMaxOn` bound, then `MeasureTheory.integral_integral_swap`); conservation collapses the A-column to `−` the
    B-column. NO divergence theorem, NO PDE. Wired into `QIQTH.lean` + `AxiomAudit` pin. HONEST: STRUCTURE only —
    no physics discharged; `2π/ℏ` untouched.
  - [x] **HT1b — DONE 2026-07-08** ([AF] std-3, budget 0, no sorry). `QIQTH.HTkkPhysical.kg_boost_charge_decomposition_1p1`:
    a SELF-CONTAINED flat-space null-coordinate instantiation (NOT the general curved kgStress machinery; the 1+1 objects
    are built explicitly in `(U,V)`). Field `φ:ℝ→ℝ→ℝ`; carried EOM+regularity hyps = jointly-continuous `φ,φU,φV,φUV`,
    the four `HasDerivAt` facts (incl. Clairaut `∂_V φU = φUV = ∂_U φV`), and KG `hKG: φUV U V = (μ/4)·φ U V`. Defs
    `T_UU=(φU)², T_VV=(φV)², T_UV=−(μ/4)φ²`; `A=V·T_VV−U·T_UV`, `B=V·T_UV−U·T_UU`; the partials `dA,dB` assembled via
    `HasDerivAt.pow/.const_mul/.mul/.sub`; conservation `dA U V+dB U V = 2(Vφ_V−Uφ_U)(φ_UV−(μ/4)φ)=0` by `rw [hKG]; ring`;
    fed to `nullTriangle_ftc`, three edge integrals rewritten via `intervalIntegral.integral_congr`. Result (general μ):
    `∫₀^R s·((φU s s)²+(φV s s)²+(μ/2)(φ s s)²) = (∫₀^R V·(φV 0 V)²) + (∫₀^R (U·(φU U R)²+(Rμ/4)(φ U R)²))`, i.e.
    `K₀(R)=H_+(R)+N_+(R)` with `N_+` EXPLICIT (massless = μ=0 special case). Wired into `AxiomAudit` pin. HONEST: classical
    boost-charge↔null-energy STRUCTURE only; `2π/ℏ` (HT2), transverse 3+1 flux + no-flux limit (HT1c), mode construction
    (HT3) are separate. [Route note: implemented directly in null coords rather than the (t,x) pull-back sketched below —
    both are valid; the null-coord version compiled cleanly.]
  - ~~[ ] **HT1b — SCOPED (GPT-5.5-pro 2026-07-08, sign-corrected).** Instantiate `nullTriangle_ftc` with the KG boost current
    ⟹ `K₀(R)=H_+(R)+N_+(R)`. ⚠ Corrections: `η_{UV}=+½` (not −½); the correct null conservation eqs are
    `∂_U T_VV+∂_V T_UV=0` and `∂_U T_UV+∂_V T_UU=0` (my first scoping interchanged the derivatives — WRONG). **First target =
    massive 1+1** (μ=m²; massless=μ=0), no transverse flux: `T_UU=φ_U²`, `T_VV=φ_V²`, `T_UV=−(μ/4)φ²`, `T₀₀=T_UU+T_VV−2T_UV`.
    Then `A=V·T_VV−U·T_UV`, `B=V·T_UV−U·T_UU`: `∂_U A+∂_V B = 2(Vφ_V−Uφ_U)(φ_UV−(μ/4)φ) = 0` by KG `φ_UV=(μ/4)φ`. Result
    `K₀(R)=∫₀^R s(φ_U²+φ_V²+(μ/2)φ²) = H_+(R)+N_+(R)`, `H_+=∫₀^R V φ_V(0,V)²`, `N_+=∫₀^R (U φ_U(U,R)²+(Rμ/4)φ(U,R)²)`.
    **KEY LEAN ROUTE (avoid null-metric machinery):** work in `(t,x)`; boost current `q=x·T_tt+t·T_tx`, `j=x·T_tx+t·T_xx`;
    prove `∂_t q−∂_x j=0` from Cartesian `kg_conserv`; pull back scalars `A=½(q+j)`, `B=½(−q+j)` at `t=(V−U)/2,x=(U+V)/2` ⟹
    `∂_U A+∂_V B=½(∂_x j−∂_t q)=0` (affine chain rule + product rule). 5 lemmas: null-components, null-conservation-from-KG,
    boost_AB_div, boost_AB_edges, HT1b capstone. Full 3+1 pointwise is a DIFFERENT theorem (transverse flux) — deferred to HT1c.~~ (superseded — DONE above)
  - [ ] **HT1c.** Transverse Fubini (add `y=(x²,x³)`, transverse boundary term carried) + the no-flux corollary
    (`Tendsto (outerFlux ·) atTop (𝓝 0)` + cutoff convergence ⟹ `K_boost = H_+`). Falloff carried as an explicit hypothesis.
  - Mathlib WALL to AVOID: the general noncompact 4D divergence theorem with null boundary (absent) — use explicit FTC/Fubini
    on the triangle instead. Full physical HT1 (with derived falloff) is NOT a days-to-week brick; the finite-cutoff identity
    WITH the explicit `N_+` term IS.
- [x] **HT2 — the `2π` IS ALREADY DERIVED (verification/attribution) — RESOLVED 2026-07-08.** Reading the actual Lean:
  `boostUnitary` is DEFINED with argument `2π·t` (modular flow `Δ^{it}=boostUnitary(2πt)`, the `2π` explicit), and
  `stripKMSrvd_boostUnitary` (axiom-free) PROVES it satisfies KMS at `β=2π` — the Bisognano–Wichmann/Unruh temperature is
  machine-checked. In `hTkk : 2π/ℏ·T_kk = (−2π∫conj(f)f').im`, that `2π` appears on BOTH sides (from differentiating
  `boostUnitary(2πt)` at 0 — the modular generator = `2π·`boost generator) and **CANCELS**, leaving the genuine content
  `T_kk/ℏ = (−∫conj(f)f').im` (the mode's BARE boost charge). **So: the `2π` is DERIVED (KMS temperature, already proven);
  the `1/ℏ` is a UNIT convention (ℏ free, like the value of G — a scale, not derivable); the ONLY genuinely-open content is
  the mode NORMALIZATION/SHAPE (HT3).** HT2 is thus NOT a new-physics brick — it is an attribution correction (F7 refined):
  `hTkk` is better than a flat "reduced not derived" — its `2π` coefficient IS the machine-checked BW temperature. ⚠ Consult
  to GPT-5.5-pro on this attempted twice, API 520 down — my reading is grounded in the actual theorem statements; re-verify
  the consult when the API is back (esp. Q3: whether HT3's physical mode NORMALIZATION is FORCED by the KG symplectic form
  up to ℏ, or leaves a further free constant — the decisive question for whether hTkk is fully-derived-modulo-ℏ or
  irreducibly-calibrated). No Lean brick needed for HT2 itself (the existing theorems already carry the `2π`).
- [ ] **HT3 — the CANONICAL positive-frequency boost-charge theorem — SCOPED (GPT-5.5-pro 2026-07-08, DECISIVE).**
  ⚠ **Physics verdict (settles the deepest question):** the coefficient is NOT irreducibly calibrated — physics DERIVES it
  (up to the ℏ unit). The one-particle vector `f_phys = j_ℏ ψ` is CANONICALLY normalized by the KG symplectic form + positive-
  frequency projection (`2ℏ·Im⟨j_ℏψ, j_ℏχ⟩ = σ(ψ,χ)`); rescaling breaks the CCR. So `q_B(f_phys) = (1/ℏ)·B_cl[ψ]` with the
  coefficient FIXED — no residual free constant beyond ℏ. GPT: "the ceiling is not 'physics only gives proportionality' —
  physics gives the coefficient." The gap is purely the LEAN formalization of the canonical KG→one-particle normalization.
  ⚠ **The one genuine subtlety:** there is NO unique normalizable mode at a POINT generator (pointlike horizon data are
  distributions; "localized near the generator" still leaves a smearing/profile choice) — so the Gaussian `f:=D·g₀` is
  calibrated until the canonical bridge is formalized. **TARGET (the stripped, tractable HT3, NOT full null quantization):**
  `HT3_posFreq_rapidityCharge_eq_classicalBoost (ψ : KG.Solution m) (hψ : GoodSchwartz/CompactCauchy) :
   rapidityBoostCharge (KG.posFreqRapidity ℏ ψ) = (1/ℏ)·KG.classicalBoostCharge ψ` — the canonical map
   `KG solution → one-particle rapidity wavefunction → (1/ℏ)·classical boost charge`. Then combine with HT1b's
  `K₀=H_+ + N_+` for the smeared horizon corollary `modularCharge = (2π/ℏ)·horizonFlux`. Rapidity picture: `H₁≃L²(ℝ,dθ)`,
  boosts = θ-translations, `b=−i∂_θ`, `−log Δ_W = 2π b` (BW). **Honest effort:** stripped Schwartz/L² version ~WEEKS; full
  AQFT null-quantization (Mellin/Rindler transforms, unbounded quadratic forms, Kontorovich–Lebedev) = months–years wall.
  SURVEY QIQTH `Fock/PauliJordan.lean` (KG two-point/symplectic), `StandardSubspace*`, `Fock/OneParticle.lean` for the
  existing `j_ℏ`/symplectic infra; scope the FIRST sub-brick (the symplectic form + `j_ℏ` positive-frequency map) or
  CHECKPOINT honestly if even the stripped version is blocked.
  - [x] **HT3 brick-1 — the KG SYMPLECTIC FORM on Cauchy data — DONE 2026-07-08** ([AF] std-3, budget 0, no sorry).
    NEW file `QIQTH/KGSymplectic.lean`. `kgSympl ψ₀ π₀ χ₀ ρ₀ = ∫ (ψ₀·ρ₀ − χ₀·π₀) ∂volume` (σ between Cauchy data).
    Landed: `kgSympl_antisymm` (`σ(a,b)=−σ(b,a)`, no integrability — pure `integral_neg`); `kgSympl_add_left` /
    `kgSympl_smul_left` (left bilinearity; add carries `Integrable` hyps, smul unconditional via `integral_const_mul`);
    `kgSympl_density_conservation` (the physics core — for two `1+1` KG solutions the density `ψ·∂_tχ−χ·∂_tψ` has `∂_t`
    equal to `∂_x` of the flux `ψ·∂_xχ−χ·∂_xψ`, both `= ψ·∂²_xχ−χ·∂²_xψ`; the `μ=m²` terms cancel via the carried wave
    equations `∂²_t=∂²_x−μ` — proved by `HasDerivAt.mul/.sub` + KG rewrite + `ring`); and the slice-independence
    capstone `kgSympl_slice_independent` (`HasDerivAt S 0 t`, the proof USING KG conservation to convert the
    differentiated density into the flux-derivative, then the carried spatial-decay hyp `∫ ∂_x flux = 0` kills it —
    same FTC/decay structure as `HTkkPhysical.nullTriangle_ftc`). SLICE-INDEPENDENCE INCLUDED (not deferred): the KG
    conservation physics (μ-cancellation) is discharged in Lean; differentiate-under-integral + spatial decay are honest
    carried HYPOTHESES (never axioms). Wired into `QIQTH.lean` + `AxiomAudit` pins. HONEST scope firewall: does NOT build
    `j_ℏ` (the positive-frequency projection — the next, hard brick), NOT the boost-charge identity, NOT `2π/ℏ`, NOT
    numerical-G/QG.
  - **⚠ `j_ℏ` REACHABILITY VERDICT (GPT-5.5-pro 2026-07-08, blunt): the FULL `j_ℏ` is a genuine MULTI-MONTH Mathlib wall
    — CHECKPOINT it.** The bounded `Lp` positive-frequency map matching the existing rapidity `L²(dθ)` (`niceWedgeGenSet`)
    needs: a weighted KG Sobolev phase space (`ψ̃∈L²(ω dk)`, `π̃∈L²(ω⁻¹dk)` — the `√ω` multiplier is UNBOUNDED on naive
    L²×L², Mathlib lacks this), the Fourier `L²→L²` unitary with inner-product rewrite lemmas, the `Lp` rapidity CoV
    isometry `f(θ)=√(m cosh θ)·a(m sinh θ)`, boost covariance, and boost-charge equality on a dense domain — "not blocked by
    deep missing mathematics, but absolutely a multi-month infrastructure build." Massless-1+1 is NOT easier (ω=|k| singular
    at 0, IR zero-mode). But there ARE tractable HIGH-VALUE sub-bricks that nail the COEFFICIENT PHYSICS before the wall:
  - [x] **HT3 brick-2 — the FOURIER-SIDE positive-frequency coefficient theorem — DONE 2026-07-08** ([AF] std-3, budget 0,
    no sorry). `QIQTH.KGSymplectic.two_hbar_im_inner_posFreq_eq_sigmaK`: on Fourier-side data `Ψ π Χ Ρ : ℝ→ℂ`
    (conjugate-symmetric = real fields, carried as hyps), with `kgOmega m k := √(k²+m²)` and `posFreqCoeff m ℏ Ψ Π k :=
    (ω_k·Ψ k + i·Π k)/√(2ℏ·ω_k)`, PROVED `2ℏ·(∫ conj(posFreqCoeff Ψ Π)·posFreqCoeff Χ Ρ dk).im = sigmaK Ψ Π Χ Ρ` where
    `sigmaK := (∫ (conj Ψ·Ρ − conj Χ·Π)).re`. Proof = pointwise `|a|²` algebra (`hnum` via `linear_combination … Complex.I_sq`
    for the `−i²`; the `√(2ℏω)` denominator is real ⟹ `hDD : √·√ = 2ℏω`) giving `2ℏ·conj(a)·b = htDiag + i·(conjΨΡ−conjπΧ)`;
    then `.im` + `integral_im`/`integral_re`/`integral_const_mul`/`integral_add`; the diagonal `htDiag.im` integrates to `0`
    because it is ODD under `k↦−k` (`htDiag(−k)=conj(htDiag k)` from conj-symmetry + evenness of ω, via the `neg`-invariance
    of `volume` `Measure.measurePreserving_neg`); `(i·z).im = z.re` and `(conjπΧ).re=(conjΧπ).re` give `sigmaK`. This PROVES
    the symplectic form = `2ℏ·Im` of the one-particle inner product — the DEFINING property that makes the normalization
    canonical (the coefficient physics, in Lean, on the Fourier side). Wired into `AxiomAudit` pin. HONEST scope firewall:
    NO Lp/rapidity `j_ℏ` (brick-4 wall), NO Parseval bridge to position-space `kgSympl` (brick-3), NO boost-charge identity,
    NO `2π/ℏ`, NO numerical-G/QG; conj-symmetry + integrability of the three product terms carried as HYPOTHESES, never axioms.
    [Note: the conjugate-momentum data is named `π` in Lean because capital `Π` is a reserved pi-type token; math is identical.]
  - [x] **HT3 brick-3 — the Parseval bridge — DONE 2026-07-08** ([AF] std-3, budget 0, no sorry).
    `KGSymplectic.lean`: `sigmaK_fourier_eq_position (ψ₀ π₀ χ₀ ρ₀ : 𝓢(ℝ,ℂ)) : sigmaK (𝓕ψ₀)(𝓕π₀)(𝓕χ₀)(𝓕ρ₀) =
    (∫ (conj ψ₀·ρ₀ − conj χ₀·π₀)).re`, and the real-field capstone `parseval_bridge_real (…) (hψ … : ∀ x,(ψ₀ x).im=0)…
    : sigmaK (𝓕ψ₀)(𝓕π₀)(𝓕χ₀)(𝓕ρ₀) = kgSympl ψ₀.re π₀.re χ₀.re ρ₀.re`. The bridge = **Plancherel for Schwartz
    functions** `SchwartzMap.integral_inner_fourier_fourier` (honest ∫, NO `Lp` classes; Mathlib's unitary `e^{−2πixξ}`
    convention ⟹ **NO 2π factor**), specialized to the scalar inner `⟪a,b⟫_ℂ = conj a·b` (`RCLike.inner_apply'`).
    Integrability DISCHARGED (bounded × integrable: `Integrable.bdd_mul` + the Schwartz `(0,0)`-seminorm bound
    `SchwartzMap.norm_le_seminorm`), never assumed. NOTE the ACTUAL Mathlib lemmas differ from the first consult's names
    (`integral_fourierIntegral_mul_eq`/`Real.fourierIntegral_conj` do NOT exist in v4.30.0); `integral_inner_fourier_fourier`
    is the right hook. **brick-2 ∘ brick-3 now gives** `2ℏ·Im⟨aK(𝓕·)⟩ = kgSympl` — the canonical-normalization identity
    grounded in the position-space symplectic form. Schwartz regularity in the TYPE; reality carried as HYPOTHESIS, never axiom.
  - **HT3 brick-4+ (the multi-month wall — user authorized investing 2026-07-08; grinding sub-bricks):** the `Lp` rapidity
    unitary matching `niceWedgeGenSet`, the bounded `j_ℏ` from the weighted phase space, boost covariance, and the
    boost-charge identity `q_B(j_ℏψ)=(1/ℏ)·B_cl`.
    - [x] **Lp brick-1 — the MASS-SHELL MEASURE = rapidity pushforward — DONE 2026-07-08** ([AF] std-3, budget 0, no sorry).
      `OneParticleMeasure.lean` `map_rapidityHalfMeasure_eq_massShellMeasure (hm : 0<m)`:
      `Measure.map (θ↦m·sinh θ) ((1/2)•volume) = volume.withDensity (fun k => (2·√(k²+m²))⁻¹)` — the exact Lorentz-invariant
      measure whose weighted `L²` is the KG one-particle space (`dk/2ω = dθ/2`; energy cancels the Jacobian, factor exactly
      `1/2` not `1/2m`). Supporting `omega_rapidity`, `jacobian_cancel`. Via `Measure.ext_of_lintegral` + `lintegral_map` +
      the 1-D CoV `lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn`. GPT-5.5-pro-scoped as the smallest honest first brick.
    - [x] **Lp brick-2 — the rapidity CHANGE OF VARIABLES on the one-particle inner product — DONE 2026-07-08** ([AF] std-3).
      `OneParticleMeasure.lean`: `massShellMeasure m`; the `k↦θ` `MeasurableEquiv` `rapidityMeasurableEquiv` +
      `rapidity_measurePreserving` ((1/2)•vol → massShellMeasure); `integral_massShellMeasure_eq_half_rapidity`
      (`∫ H ∂massShellMeasure = (1/2)•∫ H(m sinh θ) ∂vol`, via `integral_map_equiv`); conj-mul corollary
      `massShell_conj_mul_integral_eq_half_rapidity` (`starRingEnd ℂ`). The one-particle integral in rapidity form.
    - [x] **Lp brick-3 — the one-particle `L²` ISOMETRY — DONE 2026-07-09** ([AF] std-3). `OneParticleMeasure.lean`:
      `rapidityPullL2` (`Lp.compMeasurePreserving` pullback along the rapidity equivalence), `rapidityPullL2_isometry`,
      `rapidityPullL2_norm` — the one-particle space `L²(massShellMeasure m)` embeds ISOMETRICALLY into the flat rapidity
      `L²((1/2)•volume)`. The `L²`-level packaging of the rapidity change of variables.
    - [x] **Lp brick-4 — the WEIGHTED-`L²` ISOMETRY (√ω "unbounded" objection DISSOLVED) — DONE 2026-07-09** (user
      authorized the Sobolev investment; [AF] std-3). `WeightedL2.lean`: the `√ω` multiplier is unbounded on plain `L²(dk)`,
      but multiplication by a weight `w ≥ 0` is a norm-preserving map `L²(vol.withDensity w²) → L²(vol)`
      (`eLpNorm_smul_weight_eq_withDensity`, via `lintegral_withDensity_eq_lintegral_mul` + pointwise `enorm_smul`). So `√ω`
      is an ISOMETRY on the correctly-weighted KG-Sobolev domain — the structural resolution of the wall (the multiplier is
      bounded once the domain is right).
    - [x] **Lp brick-4b — the MemLp transfer — DONE 2026-07-09** ([AF] std-3). `WeightedL2.lean`
      `memLp_two_weight_smul_iff : MemLp f 2 (vol.withDensity w²) ↔ MemLp (w·f) 2 vol` — the usable membership form of the
      weight isometry (lets a wavefunction move between the weighted KG-Sobolev space and flat L²). (The full cross-measure
      `LinearIsometry` bundling is a quotient-level rabbit hole per GPT-5.5; the MemLp transfer is the sufficient form.)
    - [x] **Lp brick-5 — the POSITIVE-FREQUENCY MAP well-defined on `H^{1/2}⊕H^{-1/2} → L²` — DONE 2026-07-09** ([AF] std-3;
      the payoff of the detour). `PosFreqDomain.lean`: `a(Ψ,π)=(ω·Ψ+i·π)/√(2ℏω) = (2ℏ)^{-1/2}(√ω·Ψ)+i(2ℏ)^{-1/2}(ω^{-1/2}·π)`
      lands in flat `L²` EXACTLY WHEN the data lie in the ω- and ω^{-1}-weighted `L²` (=`H^{1/2}`, `H^{-1/2}`):
      `kg_posFreq_memLp_split` (split form), `kg_coeff_eq_split` (pointwise factorization), `kg_posFreq_memLp` (quotient form).
      The correct operator domain the naive-`L²` objection was missing.
    - [x] **Lp brick-6 — canonical normalization `σ = 2ℏ·Im⟪·,·⟫` at the HILBERT level — DONE 2026-07-09** ([AF] std-3).
      `OneParticleInner.lean`: `L2_inner_toLp_eq_integral : ⟪toLp a, toLp b⟫_ℂ = ∫ conj(a)·b` (via `L2.inner_def` +
      `MemLp.coeFn_toLp`), and `two_hbar_im_L2_inner_eq_sigmaK : 2ℏ·Im⟪toLp a, toLp b⟫_ℂ = σ_K` from brick-2 — the KG
      symplectic form is `2ℏ·Im` of the genuine one-particle inner product. Composes with brick-5 (`MemLp` of the coefficient).
    - [x] **Lp brick-7 CAPSTONE — `σ_K = 2ℏ·Im⟪a_L2,b_L2⟫` for the KG positive-freq coefficients — DONE 2026-07-09**
      ([AF] std-3). `PosFreqInner.lean` `two_hbar_im_L2_inner_posFreq_eq_sigmaK` composes brick-2 (bare-integral) + brick-6
      (integral↔L² bridge): the classical KG symplectic form `σ_K` equals `2ℏ·Im` of the one-particle Hilbert inner product
      of the `√(2ℏω)`-normalized positive-frequency coefficients. L² memberships from brick-5 (`ω=kgOmega m`). This ties the
      whole `Lp` chain to the physics σ on the actual one-particle Hilbert space — the coefficient physics of `hTkk`.
    - [x] **Lp brick-8 — BOOST COVARIANCE (unitary preserving `σ`) — DONE 2026-07-09** ([AF] std-3). `OneParticleBoost.lean`:
      the boost of rapidity `β` is `boostRapidity β : Lp ℂ 2 volume →ₗᵢ[ℂ] Lp ℂ 2 volume` (pullback along `θ↦θ+β`, via
      `Lp.compMeasurePreservingₗᵢ` + translation-invariance of `volume`), so the boost is UNITARY; `boostRapidity_inner`
      preserves `⟪·,·⟫`, `two_hbar_im_boostRapidity_inner` preserves `2ℏ·Im⟪·,·⟫ = σ`. Working in the momentum/rapidity
      representation sidesteps the measure-zero mass-shell obstruction (the one-particle space is genuinely `L²` there).
    - [x] **Lp brick-9 — PACKAGED one-particle map `jHbar` + boost-invariance of `σ` — DONE 2026-07-09** ([AF] std-3).
      `OneParticleMap.lean`: `jHbar m ℏ Ψ π h := h.toLp (posFreqCoeff m ℏ Ψ π)`; `jHbar_two_hbar_im_inner_eq_sigmaK`
      (`2ℏ·Im⟪j_ℏ u, j_ℏ v⟫ = σ_K`) and `jHbar_boost_two_hbar_im_inner_eq_sigmaK` (the rapidity boost leaves `σ_K`
      unchanged — Lorentz-invariance of the symplectic form via `j_ℏ`, at the rapidity level).
    - [x] **Lp brick-10 — BRIDGE to the pre-existing continuum Fock tower — DONE 2026-07-09** ([AF] std-3).
      **KEY DISCOVERY:** QIQT-H ALREADY has a continuum bosonic Fock/CCR tower on `Lp ℂ 2 volume` — the same space `jHbar`
      lands in — `QIQTH.Fock.OneParticle.boostUnitary` (1+1D mass-`m` boost unitary group; brick-8's `boostRapidity` is a
      rediscovery of it), `QIQTH.Fock.FockSpace` (symmetric Fock), `QIQTH.Fock.SecondQuant.boostFock = Γ(boostUnitary)`
      (second-quantized boost, vacuum-invariant). `OneParticleFockBridge.jHbar_boostUnitary_two_hbar_im_inner_eq_sigmaK`:
      `σ_K` via `jHbar` is invariant under the EXISTING Fock boost — so `hTkk`'s coefficient physics embeds in the
      pre-existing Fock tower, whose `Γ(boostUnitary)` already carries the Fock-level Lorentz covariance. So the "Fock
      second-quantization phase" was LARGELY ALREADY BUILT in QIQT-H; the bridge connects the new `j_ℏ`/`σ` to it.
    - **TRACK-A STATUS (2026-07-09): the MOMENTUM/RAPIDITY-representation `j_ℏ` is COMPLETE and BRIDGED TO FOCK** — domain
      (`H^{1/2}⊕H^{-1/2}`, brick-5), `σ = 2ℏ·Im⟪·,·⟫` (capstone), boost = unitary (brick-8/existing `boostUnitary`),
      packaged map + boost-invariance of `σ` (brick-9), embedded in the pre-existing continuum Fock/CCR tower with
      second-quantized covariance (brick-10). The ONE genuine remaining piece toward a fully-geometric position-space `j_ℏ`:
      was the GEOMETRIC position-space Lorentz covariance — **and it TOO already exists in QIQT-H** (discovered 2026-07-09,
      brick-11 audit). `QIQTH.Fock.Localization.Krep m f θ = (1/√2)·minkowskiFourier f (massShell m θ)` maps a **spacetime
      test function** `f` to its rapidity amplitude via the Minkowski Fourier transform ON the mass shell — sidestepping the
      "tilted slice / measure-zero" obstruction entirely, because `f` is a test function (its FT is evaluable pointwise on the
      shell). `boosted_localized_modes_eq` proves `(K(β_a f))(θ) = (Kf)(θ+a)` — a spacetime Lorentz boost of the test function
      IS the rapidity translation `boostUnitary` on the amplitude — and `localized_typicality_boost_invariant` gives the
      boost-invariance. Both axiom-free. So the geometric position-space boost bridge is NOT a missing multi-file phase — it
      was built in the prior one-particle-BW/localization campaign.
      **TRACK-A COMPLETE (2026-07-09): the free-field one-particle `j_ℏ` — domain (`H^{1/2}⊕H^{-1/2}`), `σ = 2ℏ·Im⟪·,·⟫`
      normalization, boost covariance (rapidity-level AND geometric position-space via `Krep`), and Fock embedding — is fully
      machine-checked axiom-free.** Track A's new contribution: the explicit `σ`-normalized Fourier-Cauchy-data chain
      (bricks 1–10) + the Fock bridge; the geometric `Krep` localization + covariance pre-existed. The only residual is a
      cosmetic reconciliation of the two parametrizations (Fourier-Cauchy-data `jHbar` ↔ spacetime-test-function `Krep`) —
      not a wall. The ACTUAL open frontier is NOT `j_ℏ` (done) but interacting matter / continuum Type III₁ / QG proper.
    - HONEST CEILING (still binding until the full `j_ℏ` lands): hTkk STRUCTURE (`K₀=H_+ + N_+`) + `2π` (BW/KMS temperature) +
      coefficient CANONICAL-NORMALIZATION (bricks 2+3: `σ=2ℏ·Im⟨a,a⟩`) are DERIVED; the `Lp` packaging of `j_ℏ` into the
      rapidity convention is the named frontier (Lp brick-1 = the measure, now landed); `1/ℏ` a unit.
- [ ] **HT4 — SMEARED physical hTkk + local limit (the capstone).** `physical_hTkk_smeared`:
  `Q[f_phys(χ_ε)] = (2π/ℏ)∫ χ_ε·T_kk`; then `physical_hTkk` by the approximate-identity limit `χ_ε → δ_{(x,v)}` ⟹ the
  pointwise `hTkk` for `f_phys`, coefficient DERIVED. Feed it into a `qiqt_gr_freefield_physical` capstone replacing the
  calibrated ansatz. [AF] std-3.

## Verbatim HAVE / HAVE-NOT (target after HT4)
- **HAVE (target):** "The free-field induced-gravity chain's localization map `hTkk` is a THEOREM: the one-particle wedge
  mode is CONSTRUCTED from φ (positive-frequency wedge smearing), and its boost charge equals `(2π/ℏ)·T_kk` with the
  coefficient DERIVED from Bisognano–Wichmann + the KG stress-tensor Noether charge (KMS β=2π) — no fitted profile, no free
  calibration. Einstein's equations for the free KG field follow with the localization map derived, not assumed."
- **HAVE-NOT (binding):** "Still free-field, flat/pp-wave, linearized-matter; does NOT discharge the Clausius/area law, the
  FQ capacity bound (`hbound`, P4), the reference-state identification (`hcap`), or the numerical value of `G` (η carried);
  NOT interacting matter, NOT the continuum Type III₁ limit, NOT emergent spacetime, NOT QG."

## Discipline (every increment)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<mod>` GREEN; every new theorem `#print axioms` std-3; `bash
scripts/axiom_budget_check.sh` budget 0; AxiomAudit pins; wire into `QIQTH.lean`; ONE commit per HT-step LOCAL ONLY (no push)
with the `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>` trailer; update this plan +
`LEAN_RESULTS_INVENTORY.md`; check sibling jobs FIRST (git log/status, ps for lake — a website-SEO sibling job commits on top,
DO NOT touch `website/`); explicit git paths only (never `-A`). NO `sorry`; carried inputs as HYPOTHESES/struct fields NEVER
axioms; NO vacuous/calibration-hiding discharge (that is the very defect being fixed); CONSULT GPT-5.5-pro before HT1/HT2/HT3;
NEVER claim the physical localization map discharged until `f_phys` is built from φ and the coefficient derived — honest
HAVE/HAVE-NOT; checkpoint with the EXACT Lean error / the precise Mathlib gap if a step stalls after a real attempt.

## Progress log
- **2026-07-08 (scoped):** dual consult. GPT-5.5-pro: the Gaussian discharge is a calibration-hiding relabel; genuine target
  = physical wedge mode from KG two-point + stress-tensor boost charge (Rindler modular H), smeared-then-local-limit. Fable
  Lean-audit: verdict "reduced, not derived" — mode shape/width free (`GaussianModeFamily`), only the unit phase carries the
  inserted `2π/ℏ`; `qiqt_gr_freefield_complete` residuals catalogued (hKG, hcap, hbound, hpp0, hK=Clausius, Raychaudhuri,
  a=2π/ℏη=G). Both converge: re-open `hTkk` as the physical-localization theorem; keep the Gaussian as a labelled lemma.
