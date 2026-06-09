# K-Localization Plan — the last physics input for the prize

*The concrete spacetime localization map `K` and Pauli–Jordan microcausality: the only gap between the
machine-checked measure machinery and the literal Lorentz-covariant Born-typicality measure on a relativistic
free field. Written 2026-06-09 after GPT-5.5-pro attack-plan consult #6. 1+1D massive neutral scalar.*

---

## 0. Where this plugs in (already done, axiom-free)

- `H = L²(ℝ, dθ)` (rapidity); `OneParticle.boostUnitary a : H ≃ₗᵢ[ℂ] H` is the boost = **translation**
  (group law `boostUnitary_add_apply`). ⚠ **Convention to lock (Phase 0):** the existing flow gives
  `(boostUnitary a ψ)(θ) = ψ(θ − a)` (it acts contravariantly `ψ ↦ ψ∘χ_{−a}`). The test-function action
  `boostTest` MUST be defined with the matching sign so that `K(boostTest a f) = boostUnitary a (K f)` holds
  on the nose. Verify this in Phase 0; do not patch it later (GPT trap #3).
- The whole measure tower (`WeylBit*`, `WeylCLM`, `WeylBitGeoCovariance`) is built and proved.
- **`SpacetimeLocalization`** (interface, `LocalizationSkeleton.lean`) already proves: *given* `K`, the
  region/boost/relabel data, K-equivariance, and `pauli_jordan` (spacelike ⇒ `Im⟪Kf,Kg⟫=0`), the localized
  boost-covariant, pushforward-invariant `μ∞` exists. **So `K` + Pauli–Jordan are the only unfilled fields.**

The job: build the concrete `K` (Phases 0–2), feed it into `SpacetimeLocalization` conditionally on a
Pauli–Jordan *certificate* (Phase 3–4), then attack the analytic support theorem (Phase 5, the wall).

---

## 1. The clean `K` (GPT-locked formulation)

Spacetime `V := Fin 2 → ℝ`, coords `(t,x)`. **Minkowski pairing** `η(p,x) = p₀x₀ − p₁x₁` (NOT Euclidean —
GPT trap #2). Proper boost `Λ a (t,x) = (cosh a·t + sinh a·x, sinh a·t + cosh a·x)`, `det Λ a = 1`,
`η(Λp,Λx)=η(p,x)`. Mass shell `p_m θ = (m cosh θ, m sinh θ)`, with the key geometry `Λ a (p_m θ) = p_m (θ+a)`.

Minkowski Fourier (wrapper over Mathlib `fourierIntegral`, convention made explicit):
`f̂_M(p) = ∫_{ℝ²} e^{−i η(p,x)} f(x) dx`.

**Test functions** — compactly-supported Schwartz, **real-valued** (neutral scalar ⇒ Weyl labels from a REAL
test space, complexified only for lemmas; GPT trap #5):
```
structure LocalTest where
  val : SchwartzMap V ℂ
  hsupp : HasCompactSupport (val : V → ℂ)
  hreal : ∀ x, (val x).im = 0     -- real-valued smearings
```

**The map** (positive mass shell ONLY — do NOT add negative energies as independent states; GPT trap #4):
```
def Krep (f : LocalTest) (θ : ℝ) : ℂ := (1 / Real.sqrt 2 : ℂ) * minkowskiFourier f (massShell m θ)
def K    (f : LocalTest) : H := MemLp.toLp (Krep m f) (Krep_memLp m f)
```
⚠ **The `1/√2` is load-bearing** (GPT trap #1): the invariant shell measure is `dp/(2ω) = dθ/2`; using `dθ`
without `1/√2` scales the symplectic form by 2 and silently changes the physics.

For real `f`: `conj(f̂_M(p)) = f̂_M(−p)`, so the negative-frequency content is recovered by conjugation —
this is how the *full* Pauli–Jordan (both frequencies) emerges from a *positive*-shell one-particle space.

---

## 2. Tractable now vs. the wall (GPT triage)

**Tractable in current Mathlib (green, axiom-free):**
- **Geometry/rapidity lemmas** — `massShell_boost` (`Λa(p_m θ)=p_m(θ+a)`), `minkowskiDot_boost`,
  `det_lorentzBoost` — `simp` + `Real.cosh_add`/`sinh_add`/`cosh_sq_sub_sinh_sq`.
- **`Krep_memLp` (boundedness from Schwartz)** — `f̂` of Schwartz is Schwartz; on the shell
  `|f̂_M(p_m θ)| ≤ C_N(1+‖p_m θ‖)^{−N}` and `‖p_m θ‖ ≳ cosh θ ≳ 1+|θ|`, so dominate by `(1+|θ|)^{−4}`.
  ⚠ Do NOT claim `L²(ℝ²) → L²(shell)` is bounded — FALSE without Sobolev `Hˢ, s>½` (GPT trap #7). Schwartz
  is the right domain.
- **Boost equivariance** — core lemma `minkowskiFourier_boost`: `f̂_M(boostTest a f)(p) = f̂_M(f)(Λa p)`
  (change of variables `y=Λa x`, `det=1`, pairing invariance) ⇒ `K(boostTest a f) = boostUnitary a (K f)`
  (pointwise a.e. equality of `Lp` reps).
- **The inner-product / mass-shell formula** `⟪Kf,Kg⟫ = ½∫ conj(f̂_M(p_θ)) ĝ_M(p_θ) dθ` and the
  **symplectic identity** `2·Im⟪Kf,Kg⟫ = full-mass-shell antisymmetric Pauli–Jordan bilinear` — this proves
  `K` induces the genuine PJ symplectic form (not a Wightman 2-pt function; GPT trap #6) and kills the
  vacuity worry (GPT trap #10).

**The wall (defer/cite):** the Pauli–Jordan SUPPORT theorem `supp Δ_m ⊆ {t²−x²≥0}` (closed light cone) — needs
distribution/Bessel/oscillatory-integral machinery Mathlib lacks. Multi-month.

---

## 3. Pauli–Jordan: the honest route (ranked)

Keep the development **axiom-free** by making locality a **hypothesis-field / certificate**, never an `axiom`:
```
structure PauliJordanLocality (m : ℝ) (K : LocalTest → H) : Prop where
  locality : ∀ f g, SpacelikeSeparated (tsupport f.val) (tsupport g.val) → Complex.im ⟪K f, K g⟫_ℂ = 0
```
Then the final theorem takes `(PJ : PauliJordanLocality m (K m))` as a **variable** (axiom-free), instantiating
`SpacetimeLocalization`.

**Kernel-certificate bridge (eventual unconditional route, 1+1):**
```
structure PauliJordanKernelCert (m) (K) where
  Δ : V → ℝ
  hLI : LocallyIntegrable Δ
  sigma_eq_kernel : ∀ f g, 2*Complex.im ⟪K f,K g⟫_ℂ = ∫ x, ∫ y, fℝ x * Δ (x−y) * gℝ y
  support_lightcone : Function.support Δ ⊆ {z | 0 ≤ minkowskiSq z}
theorem locality_from_kernel : PauliJordanKernelCert m K → PauliJordanLocality m K   -- EASY, axiom-free
```
The 1+1 kernel is the explicit, **locally integrable** (no distribution theory needed for the support step)
`Δ_m(t,x) = ½ sgn(t) J₀(m√(t²−x²)) 1_{t²≥x²}` — support in the closed light cone is immediate from the
indicator. The hard part is `sigma_eq_kernel` (the Bessel kernel IS the inverse Fourier transform of the
mass-shell commutator measure). Route (3) (causal propagator `E=E_ret−E_adv` + finite propagation speed) is
conceptually cleaner but a bigger PDE project — skip for now.

**Smallest nontrivial fragment to prove first:** the algebraic identity
`2·Im⟪Kf,Kg⟫ = fullMassShellPauliJordanBilinear m f g` (Phase 2). It certifies `K` carries the *correct*
symplectic form and resolves the both-frequencies issue — before any support analysis.

---

## 4. Phased plan (green axiom-free checkpoints)

| Phase | Deliverable | Status / scope |
|---|---|---|
| **0** Convention lock | `V`, `minkowskiDot`, `minkowskiSq`, `massShell`, `lorentzBoost`; `massShell_boost`, `minkowskiDot_boost`, `minkowskiSq_boost`, `minkowskiSq_massShell` | **DONE** 2026-06-09 (commit 914e656, `Localization.lean`, axiom-free) |
| **1a** Unimodular linear map | `lorentzBoostMat`, `lorentzBoostₗ`, `lorentzBoostₗ_apply`, **`det_lorentzBoost=1`** | **DONE** 2026-06-09 (commit pending, `Localization.lean`, axiom-free) |
| **1b** Volume-preservation | **`measurePreserving_lorentzBoost`** | **DONE** 2026-06-09 (commit pending; NO EuclideanSpace migration needed — see note) |
| **1c** Fourier wrapper + equivariance | `minkowskiFourier`, `boostTest`, `measurableEmbedding_lorentzBoost`, **`minkowskiFourier_boost`** | **DONE** 2026-06-09 (commit pending, axiom-free) |
| **2a** Localized amplitude + covariance | `Krep` (`1/√2`·f̂ on shell), **`Krep_boost`** (boost = rapidity translation θ↦θ+a) | **DONE** 2026-06-09 (commit pending, axiom-free) |
| **2b-i** Reality / both-frequencies | `minkowskiDot_neg_left`, **`minkowskiFourier_conj`** (conj(f̂_M(p))=(conj f)^_M(−p)) | **DONE** 2026-06-09 (commit pending, axiom-free) |
| **2b-ii** Symplectic form + L²-valued `K` | `Kform`, **`Kform_im_antisymm`** (symplectic antisymmetry = Pauli–Jordan not Wightman); `LocalTest` (memLp domain field), **`K : LocalTest → L²(ℝ)`** (the H-valued localization Stage-2 needs), `trivialLocalTest` | **DONE** 2026-06-09 (commit pending, axiom-free) |
| **2b-iii(a)** Boundedness, measurability half | `minkowskiFourier_continuous`, `continuous_massShell`, **`Krep_aestronglyMeasurable`** | **DONE** 2026-06-09 (commit pending, axiom-free) — part (a) of `MemLp` (Riemann–Lebesgue continuity). |
| **2b-iii(b)** Boundedness, integrability | `one_add_sq_le_cosh_sq`, `integrable_cosh_inv_sq`, `memLp_cosh_inv`, **`Krep_memLp_of_decay`** | **DONE** 2026-06-09 (commit pending, axiom-free) — ALL the measure theory discharged: `1/cosh ∈ L²` (dominated by the Cauchy density), so `‖(K f)(θ)‖ ≤ C/cosh θ ⟹ K f ∈ L²`. |
| **2b-iii(c)** ★ Boundedness CLOSED (Gaussian) | `minkowskiFourier_gaussian`, `Krep_gaussian_eq`, **`gaussian_Krep_memLp`**, **`gaussianLocalTest`** | **DONE** 2026-06-09 (commit e7696d6, axiom-free, no sorry) — a GENUINELY NON-DEGENERATE `LocalTest`: the Gaussian's localization is provably in `L²(ℝ)`. Explicit Fourier (Fubini + complex Gaussian Fourier) ⇒ real-cast amplitude `2^{−½}π exp(−m²cosh2θ/4)` ⇒ `‖Krep‖²=(π²/2)exp(−(m²/2)cosh2θ)` integrable. The general-Schwartz `1/cosh` decay (via IBP) is now an optional generalization; the boundedness is genuinely realized. |
| **2** ★ Concrete `K` (FIRST increment) | `Krep`, `Krep_memLp`, `K`; **`K_boost`** (equivariance), **`inner_K_formula`**, **`two_im_inner_eq_full_mass_shell`** | the highest-value first increment; weeks |
| **3** Conditional localized measure | instantiate `SpacetimeLocalization` from `(PJ : PauliJordanLocality m (K m))` ⇒ `concrete_localized_covariant_measure` (axiom-free, conditional) | short once 2 done |
| **4** Kernel-certificate bridge | `PauliJordanKernelCert`, `locality_from_kernel` (support ⇒ locality, easy) | short |
| **5** The wall | the 1+1 `Δ_m` Bessel kernel + `sigma_eq_kernel` (mass-shell Fourier rep) + `support_lightcone` | **multi-month** analytic (Bessel/oscillatory integrals); the genuine frontier |

**⚠ Phase-1 finding (2026-06-09, CONFIRMED in code).** Phase 1a (the unimodular linear map +
`det Λ_a = 1`) is DONE on `Fin 2 → ℝ`, clean via `Matrix.toLin'` + `LinearMap.det_toLin'` +
`Matrix.det_fin_two_of` + `Matrix.mulVec_eq_sum` (a local `mulVec_two` 2×2 helper — `Matrix.mulVec_fin_two`
lives in an unimported topology file, don't use it). **Phase 1b (volume-preservation) is BLOCKED on a
measure-instance diamond:** `map_linearMap_addHaar_eq_smul_addHaar` needs `(volume).IsAddHaarMeasure`, and on
the raw Pi type `Fin 2 → ℝ` this initially appeared to fail. **RESOLVED 2026-06-09 — NO EuclideanSpace
migration was needed.** Scratch tests showed `(volume : Measure (Fin 2 → ℝ)).IsAddHaarMeasure` synthesizes
fine (`isAddHaarMeasure_volume_pi` / generic). The two REAL causes of the earlier failure: (1) `lorentzBoostₗ`
was typed `V →ₗ[ℝ] V` with the **reducible abbrev `V`**, which blocks instance search when
`map_linearMap_addHaar_eq_smul_addHaar` infers `E = V` (synth won't unfold the abbrev) — FIX: type
`lorentzBoostₗ : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)` directly; (2) the file was **missing `open MeasureTheory`**,
without which the `volume` instance resolution differs — FIX: `open Real MeasureTheory`. With both, the boost
stays on `Fin 2 → ℝ` (no migration) and `measurePreserving_lorentzBoost` proves cleanly via
`map_linearMap_addHaar_eq_smul_addHaar volume hdet` + `det = 1`. (Lesson: prefer concrete types over reducible
abbrevs in statements that drive instance search; remember `open MeasureTheory`.)

**First increment = Phase 0–2**: a concrete, bounded, boost-equivariant `K` landing exactly in the existing
`L²(ℝ)`, with the proven symplectic-form identity. After Phase 3, the *literal* OP3b statement holds
**conditionally on a `PauliJordanLocality` certificate** — i.e. the prize reduces to one clearly-named,
axiom-free analytic obligation. Phase 5 discharges it; until then it is an honest interface, not an axiom.

**Honest scope:** Phases 0–4 are weeks-to-~2-months and independently valuable (they turn the abstract
boost-orbit instance into a genuine mass-shell field localization, conditional only on the cited support
theorem). Phase 5 is the multi-month wall and may stay cited until Mathlib's Bessel/distribution
infrastructure grows.

---

## 5. Soundness traps (must-check list, from GPT consult #6)

1. **Missing `1/√2`** ⇒ symplectic form off by ×2. Use `K = 2^{−½} f̂|_shell`.
2. **Euclidean vs Minkowski pairing** — must be `p₀t − p₁x`.
3. **Boost sign** — match `boostUnitary a ψ = ψ(·−a)`; define `boostTest` to fit. Lock in Phase 0.
4. **Positive shell only** — neutral scalar: do NOT add negative energies as independent one-particle states.
5. **Real test space** — Weyl labels from real-valued smearings (complexify only for lemmas).
6. **Wightman ≠ Pauli–Jordan** — the positive-frequency 2-pt function does NOT vanish spacelike; only its
   antisymmetric imaginary part does. Prove the `2·Im⟪⟫` identity, not vanishing of `⟪⟫`.
7. **No `L²→L²(shell)` bound** — restriction needs Schwartz/Sobolev `Hˢ,s>½`; don't claim the naive bound.
8. **Axiom leakage** — `structure` field / theorem `variable` is fine; NO `axiom`/`constant`/`sorry`.
9. **Support boundary** — use `tsupport`/closed support, strict spacelike separation, closed light cone.
10. **Vacuity guard** — `K=0` or a fake real-only `K` makes `Im⟪Kf,Kg⟫=0` trivially; the inner-product /
    mass-shell formula (Phase 2) is what proves `K` is genuine.

---

## 6. Strongest honest claim once Phases 0–4 land (Phase 5 cited)

> "We machine-check, axiom-free, a concrete Poincaré-equivariant mass-shell localization `K` of the 1+1D
> massive free field into the one-particle space, and prove it induces the genuine Pauli–Jordan symplectic
> form; combined with the (cited) spacelike support of the Pauli–Jordan kernel, this yields a canonical,
> Lorentz-boost-covariant, σ-additive Born-typicality measure on the spacelike-local field-record histories.
> The single remaining unformalized input is the support theorem `supp Δ_m ⊆ closed light cone`, isolated as
> an explicit certificate."

That is the literal Open-Problem-3b deliverable, modulo one named classical analytic fact.
