# Free-field stress-tensor formalization — discharging `hTkk` (GPT target #1, scalar half)

### ✅✅✅ STATUS UPDATE 4 (2026-06-22): Route B CORE COMPLETE + a soundness subtlety on the remaining hyps

**Proven, axiom-free (commits up to `ff200b5`):** the target `stressFluxKK = −2π·rapidityMomentum(Krep)`
(`stressFluxKK_eq_neg_rapMom`), the GR bridge to `hTkk` (`boostEnergy_eq_neg_stressFlux`), the **hard**
regularity gate `Krep` differentiability (`Krep_hasDerivAt`, the on-shell Minkowski-Fourier differentiation
under the integral), and the wrapper discharging `hkd` (`stressFluxKK_eq_neg_rapMom_cptSupp`).

**Remaining: the softer horizon-amplitude regularity** (`Integrable horizonAmp`, `Differentiable ℝ horizonAmp`,
the integrabilities) — STILL labelled hypotheses.

**⚠ SOUNDNESS SUBTLETY (must not bury — affects non-vacuity).** `Differentiable ℝ (horizonAmp)` everywhere is
a *real* constraint, not automatic. `horizonAmp = (Ioi 0).indicator(−i·Krep∘rapInv)`; at `x=0` (the bifurcation
surface) it needs the right-derivative to exist and vanish, i.e. `Krep(θ)·e^{θ} → 0` (and similarly for
derivatives) as `θ → +∞`, since `x = nullMom θ = c·e^{−θ}`.
* For merely **continuous** compactly-supported `f`, `Krep = minkowskiFourier f(massShell)` decays only
  *polynomially* in `|p| ~ e^{θ}` (Riemann–Lebesgue), so `Krep(θ)e^{θ} ↛ 0` — `Differentiable horizonAmp` FAILS.
* For **`f ∈ C_c^∞`** (smooth), `minkowskiFourier f` is Schwartz, decaying faster than `|p|^{−n} ~ e^{−nθ}` for
  ALL `n`, so `Krep(θ) = o(e^{−nθ})` ∀n — **super-exponential** decay — hence `Krep(θ)e^{θ}→0` and
  `horizonAmp` IS differentiable at `0`. So the hypotheses are jointly satisfiable (non-vacuous) **only for the
  smooth class** `f ∈ C_c^∞`, where `Krep`'s super-exponential rapidity decay holds.
* Consequence: `stressFluxKK_eq_neg_rapMom_cptSupp` is stated with `Continuous f`, but its `hAd` hypothesis is
  only satisfiable when `f` is additionally smooth. It is TRUE and NON-VACUOUS (a `C_c^∞` witness exists), but a
  rigorous non-vacuity proof (an explicit `f` discharging ALL hyps) is the honest remaining TODO — exactly the
  vacuity trap the axiom-budget check does NOT catch.

**Remaining work — REFRAMED (the infrastructure already exists).**  `QIQTH/Fock/SchwartzDecay.lean` already
provides the Fourier-decay machinery: `minkowskiFourier_eq_fourierIntegral` (= Mathlib `VectorFourier`),
`schwartz_Krep_memLp` (for `f : SchwartzMap`, `‖Krep m f θ‖ ≤ C·(cosh θ)⁻¹`, via Mathlib's
`VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le` at `k=0,n=1`), and `schwartzLocalTest`.  So the
remaining is **tractable via existing tools, not a frontier** — just laborious:
* (a) generalize `schwartz_Krep_memLp`'s `(cosh θ)⁻¹` bound to `(cosh θ)⁻ⁿ` (using `n` iterated derivatives —
  the same Mathlib lemma at higher `n`); `(cosh θ)⁻ⁿ ~ e^{−n|θ|}` gives the needed decay (e.g. `n ≥ 2` for
  `Integrable horizonAmp`, since `∫‖Krep‖·nullMom = ∫‖Krep‖·(m/√2)e^{−θ}` needs `e^{−2|θ|}` to converge at `−∞`).
* (b) from the decay: `Differentiable ℝ horizonAmp` (boundary differentiability at `x=0`) + the integrabilities.
* (c) the class reconciliation: `Krep_hasDerivAt` is proved for `Continuous f` + `HasCompactSupport f`, the decay
  for `SchwartzMap f`; both hold on `C_c^∞` (smooth + compact support) — restrict there.
* (d) a NON-VACUITY witness.  NOTE: `f = 0` already witnesses logical non-vacuity (all hyps hold trivially, the
  axiom-budget vacuity concern is technically resolved); a *nontrivial* witness needs (a)–(c).
This is genuine multi-fire but routine analysis on top of existing infrastructure; the crux (the distribution-free
Fourier computation + the Minkowski-Fourier differentiation) is done.


## Goal (one sentence)

Turn the labelled scalar input
```
hTkk : (2π/ℏ)·T_kk = (2π · ∫ θ, conj(Krep m f θ) · (d/dθ)(Krep m f) θ).im
```
into a **theorem**, by *defining* `T_kk` as the genuine null-null stress-energy flux of the free scalar
field's wedge mode across the horizon and *proving* that this flux equals `ℏ·(rapidity momentum)` of the
one-particle state. This removes the last bundled *analytic* physics input of the wedge-KMS → GR chain (the
remaining bundled input after that is the area law, GPT target #4 — a separate program).

Authority order is unchanged: **Lean > papers > GPT-5.5-pro**. Everything below ships as axiom-free,
green-building increments; budget stays 0; one commit per checkpoint.

## What already exists (verified inventory, 2026-06-21)

- One-particle space `OneP := Lp ℂ 2 (volume : Measure ℝ)` — **L²(ℝ, dθ), θ = rapidity** (`BoostOrbit.lean:36`).
- `boostUnitary t` = rapidity translation `θ ↦ θ + t`, a genuine `≃ₗᵢ[ℂ]` one-parameter group
  (`OneParticle.lean:124`, group law `boostUnitary_add_apply`). **No Stone generator yet.**
- `Krep m f θ = (1/√2)·minkowskiFourier f (massShell m θ)`, `massShell m θ = (m cosh θ, m sinh θ)`
  (`Localization.lean:194,43`); boost acts as `Krep (boostTest a f) θ = Krep f (θ+a)` (`Krep_boost`, :202).
- `Kform m f g = ∫ θ, conj(Krep m f θ)·Krep m g θ`; `Kform_im_antisymm`; **microcausality**
  `Kform_im_eq_zero_of_spacelike` (`Localization.lean:276,293`, `PauliJordan.lean:715`).
- Pauli–Jordan kernel `∫ sin(η(p_m(θ),z)) dθ` → 0 spacelike (`PauliJordan.lean:317`).
- **The analytic crux already done:** `hasDerivAt_inner_boostUnitary_imaginary` (`OneParticleBW.lean:270`):
  `d/dt⟨ξ, boostUnitary(−2πt)ξ⟩|₀ = i·(2π·Im∫ conj(f)·f')` for smooth `ξ=f.toLp`. This is the boost
  energy = rapidity momentum `⟨ξ,(−i∂_θ)ξ⟩`.
- `wedge_hBoostCharge_of_smooth` / `wedge_hbridge_of_smooth` (`OneParticleBW.lean:322`, end): both
  `WedgeKMSFlux` derivative identities now derived for smooth states **modulo exactly `hTkk`**.

**MISSING (this plan builds it):** stress tensor `T_μν`, energy density `T_00`, null component `T_kk`,
the spacetime/horizon field `φ`, the boost Noether current, the horizon flux `∫_H λ T_kk dλ`.

## Route decision

The free field is **linear**, so the one-particle sector = classical complex solutions; we never need the
second-quantized (normal-ordered) `T_μν`. Three candidate routes:

- **(A) Full 2D-spacetime Noether.** Reconstruct `φ_f(x)` on `ℝ^{1,1}`, build `T_μν=∂_μφ̄∂_νφ+c.c.−g_μν L`,
  prove `∂^μT_μν=0`, use the divergence theorem to slide the boost charge from a Cauchy slice onto the
  horizon. *Most physically complete; heaviest in Mathlib (2D Stokes / integration-by-parts, conservation).*
- **(B) Horizon null-cut (RECOMMENDED).** Work directly on the horizon `x = λ·n` (n null). The mode's
  horizon restriction is a 1-D chiral field `φ_H(λ) = ∫ Krep m f θ · exp(−i λ · k(θ)) dθ` with null momentum
  `k(θ) = (m/√2) e^{−θ}` (read off `minkowskiDot_massShell`). Then `T_kk(λ) = |∂_λ φ_H(λ)|²` is the genuine
  null-null component, and the modular Hamiltonian = horizon **dilation** generator gives
  `K = ∫_0^∞ λ·T_kk(λ) dλ`. Substituting `θ = −log(√2 λ/m)` (Mellin) turns this into the rapidity-momentum
  integral. *Avoids full Stokes; the heavy lemma is a 1-D Mellin/Plancherel identity. The cleanest honest
  path — `T_kk` is a real bilinear in `∂_λφ_H`, not a relabeling.*
- **(C) Momentum-space relabel.** Define the flux directly by its momentum kernel. *Rejected: high risk of
  circularity (if `T_kk` is defined as the rapidity momentum we prove nothing).*

**Recommendation: Route B**, with Route A kept as the rigorous-spacetime cross-check if a reviewer wants the
conservation law made explicit. Route B's `φ_H` is defined non-circularly from on-shell data (the same
`massShell` exponential that defines `Krep`), and `T_kk = |∂_λφ_H|²` is manifestly the physical null energy
density.

## Phases (Route B). New files under `QIQTH/Fock/StressTensor/`.

**Phase 0 — Boost generator as a weak derivative (foundation, ~days).**
We already have the *correlation* derivative (`hasDerivAt_inner_boostUnitary_imaginary`). Package the
"rapidity momentum" functional `P[f] := Im ∫ conj(Krep m f θ)·(d/dθ)(Krep m f) θ dθ` and its basic
properties (reality, boost-shift covariance via `Krep_boost`, finiteness on the smooth/Schwartz domain).
*Retires nothing; sets the target RHS of `hTkk` as a named object.* New: `RapidityMomentum.lean`.

**Phase 1 — Horizon restriction `φ_H` (~1 week).**
Define `horizonField m f λ := ∫ θ, Krep m f θ · Complex.exp (−Complex.I·λ·nullMom m θ) dθ`, with
`nullMom m θ := (m/√2)·Real.exp(−θ)` (justified by `minkowskiDot_massShell` on the null vector). Prove:
basic measurability/integrability on the Schwartz/Gaussian domain (lean on `gaussianLocalTest`), the
boost-intertwining `horizonField (boostTest a f) = (dilation by a) of horizonField m f`, and differentiability
`∂_λ φ_H`. New: `HorizonField.lean`. *Risk: integrability of the oscillatory θ-integral — reuse the
`abs_integral_sin_sinh_le` oscillation toolkit from `PauliJordan.lean`.*

**Phase 2 — Null stress component + horizon flux (~1 week).**
Define `Tkk m f λ := ‖∂_λ (horizonField m f) λ‖^2` (real, ≥0) and
`stressFluxKK m f := ∫ λ in Set.Ioi (0:ℝ), λ · Tkk m f λ`. Prove positivity, boost/dilation covariance, and
finiteness on the domain. This is the genuine **`T_kk` made into a defined quantity** (no longer a label).
New: `NullStressFlux.lean`.

### ✅✅ STATUS UPDATE 3 (2026-06-22): ROUTE B TARGET REACHED — `stressFluxKK = −2π·rapidityMomentum(Krep)`

`stressFluxKK_eq_neg_rapMom` (commit `ed654a1`, axiom-free): the **defined** free-field horizon null stress
flux `∫_H λ T_kk dλ` is **proven** `= −2π·rapidityMomentum(Krep m f)(Krep')` — exactly the scalar `hTkk`
asserted. The entire Fourier-analytic computation is machine-checked end-to-end: change of variables (`χ_H` is
a genuine `𝓕`), multiplication formula, conjugate **Parseval** (sesquilinear + inversion), **Fourier-derivative**,
**self-adjointness** of `−i∂_θ`, the `λ`-rescale, the chain-rule differentiation of the horizon amplitude, and
the `k↦θ` change of variables with the orientation sign. The free-field stress tensor was *never* built as an
operator — instead the null flux was **defined** (`Tkk=‖∂_λφ_H‖²`, `stressFluxKK=∫λ·Tkk`) and **proven** equal
to the boost momentum.

**Remaining for full closure (the cited regularity frontier — NOT new mathematics):** discharge the labeled
hypotheses of `stressFluxKK_eq_neg_rapMom`, all genuine on-shell regularity of the wedge mode, true for
nicely-decaying test functions: (a) `kd = Krep'` (differentiate `Krep = (1/√2)·minkowskiFourier f (massShell m θ)`);
(b) `Differentiable ℝ (horizonAmp)` (the indicator needs `Krep(+∞)=0` smooth → restrict to compactly-supported
rapidity test functions); (c) the integrability hypotheses. Then **Phase 4**: wire `stressFluxKK_eq_neg_rapMom`
into `WedgeKMSToGR` (define the chain's `T_kk` via `stressFluxKK`). The mathematical content of Route B is DONE.

### ✅ STATUS UPDATE 2 (2026-06-21, post GPT-5.5 consult): the obstacle was a DEFINITION BUG — 3b is TRACTABLE

GPT-5.5 found (and I verified independently — the counterexample is decisive) that the **half-line** definition
`stressFluxKK := ∫_{λ>0} λ·T_kk` is WRONG: it does not equal `const·rapidityMomentum`. Counterexample: `K` real,
smooth, compactly supported ⟹ `rapidityMomentum = Im∫K·K' = Im[½∫(K²)'] = 0`, but `∫_{λ>0} λ|∂_λφ_H|² > 0`. The
`1_{λ>0}` multiplier is exactly what reintroduces the `δ'`/PV distribution. Physically the half-line is the
*one-sided* modular Hamiltonian; the wedge modular flow `Δ^{it}` is the *two-sided* boost.

**CORRECTED DEFINITION — full line:** `stressFluxKK := ∫_ℝ λ·T_kk(λ) dλ`. Then (verified by hand)
`∫_ℝ λ|∂_λφ_H|² dλ = −2π · rapidityMomentum`, and this IS formalizable with current Mathlib:
* `λ|∂_λφ_H|² = conj(χ_H)·ψ_H` where `χ_H = ∂_λφ_H`, `ψ_H = λ∂_λφ_H` (single integral, NO δ').
* `χ_H = 𝓕[A]`, `ψ_H = 𝓕[B]` on the `k`-line (`k=(m/√2)e^{−θ}`, diffeo `θ↦k`), `A = −iK∘θ(k)`, `B = K'∘θ(k)/k = −iA'`.
* `∫_ℝ conj(𝓕A)·𝓕B = 2π ∫ conj(A)·B` (Mathlib `integral_sesq_fourierIntegral_eq_neg_flip` / Parseval, integrability-only).
* change of vars back: `∫conj(A)B = i∫_ℝ conj(K)K'dθ`, and `∫conj(K)K' = i·rapidityMomentum` (self-adjointness) ⟹ `−2π·rapidityMomentum`.
* **Hypothesis class:** `K ∈ C_c^∞(ℝ)` (or weighted exp-decay so `A,B ∈ L¹(dk)` — Schwartz-in-θ alone is NOT enough,
  since `∫|A|dk = ∫ k|K|dθ` needs decay as `θ→−∞`).

**REVISED Phase 3 plan (tractable, ~2–3 fires):**
- 3a′ (redo): redefine `stressFluxKK` with `∫_ℝ` (was `∫_{Ioi 0}`); re-prove dilation-invariance (full-line scaling — even simpler).
- 3b-i: the `k`-line change of variables `χ_H = 𝓕[A]`, `ψ_H = 𝓕[B]` (+ the IBP `λχ_H = ψ_H`).
- 3b-ii: apply the sesquilinear Fourier identity → `∫conj(A)B`; change vars back → `−2π·rapidityMomentum`. THE THEOREM.
- Phase 4: discharge `hTkk` (define the chain `T_kk := −(1/2π)·stressFluxKK` up to the ℏ,2π constants) + rewire.

Risk now concentrated in the Fourier change-of-variables + matching Mathlib's `Real.fourierIntegral` 2π convention —
real work but standard, NOT a frontier. (Original alarmist "cited frontier" note below is SUPERSEDED.)

### ~~⚠ STATUS UPDATE (2026-06-21): Phase 3 reached — 3a DONE, 3b is the CITED FRONTIER~~ (SUPERSEDED by Update 2 above)

Phases 0–2 + 3a are **complete and axiom-free** (commits 7db57c6, 1f3f181, d35881a, 245a5f0): the entire
definitional layer (`rapidityMomentum`, `horizonField`, `horizonFieldDeriv`, `Tkk`, `stressFluxKK`), all
boost↔dilation covariances, and the **dilation-invariance** of the flux `stressFluxKK_boostTest`.

**Phase 3b — `stressFluxKK = π · rapidityMomentum` — is BLOCKED on missing Mathlib analysis infrastructure**
(genuine assessment, both routes tried on paper):
* **Direct route.** `∫_{λ>0} λ|∂_λφ_H|²dλ` Parseval-expands to `∫∫ K(θ)K̄(θ') k(θ)k(θ') · [∫_0^∞ λe^{−iλ(k(θ)−k(θ'))}dλ] dθdθ'`.
  The inner kernel converges only as a distribution: `∫_0^∞ λe^{−iλΔ}dλ = iπδ'(Δ) + (PV part)`. The `δ'(Δ)` is
  exactly what yields the momentum coupling `∫K̄·K'` — but Mathlib has **no tempered distributions / no `δ'`**.
* **Regularize-then-limit route (c).** The regularized kernel `∫_0^∞ λe^{−(ε+iΔ)λ}dλ = (ε+iΔ)^{−2}` IS buildable
  (Mathlib's `integral_Ioi_of_hasDerivAt_of_tendsto` is ℂ-valued; antiderivative `−(t/c+1/c²)e^{−ct}`). But the
  `ε→0` limit `(ε+iΔ)^{−2} → δ'`-distribution inside the double `θ`-integral is the SAME distributional step —
  the limit kernel is not an L¹ function, so dominated convergence does not apply; identifying the boundary `δ'`
  is precisely the missing distribution theory.
* **IBP + Parseval route.** `λ∂_λφ_H = 𝓕[K']` (one IBP in θ, since `λk e^{−iλk} = −i∂_θ e^{−iλk}`) reduces it to a
  half-line Fourier–Parseval pairing. But Mathlib has **no line Fourier–Plancherel isometry** (only the weak
  sesquilinear `integral_sesq_fourierIntegral_eq_neg_flip`, integrability-only) and **no Hardy/half-line
  structure** to handle the `∫_0^∞` vs `∫_ℝ` and the on-shell change of variables `θ ↔ k`.

**Conclusion.** `stressFluxKK = π·rapidityMomentum` is a research-grade analytic formalization (it needs either
minimal tempered-distribution support, OR line Fourier–Plancherel + full-line IBP + Hardy structure) — a
multi-week-to-multi-month Mathlib-grade build, NOT a fire-sized increment. Per the honest-scale note below, the
disciplined outcome is to **declare Phase 3a the fully-rigorous milestone and Phase 3b the cited frontier**
(exactly as Araki/Type-III are cited), unless the user authorizes the deliberate infrastructure campaign.
**Decision for the user:** (A) authorize the multi-week infra build, or (B) accept 3a + cite 3b. (`CronDelete`
the loop to pause autonomous fires while deciding.)

---

**Phase 3 — Mellin/Plancherel identity = THE THEOREM (~1–2 weeks, the crux).**
Prove `stressFluxKK_eq_rapidityMomentum`:
```
stressFluxKK m f = (Real.pi) · P[f]      -- (constant fixed by the dλ↔dθ Jacobian; pin precisely)
```
i.e. the horizon dilation charge `∫₀^∞ λ T_kk dλ` equals the rapidity momentum. Route: substitute
`λ = (m/√2)⁻¹ e^{θ'}`/Mellin, apply Plancherel for the `θ ↔ log λ` transform, reduce both sides to the same
`∫ conj(Krep)·(∂_θ Krep)` integral. *Main Mathlib risk: a Plancherel/Mellin step; fallback is a direct
change-of-variables + Fubini on the explicit Gaussian-class integrals (`gaussianLocalTest`), avoiding a
general Mellin-Plancherel theorem.* New: `HorizonPlancherel.lean`.

**Phase 4 — Discharge `hTkk` and rewire the chain (~days). RETIRES THE LABEL.**
With `stressFluxKK` defined and Phase-3 proven, set `T_kk := (ℏ/(2π))·(2π/ℏ)…` — concretely, define the GR
chain's stress scalar to be `stressFluxKK` (up to the fixed ℏ, 2π constants) and prove `hTkk` as a corollary
of `stressFluxKK_eq_rapidityMomentum`. Provide `wedge_hBoostCharge_of_smooth_DERIVED` (no `hTkk` hypothesis —
it now holds by the theorem) and thread it into a `WedgeKMSFlux_complete` constructor so the **boost-charge
slot is fully derived, no scalar label left**. Update `AxiomAudit.lean`, keep budget 0.
Edits: `OneParticleBW.lean`, `WedgeKMSToGR.lean`, `AxiomAudit.lean`.

## Honest scale & risk

- **~4–6 weeks**, 4 new files. Smaller than the hUniq/Type-III campaign (no operator algebra), but Phase 3
  (Mellin-Plancherel) is a genuine analytic target and Phase 1 integrability is fiddly.
- **Value lands incrementally:** Phase 2 alone gives a *defined* free-field horizon stress flux (independently
  meaningful); Phase 4 is the payoff (`hTkk` becomes a theorem, the boost-charge=stress-flux identity is then
  fully derived from the field, closing GPT target #1's scalar half).
- **Fallback discipline (as with Araki/Type-III):** if Phase 3's general Plancherel stalls, restrict to the
  `gaussianLocalTest` class and prove the identity by explicit Gaussian integration — still a genuine,
  non-circular discharge for a concrete dense family of wedge states; document the class restriction honestly.
- **What this does NOT close:** the area law `δS=ηδA` (GPT #4 — the holographic/H2 input). After this plan the
  honest GR claim is "QIQT capacity + Klein positivity + **the now-derived free-field stress flux** + Clausius
  + conservation/regularity ⟹ Einstein eq", with the area law the single remaining bundled physics input.

## Verification (per phase)

- `~/.elan/bin/lake build QIQTH.Fock.StressTensor.<Module>` green; full `QIQTH` green.
- every new theorem `#print axioms` → only `propext, Classical.choice, Quot.sound`.
- `bash lean/mathlib/scripts/axiom_budget_check.sh` → `raw axiom count: 0 (budget 0)`.
- Phase 3 cross-checked against the physics statement (horizon dilation charge = boost generator) and the
  constant pinned by an independent Gaussian test case.
- One commit per phase, `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`.
