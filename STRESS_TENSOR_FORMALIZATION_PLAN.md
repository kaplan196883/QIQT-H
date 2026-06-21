# Free-field stress-tensor formalization — discharging `hTkk` (GPT target #1, scalar half)

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

### ⚠ STATUS UPDATE (2026-06-21): Phase 3 reached — 3a DONE, 3b is the CITED FRONTIER

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
