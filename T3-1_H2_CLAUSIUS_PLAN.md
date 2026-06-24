# T3-1 — the H2 / Clausius crux: discharge `hbound`/`hsat`/`hDnn`/`hD0`

**Status:** Stage 1 ✅ done (the finite-model witness). **Track:** GR. **Goal:** turn the four Clausius/area-law
hypotheses of the GR capstone from labelled inputs into theorems of QIQT-H's axiom-free finite-entropy core.

### Progress log
- **Stage 1 ✅** (`clausius_package_from_finite_model`, `QIQTH/ClausiusFiniteWitness.lean`) — proves all four
  premises (`hbound`/`hsat`/`hDnn`/`hD0`) hold for the constructed finite-record model `Sf=Shannon(p t)`,
  `KE=Sf+KL(p t‖p 0)`, `A=Acap` with `η·Acap=log|R|`, via `shannon_le_log_card` / `shannon_uniform_eq_log_card`
  / `KL_classical_nonneg`. **The entropy bound/saturation/positivity are now theorems, not assumptions.**
  Wired into `QIQTH.lean` + `AxiomAudit`. Axiom-free `[propext, Classical.choice, Quot.sound]`, full budget 0.

## 0. The exact target

`qiqt_gr_freefield_geom` (and the whole ladder) takes abstract functionals `Sf KE A : Point 4 → (Fin 4 → ℝ)
→ ℝ → ℝ` with four labelled thermodynamic premises (on the null cone, per generator `(x,v)`):

- `hbound : ∀ᶠ t in 𝓝 0, Sf t ≤ η·A t`  (capacity **bound** S ≤ η·A)
- `hsat   : Sf 0 = η·A 0`                  (**saturation** at the equilibrium reference)
- `hDnn   : ∀ t, 0 ≤ KE t − Sf t`          (relative-entropy **positivity**)
- `hD0    : KE 0 − Sf 0 = 0`               (positivity is **tight** at the reference)

`differential_area_law_of_relEntropy` (`DifferentialAreaLaw.lean:82`) already turns these (+ `hS`/`hK`/`hA`)
into the modular relation `δS = η δA = δ⟨K⟩` — so these four are the *entire* thermodynamic surface of the GR
derivation. They are the "H2 crux."

## 1. What the finite core already proves (axiom-free, build on)

- `QIQTH.RecordContract.shannon_le_log_card (p) (hp_nn) (h1) : Shannon univ p ≤ log (card ι)` — Gibbs/Jensen.
- `QIQTH.RecordContract.shannon_uniform_eq_log_card [Nonempty ι] : Shannon univ (fun _ => (card ι)⁻¹) = log (card ι)`.
- `QIQTH.RelEntPositivity.KL_classical_nonneg (s) (p q) (hp_nn) (hq_pos) (hp_sum) (hq_sum) : 0 ≤ KL s p q`,
  with `KL s p q := ∑ i∈s, p i · log (p i / q i)`.
- `QIQTH.BranchLedger.Shannon s p := −∑ i∈s, p i · log (p i)`.

**Gap:** these are facts about a *finite distribution*; nothing lifts them to the spacetime functionals
`Sf`/`KE`/`A`. So the four premises are genuinely labelled. T3-1 = build that bridge.

## 2. The construction (the bridge)

Per generator, take a finite record set `R` (`Fintype`, `Nonempty`) and a deformation-dependent law
`p : ℝ → R → ℝ` (a probability distribution for each `t`), uniform at the reference `p 0 = (card R)⁻¹`. Define

- `Sf t := Shannon univ (p t)`              (record entropy)
- `KE t := Sf t + KL univ (p t) (p 0)`      (modular energy = entropy + relative entropy: the free-energy split)
- `A  t := Acap`, with the **capacity identification** `η·Acap = log (card R)`  (the FQ area = capacity postulate)

Then the four premises are **theorems**:
- `hbound`: `Shannon (p t) ≤ log(card R) = η·Acap` ∀ t — `shannon_le_log_card` + the identification.
- `hsat`:   `Shannon (p 0) = Shannon(uniform) = log(card R) = η·Acap` — `shannon_uniform_eq_log_card`.
- `hDnn`:   `KE t − Sf t = KL (p t) (p 0) ≥ 0` — `KL_classical_nonneg` (q = uniform > 0).
- `hD0`:    `KE 0 − Sf 0 = KL (p 0) (p 0) = 0` — each term `p·log(p/p) = p·log 1 = 0`.

## 3. Stages

### Stage 1 — `clausius_package_from_finite_model` *(standalone witness; achievable now)*
New file `QIQTH/ClausiusFiniteWitness.lean`. Prove: for any finite `R`, deformation law `p` (nonneg, sums to 1,
uniform at 0) and capacity identification `η·Acap = log(card R)`, the constructed `(Sf, KE, A)` satisfy
`hbound ∧ hsat ∧ hDnn ∧ hD0`. **This proves the four premises are theorems of the finite QIQT entropy model +
the area-capacity postulate — not independent physical assumptions.** Axiom-free. **Risk: low.**
**✅ DONE** — `clausius_package_from_finite_model`, axiom-free, full budget 0.

### Stage 2 — the honest obstruction to capstone-wiring *(documented, the real frontier)*
Wiring Stage 1 into `qiqt_gr_freefield_geom` does **not** go through with constant `A`, and this is the genuine
H2/continuum content, not a gap in effort:
- The geom capstone needs `A'(0) = ad = −∑W∂θ = R_kk ≠ 0` (the focusing); a **constant** capacity `A` forces
  `ad = 0`. So `A(t)` must be the *varying geometric area*.
- But `A(t) = η⁻¹·log(card R_t)` with an **integer** cardinality cannot track a *continuous* area `A(t)`.
  Reconciling the discrete record-capacity with the continuum area is exactly the **continuum capacity /
  FQ-at-the-horizon** frontier (the `Q_R = A/4ℓ_P²` postulate made dynamical).
So the differential wiring is the cited continuum frontier. Stage 1's witness is the honest, real increment:
the entropy *inequalities* are finite-core theorems; what stays labelled is the **dynamical area-capacity
identification** (one clean postulate) + the realization derivatives `hS`/`hK`/`hA` (Gap-2 localization).

## 4. Verification (per stage)
- `~/.elan/bin/lake build QIQTH.ClausiusFiniteWitness` green; `#print axioms` = standard 3; budget 0.
- One commit per stage, `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`.

## 5. Honest outcome statement
T3-1 cracks the H2 crux into: **(proved)** the Shannon/Jensen/Klein entropy inequalities `hbound`/`hsat`/`hDnn`/
`hD0` for a constructed finite model; **(irreducible)** the dynamical area = capacity postulate `η·A = log|R|`
(the FQ holographic input) and the thermodynamic realization `hS`/`hK`/`hA` (the same Gap-2 localization as
T3-3). The bound/saturation/positivity are no longer assumptions — only the holographic identification is.
