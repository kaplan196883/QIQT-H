# Plan — Wire Route B + Audit `StripKMSrvd` (closing the QIQT→GR modular/flux loose ends)

**Created 2026-06-22.** Follow-up to: Route B fully closed (`STRESS_TENSOR_FORMALIZATION_PLAN.md` STATUS UPDATE 5)
and the Type-III/RvD modular uniqueness derived axiom-free (`oneParticleBW_complete`, RvD Thm 3.8).

## Context (current QIQT→GR state)

`qiqt_gr_from_wedge_kms_complete` (`QIQTH/WedgeKMSToGR.lean`) derives the Einstein field equations,
axiom-free (`[propext, Classical.choice, Quot.sound]` only), conditional on a thin physics surface.

- **DERIVED axiom-free:** QIQT-H entropy content → area law; all geometry (Bianchi, `∇·G=0`,
  null-cone→tensor, const `Λ`); **Type-III/Tomita–Takesaki modular uniqueness** (`oneParticleBW_complete`
  = RvD Thm 3.8, with `h1`/`hdense` both now theorems); the second-quantized modular flow
  (`SecondQuantModularFlow.lean`); **Route B** = the free-field `T_kk` stress-flux scalar
  (`boostEnergy_eq_neg_stressFlux_schwartz_closed`).
- **Genuine remaining inputs:** `StripKMSrvd` (boost wedge-KMS); `hFocus` (Raychaudhuri area↔θ);
  Lorentzian structural facts.

**Two loose ends this plan closes:**
1. Route B is NOT yet wired into the wedge→GR chain — `wedge_hBoostCharge_of_smooth`
   (`QIQTH/Fock/OneParticleBW.lean:322`) still carries `hTkk` as a *hypothesis*. `grep` confirms
   `stressFluxKK`/`boostEnergy` are unreferenced in `OneParticleBW`/`WedgeKMSToGR`/`QiqtToGR`.
2. `StripKMSrvd`'s status for the concrete free field is unaudited (all theorems thread it as a hypothesis).

---

## Task 1 — Wire Route B → `wedge_hBoostCharge_of_smooth`

**Goal.** A theorem `wedge_hBoostCharge_of_schwartz` that discharges the `hTkk` hypothesis using Route B, for
the free-field wedge mode `f = Krep m ⇑g` (`g : SchwartzMap V ℂ`, `m > 0`), `f' = deriv (Krep m ⇑g)`, and
`Tkk := −(ℏ/2π)·stressFluxKK m ⇑g`. Then `2π/ℏ·Tkk = −stressFluxKK = (2π·∫conj(Krep)·Krep').im` is exactly
`boostEnergy_eq_neg_stressFlux_schwartz_closed`.

**`wedge_hBoostCharge_of_smooth` hypotheses to supply** (for `f = Krep m ⇑g`, `f' = deriv(Krep)`):
- `hf2 : MemLp f 2` — `schwartz_Krep_memLp` (have).
- `hf_int : Integrable f` — **(1b, may be new)** `∫‖Krep θ‖ dθ < ∞`: dominate by `C·cosh⁻²` (`schwartz_Krep_decay_sq`)
  and `cosh⁻²` is integrable over ℝ. Needs `Integrable (fun θ => (cosh θ)⁻²)` (bound `cosh⁻² ≤ 4·e^{−2|θ|}`,
  or `≤ 4·e^{−|θ|}`, + an `exp(−|·|)`-integrability lemma — small sub-task).
- `hF0_int : Integrable (conj f · f)` — `= ‖Krep‖²` integrable, from `MemLp f 2` (or `horizonAmp_sq`-style).
- `hf_meas : AEStronglyMeasurable f` — from `Krep` continuity / `MemLp.1`.
- `hfd : ∀x, HasDerivAt f (f' x) x` — `schwartz_Krep_hasDerivAt …` (have, with `f' = deriv` via `.deriv`).
- `hf'_meas : AEStronglyMeasurable f'` — `measurable_deriv` (have).
- `B, hB : ∀x ‖f' x‖ ≤ B` — **(1a)** from `Krep_deriv_norm_le` (`‖Krep'θ‖ ≤ C·cosh⁻¹θ ≤ C`, since `cosh⁻¹ ≤ 1`); `B = C`.

**Steps.**
- 1a. `Krep_deriv_bounded` : `∃ B, ∀θ, ‖deriv(Krep m ⇑g) θ‖ ≤ B` (from `Krep_deriv_norm_le` + `cosh⁻¹ ≤ 1`).
- 1b. `Krep_integrable` : `Integrable (Krep m ⇑g)` over θ (decay `cosh⁻²` + `cosh⁻²` integrable). If the
      `cosh⁻²`-integrability lemma is non-trivial, prove `integrable_inv_cosh_sq` first.
- 1c. Assemble `hf_meas`, `hF0_int` from existing `MemLp`/continuity facts.
- 1d. `wedge_hBoostCharge_of_schwartz` : instantiate `wedge_hBoostCharge_of_smooth` with the above +
      `Tkk := −(ℏ/2π)·stressFluxKK m ⇑g`; discharge `hTkk` by `boostEnergy_eq_neg_stressFlux_schwartz_closed`.
      (May need the `f`-over-θ vs `Krep`-over-θ identification — should be direct.)
- Verify: `lake build` green, `#print axioms` standard-only, budget 0, commit on `main`.

**Risks.** `cosh⁻²` integrability over ℝ (the `exp(−|θ|)` issue avoided in Route B's x-side route — may need a
small lemma). Possible convention mismatch between `wedge_hBoostCharge`'s `f` and `Krep`.

**Placement.** New file `QIQTH/Fock/StressTensor/WedgeBoostWiring.lean` (imports `OneParticleBW` +
`L2Plancherel`), so the heavy StressTensor imports stay out of `OneParticleBW`.

---

## Task 2 — Audit `StripKMSrvd` for the free field

**Goal.** Determine whether `StripKMSrvd V 𝒦` (RvD Def 3.4 wedge-KMS) is constructively available for the
concrete free-field boost, or is the single irreducible labelled physical input.

**Steps (read/audit; Lean only if a short derivation surfaces).**
- 2a. Find the free-field `StandardSubspace 𝒦` (wedge subspace) and the free-field boost group `V`
      (`boostUnitary`?) in `Fock/OneParticleBW`, `SecondQuantModularFlow`, `RelativeModularFlow`,
      `ContinuumLambdaField`.
- 2b. Search for any theorem proving `StripKMSrvd` for a concrete `(V, 𝒦)` (vs. always a hypothesis).
- 2c. Check whether `SecondQuantModularFlow`/RvD gives the modular `σ_t` KMS that *implies* `StripKMSrvd`
      for the boost (i.e. is the boost = the modular flow by construction, making KMS automatic?).
- 2d. **Report** one of: (i) `StripKMSrvd` is proven for the free field (modular side input-free);
      (ii) derivable from the existing construction — name the missing lemma(s) and difficulty;
      (iii) irreducible labelled input = the physical KMS/thermality of the vacuum w.r.t. the boost
      (BW/Reeh–Schlieder content) — the honest cited surface.

**Deliverable.** A precise written verdict (in this file + memory), and — if (i)/(ii) is cheap — the lemma.

---

---

## STATUS UPDATE (2026-06-22)

### Task 1 — DONE ✅ (commit `da1cd3f`)

`wedge_boostCharge_eq_neg_stressFlux` (`QIQTH/Fock/StressTensor/WedgeBoostWiring.lean`):
for any Schwartz `g`, `m > 0`,
```
HasDerivAt (fun t => ⟪Krep, boostUnitary(−2π t) Krep⟫) (i·(−stressFluxKK m g)) 0
```
— the boost/modular-energy derivative of the free-field wedge mode **equals** `i·(−stressFluxKK m g)`,
**with no `hTkk` hypothesis**. The labelled scalar `hTkk` of `hasDerivAt_inner_boostUnitary_imaginary`
(`Tkk := −(ℏ/2π)·stressFluxKK`) is discharged via Route B
(`boostEnergy_eq_neg_stressFlux_schwartz_closed`). All wedge-mode regularity supplied here:
- `Krep_integrable` (`∫‖Krep‖ < ∞` — dominated by `cosh⁻²`, via new `integrable_exp_neg_abs` +
  `integrable_inv_cosh_sq`);
- `Krep_deriv_bounded` (`‖Krep'‖ ≤ C·cosh⁻¹ ≤ C`, from `Krep_deriv_norm_le`);
- `schwartz_Krep_memLp`, `(schwartz_Krep_memLp …).star.integrable_mul …` (the `conj(Krep)·Krep ∈ L¹`
  Hölder fact), `Krep_continuous`, `schwartz_Krep_hasDerivAt`.

Axiom-free (`[propext, Classical.choice, Quot.sound]`), budget 0, no `sorry`. Imported into `QIQTH.lean`;
audit entry added to `AxiomAudit.lean`. **The last labelled physics scalar of the localization slot is now an
unconditional theorem for the free field.**

### Task 2 — VERDICT (CORRECTED 2026-06-22 after GPT-5.5-pro review)

⚠ **My first verdict below ("(iii) irreducible") was an OVERCLAIM / sandbagging.** GPT-5.5-pro review
(reproduced after) shows `StripKMSrvd` for the free-field boost is **NOT irreducible** — it is a
**dischargeable theorem** via an explicit, non-circular rapidity Hardy-space proof. And `hFocus`, `hDnn`,
`conserv` are mostly **mathematical theorems**, not physical citations. The ONE genuinely irreducible
*physical* input is the **Clausius/area-saturation law** (`hbound`, `hsat`). See "CORRECTED VERDICT" below;
the original-verdict text is retained (struck) for the record.

#### Original (incorrect) verdict — retained for honesty

~~(iii) irreducible labelled input.~~ The points below about *non-vacuity* and *what is consumed vs derived*
remain correct; only the "irreducible / can't be discharged" conclusion was wrong.

**`StripKMSrvd` for the concrete free-field boost is the single irreducible labelled physical input** of the
QIQT→GR chain's modular side — the Bisognano–Wichmann / Reeh–Schlieder thermality of the vacuum w.r.t. the
boost. Precisely:

1. **Never discharged for the boost.** Every theorem consuming it threads `hKMS : StripKMSrvd V 𝒦` as a
   *hypothesis* about the candidate group `V`. `oneParticleBW_wedge_complete` (`OneParticleBW.lean:870`)
   takes `hVboost : V = boostUnitary(−2π·)` + `hKMS : StripKMSrvd V 𝒦_W` and **derives** everything else —
   invariance (`boostUnitary_mapsTo_wedgeSubspace`, geometric/proven), strong continuity, group law,
   isometry — concluding the BW identification `modUnitary 𝒦_W t = boostUnitary(−2π t)`. No theorem proves
   `StripKMSrvd boostUnitary 𝒦_W`.

2. **Proven satisfiable / NON-VACUOUS (machine-checked).** `modCorr_halfStripReal` (`KMSCorrelation.lean:647`)
   proves the **modular flow `Δ^{it}` itself** satisfies RvD Prop 3.5's half-strip KMS reality form —
   *geometrically*, axiom-free, no circularity (the device vector is literally `Δ^{iz}ξ`, and
   `Δ^{1/2}ξ = Jξ` on `𝒦` via `modCorr_midline_real`). Contrast `stripKMS_trivial` (`OneParticleBW.lean:543`),
   which exposed the *old* `StripKMS` as vacuously true: `StripKMSrvd` (with `DiffContOnCl` + uniform bound +
   the corrected RvD Def 3.4 plain-flip edge) is a **genuine, satisfiable constraint**.

3. **Why irreducible for the boost.** `boostUnitary` is the *geometric* rapidity-translation `θ ↦ θ + t`
   (`OneParticle.boostUnitary = boostFlow.unitary`, `boostFlow := translationFlow`), defined independently of
   the modular `R`-operator. Proving `StripKMSrvd boostUnitary 𝒦_W` IS proving the free-field vacuum is KMS
   (thermal) w.r.t. the geometric boost — the **Bisognano–Wichmann theorem itself**. Doing so from within is
   either *circular* (it would go via `boost = Δ`, which is the conclusion) or requires the explicit
   free-field rapidity two-point analyticity computation (the BW theorem done by hand on `L²(ℝ,dθ)`). The
   latter is route **(ii) — derivable in principle but substantial and not done**: the missing lemma is the
   explicit characterization of `𝒦_W` as the RvD/Hardy real subspace + the strip-analyticity of the rapidity
   cross-correlation `∫conj(η(θ))ξ(θ+t)dθ` for `ξ,η ∈ 𝒦_W`. RvD/BGL themselves take this as their starting
   datum.

**Honest boundary.** The QIQT→GR modular chain rests on exactly one clearly-citable AQFT input:
*the free-field vacuum's boost-KMS thermality* (`StripKMSrvd boostUnitary 𝒦_W` = Bisognano–Wichmann), its
non-vacuity machine-verified. Everything downstream — RvD Thm 3.8 uniqueness (`oneParticleBW_complete`),
the BW identification, the second-quantized modular flow, Route B's stress flux, and now (Task 1) the
boost-charge = stress-flux scalar — is **derived, axiom-free**.

#### CORRECTED VERDICT (GPT-5.5-pro review, 2026-06-22)

**`StripKMSrvd(boostUnitary, 𝒦_W)` is dischargeable for the free 1+1 scalar — NOT irreducible.** The proof is
non-circular and explicit (route b):

- One-particle space `L²(ℝ,dθ)`, `p(θ)=m(coshθ,sinhθ)`. **Key identity `p(θ+iπ) = −p(θ)`.**
- A wedge-supported real test function `f` has rapidity wavefunction `ψ_f(θ)=c·f̂(p(θ))` in the **Hardy space
  `H²(S_π)`** on the strip `0<Im ζ<π` (damping from `Im p(θ+iλ)·x ≤ 0` for `x∈W_R`, using ONLY wedge support
  + energy positivity), with boundary relation `ψ_f(θ+iπ)=conj(ψ_f(θ))` (real `f`).
- The KMS function `F(z)=∫ H^#(θ+πz)·Ξ(θ−πz)dθ` has top edge `⟪η,V_t ξ⟫`, bottom edge `⟪V_t ξ,η⟫` (the iπ-flip
  IS the conjugation), bounded by Cauchy–Schwarz. **It never uses Δ/J/boost=Δ.**
- Honest logic: `supp f⊂W ⟹ ψ_f∈H²(S_π) ⟹ boost-KMS ⟹[RvD uniq, DONE] boost=Δ`. The *circular* route
  (`boost=Δ ⟹ KMS`) is the one we avoid.
- This is the EASY free-field one-particle Hardy computation, **not** equivalent to full AQFT BW (that was
  also an overstatement). Effort: a few pages on paper; Lean multi-week IF the Schwartz/Fourier/holomorphic-
  parameter-integration infra exists, else 1–3 months. (Caveat: `StripKMSrvd` gives the modular GROUP only;
  full 1-particle BW also identifies `J` — the project may not need it.)

**GR side — math mislabeled as physics.** `hFocus` (Raychaudhuri) is differential geometry, a theorem given the
local-horizon setup — not a citation. `hDnn`/`hD0` (relative-entropy positivity) is a mathematical theorem
(Klein/Araki), heavy but not a new axiom. `conserv` (∇·T=0) is derivable for the explicit KG stress tensor.

**The ONE genuinely irreducible physical input** is the **Clausius/area-law package** (`hbound`, `hsat`):
`δQ=TδS`, `δS=ηδA` + saturation. Free-field BW gives the Unruh temperature but NOT the universal entropy
density `η` / Newton's `G`, so this can be repackaged into one clean postulate but not eliminated. (A fully
hypothesis-free GR is not an honest target — Jacobson's derivation is inherently conditional.)

**Minimal honest input set & next discharge targets**: (1) route-b Hardy proof of boost-KMS [retires `hKMS`];
(2) `hFocus`/Raychaudhuri [geometry theorem]; (3) relative-entropy positivity [math]; leaving the
Clausius/area-saturation law as the single labelled physical postulate.

---

## Verification discipline (both tasks)
- Per Lean increment: `lake build` green; every new theorem `#print axioms` shows only
  `[propext, Classical.choice, Quot.sound]`; `scripts/axiom_budget_check.sh` → `budget 0`; commit on `main`
  ending `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`.
- Total honesty both directions: state plainly what becomes derived vs. what remains a labelled physical input.
- Order: Task 1 (wiring) first (concrete, unblocks the free-field `hFlux` being self-contained), then Task 2 (audit).
