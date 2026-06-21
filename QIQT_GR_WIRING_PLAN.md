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

## Verification discipline (both tasks)
- Per Lean increment: `lake build` green; every new theorem `#print axioms` shows only
  `[propext, Classical.choice, Quot.sound]`; `scripts/axiom_budget_check.sh` → `budget 0`; commit on `main`
  ending `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`.
- Total honesty both directions: state plainly what becomes derived vs. what remains a labelled physical input.
- Order: Task 1 (wiring) first (concrete, unblocks the free-field `hFlux` being self-contained), then Task 2 (audit).
