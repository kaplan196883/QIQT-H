# Axiom contract audit (QIQT-H Lean development)

**Date:** 2026-06 · **Trigger:** GPT-5.5-pro adversarial review (#3 of the "do all 1/2/3" pass).

Two soundness bugs in this project (`IsTensorMultiplicative := ∀ρσ,True` feeding `step3`; the
unsatisfiable `∀-Dd2` flagship hypothesis) shared one failure mode: a **vacuous / too-permissive
predicate** that the `#print axioms` budget check (`scripts/axiom_budget_check.sh`) cannot see.
This document audits the **33 remaining axioms** (down from 35 — see the deletion banner) for that family and for **circularity** (a
"bridge" axiom whose conclusion is essentially the Born claim).

**Tooling:** `scripts/vacuity_lint.sh` greps for vacuous Prop bodies (`:= True`, `↦ True`,
`→ True`, `∀…,True`, `∃…,True`). It is informational; each hit is triaged below.

The detector for the *soundness* family is not the count — it is (a) attempting to discharge the
axiom by proof, and (b) the positive/negative model witnesses in `QIQTH/GoldsteinStruyveModels.lean`.

> **RESOLVED (2026-06-06).** Both content-free placeholder axioms below have been **DELETED**:
> `BornTypicality.LLN_typicality_axiom` (the whole `LLN`-placeholder, headline #1) and
> `TypicalityMackeyGleason.mackey_gleason_to_trace_density` (the entire `TypicalityMackeyGleason`
> module, headline #2). Both are superseded by axiom-free finite results (`BornTypicalityFinite` /
> `EffectGleason` and the finite Born-representation thread — see `FINITE_BORN_REPRESENTATION.md`).
> Axiom count **35 → 33**. The continuum LLN / Bunce–Wright generalizations remain open (they were
> never these placeholders). Headlines #1/#2 below are retained as the historical record.

---

## Triage of the vacuous-body sites the linter flags

After the deletion (2026-06-06) only ONE vacuous-body site remains; the three in the deleted modules
(`BornTypicality.lean` `∃_N,True`; `TypicalityMackeyGleason.lean` `HasTraceDensityForm`/`IsNormal`/
`IsNoncontextual := True`) are gone.

| Site | Kind | Verdict |
|------|------|---------|
| `LorentzWitness.lean:180` `le _ _ := True` | trivial preorder **instance field** | harmless (a deliberately-trivial order witness, not an axiom hypothesis) |

No site matches the dangerous pattern **vacuous HYPOTHESIS → concretely-falsifiable CONCLUSION**
(that was the `step3`/`IsTensorMultiplicative` bug, now fixed). So **no new soundness hole** is
present. But two *content-free* conclusions overstate what is proved:

### ✅ Headline finding #1 — RESOLVED (axiom deleted 2026-06-06; historical record below)

`BornTypicality.LLN_typicality_axiom` is meant to deliver "μ-typical IC sequences have empirical
frequencies converging to the Born weights." Its **conclusion is literally `∀ ε>0, ∀ k, ∃ _N, True`**
— i.e. `True`. So every downstream claim that "frequencies converge to Born" currently rests on a
**vacuous** axiom: it asserts nothing. This is honest as a flagged placeholder, but it must NOT be
cited as "Born derived as a frequency." Giving it real content (a genuine LLN in the AQFT/IC
framework) is open, multi-week work.

### ✅ Headline finding #2 — RESOLVED (axiom + module deleted 2026-06-06; historical record below)

`TypicalityMackeyGleason.HasTraceDensityForm := True`, so `mackey_gleason_to_trace_density`
(`… → HasTraceDensityForm w`) and the "theorem" `qiqth_typicality_mackey_gleason` prove a
`True` conclusion. Sound, but no content. The genuine trace-density result exists only at the
**finite** level (`EffectGleason.finite_effect_gleason`), which is axiom-free; the continuum
Type-II Bunce–Wright statement here is a named placeholder.

---

## The 33 axioms by cluster

Most are one of: **(T)** opaque-type declarations (`axiom Foo : Type`) — harmless, just abstract
carriers; **(F)** opaque function symbols on those types; **(S)** genuine standard theorems
axiomatized because the operator-algebra infrastructure is absent from Mathlib.

- **ArakiInterface.lean (11):** `NormalState`,`NormalUCPChannel` (T); `IsFaithful`,`mixture`,
  `AkRelEnt`,`NormalUCPChannel.pull` (F); `Akre_nonneg`,`donald_araki`,`dpi_ucp`,`IHol_le_Shannon`,
  `AkRelEnt_eq_zero_iff` (S — Araki relative entropy, DPI for UCP channels, Holevo≤Shannon). Genuine
  statements; consistent (the finite matrix model satisfies them). No vacuity.
- **DPI.lean (4):** `Channel`,`Channel.pull`,`restrict` (T/F); `DPI_inequality` (S). Standard data
  processing. No vacuity.
- **Donald.lean (8):** `State`,`D`,`H`,`crossEnt`,`mixture` (T/F); `D_eq_crossEnt_sub_H`,
  `crossEnt_mixture`,`crossEnt_self` (S — Donald's identity). No vacuity.
- **EntropyBridge.lean (6):** `RState`,`refState` (T/F); `Sren_CPW`,`chi_R`,`dK_modular` (F);
  `bridge_identity` (S). `bridge_identity` relates three otherwise-free entropy functions
  (`χ_R = ΔK − (S_ren − S_ren(σ))`); it is **not** circular w.r.t. Born (it does not mention or
  assume the Born measure), but its content is thin — it constrains free symbols.
- **RelEntPositivity.lean (2):** `D_nonneg`,`D_eq_zero_iff_eq` (S — positivity / faithfulness of
  relative entropy). No vacuity.
- **Bell.lean (1):** `tsirelson_bound` `∃ q, 2 < |q|` (S, existential — true, harmless).
- **MarginalLocality.lean (1):** `set_level_locality_from_unitary_dilation` (S).
- ~~**TypicalityMackeyGleason.lean (1):** `mackey_gleason_to_trace_density`~~ — **DELETED 2026-06-06** (#2; module removed, superseded by `EffectGleason`).
- ~~**BornTypicality.lean (1):** `LLN_typicality_axiom`~~ — **DELETED 2026-06-06** (#1; superseded by `BornTypicalityFinite`).

## Circularity check (the real risk for a Born-rule program)

A "bridge" axiom is dangerous if its conclusion is essentially the desired Born claim. Checked:
- `bridge_identity` — relates entropy functionals only; does **not** assume a Born measure or its
  uniqueness. Not circular.
- `mackey_gleason_to_trace_density` — concludes `True`; cannot be circular (nor content-bearing).
- `LLN_typicality_axiom` — concludes `True`; the convergence-to-Born content is **absent**, so it
  cannot be "secretly assuming Born" — but equally it proves nothing.

**Conclusion.** No new soundness hole and no Born-circularity found among the 35. The honest
status: the continuum Born-rule punchline (`LLN_typicality_axiom`) and the continuum trace-density
form (`mackey_gleason_to_trace_density`/`HasTraceDensityForm`) are **vacuous placeholders**. The
genuine, axiom-free results are finite-dimensional (`EffectGleason`, the full Goldstein–Struyve
chain). Any claim of a continuum Born derivation is unsupported until those two conclusions are
given real content.

**Update (2026-06-06).** The content-free *finite* placeholder `LLN_typicality_axiom` now has a
genuine **axiom-free finite replacement**: `BornTypicalityFinite` (finite weak LLN, Chebyshev,
union bound), `BornTypicalityQuantum` (quantum bridge), `BornMeasureUniqueness` (product-measure
uniqueness), and the **finite no-collapse Born representation** joining them to the capacity core
(`BornJoin` / `BornJoinGleason`, single-trial Born forced from non-contextuality via
`OneSiteGleason.oneSite_forced`). All standard-three axioms; budget unchanged at 35. See
`FINITE_BORN_REPRESENTATION.md` for the claim→theorem map and the GPT-5.5-pro-verified scope.
`HasTraceDensityForm` (the *continuum* trace-density form) remains a content-free placeholder —
the continuum punchline is still gated.

---

## Postulate / derivation contract — the gravity / `1/4` / modular thread (register update, 2026-07-01)

**Trigger:** a live correction — the Route-1 (free-field modular) work must not be misread as saying "the `1/4`
is not derived." This section pins the postulate-vs-derived-vs-carried contract for the gravity thread so the
register is unambiguous. (The finite core is now **axiom-free, budget 0**; the 33 axioms above are the historical
continuum-interface record. The items here are *not* axioms — they are the postulate/derivation ledger.)

| Statement | Status | Where (Lean) |
|---|---|---|
| Regional capacity **finiteness** `N_R < ∞` | **POSTULATE** (the one irreducible input — P4-MICRO) | `FQBoundMicro` (`HolographicCapacityBound`), `FQBoundCGP` (`Phase5Master`) — two provably-distinct layers, `EntropyNotCardinality` |
| Area **floor** `S_vN ≤ Q_R` | **DERIVED THEOREM** | `FQBoundMicro.area_floor_vonNeumann` |
| Area **form** `Q_R ∝ A` (`S ∝ A`) | **DERIVED** (conditional Sakharov bridge) | `SakharovRatio` / `GRFromMicro` |
| The **`1/4` ratio** `S_ent·G_ind/A = (4π)/(16π) = 1/4` | **DERIVED THEOREM** (re-derivation of standard induced gravity; matter/regulator-independent, circularity-clean) | `SakharovRatio.sakharov_ratio`, `geometric_quarter` (pinned, AxiomAudit ~6266) |
| The free-field **modular-energy bound** `ΔS ≤ 2π Δ⟨K_boost⟩` (+ first law, rigidity) | **DERIVED THEOREM** (JLMS *modular route*; formalized modular QFT) | `ModularEnergyBound.*` (B1–B7) |
| `A/4G` **from the JLMS free-field modular identity** | **NOT DERIVABLE** here (no `G`, no area operator, cutoff-dependent coeff; `δA/4G=2π∫δT_kk` needs Einstein eqns) — stays a *gravitational input* along this route | — (`ROUTE1_MODULAR_PLAN.md`) |
| The **value of `G`** (and `ℓ_P`) | **CARRIED / OPEN** (neither route derives it) | inventory §8 frontier |
| Continuum Type III₁→II crossed-product **dual-weight trace** (where `A/4G` would live) | **CITED MULTI-YEAR FRONTIER** | §8 |

**The distinction to keep everywhere:** "the JLMS free-field *modular route* cannot derive `A/4G`" (true, narrow)
is **not** "the `1/4` is not derived" (false — the `1/4` ratio *is* a derived theorem via the *separate* Sakharov
bridge). Three separate objects, never conflated: **(a)** the `1/4` ratio — *derived* (`sakharov_ratio`); **(b)**
the modular route — a *distinct* axiom-free result that does not touch `A/4G`; **(c)** the value of `G` — *open*.
