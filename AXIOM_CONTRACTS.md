# Axiom contract audit (QIQT-H Lean development)

**Date:** 2026-06 · **Trigger:** GPT-5.5-pro adversarial review (#3 of the "do all 1/2/3" pass).

Two soundness bugs in this project (`IsTensorMultiplicative := ∀ρσ,True` feeding `step3`; the
unsatisfiable `∀-Dd2` flagship hypothesis) shared one failure mode: a **vacuous / too-permissive
predicate** that the `#print axioms` budget check (`scripts/axiom_budget_check.sh`) cannot see.
This document audits the **35 remaining axioms** for that family and for **circularity** (a
"bridge" axiom whose conclusion is essentially the Born claim).

**Tooling:** `scripts/vacuity_lint.sh` greps for vacuous Prop bodies (`:= True`, `↦ True`,
`→ True`, `∀…,True`, `∃…,True`). It is informational; each hit is triaged below.

The detector for the *soundness* family is not the count — it is (a) attempting to discharge the
axiom by proof, and (b) the positive/negative model witnesses in `QIQTH/GoldsteinStruyveModels.lean`.

---

## Triage of the 5 vacuous-body sites the linter flags

| Site | Kind | Verdict |
|------|------|---------|
| `BornTypicality.lean:134` `∃ _N : ℕ, True` | **vacuous CONCLUSION** of `LLN_typicality_axiom` | ⚠️ **content-free** (see headline #1) |
| `TypicalityMackeyGleason.lean:68` `HasTraceDensityForm := True` | vacuous CONCLUSION of `mackey_gleason_to_trace_density` | ⚠️ **content-free** (see headline #2) |
| `TypicalityMackeyGleason.lean:59,63` `IsNormal/IsNoncontextual := True` | vacuous HYPOTHESES of that axiom | sound — its conclusion is itself `True`, so no falsifiable conclusion is reachable |
| `LorentzWitness.lean:180` `le _ _ := True` | trivial preorder **instance field** | harmless (a deliberately-trivial order witness, not an axiom hypothesis) |

No site matches the dangerous pattern **vacuous HYPOTHESIS → concretely-falsifiable CONCLUSION**
(that was the `step3`/`IsTensorMultiplicative` bug, now fixed). So **no new soundness hole** is
present. But two *content-free* conclusions overstate what is proved:

### ⚠️ Headline finding #1 — the Born-frequency punchline is a placeholder

`BornTypicality.LLN_typicality_axiom` is meant to deliver "μ-typical IC sequences have empirical
frequencies converging to the Born weights." Its **conclusion is literally `∀ ε>0, ∀ k, ∃ _N, True`**
— i.e. `True`. So every downstream claim that "frequencies converge to Born" currently rests on a
**vacuous** axiom: it asserts nothing. This is honest as a flagged placeholder, but it must NOT be
cited as "Born derived as a frequency." Giving it real content (a genuine LLN in the AQFT/IC
framework) is open, multi-week work.

### ⚠️ Headline finding #2 — typicality Mackey–Gleason is content-free

`TypicalityMackeyGleason.HasTraceDensityForm := True`, so `mackey_gleason_to_trace_density`
(`… → HasTraceDensityForm w`) and the "theorem" `qiqth_typicality_mackey_gleason` prove a
`True` conclusion. Sound, but no content. The genuine trace-density result exists only at the
**finite** level (`EffectGleason.finite_effect_gleason`), which is axiom-free; the continuum
Type-II Bunce–Wright statement here is a named placeholder.

---

## The 35 axioms by cluster

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
- **TypicalityMackeyGleason.lean (1):** `mackey_gleason_to_trace_density` — **content-free** (#2).
- **BornTypicality.lean (1):** `LLN_typicality_axiom` — **content-free** (#1).

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
