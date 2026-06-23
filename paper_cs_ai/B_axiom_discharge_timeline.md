# Axiom-discharge timeline & reviewer-caught cases (deliverable B)

Feed material for the methodology paper, §4.3 ("The audit in action") and §4.4 ("What the
reviewer caught"). Source: audit-note comments in `lean/mathlib/scripts/axiom_budget_check.sh`
and `QIQTH/AxiomAudit.lean`. All numbers are project-specific (non-standard) axiom counts;
the three standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) are never counted.

## B.1 — The headline artifact metric (for §4.2 / Table)

| Snapshot | Project axioms | Build | `sorry` |
|---|---|---|---|
| Pre-strengthening (paper-era baseline) | **57** | green | 0 |
| After consolidation + Step-1 deletion | 40 | green | 0 |
| After capacity-exclusion pass (paper's last recorded number) | 37 | green | 0 |
| 2026-06-21 (current) | **0** | green | 0 |

192 modules · ~2,010 theorems/lemmas · 830 `#print axioms` directives · 0 axioms · 0 `sorry`
· 1 benign vacuity-lint site. The axiom budget is **CI-enforced at 0** (raise only with a
written audit note).

## B.2 — The discharge trajectory (for §4.3, the "ratchet" figure)

A monotone-down ratchet, with a few passes that *temporarily added* a named interface axiom
(making a new conditional result explicit) before discharging it — itself part of the honest
story: the budget rose when new conditional structure was introduced, then fell as it was proved.

```
57 ──consolidation + delete 5 false/unused GS Step-1 sub-axioms──▶ 40
40 ──infrastructure finite-discharge (Open Problems 6/9)─────────▶ 37
37 ──Goldstein–Struyve Step 1 (Schur) + Step 3 proved axiom-free─▶ 35
35 ──delete 2 content-free placeholder axioms───────────────────▶ 33
33 ──Bell `tsirelson_bound` retired (attainability proved)───────▶ 32
32 ──SOUNDNESS FIX: inconsistent `…locality…(h_alg:True)` removed─▶ 31   ◀── case study 2
31 ──Klein's inequality discharged (RelEntPositivity ×2)─────────▶ 29
29 ──DonaldSystem typeclass refactor (8 Donald axioms → theorem)─▶ 21
21 ──DPI discharged (concrete MixedUnitaryChannel, ×4)───────────▶ 17
17 ──ArakiInterface discharged ×9 (incl. Donald A1–A3)───────────▶ 8
 8 ──Klein-equality direction (`AkRelEnt_eq_zero_iff`)───────────▶ 7
 7 ──Holevo bound `χ ≤ H(p)` proved (operator-monotone log)──────▶ 6   (this closes ArakiInterface 11→0)
 6 ──EntropyBridge module → `EntropyBridgeSystem` typeclass + instance ▶ 0
                                                          ★ AXIOM-FREE
```
(The GleasonSelector and LorentzSelection passes — case study 1 below — sit on this line too:
each introduced standard interface axioms and then discharged them in the same session, net 0.)

## B.3 — Case study 1 (§4.4): the reviewer caught a *false* axiom

**Module:** `QIQTH/GleasonSelector.lean`. The formalizer (Claude Code) initially encoded the
Busch/effect-Gleason step as an interface axiom `effect_gleason_representation`: a normalized,
additive, homogeneous, ray-certain effect-valuation equals the Born functional. The
independent reviewer (GPT-5.5-Pro), on its **third** review pass, flagged that this axiom is
**false as stated** — it omits *positivity*. The concrete refutation, then itself formalized:
on $\mathbb{C}^2$ the weight $w(E) = E_{00} + E_{01}$ satisfies normalization, additivity,
homogeneity, and ray-certainty, yet is **not** the Born functional
(`naive_gleason_premises_insufficient`).

**Resolution (proved, not patched):** the false axiom was retired and replaced by *derived*
content — `support_of_positive_certain` (positivity + certainty ⇒ ray-support, via the
Cauchy–Schwarz null-radical argument) and the capstone `positive_ray_certain_forces_born`
(positivity + normalization + ray-certainty ⇒ Born). The two standard linear-algebra lemmas
this rested on (`positive_functional_hermitian` via polarization; `psd_null_radical` via a
real-quadratic discriminant) were then *also* discharged, leaving the module **axiom-free**.

**The methodological point:** a capable single agent encoded a plausible-but-false premise; an
*independent* adversarial reviewer with a different vantage caught it; the fix made the result
*stronger* (Born now follows from positivity, an honest hypothesis). This is the loop's value
in one episode — and it is checkable, since both the counterexample and the capstone are in
the kernel-checked development.

## B.4 — Case study 2 (§4.4): the audit's blind spot, and the lint that closes it

**Module:** `QIQTH/MarginalLocality.lean`. An interface axiom
`set_level_locality_from_unitary_dilation (… (h_alg : True)) : IsLocalUnder r T` was
**logically inconsistent**: because its hypothesis is `True` (constrains nothing), it asserts
`∀ a, r (T a) = r a` for arbitrary `r, T` — false (`r = id, T = not` gives `not a = a`, i.e.
`False`). **Crucially, the axiom-budget check did not and could not catch this:** counting
axioms and scanning for `sorry` says nothing about whether a declared axiom is *vacuous or
inconsistent*. This is the soundness blind spot of "it compiles + the axiom count is low."

**Resolution:** the axiom was removed and the one theorem using it now takes locality as an
*explicit hypothesis* (`h_local : IsLocalUnder r T`) — the interface-as-hypothesis pattern,
which relocates the assumption into the open instead of hiding it in an axiom. The project
added a dedicated **vacuity lint** (`scripts/vacuity_lint.sh`) as a second guard beyond the
axiom counter; it scans for vacuous `Prop` bodies (`:= True`, trivial antecedents). It
currently reports a single *benign* site — an indiscrete-preorder definition
(`LorentzWitness.lean:180`, `le _ _ := True` with `le_refl`/`le_trans` proved) — i.e. a
legitimate order instance, not a hidden assumption.

**The methodological point (the trust thesis in miniature):** "machine-checked" is necessary
but not sufficient; "axiom budget = 0" is necessary but not sufficient. Soundness auditing
needs a *third* instrument — vacuity/inconsistency scanning — and an honest analyst willing to
treat a `True` hypothesis as a red flag. This is exactly why the paper's contribution is the
*audited* loop, not merely a passing build.

## B.5 — Honest framing guard (so §4 does not overclaim)

State plainly in §4.3: **axiom-free in Lean certifies the *conditional/structural mathematics*,
not the *physics*.** The case study's theory (QIQT-H) still has open physical postulates (the
holographic (FQ) bound, the Macroscopic Definiteness Conjecture, the Born/Canonical-IC
Principle, Lorentz covariance). The methodology paper's claim is about *trustworthy
formalization* — that the loop + audit make the proved/conditional/cited boundary explicit and
shrink the conditional part to zero for the deductive core — **not** that AI proved a new
physics result. Keep that sentence in §4 and again in §5.3 (threats to validity).
