# Scoping: process metrics + ablation for the AI loop (addressing reviewer concern #5)

**Goal.** Convert the cs.AI paper from "Accept" to "strong accept" by adding the one thing all three
GPT-5.5-Pro reviews flagged as the remaining gap: *evidence that the two-model loop is effective*, not
merely that it succeeded once. The reviewer's explicit ask (Review 3, highest-leverage change):

> a compact empirical/process-evidence section — LLM-call/session counts, human hours, build
> iterations, axioms introduced and discharged over time, reviewer critiques classified
> TP/FP/clarification and how many led to code changes, and **a comparison to a "formalizer +
> compiler only" baseline on a small representative module/track**.

This splits into three honesty-distinct buckets. **A** is extractable from the artifact now (real,
reproducible). **B** is a genuine experiment that must be *run*. **C** is unrecoverable and must be
disclosed, not faked.

---

## Bucket A — Retrospective process metrics (extractable now)

All reproducible from `git` and the audit docs at the pinned commit. Draft "process audit" table:

| Metric | Value | Source / how to reproduce |
|---|---|---|
| Project span | 2026-05-25 → 2026-06-24 (~30 days) | `git log --reverse --format=%ad` |
| Total commits (repo) | 1455 | `git log --oneline \| wc -l` |
| Commits touching `lean/` | 1016 | `git log --oneline -- lean/ \| wc -l` |
| Commits referencing GPT-5.5 | 61 | `git log --oneline \| grep -ci gpt-5.5` |
| Commits referencing axiom/discharge | 231 | `git log` grep |
| Project-axiom trajectory | 57 → 40 → 37 → 35 → 33 → 32 → 31 → 29 → 21 → 17 → 8 → 7 → 6 → 0 | `B_axiom_discharge_timeline.md` §B.2 (sourced from `axiom_budget_check.sh` + `AxiomAudit.lean`) |
| Discharge events | ~13 named, each tied to a module/technique | §B.2 |
| Up-ticks (axiom introduced then discharged) | several (noted in §B.2/B.3) | the honest non-monotone part of the ratchet |
| Documented reviewer/consultation rounds | ≥4 design consultations + 1 audit round (Lean) + 3 cs.AI-paper review rounds | `QIQTH.lean` round comments; this paper's review history |
| Reviewer saves (confirmed true positives) | 2, fully documented + kernel-checked | §B.3 (false axiom), §B.4 (vacuous axiom) |
| Final artifact | 192 modules · ~2,010 thms · 830 `#print axioms` · 0 axioms · 0 `sorry` · 1 benign vacuity site | audit module / track-state tool |

**Caveat to state with the table.** Commit counts are a *lower-bound proxy* for formalizer iterations,
not a true LLM-call count (multiple agent turns collapse into one commit; some commits are mechanical).
We label them as such.

**Action (feasible now):** turn the above into a short table + the existing 57→0 ratchet figure;
script the extraction (a `scripts/process_metrics.sh` that regenerates every number) so the section is
artifact-reproducible like the rest of §4.

---

## Bucket B — The ablation (must be run)

The reviewer wants "formalizer + compiler only vs. + audit vs. + reviewer." Two complementary designs;
do **B1** first (cheap, already-evidenced), then **B2** if we want a denominator.

### B1 — Retrospective counterfactual on the two documented saves (cheap, high-credibility)

The two saves (§B.3, §B.4) are *already* an instrument-detection comparison; we make it explicit and
reproducible. Re-introduce each faulty declaration on a throwaway branch and run each instrument:

| Fault (real episode) | compiler-only | + axiom budget | + vacuity lint | + adversarial reviewer |
|---|---|---|---|---|
| Case 1: false (positivity-omitting) Gleason axiom, well-typed | green ✗ undetected | counts it, ✗ not flagged false | ✗ not vacuous | ✓ **caught** (3rd pass) |
| Case 2: `(h_alg : True)` inconsistent locality axiom | green ✗ undetected | counts it, ✗ not flagged | ✓ **caught** (trivial antecedent) | ✓ caught |

This is honest, concrete, and reproducible (re-add the two axioms, run `lake build`,
`axiom_budget_check.sh`, `vacuity_lint.sh`, and re-show the archived reviewer transcript). It directly
demonstrates the claim "compiles + low axiom count is necessary but not sufficient." **Limitation
(disclose): n = 2 faults — an existence/profile result, not a rate.**

### B2 — Prospective seeded-fault study (gives a real catch-rate denominator)

To answer "how often does each instrument catch a fault," inject a controlled set of known-unsound
shortcuts and measure detection. Protocol:

- **Faults:** seed N ≈ 10–15 unsound edits across a few representative modules, drawn from a fixed
  taxonomy — (i) false-but-well-typed axiom, (ii) vacuous/`True`-antecedent axiom, (iii) over-strong
  hypothesis that trivializes the goal, (iv) `sorry` (control: must be caught by everyone), (v) a
  *sound* edit (control: must NOT be flagged → measures false-positive/over-flagging).
- **Configs:** C1 compiler-only; C2 +`#print axioms` budget; C3 +vacuity lint; C4 +adversarial
  reviewer (fixed prompt, fixed model/version, blind to which edits are faults).
- **Metrics per config:** true positives, false positives (sound edits flagged), misses; for C4 also
  classify each critique TP/FP/clarification and whether it led to a code change.
- **Report:** a detection-rate table + the reviewer's TP/FP/clarification breakdown — exactly the
  numbers the reviewer asked for.
- **Controls/honesty:** pre-register the fault set and the reviewer prompt; run C4 blind; report
  model/version and that results are version-specific; N is small, so report as indicative not
  definitive.

**Effort:** B1 ≈ a few hours (re-add 2 axioms, run 3 scripts, cite archived transcript). B2 ≈ 1–2 days
(design fault set, run 4 configs × ~12 edits, score). B2 is the genuine new experiment.

---

## Bucket C — Unrecoverable (disclose, do not fabricate)

- **Exact LLM-call counts / agent turns:** not logged. Proxy = commit counts (Bucket A), labelled as a
  lower bound.
- **Human hours:** not tracked. Disclose; optionally give a coarse self-reported estimate clearly
  marked as such, or omit.
- **Complete per-critique reviewer log over the whole project:** not kept. We have the round count and
  2 confirmed saves (Bucket A) and can produce a real TP/FP rate *prospectively* (B2), but cannot
  reconstruct a retrospective denominator. Disclose.

---

## Paper integration

- **New §3.8 "Process metrics and an instrument ablation"** (or fold into §4): the Bucket-A table +
  ratchet figure; the B1 instrument-detection table; B2 results if run.
- **Strengthen §4.5:** replace "no denominator" caveat with the B1 table (and B2 rate if available),
  keeping the honest n-limitation.
- **§5.3:** downgrade the "no controlled comparison" threat to "a small controlled ablation (B1/B2);
  large-scale validation remains future work."
- **Honesty guard:** version-specificity, small N, commit-count-as-proxy, single team — all stated.

## Recommended order

1. **Now:** Bucket A extraction + `scripts/process_metrics.sh` + B1 retrospective table (all
   feasible, reproducible, no new experiment). This alone materially answers #5.
2. **If pursuing strong-accept:** run B2 (the seeded-fault study) for a real catch-rate denominator.
3. Write §3.8 + update §4.5/§5.3; regenerate; re-review.

**Bottom line:** A + B1 are doable immediately and convert #5 from "honestly disclosed limitation" to
"addressed with reproducible evidence." B2 is the extra mile for a quantified catch rate.
