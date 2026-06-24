---
name: lean-track-state
description: Produce an audited state report for a "track" in a Lean 4 / Mathlib project — axiom status, every hypothesis/assumption (including ones hidden inside data structures), proven-vs-open surface, and curated physics/regularity/data piles. Use when the user asks for a track state report, assumption surface, axiom audit, proven-vs-open status, theorem-spine report, or a physics/regularity/data hypothesis split.
---

# lean-track-state

Generate a **state report** for a *track* (a goal realized by a spine of Lean theorems). Built on the
generic, config-driven tool `scripts/lean-track.py` (package `scripts/lean_track/`). The tool is the
**deterministic source of truth**; this skill adds only interpretation, always clearly marked `[AI]`.

## The honesty contract (non-negotiable)

Every claim carries a provenance badge and you must preserve it:
- `[L]` Lean/kernel fact (declaration, type, `collectAxioms`) — from the tool.
- `[P]` Lean-checked prober result (auto-dischargeable / `False`-provable) — from the tool.
- `[D]` deterministic post-processing (dedup, dependency, proof-unused) — from the tool.
- `[C:rule]` a version-controlled curation rule in the track `.toml` — from the tool.
- `[AI]` **your** semantic judgment — only you emit this.

Hard prohibitions:
1. **Never** call an `[AI]` label a Lean fact. "Lean says `hbound` is a `Prop` hypothesis" is fine; "Lean says `hbound` is the Clausius law" is **forbidden** — that's `[AI]` or a `[C]` curation rule.
2. **Never** turn a prober failure into "mathematically independent." `unresolved`/`surface` means "not discharged by this analysis," not "necessary."
3. **Never** hide a missing declaration or a non-standard axiom.
4. **Never** report `literal_axiom_free` for something that uses `Classical.choice` — that's `policy_clean`, report both.

## Inputs (accept any)

1. A track config path — `tracks/gr.toml`.
2. A track id — `gr` → find `tracks/gr.toml`.
3. Explicit theorem names — write a draft config (`tracks/_draft_<id>.toml`) and mark `spine_provenance = ai_draft`.
4. A goal/keyword (no spine given) — **discover** candidate theorems (see below), confirm with the user (or mark draft), then proceed.

## Procedure

1. Locate the project (nearest `lakefile.lean`/`lakefile.toml`/`lean-toolchain`). Confirm the library builds (the tool needs the oleans).
2. Ensure a track config exists; create/extend it if needed. Do **not** present a discovered spine as human-curated.
3. Run the tool:
   ```
   python scripts/lean-track.py report -c tracks/<id>.toml
   ```
   It writes `reports/<id>/{facts.curated.json, agent_summary.json, report.machine.md}` and prints a one-line summary.
4. **Read `agent_summary.json`** (structured) — not the Markdown. It gives, per theorem: present, kind, `axiom_free_literal`, `policy_clean`, `isFalse` (no-go), `falseProvable` (vacuity), `n_prop`, `n_packed`, `uses_spine`, the `surface` list (each with any `[C]` curation label), and `dischargeable`.
5. Build the interpreted report:
   - Headline the **capstone's** assumption surface (`role = capstone`), deduplicated — *not* the cross-spine sum (that double-counts shared hypotheses).
   - Apply the curated piles from the tool. For any **uncategorised** surface hypothesis, you may propose a label — mark it `[AI]` and, if you want it to persist, write a suggested `category_rules` entry into `reports/<id>/curation.suggestions.toml` (do not silently edit the track config).
   - Surface the **packed Prop fields** (`n_packed`) prominently — assumptions hidden inside data structures (e.g. an `EffectMeasure` argument packing `additive`/`normalized`/`nonneg`) are real premises that a naive hypothesis count misses.
   - Flag any `falseProvable` theorem loudly (🚨 vacuous context) and any non-standard axiom.
   - Note no-go theorems (`isFalse=true`) — their content is "X does **not** imply Y."
6. Output `reports/<id>/report.interpreted.md`: a provenance summary, the machine facts (link/cite the tool's report), the curated piles, the capstone surface with your `[AI]` notes, and a short honest "current state" (proven / conditional-on / open). Cite theorem + binder names verbatim.

## Discovery (when no spine is given)

1. Look for existing manifests: `tracks/*.toml`.
2. Grep the source for `theorem`/`lemma` whose name, namespace, docstring, or type mentions the goal keywords.
3. Rank: exact namespace match; names containing `capstone`/`main`/`complete`/`final`/`soundness`; type mentions the goal; source order. Capstone = the most-downstream theorem whose conclusion is the track's goal.
4. If ambiguous, ask the user, or emit a draft and say so.

## Staying generic (across projects, not just this one)

- Read **everything** project-specific from the `.toml`: `lean_import`, `allowed_axioms`, the theorem manifest, the category rules. Hardcode nothing.
- If the prober's tactic profile is too weak for a project, that only means fewer auto-discharges — never a correctness problem (failures are reported as `unresolved`, never "independent").
- The tool handles missing names gracefully (`present:false`); report them, don't crash.

## Tool reference

```
python scripts/lean-track.py report  -c tracks/<id>.toml [--no-prober] [-o <dir>]
python scripts/lean-track.py extract -c tracks/<id>.toml          # raw Lean facts only ([L])
python scripts/lean-track.py diff --old <old>/agent_summary.json --new <new>/agent_summary.json
```
`diff` is for CI / progress tracking: it reports new/retired project axioms and added/discharged surface
assumptions between two runs.

Track `.toml` schema: `[track]` (id/title/subtitle); `[project]` (lean_import, allowed_axioms, timeout_sec);
`[[theorems]]` (name, role ∈ {capstone, spine, nogo, lemma}); `[[category_rules]]` (id, category, label,
name_regex, type_regex — first match wins; these are the *only* place curated labels live, and they are
version-controlled and auditable).
