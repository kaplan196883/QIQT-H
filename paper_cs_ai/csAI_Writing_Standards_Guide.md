# arXiv cs.AI Writing Standards Guide — AI-Methodology / Agentic-Formalization Genre

Extracted from 10 representative sample papers (see `sample_papers_evaluation_report.md`)
in the closest genre: LLM-agent systems for autoformalization, theorem proving, and
AI-assisted scientific discovery. Calibrated for the QIQT-H human–AI methodology paper.

## 1. Genre and positioning

These are **systems / methodology papers**, not theorem papers. The unit of contribution
is *a method or system and evidence it works*, not a proof. The reader is an AI/ML
researcher who cares about: what's novel about the agent architecture, what was achieved
that wasn't achievable before, how it was evaluated, and what the limits are. Physics here
is the **case study / evaluation domain**, framed for an AI audience.

## 2. Structure (typical 8–12 pages, two-column or single-column preprint)

| Section | Share | Function |
|---|---|---|
| **Abstract** | ~200–250 words | Problem → method → what was achieved → significance. Lead with the *method* novelty. |
| **1. Introduction** | ~15–20% | The problem (AI for foundational science is unverifiable / hard); the gap; **explicit contributions list** (bulleted, 3–5 items); roadmap. |
| **2. Related Work** | ~10–15% | Autoformalization, neural theorem proving, agentic LLM systems, AI-for-science. Position *against* the nearest neighbors explicitly. |
| **3. The System / Method** | ~25–30% | The architecture: roles, the loop, the human's role, tooling (Lean/Mathlib, MCP, compiler feedback), the review channel. Diagrams expected. |
| **4. Case Study / Results** | ~20–25% | What was formalized (QIQT-H), with concrete artifacts: theorem counts, the axiom audit, the blueprint. Honest proved/conditional/cited split. |
| **5. Discussion / Limitations** | ~10% | What generalizes, failure modes, threats to validity, what the human still had to do. |
| **6. Conclusion** | ~5% | Restate the contribution; future work. |
| **References** | — | 30–60 entries; numeric `[n]` style. |

## 3. Style conventions

- **Voice:** first-person plural ("we present", "we evaluate"). Active, direct.
- **Contributions paragraph:** an explicit bulleted list at the end of the Introduction is
  near-universal in this genre. Use it.
- **Claims are calibrated and evidenced:** every capability claim is paired with a concrete
  artifact or number ("X Lean declarations", "Y axioms in the audit", "green `lake build`").
  This genre is allergic to vague claims — your axiom-budget discipline is an asset here.
- **Reproducibility is expected:** a public repo + artifact link in the abstract/intro is
  standard. The verified blueprint + doc-gen4 is exactly the artifact reviewers want.
- **Diagrams:** an architecture/loop figure is effectively required (the formalizer ⇄
  compiler ⇄ reviewer loop). A pipeline figure and a sample dependency-graph screenshot land well.
- **Terminology:** use the field's words — *autoformalization*, *neural/agentic theorem
  proving*, *verifier-in-the-loop*, *self-correction*, *human-in-the-loop*, *MCP tools*.
- **AI-assistance disclosure:** in this genre it is the *subject*, so
  state the exact models and roles (Claude / Claude Code as formalizer; GPT-5.5 Pro as
  reviewer) plainly in the method and acknowledgements.

## 4. What distinguishes strong papers in this set

- A **clear, single architectural idea** stated early and returned to (e.g. Ax-Prover's
  "LLM reasoning + Lean tools via MCP"; LeanMarathon's "legible, recoverable, drift-resistant
  long-horizon harness"). QIQT-H's is: *a closed human-directed loop — formalizer with
  compiler self-correction + an independent adversarial AI reviewer — applied to a
  researcher's own new theory, with an explicit axiom audit as the honesty mechanism.*
- **Honest scoping.** The best papers (the survey, the "New Frontier" position paper)
  delineate what is and isn't achieved. Your proved/conditional/cited table is a strength,
  not a weakness — foreground it.
- **A concrete, checkable deliverable.** Ax-Prover ships benchmarks; MerLean ships 2,000+
  Lean declarations; LeanArchitect ships blueprints. You ship a *whole verified theory* +
  blueprint + audit. Quantify it.

## 5. Anti-patterns to avoid (genre-specific)

- Overclaiming "AI discovered/proved a new physics result" — your honest line is *AI
  formalized and stress-tested a human-originated theory's deductive core*. Stay there.
- Burying the method behind the physics. For cs.AI, the *loop* is the headline; QIQT-H is
  the demonstration.
- Missing the nearest neighbors (Ax-Prover, MerLean, the AI-Scientist line). Reviewers will
  know them; contrast explicitly.
- No reproducibility artifact. Link the repo + blueprint URL up front.
