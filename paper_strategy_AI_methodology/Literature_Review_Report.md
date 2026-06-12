# Literature Review Report — AI-Methodology / Agentic-Formalization Paper

Generated 2026-06-11. Literature base: ~35 papers across three search rounds, organized by
theme. Relevance filtered to ≥7/10. This corpus grounds the gap analysis
(`research_gaps_gap_report.md`) and originality assessment.

## Coverage
- **Total papers:** ~35 (well above the 20 minimum)
- **Time span:** 2022 foundational works → June 2026 frontier
- **Venues:** arXiv cs.AI / cs.LO / math.LO / quant-ph; one journal (Adv. Sci.)
- **Core concepts covered:** autoformalization, agentic/neural theorem proving,
  human–AI scientific discovery, LLM-as-judge / adversarial review, verification &
  hallucination, formalizing physics in Lean.

## Theme A — Autoformalization (NL/LaTeX → formal)
- Wu, Jiang et al., *Autoformalization with Large Language Models* (2205.12615, 2022) — seminal.
- Jiang, Welleck et al., *Draft, Sketch, and Prove* (2210.12283, 2022) — draft→sketch→prove.
- Weng et al., *Autoformalization in the Era of LLMs: A Survey* (2505.23486, 2025).
- CRAMF, *Automated Formalization via Conceptual Retrieval-Augmented LLMs* (2508.06931, 2025).
- *Aria: Iterative Auto-Formalization via Dependency Graph* (2510.04520, 2025).
- *Towards a Common Framework for Autoformalization* (2509.09810, 2025).

## Theme B — Agentic / neural theorem proving (with self-correction)
- Breen et al., *Ax-Prover* (2510.12787, 2025) — **nearest neighbor**: LLM+Lean via MCP, math+quantum physics.
- *MA-LoT* / *ProofNet++* (2025) — multi-agent generate+correct, verifier-in-the-loop.
- *LeanMarathon* (2606.05400, 2026) — long-horizon multi-agent Lean autoformalization.
- *Learning to Repair Lean Proofs from Compiler Feedback* (2602.02990, 2026).
- *Prover Agent* (2506.19923, 2025); *A Minimal Agent for Automated Theorem Proving* (2602.24273, 2026).
- *Goedel-Prover-V2*; *MPS-Prover* (2505.10962, 2025) — verifier-guided self-correction / search.

## Theme C — Human–AI scientific discovery & research agents
- Lu et al., *The AI Scientist* (2024); Yamada et al., *The AI Scientist-v2* (2504.08066, 2025).
- Gottweis et al., *Towards an AI Co-Scientist* (2025).
- *The Agentic Researcher* (2603.15914, 2026); *AgentRxiv* (2503.18102, 2025).
- Brenner, Cohen-Addad, Woodruff, *Solving an Open Problem in Theoretical Physics using AI-Assisted Discovery* (2603.04735, 2026) — **near neighbor: AI solves physics, but NO formal prover**.
- *Why LLMs Aren't Scientists Yet* (2601.03315, 2026); surveys (2505.13259; 2503.24047).

## Theme D — LLM-as-judge / adversarial review (the reviewer role)
- *When AIs Judge AIs* (2508.02994, 2025); *Multi-Agent Debate for LLM Judges* (2510.12697, 2025).
- *Judging with Many Minds* (2505.19477, 2025); *Meta-Judges* (2504.17087, 2025).
- *Auditing Multi-Agent LLM Reasoning Trees…* (2602.09341, 2026).

## Theme E — Verification, trust, hallucination in AI math/science
- *The Need for Verification in AI-Driven Scientific Discovery* (2509.01398, 2025) — key motivation.
- *Self-Consistency-Based Hallucination Detection* (2504.09440, 2025).
- *Tool Receipts, Not Zero-Knowledge Proofs* (2603.10060, 2026).
- *Formal Mathematical Reasoning: A New Frontier in AI* (2412.16075, 2024) — position/agenda.

## Theme F — Formalizing physics in Lean (the case-study domain)
- *Formalization of QFT* (2603.15770, 2026) — **nearest physics neighbor: established QFT axioms in Lean**.
- *A Formalization of the Generalized Quantum Stein's Lemma in Lean* (2510.08672, 2025).
- *PhysProver* (2601.15737, 2026); *PhysLean / physlib*; *Formalization of physics index notation in Lean 4* (2411.07667).
- *Formalizing Chemical Physics using the Lean Theorem Prover* (2210.12150, 2022).
- Tooby-Smith, *A Perspective on Interactive Theorem Provers in Physics* (Adv. Sci., 2026).

## Synthesis
The field has (i) maturing autoformalization and agentic proving with self-correction, (ii) a
booming AI-scientist literature, (iii) a separate LLM-as-judge literature, and (iv) early
physics-in-Lean efforts on *established* results. What no single line combines: a
human-directed loop that formalizes a researcher's **own new foundational theory**, pairs a
**self-correcting formalizer** with an **independent adversarial AI reviewer**, instruments
**soundness via an axiom audit**, and publishes a **verified human-readable bridge** — in the
**foundations-of-physics** domain. That intersection is the paper.
