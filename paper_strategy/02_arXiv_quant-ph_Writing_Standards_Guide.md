# arXiv quant-ph — Writing Standards Guide (foundations subfield)

Distilled from the 10 sample papers. These are conventions, not rules; deviate when justified.

## Structural template (foundations / axiomatic papers)

| Section | Typical share | Notes |
|---|---:|---|
| Title | — | Declarative or "from-X-to-Y" form. Avoid acronym-only titles. |
| Abstract | ~200–250 words | One paragraph. Pattern: (1) problem; (2) what we propose; (3) result/derivation; (4) implications / falsifiability. |
| 1. Introduction | 15–18% | Frame the measurement problem; survey alternative approaches; state thesis; preview structure. |
| 2. Background / Setup | 10–15% | Notation; recall holographic bounds, Wald entropy, Born rule. Keep short — refer rather than reprove. |
| 3. Axiomatic core | 20–25% | State QIQT axioms A1–A7. One subsection per axiom with motivation. |
| 4. Mechanism: how `Q_max` resolves measurement | 25–30% | The technical heart. Derive single-outcome selection from `P_Q`. Recover Born rule. |
| 5. Comparison with existing approaches | 15% | Tables comparing to Srikanth 2003, CSL, GRW, DP, MWI, RQM/QBism, ’t Hooft CA, Palmer RaQM. |
| 6. Empirical positioning & falsifiability | 8% | What experiment could refute QIQT? CSL bounds, neutrino coherence, quantum computer scaling à la Palmer. |
| 7. Conclusion / outlook | 5–8% | Brief; flag that QIQT-H extensions (cosmology, galaxies) are deferred to companion papers. |
| Acknowledgements + References | — | 40–60 refs typical for foundations; 60+ acceptable when bridging fields. |
| Appendices (optional) | — | Detailed derivations, technical lemmas, parameter estimates. |

## Total length
- arXiv `quant-ph` foundations preprints typically **8,000–14,000 words** (15–25 pages REVTeX two-column or 25–40 single-column).
- Target for this paper: **~10,500 words main text + appendices**.

## Style patterns

| Convention | Practice in samples |
|---|---|
| Voice | Active "we" dominates; passive used for technical results. Pure first-person singular is rare. |
| Equation density | Heavy — sample papers run ~1 numbered equation per 200 words. |
| Notation | LaTeX, REVTeX 4.2; bra–ket consistent; explicit subscripts (`Q_R`, `Q_max`) over compact shorthand. |
| Citation density | ~1 citation per 100–150 words; survey sections denser. Use [1,2,3] grouped numeric. |
| Hedging | Foundations papers are upfront about speculation: "we propose", "we conjecture", "this requires further development". |
| Originality framing | Always explicitly contrast with at least 2 named alternative interpretations / models. |
| Quantitative anchors | Even speculative foundations papers cite at least one number (collapse rate, decoherence bound, dimension count). |

## Format specifications
- **Typesetting:** REVTeX 4.2 (preferred) or Springer / standard LaTeX article class.
- **Figures:** Minimal in foundations papers; 0–3 typical. Conceptual diagrams help if used sparingly.
- **Tables:** Common (1–3) for comparing interpretations. QIQT-H paper should include one such table.
- **Math display:** Always numbered if referenced; un-numbered only for purely illustrative formulas.

## Section-heading norms
- "Introduction", "The measurement problem", "Axioms of …", "From `Q_max` to single outcomes", "Comparison with existing approaches", "Empirical bounds and falsifiability", "Conclusion".
- Subsections use **bold-italic** in REVTeX or `\subsection{}`; keep to ≤2 levels of nesting.

## Tone
- **Honest about limits.** Hardy (2001), Jacobson (1995), Srikanth (2003) all openly flag what their paper does *not* solve. QIQT-H paper should follow this.
- **Engage rivals seriously.** A foundations paper that doesn't engage CSL, MWI, RQM, and 't Hooft will be desk-rejected.
- **No "manifesto" voice.** Don't oversell. The thesis is bold enough — let it speak.

## Things to avoid (common failure modes for foundations submissions)
- Claiming to "solve" the measurement problem without engaging CSL/DP empirical bounds.
- Ignoring decoherence literature (must distinguish dynamical-decoherence-only accounts from genuine single-outcome selection).
- Heavy notational invention before the reader sees motivation.
- Mixing scopes (cosmology, dark matter, etc.) in a foundations paper — keep it tight.
