# QIQT-H — Program Status: where we are, and what the breakthrough would be

*Living status document. Last updated 2026-05-31, after a holistic GPT-5.5-pro
adversarial review. This is the honest map: what is done, what is the prize we
are chasing, and what must be fixed before arXiv.*

---

## 1. One-paragraph honest verdict

QIQT-H is **not (yet) a breakthrough solution to the measurement problem.** In
its honest current form it is:

> exactly-unitary global wavefunction Φ  +  a primitive **actuality selector λ**
> (which macroscopic realization is the actual one)  +  an **unconstructed
> typicality measure μ** (meant to deliver Born)  +  a **holographic
> finite-record bound** Q_R = A(∂R)/4ℓ_P².

That is a **legitimate, publishable research-program architecture**. What is
*missing* is the one object that would make it a genuine breakthrough: a
**canonical, Lorentz-covariant construction of μ / λ-selection** that yields the
Born rule and operational no-signaling *without fiat*. Until μ is constructed,
this is an interpretation/architecture, not a derivation.

---

## 2. THE BREAKTHROUGH WE ARE LOOKING FOR (the prize)

**A canonical, Lorentz-covariant law assigning to each unitary global Φ a measure
μ over actuality selectors (λ / history valuations) such that:**

1. Born weights are recovered for **all** decoherent record partitions;
2. independent experiments **tensor-factorize** correctly;
3. **LLN / frequency** behaviour follows (typical λ-histories show Born frequencies);
4. **operational no-signaling** holds after μ-averaging;
5. **free settings / measurement independence** are preserved (no superdeterminism);
6. the construction is **covariant** — no hidden foliation;
7. μ is **derived** (from finite-record covariance + noncontextuality + tensor
   multiplicativity + locality), **not** "choose the Born measure by hand."

If (1)–(7) are achieved, QIQT-H becomes a genuine breakthrough. **Caveat (honest):**
this may be a restatement of the measurement problem itself — every single-world
program (Everett, Bohm, modal, Kent) owes essentially this same object. So the
prize is real, hard, and shared; sharply *stating* it is itself a contribution.

**The single sharpening that would most raise the contribution short of the full
prize — the "Record Quotient Theorem":**
> For every internal observer in a finite causal region R at distinguishability
> scale ε, every reportable proposition factors through a *finite Boolean record
> algebra* B_{R,ε} whose atoms are einselected, redundantly encoded,
> ε-distinguishable records, with |At(B_{R,ε})| ≤ e^{Q_R}; actual reports are
> valuations selected by λ.

This is what makes "we measure in 0/1 because we are macroscopic" precise: not
"the world is binary," but "internal macroscopic reports are finite-valued
elements of a finite record quotient." Proving this is the most tractable real
contribution on the path.

---

## 3. WHERE WE ARE — what is genuinely done / novel (publishable)

- **Division-of-labor clarity** (cleaner than most "decoherence solves outcomes"
  arguments): decoherence conserves weights · einselection ⇒ robust Boolean
  records · holography ⇒ finitely many distinguishable records · λ ⇒ which is
  actual · μ ⇒ Born frequencies.
- **Lean formalization + assumption audit** (*the strongest original component*):
  no-signaling, CHSH→Tsirelson 2√2 with rigorous singlet, microcausality,
  Donald's identity, `NoConcentration` (decoherence conserves |c_k|²),
  support-preservation ≠ Born-equivariance, structural audits. 40 project axioms
  (down from 57). Publishable **as a formal dependency analysis**, NOT as a
  completed Born derivation.
- **Finite distinguishable-record quotient** M_ε(R) ≤ e^{Q_R} — potentially
  interesting if made precise (→ Record Quotient Theorem above).

## 3b. What holography's REAL (narrow) job is

Q_R does **non-redundant** work *only* as: "for a finite causal region at scale
ε, the empirically accessible record algebra is a finite Boolean quotient with
≤ e^{Q_R} atoms." It does **NOT**: select an outcome · forbid the cat state
α|0⟩^N+β|1⟩^N · derive Born · produce collapse · create exact superselection.
Sell it as the former (defensible); never as the latter (fails).

---

## 4. GAP RANKING (severity for publishability)

| # | Gap | Severity | Fix |
|---|-----|----------|-----|
| 1 | **Bell: PI-vs-measurement-dependence contradiction** | **FATAL in current text** | Commit to PI-violation horn; drop measurement-dependence/Palmer-as-our-position |
| 2 | **Unconstructed μ + no-signaling/fine-tuning** | Fatal to *breakthrough*; OK as flagged open problem | = the prize (§2) |
| 3 | **Lorentz covariance of A_R[Φ,λ]** | Fatal to *"relativistic completion"* claims; OK as open problem | covariant causal-diamond Q_R/ε; covariance of selection map |
| 4 | **λ = "microscopic initial conditions"** | **MUST FIX before submission** | relabel → atemporal global actuality/history selector (Conway–Kochen) |
| 5 | **Born interface axioms in Lean** | Non-fatal *if transparent* | dependency table; don't claim Born machine-derived |
| 6 | **MDC strong form** | Non-fatal; already demoted | keep as open/speculative |

---

## 5. MUST-FIX SET BEFORE arXiv (the checklist)

- [ ] **(0)** Fix manifesto overclaim "There is only Φ" → "Only Φ is *dynamical*;
      a run also contains the non-dynamical actuality fact λ." (README + §1.0a)
- [ ] **(1)** **Bell → PI horn**: rewrite §6.9 + README Bell line; delete
      measurement-dependence-as-our-position; recommend keeping Palmer only as a
      *contrasting* sister program, not as QIQT-H's stance. State: keep free
      settings + outcome-definiteness ⇒ deny **Parameter Independence** at the
      ontic level; operational no-signaling holds after μ-averaging.
- [ ] **(2)** **λ relabel**: "microscopic initial conditions" → "atemporal global
      actuality/history selector" across all four papers + Lean docstrings + memory.
- [ ] **(3)** **Claim calibration**: "solves/dissolves the measurement problem" →
      "decomposes the problem; λ and μ are the remaining primitive/open structures."
- [ ] **(4)** **μ status**: explicitly "unconstructed / interface-level"; do not
      claim Born is derived.
- [ ] **(5)** **Holography status**: "Q_R bounds distinguishable-record capacity
      only; does not exclude superpositions or select outcomes."
- [ ] **(6)** **Lean**: theorem-dependency table separating machine-verified
      results from project/interface axioms (largely exists — surface it).

**Submission gate:** item (1) is the one *load-bearing inconsistency* — do NOT
submit with it unresolved. The rest are honesty/calibration; with them done, the
paper is defensible as a research-program / foundations-architecture paper.

---

## 6. What critics will say if we DON'T fix it

> "This is Everett plus a primitive actual-world index and an unspecified Born
> measure, with internally inconsistent Bell language."

The fixes above convert that into the accurate, defensible:

> "An exactly-unitary single-world architecture that *decomposes* the measurement
> problem into a robustness part (decoherence), a finiteness part (holography),
> and two clearly-stated primitives (λ actuality, μ typicality), with a
> machine-checked dependency audit and a sharply-posed open problem (covariant μ)."
