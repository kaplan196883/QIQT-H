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

Status legend: ✅ DONE (committed) · ◻ OPEN (research agenda).

| # | Gap | Severity | Status / Fix |
|---|-----|----------|-----|
| 1 | **Bell: PI-vs-measurement-dependence contradiction** | was **FATAL** | ✅ DONE — committed to PI-violation horn; §6.9/Position/Tutorial rewritten; Palmer reframed as opposite horn |
| 2 | **Unconstructed μ + no-signaling/fine-tuning** | Fatal to *breakthrough*; OK as flagged open problem | ◻ OPEN — = the prize (§2); Open Problem 1 |
| 3 | **Lorentz covariance of A_R[Φ,λ]** | Fatal to *"relativistic completion"* claims; OK as open problem | ◻ OPEN — now a numbered Open Problem 3b with 5 explicit requirements (§4a below + paper §11.4) |
| 4 | **λ = "microscopic initial conditions"** | was MUST-FIX | ✅ DONE — relabeled "atemporal global actuality selector" across 4 papers + Lean docstrings + memory |
| 5 | **Born interface axioms in Lean** | Non-fatal *if transparent* | ✅ adequate — AxiomAudit.lean enumerates; abstract states it is conditional |
| 6 | **MDC strong form** | Non-fatal; already demoted | ✅ DONE — disavowed (cat-state) in §7.6 + README; restated as open superselection question |

**As of HEAD (2026-06): the one load-bearing inconsistency (#1) is resolved and the must-fix calibration set is committed. The remaining gaps (#2, #3) are the genuine research agenda — honest open problems, not contradictions.**

---

## 4a. OPEN PROBLEM 3b — Lorentz covariance of the selection structure (detail)

Equal in rank to the Born/μ problem; the relativistic counterpart of it. **Not** secured by operational no-signaling (no-signaling ≠ Lorentz invariance of the beable). QIQT-H is structurally *better placed* than Bohm — Φ's dynamics is exactly-unitary and already covariant, and λ is non-dynamical (no collapse/guidance event to time-order, so nothing needs a "now") — but that is "better placed," not "proved." Five requirements, increasing difficulty:

1. **λ as a genuinely 4D object** — defined geometrically over the whole spacetime history (a globally consistent decoherent history / bundle section), Poincaré acting geometrically, NO Cauchy slice. "Initial data on Σ₀" reintroduces a preferred frame and fails. (Definitional; discipline.)
2. **Covariant region structure** — $Q_R$, ε(R) on **causal diamonds** via the **Bousso light-sheet** bound, not spatial slices (slice-area is frame-dependent). CPW/Witten scaffolding is already diamond-based + microcausal, so scaffolding is covariant; burden is λ and $A_R$. *Concrete, fixable now — do first.*
3. **The covariance identity (core theorem)** — prove $A_{gR}[U_g\Phi,\, g\!\cdot\!\lambda] = g\cdot A_R[\Phi,\lambda]$ for every Poincaré $g$ ("every frame agrees on the facts"). OPEN.
4. **Foliation-free global consistency** — the family $\{C_R\}$ restriction-compatible on nested diamonds and jointly consistent on spacelike diamonds, with the consistency condition statable in the **causal partial order alone** (no global time function). Operational no-signaling is its observable shadow; the ontic statement must be proved. OPEN.
5. **Poincaré-invariant typicality** — μ over λ must satisfy $\mu(g\cdot S)=\mu(S)$, else a preferred frame re-enters through the statistics even if λ is clean. **Couples to Open Problem 1**: covariant μ is strictly harder than μ; relativistic analogue of Bohm's $|\psi|^2$-equilibrium frame-dependence. HARDEST. OPEN.

Honest riders: 3–5 are genuine open theorems; the Lorentz-friendliness is *bought with* an atemporal / all-at-once (block, mildly retrocausal-flavored) reading of λ (owned, not hidden); this places QIQT-H in the Kent / Wharton–Sutherland family rather than the foliation-bound Bohm/GRW family — a structural advantage that is, as yet, a promissory note.

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

**Status update (2026-06):** items (0)–(6) are all COMMITTED. The load-bearing
inconsistency (1) is resolved. What remains is the genuine research agenda — the
two breakthrough-defining open problems (μ construction; Lorentz covariance,
Open Problem 3b §4a) plus the supporting open problems (ε(R) form, recoherence
stability). These are honest gaps in a research-program paper, not blockers.

---

## 6. What critics will say if we DON'T fix it

> "This is Everett plus a primitive actual-world index and an unspecified Born
> measure, with internally inconsistent Bell language."

The fixes above convert that into the accurate, defensible:

> "An exactly-unitary single-world architecture that *decomposes* the measurement
> problem into a robustness part (decoherence), a finiteness part (holography),
> and two clearly-stated primitives (λ actuality, μ typicality), with a
> machine-checked dependency audit and a sharply-posed open problem (covariant μ)."
