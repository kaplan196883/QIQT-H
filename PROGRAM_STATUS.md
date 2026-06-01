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
5. **Poincaré-*equivariant* typicality** — μ over λ must satisfy $g_*\mu_\Phi = \mu_{U_g\Phi}$ (equivariance, NOT strict invariance $\mu(g\cdot S)=\mu(S)$ — too strong, since Born depends on Φ; invariance is the special case of Poincaré-invariant Φ). **Couples to Open Problem 1**: an equivariant μ_Φ is strictly harder than a single-frame μ; relativistic analogue of Bohm's $|\psi|^2$-equilibrium frame-dependence. HARDEST. OPEN.

Honest riders: 3–5 are genuine open theorems; the Lorentz-friendliness is *bought with* an atemporal / all-at-once (block, mildly retrocausal-flavored) reading of λ (owned, not hidden); this places QIQT-H in the Kent / Wharton–Sutherland family rather than the foliation-bound Bohm/GRW family — a structural advantage that is, as yet, a promissory note.

**Proposed construction (intended line of attack; paper §11.4):**
- **Dirac, not Schrödinger.** Φ is a relativistic quantum field (Dirac field for matter), with a genuine Poincaré action U_g via the spinor rep S(Λ). Required, not cosmetic: req-3's identity A_{gR}[U_gΦ,g·λ]=g·A_R is only statable with a covariant U_g, which Galilean Schrödinger lacks. Also: the Dirac field is the natural matter content of the CPW/Witten AQFT algebras — this just names the QFT the scaffolding already presupposes. (Carrier is the field, not the one-particle Dirac eq, which has Klein/negative-energy pathologies.)
- **λ = holographic boundary data on causal-diamond screens.** C_D = A_D[Φ,λ] reconstructed from λ|_{∂D}. Forcing motivation: the capacity Q_R = A(∂R)/4ℓ_P² is itself a boundary quantity, so the fact that spends it should live on the boundary. Discharges three requirements at once: (1) ∂D is a covariant slice-free object (boundary data ≠ Cauchy data); (2) Q_R and λ share the screen; (4) boundary data on nested/overlapping diamonds glues by edge-agreement → order-theoretic gluing, no global time.
- **Honest status:** "boundary data fixes the bulk record" = holographic bulk reconstruction (HKLL / entanglement-wedge), subtle and non-literal even in AdS/CFT, open for general causal diamonds. So the proposal *relocates* req 3–4 to the sharper theorem "does holographic screen data on a causal diamond uniquely + covariantly fix the λ-selected bulk record?" — not yet solved, but λ now has a concrete covariant home and Φ a covariant U_g.

**GPT-5.5-pro sharpening (paper §11.4 has the full version):**
- **Correction A — gluing is over BULK OVERLAPS, not screen intersections.** For K⊂D, ∂K ⊄ ∂D, so "edge agreement" is too weak. Correct condition: ρ_{D,L}(C_D)=ρ_{E,L}(C_E) ∀ L⊂D∩E. Formally: X_Φ(D)=Stone(B_Φ(D)) a presheaf on the causal-diamond poset; λ = a GLOBAL SECTION λ∈Γ(X_Φ)=lim X_Φ(D). Req 4 = "a global section exists."
- **Correction B — obstruction is ROBERTS NET COHOMOLOGY, not plain topology.** Gluing cocycle [g_{ij}]∈Ȟ¹(Aut(X_Φ)) (→H² gerbe if projective); same machinery that classifies DHR superselection sectors. Split property + Haag duality HELP (finite pointer algebras, causal complements) but do NOT trivialize it — the split inclusion is non-canonical, breaks covariance unless a Poincaré-natural split is proved. Kochen–Specker: λ selects ONE realm, not a global valuation.
- **Correction C — req 5 is EQUIVARIANCE not invariance** (folded into req 5 above).
- **Req 3 becomes automatic** from equivariant naturality: build X_Φ naturally from the covariant net over Diam⋊G (G = Poincaré / its spin cover ISpin(1,3) for Dirac), λ an equivariant global section, then A_{gD}[U_gΦ,gλ]=γ_g(λ_D)=g·A_D[Φ,λ] in one line. BW/Borchers give modular covariance. Breaks if: non-canonical pointer basis / split, frame-dependent ε(D), gauge/edge modes, tie-breaking.
- **The measure: the DECOHERENCE FUNCTIONAL is the answer.** μ_Φ(Cyl(α))=D_Φ(α,α)=⟨Φ|C_α†C_α|Φ⟩=τ_D(h_{Φ,D}P_α), extended by Kolmogorov–Carathéodory. Covariant via C_{gα}=U_gC_αU_g⁻¹ ⇒ equivariance; Born by construction. Type II trace τ_D is only a CARRIER (writes local Born weights, doesn't pin μ); BW/KMS geometric only for wedges/CFT-diamonds.
- **No-signaling survives conditional on a SCREEN-LOCAL MARGINAL LEMMA**: μ-pushforward of λ to any local instrument = AQFT Born state, independent of spacelike settings. Forced reformulation: if λ is the whole history (incl. settings), Bell MI ρ(λ|a,b)=ρ(λ) is ill-posed → restate MI for the PAST/common-cause component of λ.
- **7 repairs to borrow Gell-Mann–Hartle/Isham-HPO wholesale:** (1) realm-selection / Dowker–Kent; (2) contrary inferences → recorded histories only; (3) frame-dependent time-ordered class operators → Schwinger–Keldysh / Tomonaga–Schwinger; (4) Type III₁ exact-projection obstruction; (5) approximate decoherence needs ε(D) stable under gluing; (6) **holographic capacity log#Atoms(B_Φ(D))≤Q_D is NOT automatic in GMH — QIQT-H's new ingredient**; (7) the MI reformulation.

**THE LINCHPIN — Poincaré-equivariant holographic recorded-history sheaf theorem (paper §11.4):** for a covariant Haag–Kastler net (locality, isotony, time-slice, Haag duality, split/nuclearity, BW covariance) and every admissible Φ, ∃ finite Boolean record algebras B_Φ(D) with log#Atoms≤Q_D and DecErr≤ε(D), boundary reconstruction B_{Φ,∂}(D)≅B_Φ(D), a sheaf X_Φ over Diam, a nonempty Γ(X_Φ), a Born/decoherence-functional measure μ_Φ with Kolmogorov consistency, Poincaré equivariance, and no-signaling marginals. Then A_D[Φ,λ]=λ_D (mere evaluation) and req-3 covariance is immediate. **This is the real target of OP3b**; proving it even for FREE FIELDS first would convert the Lorentz promissory note into a result.

**Lean formalization target (genuinely startable now):** prove, in Lean, "equivariant naturality + Kolmogorov consistency ⟹ a covariant single-outcome selection map" — the poset/sheaf layer (Diam poset, presheaf X_Φ, restriction maps, Γ as a projective limit, Kolmogorov consistency as a finitely-additive set function), with the evaluation-gives-covariance one-liner PROVED (same shape as the already-machine-checked MarginalLocality.lean). Deferred to named interface axioms (same strategy as AxiomAudit.lean): existence of finite record algebras + holographic bound (hyp 1–3), boundary reconstruction (2), the decoherence-functional measure + σ-additive extension (6), no-signaling marginal lemma (9) — all on Type III₁ / Tomita–Takesaki / Haagerup-L^p analysis beyond current Mathlib. Deliverable = machine-checked conditional theorem + explicit AQFT axiom audit.

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
