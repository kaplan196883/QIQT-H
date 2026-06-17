# Formalization scope note — drop-in for the foundations paper

Per the GPT-5.5-pro consult (2026-06-12, `paper_strategy/46`-adjacent / memory
`project_main_article_packaging`): the Lean formalization strengthens the **mathematical substrate** of the
paper (the Araki / modular / CGP machinery) but is **orthogonal to the load-bearing physical novelty** (FQ,
H2, Theorem 6, Born). The text below is the scope-control insert. Place it in the mathematical preliminaries
or a short appendix; it is the exact wording that maximizes credibility and prevents overclaiming.

---

## Prose paragraph (ready to LaTeX-ify)

> **Machine-checked mathematical substrate.** A companion Lean 4 / Mathlib formalization
> [cite the formalization paper / artifact DOI] independently verifies the bounded modular-theoretic and
> coherent-state relative-entropy results used here as standard mathematical input. Specifically it
> machine-checks: the finite Araki/Umegaki convention lock
> $S_{\mathrm{Araki}}(\rho\|\sigma)=\operatorname{tr}\rho(\log\rho-\log\sigma)$; the bounded
> Rieffel–Van Daele standard-subspace Tomita–Takesaki construction (modular conjugation $J$, the relation
> $JRJ=2-R$, the continuum modular unitary group $\Delta^{it}$ and its strong continuity); the
> Casini–Grillo–Pontello one-particle relative entropy as a bounded scalar spectral integral together with
> its **positivity** $S(\xi)\ge 0$ for localized $\xi$; the free-field (Fock) modular flow
> $\Gamma(\Delta^{it})$ with Tomita's relation $\sigma_t(W(u))=W(\Delta^{it}u)$ and the vacuum as the modular
> state; the coherent-state relative modular operator
> $\Delta_{W(f)\Omega|\Omega}^{it}=W(f)\Gamma(\Delta^{it})W(f)^\ast$ with its Connes cocycle
> $[D\omega_{W(f)\Omega}:D\omega_\Omega]_t=W(f)W(-\Delta^{it}f)$ and cocycle chain rule; and the **entropy
> reduction** $S_{\mathrm{Araki}}(\omega_{W(f)\Omega}\|\omega_\Omega)=S_{\mathrm{CGP}}(f)$ identifying the
> coherent-state Araki relative entropy with the one-particle CGP entropy. The development carries no
> \texttt{sorry} and, as reported by \texttt{\#print axioms}, depends only on the standard classical
> foundations of Lean/Mathlib (\texttt{propext}, \texttt{Classical.choice}, \texttt{Quot.sound}); in
> particular it introduces no project-specific or interface axioms.
>
> This formalization deliberately does **not** cover the framework's distinctive physical content: the
> holographic capacity axiom (FQ) and the bound $S_{\mathrm{ren}}\le Q_R$, the Chandrasekaran–Penington–Witten
> crossed-product Type II construction, the Macroscopic Definiteness postulate (H2), the Donald/Fano argument
> of Theorem~6, and the Born-rule-from-typicality problem. What is verified is the modular and
> relative-entropy *calculus* on which $\chi_R$ rests, for the free-field coherent-state case — **not** the
> dressed Type II regional content map itself, nor the finite-capacity postulate or the macroscopic-definiteness
> conjecture, which remain explicit physical assumptions of this paper.

> **Verified-scope caveat (GPT-5.5-pro, 2026-06-12).** Phrase this as: *"the modular/relative-entropy calculus
> motivating $\chi_R$ is machine-checked in finite and free coherent sectors; the actual Type II regional
> content map is not."* Do not let "machine-checked substrate" be read as machine-checking the dressed Type II
> framework. Two further precisions: $\log\!\big((2-r)/r\big)$ is bounded only in the regular regime
> $\sigma(R)\subseteq[a,2-a]$ (the achievement is "no unbounded $\log\Delta$ is constructed", not a bounded
> integrand); and the relative-modular identity $\Delta_{u\Omega|\Omega}^{it}=u\,\Delta^{it}u^\ast$ requires
> $u=W(f)\in M$ (i.e.\ $f$ in the real standard subspace) under a stated slot convention.

## Companion "what is / is not formalized" table

| Component | Status in the formalization |
|---|---|
| Araki/Umegaki convention $S_{\mathrm{Araki}}=\operatorname{tr}\rho(\log\rho-\log\sigma)$ | **Machine-checked** |
| Bounded Tomita–Takesaki ($J$, $JRJ=2-R$, $\Delta^{it}$, strong continuity) | **Machine-checked** |
| CGP one-particle relative entropy + positivity $S(\xi)\ge0$ | **Machine-checked** |
| Fock modular flow $\Gamma(\Delta^{it})$, $\sigma_t(W(u))=W(\Delta^{it}u)$ | **Machine-checked** |
| Coherent-state relative modular operator + Connes cocycle + chain rule | **Machine-checked** |
| Entropy reduction $S_{\mathrm{Araki}}(\omega_{W(f)\Omega}\|\omega_\Omega)=S_{\mathrm{CGP}}(f)$ | **Machine-checked** |
| Holographic capacity axiom FQ; $S_{\mathrm{ren}}\le Q_R$ | Not formalized (postulate) |
| CPW/Witten crossed-product Type II construction | Not formalized (borrowed) |
| Macroscopic Definiteness Conjecture (H2) | Not formalized (central postulate) |
| Donald's identity (Type II) + Fano step of Theorem 6 | Not formalized |
| Decoherence / Quantum Darwinism (H3) | Not formalized |
| Born rule from typicality | Not formalized (open problem) |

## Upgrades this licenses in the paper body

- The finite-case sentence "this reduces to the usual Umegaki entropy" → **Proposition** (machine-checked).
- The cited CGP/Longo coherent-state entropy formula → **Theorem** (machine-checked, with explicit hyps).
- $\sigma_t(W(u))=W(\Delta^{it}u)$ and the cocycle $[D\omega:D\omega]_t=W(f)W(-\Delta^{it}f)$ → stated as
  machine-checked background.
- $\chi_R$ positivity may be cited as a checked instance (free-field coherent sector).

**Do NOT upgrade:** FQ, $S_{\mathrm{ren}}\le Q_R$, H2, Theorem 6 ("machine-checked"), H3, Born.
