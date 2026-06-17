# Theorem ↔ Paper Index — the machine-checked modular / relative-entropy substrate

**Artifact:** QIQT-H Lean 4 / Mathlib formalization, module aggregator `QIQTH`.
**Pinned commit:** `4720763a7b59`  ·  **Toolchain:** `leanprover/lean4:v4.30.0`.
**Verification status:** full `lake build QIQTH` green; no `sorry`; every theorem below verified by
`QIQTH/AxiomAudit.lean` to depend only on the standard Lean/Mathlib classical foundations
`{propext, Classical.choice, Quot.sound}` (i.e. **no project-specific / interface axioms** — see the
wording note at the bottom).

This index maps the notation of the foundations paper (and the standard CGP/Longo/Araki literature it
cites) to the exact Lean declarations. It is the table to ship with the DOI'd artifact.

---

## A. Finite Araki relative entropy (convention lock)

| Paper / literature object | Lean declaration | File:line |
|---|---|---|
| Relative modular operator `Δ = L_σ R_ρ⁻¹` on Hilbert–Schmidt space; `log Δ = L_{log σ} − R_{log ρ}` | `QIQTH.log_relMod` | `QIQTH/ArakiEntropy.lean:304` |
| **Convention lock** `S_Araki(ρ‖σ) = −⟨ρ^½, (log Δ) ρ^½⟩_HS = tr ρ(log ρ − log σ)` (= Umegaki) | `QIQTH.arakiEntropy_eq_relEntropy` | `QIQTH/ArakiEntropy.lean:330` |

## B. Bounded Tomita–Takesaki (Rieffel–Van Daele standard subspace)

| Paper / literature object | Lean declaration | File:line |
|---|---|---|
| RvD operator `R = P + Q` (`0 ≤ R ≤ 2`), complex-linear repackaging | `QIQTH.StandardSubspaceModular.rvdRC` | `StandardSubspaceModular.lean` |
| `T = √R·√(2−R)` (polar factor) | `QIQTH.StandardSubspaceModular.rvdT` | `StandardSubspaceModular.lean` |
| Modular conjugation `J` (antiunitary, `J²=1`) | `QIQTH.StandardSubspaceModular.modConj` | `StandardSubspaceModular.lean` |
| **`J R J = 2 − R`** (modular reflection, bounded form of `JΔJ=Δ⁻¹`) | `QIQTH.StandardSubspaceModular.modConj_rvdRC_modConj` | `StandardSubspaceModularFlow.lean:712` |
| Bounded Tomita fixedness `J(Tξ) = (2−R)ξ` for `ξ∈𝒦` | `QIQTH.StandardSubspaceModular.modConj_rvdT_of_mem_K` | `StandardSubspaceModularFlow.lean:737` |
| **`Δ^{it} = u_t(R)`** the continuum modular unitary group | `QIQTH.StandardSubspaceModular.modUnitary` | `StandardSubspaceModularFlow.lean:158` |
| group law `Δ^{i(s+t)} = Δ^{is}Δ^{it}`, unitarity, strong continuity | `..modUnitary_add` / `_unitary` / `_stronglyContinuous` | `StandardSubspaceModularFlow.lean:171,201,252` |
| continuous J-conjugation of the functional calculus | `QIQTH.StandardSubspaceModular.modConj_cfcΩ` | `StandardSubspaceModularFlow.lean:1060` |

## C. One-particle CGP relative entropy + positivity

| Paper / literature object | Lean declaration | File:line |
|---|---|---|
| `χ`-style cost `S(ξ) = −∫ log((2−r)/r) dμ^R_ξ` (bounded scalar spectral integral) | `QIQTH.cgpEntropy` | `ModularRelativeEntropy.lean:69` |
| operator-expectation form `S(ξ) = −⟨ξ, g(R) ξ⟩`, `g(R)=log((2−R)/R)` (regular regime) | `QIQTH.cgpEntropy_eq_neg_re_inner` | `ModularRelativeEntropy.lean:191` |
| CGP spectral balance `∫(2−r)²F dμ = ∫r(2−r)F(2−r)dμ` (`ξ∈𝒦`) | `QIQTH.rvdSpec_balance` | `ModularRelativeEntropy.lean:443` |
| **★ Positivity `S(ξ) ≥ 0`** for localized `ξ∈𝒦` | `QIQTH.cgpEntropy_nonneg` | `ModularRelativeEntropy.lean:540` |

## D. Free-field (Fock) modular theory

| Paper / literature object | Lean declaration | File:line |
|---|---|---|
| **`Γ(Δ^{it})`** second-quantized modular flow (Fock Hilbert space) | `QIQTH.Fock.secondQuantModFlowH` | `Fock/SecondQuantModularFlow.lean:101` |
| **Tomita's theorem at field level** `σ_t(W(u)) = W(Δ^{it}u)` | `QIQTH.Fock.secondQuantModFlowH_weylH` | `Fock/SecondQuantModularFlow.lean:167` |
| vacuum is the modular state `⟨Ω,W(Δ^{it}u)Ω⟩=⟨Ω,W(u)Ω⟩` | `QIQTH.Fock.weylVacuum_modFlow_invariant` | `Fock/SecondQuantModularFlow.lean:194` |
| strong continuity of `Γ(Δ^{it})` on coherent vectors | `QIQTH.Fock.secondQuantModFlowH_continuous_expVec` | `Fock/SecondQuantModularFlow.lean:256` |

## E. Coherent-state relative modular operator, Connes cocycle, entropy reduction

| Paper / literature object | Lean declaration | File:line |
|---|---|---|
| relative modular operator `Δ_{W(f)Ω|Ω}^{it} = W(f)Γ(Δ^{it})W(f)*` | `QIQTH.Fock.relModFlowH` | `Fock/RelativeModularFlow.lean:55` |
| Connes cocycle `[Dω_{W(f)Ω}:Dω_Ω]_t = W(f)W(−Δ^{it}f)` | `QIQTH.Fock.connesCocycleH` | `Fock/RelativeModularFlow.lean:91` |
| cocycle chain rule `u_{s+t} = u_s σ_s(u_t)` | `QIQTH.Fock.connesCocycleH_chain` | `Fock/RelativeModularFlow.lean:103` |
| vacuum characteristic function `⟨Ω,Δ_rel^{it}Ω⟩ = exp(⟨f,Δ^{it}f⟩−⟨f,f⟩)` | `QIQTH.Fock.relModFlow_vacuum_char` | `Fock/RelativeModularFlow.lean:126` |
| **★★ Entropy reduction** `d/dt|₀⟨Ω,Δ_rel^{it}Ω⟩ = −i·S_CGP(f)`, i.e. `S_Araki(ω_{W(f)Ω}‖ω_Ω) = S_CGP(f)` | `QIQTH.Fock.hasDerivAt_relModFlow_vacuum` | `Fock/RelativeModularFlow.lean:158` |
| supporting: differentiation under the spectral integral `d/dt|₀⟨ξ,U_t ξ⟩=i∫g dμ` | `QIQTH.hasDerivAt_inner_modUnitary` | `ModularRelativeEntropy.lean:457` |

---

## Reproduce the axiom check

```
cd lean/mathlib && ~/.elan/bin/lake build QIQTH.AxiomAudit
```
emits, for every theorem above, `'<name>' depends on axioms: [propext, Classical.choice, Quot.sound]`.

## ⚠ Wording note (for external / paper-facing use)

`propext`, `Classical.choice`, `Quot.sound` ARE the standard foundational axioms of classical Lean/Mathlib.
The phrase "**axiom-free**" in this corpus means **"no project-specific or interface axioms beyond those
standard classical foundations."** For referee-facing prose use:
> *"machine-checked in Lean 4/Mathlib with no `sorry` and no axioms beyond the standard classical
> foundations (`propext`, `Classical.choice`, `Quot.sound`)."*

## Explicit NON-goals of this artifact (do not cite as formalized)

The holographic capacity axiom **FQ** / `S_ren ≤ Q_R`; the CPW/Witten Type II crossed product; the
**Macroscopic Definiteness Conjecture (H2)**; Donald's identity in the Type II/semifinite setting; the
Theorem-6 Fano step; Born-from-typicality. The formalization is the standard modular/relative-entropy
substrate for the free-field coherent-state case — **not** the paper's novel physical postulates.
