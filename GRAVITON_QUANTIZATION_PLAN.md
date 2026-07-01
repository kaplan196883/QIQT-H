# Quantizing the free graviton — the campaign

**Goal:** canonically quantize the free linearized graviton, building up from the two-helicity CCR algebra to the
momentum-space field and its propagator, each increment axiom-free (std-3), budget 0, green, one commit. Reuses the
kinematics (`EmergentDynamics.lean` G11a/b: the helicity ±2 polarizations `e_±`, the propagator numerator) and the
classical field EOM (G11c). Honest scope labels stay (free field; single-mode → momentum continuum; classical ≠
interacting) — but nothing here is postponed as "too hard"; each rung is built.

## Where the graviton is now (verified)
Classical free graviton COMPLETE in Lean: 2 helicity-±2 polarizations (exactly 2, gauge quotient), spin-2 eigenvalue
form, masslessness `k²=0`, the propagator numerator (physical-state projector), and the wave equation `∂²_t = ∂²_z`
on an actual field. The quantization core is now started.

## Increments

- [x] **Q1 — the two-helicity bosonic CCR algebra ✅ (`QIQTH/GravitonQuantization.lean`, `QIQTH.GravitonQuant`).**
  Canonical quantization of the free graviton at a single momentum mode, realized concretely on the Bargmann–Fock
  space `Fock = ℂ[X₀,X₁] = MvPolynomial (Fin 2) ℂ` (one variable per helicity): `creat i = (X_i·)` (a†),
  `annih i = ∂/∂X_i` (a). Proved: **`ccr`** `[a_i,a†_j] = δ_ij` (the defining CCR), **`annih_comm`** `[a_i,a_j]=0`
  (Clairaut, by MvPolynomial induction — Mathlib has no `pderiv_comm`), **`creat_comm`** `[a†_i,a†_j]=0`,
  **`annih_vacuum`** `a_i|0⟩=0` (vacuum `|0⟩=1`), **`one_particle_state`** `|1_i⟩=a†_i|0⟩=X_i`,
  **`number_one_particle`** `N_i|1_j⟩=δ_ij|1_i⟩` (the number operator `N_i=a†_i a_i` counts occupation). Helicity
  labels: `0↔e₊` (+2), `1↔e₋` (−2). All [AF] std-3, pinned, budget 0.
- [x] **Q2 — the number operator + occupation eigenstates ✅.** `numberOp i = creat i ∘ₗ annih i` (a `LinearMap`),
  `numberOp_apply` (`N_i p = X_i·∂_i p`); **`numberOp_pow`** — the monomials `X_i^n = |n_i⟩` diagonalize `N_i` with
  eigenvalue `n` (`N_i|n_i⟩ = n|n_i⟩`, spectrum = ℕ = bosonic occupation); `numberOp_vacuum` (`N_i|0⟩=0`),
  `numberOp_one_particle` (`N_i|1_j⟩=δ_ij|1_i⟩`). All [AF] std-3, pinned, budget 0.
- [x] **Q3 — the Hamiltonian + zero-point energy ✅.** `totalNumber = N₀+N₁`; `hamiltonian ω = ω•(N₀+N₁+1)`;
  **`hamiltonian_vacuum`** `H|0⟩=ω|0⟩` (the graviton **zero-point energy** ω), **`hamiltonian_one_particle`**
  `H|1_i⟩=2ω|1_i⟩` (one quantum ω above zero-point). All [AF] std-3, pinned, budget 0. (Full monomial spectrum
  `H|m,n⟩=ω(m+n+1)|m,n⟩` = a follow-on.)
- [x] **Q4 — helicity as the little-group charge ✅.** `helicityOp = 2(N₀ − N₁)`; **`helicityOp_plus`** `J|1₀⟩=+2|1₀⟩`
  (mode 0 = `e₊`, helicity +2), **`helicityOp_minus`** `J|1₁⟩=−2|1₁⟩` (mode 1 = `e₋`, helicity −2),
  `helicityOp_vacuum` `J|0⟩=0`. Ties the quantized occupation to the kinematic helicity-±2 eigenstates
  (`EmergentDynamics` `eR`/`eL_helicity`). All [AF] std-3, pinned, budget 0.
- [x] **Q5 — ladder operators + coherent states ✅.** `creat_pow` (`a†_i|n⟩=|n+1⟩`, raising) + `annih_pow_succ`
  (`a_i|n+1⟩=(n+1)|n⟩`, lowering) on the polynomial rep; **`coherent α = e^{αX}`** in the Bargmann–Fock completion
  `ℂ⟦X⟧` (single mode; the exponential isn't a polynomial) with **`annih_coherent`** `a|α⟩=α|α⟩` — the coherent
  state is an eigenstate of the annihilation operator `a=d/dX`, the quantum→classical bridge (definite amplitude
  `α`). All [AF] std-3, pinned, budget 0. (Recovering the G11c classical wave as the field expectation awaits Q6.)
- [ ] **Q6 — multi-mode: the momentum continuum (frontier scoping).** Index the CCR by momentum `k` (add `X_{k,λ}`),
  the field `h_{μν}(x) = ∑_λ ∫ (a_λ(k) e^λ e^{ikx} + h.c.)`; the two-point function/propagator as a vacuum
  expectation. Built one mode at a time; the free field is the (restricted) tensor product of single-mode Fock
  spaces.

## Discipline
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green; `#print axioms` std-3; `bash
scripts/axiom_budget_check.sh` budget 0; wire into `QIQTH.lean` + `AxiomAudit.lean`; one commit per increment with
the `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>` trailer; push via schannel; update this checklist +
`LEAN_RESULTS_INVENTORY.md`. Honest labels: free graviton; single-mode → continuum is additive; classical ≠
interacting; NOT a claim of quantum gravity (this is standard free-field QFT, machine-checked).

## Progress log
- **2026-07-02 — Q1 ✅** the two-helicity bosonic CCR algebra on the Bargmann–Fock space; the canonical
  quantization of the free graviton's polarization d.o.f. All [AF] std-3, budget 0.
- **2026-07-02 — Q2 ✅** the number operator `N_i=a†_i a_i`; the occupation eigenstates `X_i^n=|n_i⟩` with
  `N_i|n_i⟩=n|n_i⟩` (spectrum ℕ); vacuum/one-particle occupation. All [AF] std-3, budget 0.
- **2026-07-02 — Q3 ✅** the Hamiltonian `H=ω(N₀+N₁+1)`; the graviton zero-point energy `H|0⟩=ω|0⟩` and the
  one-graviton energy `H|1_i⟩=2ω|1_i⟩`. All [AF] std-3, budget 0.
- **2026-07-02 — Q4 ✅** the helicity operator `J=2(N₀−N₁)`; one-graviton states carry helicity `±2`
  (`J|1₀⟩=+2|1₀⟩`, `J|1₁⟩=−2|1₁⟩`), tying the occupation to the kinematic spin-2. All [AF] std-3, budget 0.
- **2026-07-02 — Q5 ✅** the ladder operators (raising `a†|n⟩=|n+1⟩`, lowering `a|n+1⟩=(n+1)|n⟩`); the coherent
  state `|α⟩=e^{αX}` in the Bargmann–Fock completion `ℂ⟦X⟧` with `a|α⟩=α|α⟩` (the quantum→classical bridge).
  All [AF] std-3, budget 0.
