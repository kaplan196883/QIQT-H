# Scoping: finite-dimensional Effect (POVM) Gleason in Lean

*Target: prove the finite-dimensional Busch / Caves–Fuchs–Manne–Renes effect-Gleason
theorem, axiom-free, to discharge the project's Born-uniqueness inputs and complete the
Stage-1 "minimal breakthrough" of `PRIZE_ROADMAP.md`. Module: `QIQTH/EffectGleason.lean`.*

## Why this is the highest-yield bounded target

- **Real theorem, not an interface.** Unlike the AQFT/Type-III inputs, this is provable
  outright in finite dimensions.
- **Zero open-math (Wall-3) dependency.** Everything bottoms out in finite matrices +
  Mathlib's Hermitian spectral theorem.
- **Directly axiom-reducing** (see "Discharges" below): plausibly 37 → ~34.
- **Citable on its own:** finite-dimensional POVM-Gleason is not in Mathlib.

## The fork: Busch effect-Gleason, NOT original projection-Gleason

- **Route A (original Gleason 1957, projections/frame functions).** Nonnegative frame
  functions on the sphere (dim ≥ 3) are `⟨x,Tx⟩`. Hard: requires proving regularity of
  frame functions on S² via degree-≤2 spherical harmonics. **Do not attempt.**
- **Route B (Busch 2003 / CFMR 2004, effects/POVMs). ← TARGET.** A generalized probability
  measure on effects is `tr(ρ·)`. Elementary, finite-dimensional, works even in dim 2,
  because effects contain `tE` for `t∈[0,1]` so additivity ⇒ linearity *directly*. This is
  the route `PRIZE_ROADMAP.md` already committed to.

## Theorem statement

> **Finite Effect-Gleason.** For `μ : Matrix (Fin d) (Fin d) ℂ → ℝ` with, on effects
> `IsEffect E := E.PosSemidef ∧ (1-E).PosSemidef`:
> (i) `μ 1 = 1`; (ii) `0 ≤ μ E` for every effect `E`; (iii) `μ(E+F) = μ E + μ F` whenever
> `E`, `F`, `E+F` are effects (coexistent) — then there is a **unique** `ρ` with
> `ρ.PosSemidef`, `ρ.trace = 1`, and `μ E = (ρ * E).trace` for every effect `E`.

This is the **mixed-state** generalization of the pure-state result already in
`GleasonSelector.positive_ray_certain_forces_born` (which assumes linearity + ray-certainty
and yields a pure state `|ψ⟩⟨ψ|`).

## Proof skeleton

**G1 — additive-on-effects ⇒ ℝ-homogeneous (the load-bearing new core).**
- `μ 0 = 0` (from `μ(I) = μ(I+0) = μ I + μ 0`).
- **Monotonicity:** `E ≤ F` (i.e. `(F-E)` an effect) ⇒ `μ E ≤ μ F` (since `μ F = μ E + μ(F-E)`, `μ(F-E) ≥ 0`).
- **Natural-multiple:** for `E` effect and `n ≥ 1`, `(1/n)•E` summed `n` times equals `E`
  and every partial sum `(k/n)•E ≤ E ≤ I` is an effect, so by induction
  `μ E = n · μ((1/n)•E)`, i.e. `μ((1/n)•E) = μ E / n`.
- **Rational homogeneity:** `μ((m/n)•E) = (m/n)·μ E` for `0 ≤ m ≤ n`.
- **Real homogeneity:** squeeze rationals from below/above using monotonicity
  (`(p)•E ≤ (t)•E ≤ (q)•E` for rationals `p ≤ t ≤ q`) ⇒ `μ(t•E) = t·μ E`, `t∈[0,1]`.

**G2 — extend to an ℝ-linear functional `Λ` on Hermitians.**
- Every Hermitian `H` splits `H = H₊ − H₋` (positive/negative spectral parts via
  `Matrix.IsHermitian.spectral_theorem`), each rescaled by `1/‖H‖` into an effect.
- Define `Λ H := ‖H‖·(μ(H₊/‖H‖) − μ(H₋/‖H‖))`; well-defined and ℝ-linear from G1 + additivity.

**G3 — Riesz representation on Hermitians.**
- Hermitian `d×d` matrices form a real inner-product space under `⟨A,B⟩ := (A*B).trace`
  (real because `A,B` Hermitian ⇒ `tr(AB)∈ℝ`); finite-dim Riesz gives a unique Hermitian `ρ`
  with `Λ H = (ρ*H).trace`.

**G4 — positivity + normalization.**
- `μ P ≥ 0` on rank-one projections `P=|x⟩⟨x|` ⇒ `⟨x,ρx⟩ ≥ 0` ⇒ `ρ.PosSemidef`.
- `μ 1 = 1` ⇒ `ρ.trace = 1`. Uniqueness from non-degeneracy of the trace form.

## Reuse from `GleasonSelector` (already axiom-free)

- `positive_functional_hermitian` — positive linear functional is Hermitian (`*`-property). **→ G3.**
- `psd_null_radical` — Cauchy–Schwarz null-radical. **→ G1/G4.**
- `rankOne_sandwich`, `born`, `born_add/smul/one` — rank-one representation algebra.
- `positive_ray_certain_forces_born` — the **pure-state** special case (G is its mixed
  generalization, dropping the certainty hypothesis).

So G3/G4 largely reuse existing lemmas; **the genuinely new work is G1 (Cauchy + bound) and
G2 (spectral split + well-definedness).**

## Mathlib inventory

- ✅ `Matrix.IsHermitian.spectral_theorem`, `LinearMap.IsSymmetric.eigenvectorBasis` (G2).
- ✅ `Matrix.PosSemidef` with `.zero`, `.one`, `.add`, nonneg-scalar `.smul` (effect closure).
- ✅ `Matrix.trace`, trace cyclicity; finite-dim Riesz / `Module.Dual` (G3).
- ❌ Gleason, frame functions, POVM/effect/density abstractions, Mackey–Gleason — none.

## Discharges (honest count)

- **Directly:** the finite-dimensional case of
  `TypicalityMackeyGleason.mackey_gleason_to_trace_density` (**1 axiom**). Caveat: that axiom
  is stated at Type-II generality; finite Gleason discharges its finite-dim/Type-I shadow —
  which is exactly the regime where `CoreNoCollapse`/`CapacityModel`/`RecordGleason` live, so
  for the finite record model it is a full discharge. Continuum Bunce–Wright stays a named
  input.
- **Makes retirable:** the `GoldsteinStruyveFinDim` route (**2 axioms**:
  `step1_schur_classification`, `step3_tensor_multiplicativity`) — an alternative finite-dim
  Born-uniqueness spine that Gleason supersedes (re-route `canonical_ic_measure_principle`).
- **Completes Stage 1:** discharges the `hsupp` (ray-support) hypothesis of
  `born_is_forced` from first principles (effect-additivity ⇒ linearity).
- **Net plausible:** 37 → ~34. *Untouched:* the 31 entropy/Type-II axioms
  (Araki/Donald/DPI/EntropyBridge/RelEntPositivity) — orthogonal to Gleason.

## Difficulty & risk

- ~300–600 lines; a few focused sessions; **no Wall-3 dependency**.
- Riskiest: **G1** (the ℚ→ℝ homogeneity upgrade — needs the right monotonicity squeeze) and
  **G2** (well-definedness of the extension across effect decompositions).
- G3/G4 mostly reuse `GleasonSelector` lemmas.

## Staged Lean plan (`QIQTH/EffectGleason.lean`) — progress

1. **G1 — DONE (axiom-free, committed).** `IsEffect`, effect closure
   (`isEffect_zero/one/smul/sub`), `EffectMeasure` (normalized/nonneg/coexistent-additive),
   `map_zero`, `mono`, `map_smul_add`, **`cauchy_unit_interval`** (additive + monotone on
   `[0,1]` ⇒ ℝ-linear, via the `⌊t·n⌋` squeeze) and **`map_smul`** (`μ(t•E) = t·μ E`). The
   load-bearing real-analysis core — the part original projection-Gleason needs spherical
   harmonics for — is complete.
2. **G2 — NEXT, with an identified Mathlib gap.** Hermitian split + `Λ` extension. **Blocker
   to build first:** a PSD **Löwner-order bound** `∀ A, A.PosSemidef → ∃ c ≥ 0, (c•1 −
   A).PosSemidef` — *not in Mathlib* (only `PosSemidef.trace_nonneg` /
   `conjTranspose_mul_mul_same` exist). Must be derived from `Matrix.IsHermitian.
   spectral_theorem` (eigenvalues `≤ trace`, so `c := trace A` works), as a reusable
   `Matrix.PosSemidef` order lemma. Then: extend `μ` to the PSD cone (`ν A := c·μ(A/c)`,
   well-defined by `map_smul`), to Hermitians (`Λ H := ν H₊ − ν H₋`), then ℂ-linearly.
3. **G3:** trace-form Riesz **via matrix units** — `ρ` defined by `ρ j i := Λ (single i j)`,
   then `Λ M = (ρ*M).trace` by `matrix_eq_sum_single` + linearity + `trace_single_mul`
   (avoids abstract Riesz). Mathlib has the matrix-unit API (`Matrix.single`,
   `matrix_eq_sum_single`, `trace_single_eq_same`).
4. **G4:** positivity (`μ` on rank-one projections ⇒ `ρ.PosSemidef`) + normalization
   (`μ 1 = 1 ⇒ ρ.trace = 1`); uniqueness from trace-form non-degeneracy.
5. **Capstone `finite_effect_gleason`** + re-route `TypicalityMackeyGleason` finite case and
   retire the Goldstein–Struyve axioms; update `AxiomAudit.lean` and the budget.

**STATUS: COMPLETE (2026-06).** All of G1–G4 are proved axiom-free in `EffectGleason.lean`;
the capstone `finite_effect_gleason` is the finite-dimensional effect (Busch) Gleason
theorem: a normalized, nonnegative, coexistent-additive functional `μ` on effects equals
`μ E = tr(ρ E)` for a density matrix `ρ` (PSD, trace 1). The full ladder, all standard-three
axioms only:
- **G1** — `cauchy_unit_interval` (additive + monotone on [0,1] ⇒ ℝ-linear), `map_smul`.
- **G2** — PSD/Hermitian Löwner bounds `posSemidef_sumNorm_sub(_herm)` (the lemmas absent
  from Mathlib, proved without the spectral theorem), cone extension `coneExt` (ν), and the
  ℝ-linear Hermitian extension `hermExt` (Λ): `hermExt_add`, `hermExt_smul`, `hermExt_nonneg`.
- **G3** — complexification `reHerm`/`imHerm`, ℂ-linear `cExt` (Λ_ℂ): `cExt_add`, `cExt_smul`;
  trace (Riesz) representation `cExt_trace` (`Λ_ℂ M = tr(ρM)`, `ρ a b := Λ_ℂ(E_{ba})`).
- **G4** — `rho_isHermitian`, `rho_posSemidef`, `rho_trace`, and `finite_effect_gleason`.

This is the Born rule derived from positivity + additivity alone, in finite dimension. **Out
of scope (unchanged):** the continuum Type-II/III Bunce–Wright generalization (Wall 1 deeper),
a named interface input; and retiring the project's finite Mackey-Gleason / Goldstein–Struyve
Born-uniqueness axioms by routing `canonical_ic_measure_principle` through this capstone
(a follow-up refactor, 37 → ~34).
