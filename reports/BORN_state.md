# QIQT-H state report — BORN
*Target 1 — QIQT-H compatible with Born (spine + no-go audits)*

_Generated 2026-06-23 21:22 UTC · git `fd82276` · 13 theorems_

## Axiom status
- **Project-specific axioms: 0** (target 0)
- All theorems axiom-free (only `propext`, `Classical.choice`, `Quot.sound`): **YES**

| theorem | axioms |
|---|---|
| `QIQTH.BornJoinGleason.finite_noCollapseBorn_fromNoncontextuality` | ✓ standard-3 only |
| `QIQTH.EffectGleason.EffectMeasure.finite_effect_gleason` | ✓ standard-3 only |
| `QIQTH.GleasonSelector.positive_ray_certain_forces_born` | ✓ standard-3 only |
| `QIQTH.RefinementBorn.continuous_additive_fMeasure_eq_born` | ✓ standard-3 only |
| `QIQTH.RecordGleason.decoherent_partition_additive` | ✓ standard-3 only |
| `QIQTH.BornJoin.ActualEnsemble.finite_noCollapseBornRepresentation` | ✓ standard-3 only |
| `QIQTH.BornMeasureUniqueness.product_born_measure_unique` | ✓ standard-3 only |
| `QIQTH.BornTypicalityFinite.chebyshev_freq` | ✓ standard-3 only |
| `QIQTH.BornTypicality.qiqth_born_typicality_conditional` | ✓ standard-3 only |
| `QIQTH.NoBornFromNothing.born_distribution_realizable_conditional` | ✓ standard-3 only |
| `QIQTH.NoConcentration.decoherence_does_not_concentrate` | ✓ standard-3 only |
| `QIQTH.EquivarianceGap.support_preservation_does_not_imply_measure_preservation` | ✓ standard-3 only |
| `QIQTH.OperationalNoGo.operational_data_insufficient` | ✓ standard-3 only |

## Theorems — facts from Lean

### `QIQTH.BornJoinGleason.finite_noCollapseBorn_fromNoncontextuality`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
∃ ρ,
  ρ.PosSemidef ∧
    ρ.trace = 1 ∧
      (∀ (ω : E.Ω), ∃! h, ∀ (t : Fin n), ∃ r ∈ (E.V ω t).config.active, (E.V ω t).ctx.valueOf r = h t) ∧
        (∀ (a : Fin m), E.p a = (ρ * P a).trace.re) ∧
          (∀ (h : Fin n → Fin m), E.P.massSet {ω | E.actualHist ω = h} = QIQTH.BornTypicalityFinite.w E.p h) ∧
            E.P.massSet {ω | (↑n * ε) ^ 2 ≤ (QIQTH.BornTypicalityFinite.count k (E.actualHist ω) - ↑n * E.p k) ^ 2} ≤
              E.p k * (1 - E.p k) / (↑n * ε ^ 2)
```
- **hypotheses (4):**
```
1. hP : ∀ (a : Fin m), QIQTH.EffectGleason.IsEffect (P a)
2. hcal : ∀ (a : Fin m), M.μ (P a) = E.p a
3. hε : 0 < ε
4. hn : 0 < n
```
- **data binders (8):** `m`, `n`, `d`, `E`, `M`, `P`, `k`, `ε`

### `QIQTH.EffectGleason.EffectMeasure.finite_effect_gleason`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
∃ ρ,
  ρ.PosSemidef ∧
    ρ.trace = 1 ∧ ∀ (E : Matrix (Fin d) (Fin d) ℂ), QIQTH.EffectGleason.IsEffect E → ↑(m.μ E) = (ρ * E).trace
```
- **hypotheses (0):**
  *(none)*
- **data binders (2):** `d`, `m`

### `QIQTH.GleasonSelector.positive_ray_certain_forces_born`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
w E = QIQTH.GleasonSelector.born ψ E
```
- **hypotheses (8):**
```
1. hψ : star ψ ⬝ᵥ ψ = 1
2. hadd : ∀ (A B : Matrix n n ℂ), w (A + B) = w A + w B
3. hhom : ∀ (c : ℂ) (A : Matrix n n ℂ), w (c • A) = c * w A
4. hpsd : ∀ (A : Matrix n n ℂ), QIQTH.GleasonSelector.NonnegC (w (A.conjTranspose * A))
5. hP_herm : (Matrix.vecMulVec ψ (star ψ)).conjTranspose = Matrix.vecMulVec ψ (star ψ)
6. hP_idem : Matrix.vecMulVec ψ (star ψ) * Matrix.vecMulVec ψ (star ψ) = Matrix.vecMulVec ψ (star ψ)
7. hray : w (Matrix.vecMulVec ψ (star ψ)) = 1
8. hone : w 1 = 1
```
- **data binders (6):** `n`, `inst._@.QIQTH.GleasonSelector.2607588966._hygCtx._hyg.3`, `inst._@.QIQTH.GleasonSelector.2607588966._hygCtx._hyg.6`, `ψ`, `w`, `E`

### `QIQTH.RefinementBorn.continuous_additive_fMeasure_eq_born`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
QIQTH.RefinementBorn.fMeasure (⇑f) w k = w k
```
- **hypotheses (3):**
```
1. hf : Continuous ⇑f
2. h1 : f 1 ≠ 0
3. hsum : ∑ j, w j = 1
```
- **data binders (4):** `n`, `f`, `w`, `k`

### `QIQTH.RecordGleason.decoherent_partition_additive`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
QIQTH.GleasonSelector.born ψ ((∑ a ∈ S, C a).conjTranspose * ∑ a ∈ S, C a) =
  ∑ a ∈ S, QIQTH.GleasonSelector.born ψ ((C a).conjTranspose * C a)
```
- **hypotheses (1):**
```
1. hdec : QIQTH.RecordGleason.Decoherent ψ C
```
- **data binders (8):** `n`, `inst._@.QIQTH.RecordGleason.3777836625._hygCtx._hyg.3`, `inst._@.QIQTH.RecordGleason.3777836625._hygCtx._hyg.6`, `ψ`, `ι`, `inst._@.QIQTH.RecordGleason.3777836625._hygCtx._hyg.22`, `C`, `S`

### `QIQTH.BornJoin.ActualEnsemble.finite_noCollapseBornRepresentation`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
(∀ (ω : E.Ω), ∃! h, ∀ (t : Fin n), ∃ r ∈ (E.V ω t).config.active, (E.V ω t).ctx.valueOf r = h t) ∧
  (∀ (h : Fin n → Fin m), E.P.massSet {ω | E.actualHist ω = h} = QIQTH.BornTypicalityFinite.w E.p h) ∧
    E.P.massSet {ω | (↑n * ε) ^ 2 ≤ (QIQTH.BornTypicalityFinite.count k (E.actualHist ω) - ↑n * E.p k) ^ 2} ≤
      E.p k * (1 - E.p k) / (↑n * ε ^ 2)
```
- **hypotheses (2):**
```
1. hε : 0 < ε
2. hn : 0 < n
```
- **data binders (5):** `m`, `n`, `E`, `k`, `ε`

### `QIQTH.BornMeasureUniqueness.product_born_measure_unique`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
μ S = ((QIQTH.BornTypicalityQuantum.kronN fun x => ρ) * QIQTH.BornTypicalityQuantum.eventEffect E S).trace.re
```
- **hypotheses (5):**
```
1. hρ : ρ.PosSemidef
2. hE : ∀ (k : Fin m), (E k).PosSemidef
3. hμ0 : μ ∅ = 0
4. hμins : ∀ (a : Fin n → Fin m) (S : Finset (Fin n → Fin m)), a ∉ S → μ (insert a S) = μ {a} + μ S
5. hpt : ∀ (ω : Fin n → Fin m), μ {ω} = ∏ t, QIQTH.BornTypicalityQuantum.bornProb ρ E (ω t)
```
- **data binders (7):** `n`, `d`, `m`, `ρ`, `E`, `μ`, `S`

### `QIQTH.BornTypicalityFinite.chebyshev_freq`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
∑ ω with (↑N * ε) ^ 2 ≤ (QIQTH.BornTypicalityFinite.count k ω - ↑N * p k) ^ 2, QIQTH.BornTypicalityFinite.w p ω ≤
  p k * (1 - p k) / (↑N * ε ^ 2)
```
- **hypotheses (4):**
```
1. hp : ∀ (i : Fin m), 0 ≤ p i
2. hp1 : ∑ i, p i = 1
3. hε : 0 < ε
4. hN : 0 < N
```
- **data binders (5):** `m`, `N`, `p`, `k`, `ε`

### `QIQTH.BornTypicality.qiqth_born_typicality_conditional`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
QIQTH.BornTypicality.expectedIndicator outcome M.μ k = c k ^ 2
```
- **hypotheses (0):**
  *(none)*
- **data binders (8):** `Γ`, `Outcome`, `inst._@.QIQTH.BornTypicality.2233249802._hygCtx._hyg.4`, `inst._@.QIQTH.BornTypicality.2233249802._hygCtx._hyg.7`, `outcome`, `c`, `M`, `k`

### `QIQTH.NoBornFromNothing.born_distribution_realizable_conditional`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
∃ μ,
  (∀ (γ : Γ), 0 ≤ μ γ) ∧ ∑ γ, μ γ = 1 ∧ ∀ (k : Outcome), QIQTH.NoBornFromNothing.outcomeMarginal outcome μ k = c k ^ 2
```
- **hypotheses (3):**
```
1. h_surj : Function.Surjective outcome
2. hc_nn_sq : ∀ (k : Outcome), 0 ≤ c k ^ 2
3. hc_norm : ∑ k, c k ^ 2 = 1
```
- **data binders (6):** `Γ`, `Outcome`, `inst._@.QIQTH.NoBornFromNothing.2276587801._hygCtx._hyg.4`, `inst._@.QIQTH.NoBornFromNothing.2276587801._hygCtx._hyg.7`, `outcome`, `c`

### `QIQTH.NoConcentration.decoherence_does_not_concentrate`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
0 < QIQTH.NoConcentration.branchWeight c 0 ∧ 0 < QIQTH.NoConcentration.branchWeight c 1
```
- **hypotheses (2):**
```
1. h0 : c 0 ≠ 0
2. h1 : c 1 ≠ 0
```
- **data binders (1):** `c`

### `QIQTH.EquivarianceGap.support_preservation_does_not_imply_measure_preservation`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
∃ T μ,
  Function.Bijective T ∧
    QIQTH.EquivarianceGap.SupportPreserving Set.univ T ∧ ¬QIQTH.EquivarianceGap.MeasurePreserving T μ
```
- **hypotheses (0):**
  *(none)*
- **data binders (0):** *(none)*

### `QIQTH.OperationalNoGo.operational_data_insufficient`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
∃ outcome ν₁ ν₂,
  (∀ (k : Fin 2), QIQTH.OperationalNoGo.marginal3to2 ν₁ outcome k = QIQTH.OperationalNoGo.marginal3to2 ν₂ outcome k) ∧
    ν₁ ≠ ν₂
```
- **hypotheses (0):**
  *(none)*
- **data binders (0):** *(none)*

## Current state (factual)
- Theorems present: **13/13**
- All axiom-free: **YES**
- Total Prop-hypotheses across the spine: **32**
- Per-theorem hypothesis counts: `finite_noCollapseBorn_fromNoncontextuality`=4, `finite_effect_gleason`=0, `positive_ray_certain_forces_born`=8, `continuous_additive_fMeasure_eq_born`=3, `decoherent_partition_additive`=1, `finite_noCollapseBornRepresentation`=2, `product_born_measure_unique`=5, `chebyshev_freq`=4, `qiqth_born_typicality_conditional`=0, `born_distribution_realizable_conditional`=3, `decoherence_does_not_concentrate`=2, `support_preservation_does_not_imply_measure_preservation`=0, `operational_data_insufficient`=0
